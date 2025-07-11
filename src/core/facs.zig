const std = @import("std");
const logic = @import("logic.zig");
const Node = logic.Node;
const LogicNode = logic.LogicNode;
const Allocator = std.mem.Allocator;

pub const FactError = error{
    TautologyDetected,
    InconsistentImplications,
    InconsistentAssumptions,
    NotAnAndCondition,
    InvalidRuleFormat,
    UnknownOperator,
    OutOfMemory,
    LogicParsingFailed,
};

pub const BetaRule = struct {
    condition: *Node,
    conclusion: *Node,
};

pub const LogicPair = struct {
    atom: *Node,
    value: bool,

    pub const Context = struct {
        pub fn hash(_: Context, key: LogicPair) u64 {
            var hasher = std.hash.Wyhash.init(0);
            key.atom.deepHashNodes(&hasher);
            hasher.update(@as(u64, @intFromBool(key.value)));
            return hasher.final();
        }
        pub fn eql(_: Context, a: LogicPair, b: LogicPair) bool {
            return a.atom.eqlNodes(b.atom) and a.value == b.value;
        }
    };

    pub fn deinit(_: LogicPair, allocator: Allocator) void {
        _ = allocator;
    }

    pub fn format(self: LogicPair, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype, allocator: Allocator) !void {
        const atom_str = try self.atom.toString(allocator);
        defer allocator.free(atom_str);

        if (self.value) {
            try writer.print("({s}: True)", .{atom_str});
        } else {
            try writer.print("({s}: False)", .{atom_str});
        }
    }
};

pub fn baseFact(atom: *Node) *Node {
    if (atom.logic_node == .Not) {
        return atom.logic_node.Not.acquire();
    } else {
        return atom.acquire();
    }
}

pub fn asPair(_: Allocator, atom: *Node) !LogicPair {
    if (atom.logic_node == .Not) {
        return .{ .atom = atom.logic_node.Not, .value = false };
    } else {
        return .{ .atom = atom, .value = false };
    }
}

pub const Implication = struct {
    from: *Node,
    to: *Node,
    pub const Context = struct {
        pub fn hash(_: Context, key: Implication) u64 {
            var hasher = std.hash.Wyhash.init(0);
            key.from.deepHashNodes(&hasher);
            key.to.deepHashNodes(&hasher);
            return hasher.final();
        }
        pub fn eql(_: Context, a: Implication, b: Implication) bool {
            return a.from.eqlNodes(b.from) and a.to.eqlNodes(b.to);
        }
    };

    pub fn deinit(self: Implication, allocator: Allocator) void {
        self.from.release(allocator);
        self.to.release(allocator);
    }
};

pub fn transitiveClosure(allocator: Allocator, initial_implications: std.ArrayList(Implication)) !std.HashMap(Implication, void, Implication.Context, std.hash_map.default_max_load_percentage) {
    var full_implications = std.HashMap(Implication, void, Implication.Context, std.hash_map.default_max_load_percentage).init(allocator);
    errdefer full_implications.deinit();

    var literals = std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage).init(allocator);
    errdefer literals.deinit();

    for (initial_implications.items) |impl| {
        try full_implications.put(.{ .to = impl.to.acquire(), .from = impl.from.acquire() }, {});
        try literals.put(impl.from.acquire(), {});
        try literals.put(impl.to.acquire(), {});
    }

    var lit_k_it = literals.iterator();

    while (lit_k_it.next()) |k_entry| {
        const k = k_entry.key_ptr.*;
        var liter_i_it = literals.iterator();
        while (liter_i_it.next()) |i_entry| {
            const i = i_entry.key_ptr.*;

            if (full_implications.contains(.{ .from = i, .to = k })) {
                var liter_j_it = literals.iterator();
                while (liter_j_it.next()) |j_entry| {
                    const j = j_entry.key_ptr.*;

                    if (full_implications.contains(.{ .from = k, .to = j })) {
                        try full_implications.put(.{ .from = i.acquire(), .to = j.acquire() }, {});
                    }
                }
            }
        }
    }

    var liter_cleanup_it = literals.iterator();
    while (liter_cleanup_it.next()) |entry| {
        entry.key_ptr.*.release(allocator);
    }

    return full_implications;
}

pub fn deduceAlphaImplication(allocator: Allocator, implication_list: std.ArrayList(Implication)) !std.AutoHashMap(*Node, std.AutoHashMap(*Node, void, Node.NodeContext)) {
    var combined_implications = std.ArrayList(Implication).init(allocator);
    defer {
        for (combined_implications.items) |impl| impl.deinit(allocator);
        combined_implications.deinit();
    }

    for (implication_list.items) |impl| {
        try combined_implications.append(.{
            .from = impl.from.acquire(),
            .to = impl.to.acquire(),
        });
    }

    for (implication_list.items) |impl| {
        const not_to = try logic.createNot(allocator, impl.to);
        defer not_to.release(allocator);
        const not_from = try logic.createNot(allocator, impl.from);
        defer not_from.release(allocator);

        try combined_implications.append(.{
            .from = not_to.acquire(),
            .to = not_from.acquire(),
        });
    }

    var full_implications = try transitiveClosure(allocator, combined_implications);
    defer {
        var it = full_implications.iterator();
        while (it.next()) |entry| {
            const key = entry.key_ptr.*;
            key.from.release(allocator);
            key.to.release(allocator);
        }
        full_implications.deinit();
    }

    var res = std.AutoHashMap(*Node, std.AutoHashMap(*Node, void, Node.NodeContext)).init(allocator);
    errdefer {
        var res_iter = res.iterator();
        while (res_iter.next()) |entry| {
            entry.key_ptr.*.release(allocator);
            var inner = entry.value_ptr.*;
            var inner_iter = inner.keyIterator();
            while (inner_iter.next()) |key| {
                key.*.release(allocator);
            }
            inner.deinit();
        }
        res.deinit();
    }

    var it = full_implications.iterator();
    while (it.next()) |entry| {
        const impl = entry.key_ptr.*;
        const a = impl.from;
        const b = impl.to;

        if (a.eqlNodes(b)) continue;

        var inner_map = res.getPtr(a) orelse blk: {
            const new_inner = std.AutoHashMap(*Node, void, Node.NodeContext).init(allocator);
            try res.put(a.acquire(), new_inner);
            break :blk res.getPtr(a).?;
        };

        try inner_map.put(b.acquire(), {});
    }

    var res_iter = res.iterator();
    while (res_iter.next()) |entry| {
        const a = entry.key_ptr.*;
        var inner_map = entry.value_ptr;

        if (inner_map.remove(a)) {
            a.release(allocator);
        }

        const na = try logic.createNot(allocator, a);
        defer na.release(allocator);

        if (inner_map.contains(na)) {
            return FactError.InconsistentImplications;
        }
    }

    return res;
}

pub fn applyBetaToAlphaRoute(
    allocator: Allocator,
    alpha_implications: *const std.AutoHashMap(*Node, std.AutoHashMap(*Node, void)),
    beta_rules: []const BetaRule,
) !std.AutoHashMap(*Node, struct {
    implications: std.AutoHashMap(*Node, void),
    beta_indices: std.ArrayList(usize),
}) {
    // Initialize the result map
    var x_impl = std.AutoHashMap(*Node, struct {
        implications: std.AutoHashMap(*Node, void),
        beta_indices: std.ArrayList(usize),
    }).init(allocator);
    errdefer {
        var iter = x_impl.iterator();
        while (iter.next()) |entry| {
            entry.key_ptr.*.release(allocator);
            entry.value_ptr.implications.deinit();
            entry.value_ptr.beta_indices.deinit();
        }
        x_impl.deinit();
    }

    var all_facts = std.AutoHashMap(*Node, void, Node.NodeContext).init(allocator);
    defer {
        var iter = all_facts.keyIterator();
        while (iter.next()) |key| key.*.release(allocator);
        all_facts.deinit();
    }

    var alpha_iter = alpha_implications.keyIterator();
    while (alpha_iter.next()) |key| {
        try all_facts.put(key.*.acquire(), .{});
    }

    for (beta_rules) |rules| {
        if (rules.condition.logic_node != .And) {
            return FactError.NotAnAndCondition;
        }

        for (rules.condition.logic_node.And.args) |arg| {
            try all_facts.put(arg.acquire(), .{});
        }
    }

    var facts_iter = all_facts.keyIterator();
    while (facts_iter.next()) |fact_ptr| {
        const fact = fact_ptr.*;
        var implications = std.AutoHashMap(*Node, void, Node.NodeContext).init(allocator);
        errdefer implications.deinit();

        var beta_indices = std.ArrayList(usize).init(allocator);
        errdefer beta_indices.deinit();

        if (alpha_implications.get(fact)) |alpha_impl| {
            var impl_iter = alpha_impl.keyIterator();
            while (impl_iter.next()) |impl| {
                try implications.put(impl.*.acquire(), {});
            }
        }

        try x_impl.put(fact.acquire(), .{
            .implications = implications,
            .beta_indices = beta_indices,
        });
    }

    var changed = true;
    while (changed) {
        changed = false;

        for (beta_rules, 0..) |rule, rule_idx| {
            _ = rule_idx;
            const bcond = rule.condition;
            const bimpl = rule.conclusion;

            if (bcond.logic_node != .And) {
                return FactError.NotAnAndCondition;
            }
            const bargs = bcond.logic_node.And.args;

            var x_impl_iter = x_impl.iterator();
            while (x_impl_iter.next()) |entry| {
                const x = entry.key_ptr.*;
                const x_data = entry.value_ptr;
                const ximpls = &x_data.implications;

                if (ximpls.contains(bimpl) or x.eqlNodes(bimpl)) {
                    continue;
                }

                var all_satisfied = true;
                for (bargs) |barg| {
                    if (!x.eqlNodes(barg) and !ximpls.contains(barg)) {
                        all_satisfied = false;
                        break;
                    }
                }

                if (all_satisfied) {
                    try ximpls.put(bimpl.acquire(), {});
                    changed = true;

                    if (x_impl.get(bimpl)) |bimpl_data| {
                        var bimpl_iter = bimpl_data.implications.keyIterator();
                        while (bimpl_iter.next()) |impl| {
                            if (!ximpls.contains(impl.*)) {
                                try ximpls.put(impl.*.acquire(), {});
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn rulesToPrereq(
    allocator: Allocator,
    rules: *const std.HashMap(LogicPair, std.HashMap(LogicPair, void, LogicPair.Context, std.hash_map.default_max_load_percentage), LogicPair.Context, std.hash_map.default_max_load_percentage),
) !std.AutoHashMap(*Node, std.HashMap(*Node, void, Node.NodeContext), Node.NodeContext, std.hash_map.default_max_load_percentage) {
    var prereq = std.HashMap(*Node, std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage), Node.NodeContext, std.hash_map.default_max_load_percentage).init(allocator);
    errdefer prereq.deinit();

    var rules_iter = rules.iterator();
    while (rules_iter.next()) |rules_entry| {
        const key_pair = rules_entry.key_ptr.*;
        const implications = rules_entry.value_ptr;

        const base_key = baseFact(key_pair.atom);
        defer if (base_key != key_pair.atom) base_key.release(allocator);

        var impl_iter = implications.keyIterator();
        while (impl_iter.next()) |impl| {
            const base_impl = baseFact(impl.atom);
            defer if (base_impl != impl.atom) base_impl.release(allocator);

            if (base_key.eqlNodes(base_impl)) continue;

            var inner_map = try prereq.getOrPut(base_impl);
            if (!inner_map.found_existing) {
                inner_map.key_ptr.* = base_impl.acquire();
                inner_map.value_ptr.* = std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage).init(allocator);
            }

            try inner_map.value_ptr.put(base_key.acquire(), .{});
        }
    }
    return prereq;
}

pub const FactRules = struct {
    allocator: Allocator,
    full_implications: std.HashMap(LogicPair, std.HashMap(LogicPair, void, LogicPair.Context, std.hash_map.default_max_load_percentage), LogicPair.Context, std.hash_map.default_max_load_percentage),
    beta_rules: std.ArrayList(struct {
        condition: std.HashMap(LogicPair, void, LogicPair.Context, std.hash_map.default_max_load_percentage),
        conclusion: LogicPair,
    }),
    beta_triggers: std.HashMap(LogicPair, std.ArrayList(usize), LogicPair.Context, std.hash_map.default_max_load_percentage),
    prereq: std.HashMap(*Node, std.HashMap(*Node, void, Node.NodeContext), Node.NodeContext, std.hash_map.default_max_load_percentage),
    defined_facts: std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage),

    pub fn compile(allocator: Allocator, alpha_rules: *const std.ArrayList(Implication), beta_rules_raw: []const BetaRule) !FactRules {
        var self: FactRules = undefined;
        self.allocator = allocator;
        self.full_implications = std.HashMap(LogicPair, std.HashMap(LogicPair, void, LogicPair.Context, std.hash_map.default_max_load_percentage), LogicPair.Context, std.hash_map.default_max_load_percentage).init(allocator);
        errdefer self.full_implications.deinit();
    }
};
