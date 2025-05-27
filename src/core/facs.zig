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

pub fn deduceAlphaImplication(allocator: Allocator, implication_list: std.ArrayList(Implication)) !std.HashMap(*Node, std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage), Node.NodeContext, std.hash_map.default_max_load_percentage) {
    var combined_implications = std.ArrayList(Implication).init(allocator);
    defer {
        for (combined_implications.items) |impl| impl.deinit(allocator);
        combined_implications.deinit();
    }

    for (implication_list.items) |impl|
        try combined_implications.append(.{ .from = impl.from.acquire(), .to = impl.to.acquire() });

    for (implication_list.items) |impl| {
        const not_to = try logic.createNot(allocator, impl.to);
        defer not_to.release(allocator);
        const not_from = try logic.createNot(allocator, impl.from);
        defer not_from.release(allocator);

        try combined_implications.append(.{ .from = not_to, .to = not_from });
    }

    var full_implications = try transitiveClosure(allocator, combined_implications);
    defer {
        var it = full_implications.iterator();
        while (it.next()) |entry| {
            entry.key_ptr.to.release(allocator);
            entry.key_ptr.from.release(allocator);
        }
        full_implications.deinit();
    }

    var res = std.HashMap(*Node, std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage), Node.NodeContext, std.hash_map.default_max_load_percentage).init(allocator);
    errdefer {
        var it = res.iterator();
        while (it.next()) |entry| {
            entry.key_ptr.*.release(allocator);
            var inner_map = entry.value_ptr.*;
            var inner_it = inner_map.iterator();
            while (inner_it.next()) |inner_entry| {
                inner_entry.key_ptr.*.release(allocator);
            }
            inner_map.deinit();
        }
        res.deinit();
    }

    var full_impl_it = full_implications.iterator();
    while (full_impl_it.next()) |entry| {
        const a = entry.key_ptr.from;
        const b = entry.key_ptr.to;

        if (a.eqlNodes(b)) continue;

        var innet_set_ptr = res.getPtr(a);
        if (innet_set_ptr == null) {
            var new_set = std.HashMap(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage).init(allocator);
            try new_set.put(b.acquire(), {});
            try res.put(a.acquire(), new_set);
        } else {
            try innet_set_ptr.?.put(b.acquire(), {});
        }
    }

    var res_it = res.iterator();
    while (res_it.next()) |entry| {
        const a = entry.key_ptr.*;
        var impl_set = entry.value_ptr.*;


    }

}
