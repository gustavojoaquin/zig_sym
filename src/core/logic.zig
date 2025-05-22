const std = @import("std");
const Allocator = std.mem.Allocator;
const eql = std.mem.eql;
const Order = std.math.Order;

const LogicError = error{ InvalidArguments, CustomAllocationFailure };

fn is_newly_allocated_by_create_not(returned_node: *const LogicNode, original_arg_to_not: *const LogicNode) bool {
    if (returned_node.* == .True or returned_node.* == .False) {
        return false;
    }
    if (original_arg_to_not.* == .Not and returned_node == original_arg_to_not.Not) {
        return false;
    }
    return true;
}

/// Represents a fuzzy boolean value: True, False, or Unknown (null).
pub const FuzzyBool = ?bool;

/// Returns True if all args are True, False if they are all False, else None.
///
/// Args:
///     args: A slice of FuzzyBool values.
///
/// Returns:
///     True if all args are true.
///     False if all args are false.
///     None if there is any None, or if there are both True and False values.
pub fn torf(args: []const FuzzyBool) FuzzyBool {
    var saw_true = false;
    var saw_false = false;
    for (args) |a| {
        if (a) |val| {
            if (val) {
                if (saw_false) return null;
                saw_true = true;
            } else {
                if (saw_true) return null;
                saw_false = true;
            }
        } else {
            return null;
        }
    }
    return saw_true;
}

/// Checks if a group of fuzzy boolean values is consistent.
/// Returns True if all args are True, None if there is any None,
/// else False (unless `quick_exit` is true and more than one False is seen).
///
/// Args:
///     args: A slice of FuzzyBool values.
///     quick_exit: If true, returns None as soon as a second False is seen.
///
/// Returns:
///     True if all args are true.
///     None if there is any None, or if `quick_exit` is true and more than one False is seen.
///     False otherwise (all args are True or False, and at most one False if quick_exit is true).
pub fn fuzzyGroup(args: []const FuzzyBool, quick_exit: bool) FuzzyBool {
    var saw_other = false;
    for (args) |a| {
        if (a) |val| {
            if (!val) {
                if (quick_exit and saw_other) return null;
                saw_other = true;
            }
        } else {
            return null;
        }
    }
    return !saw_other;
}

/// Converts a value to FuzzyBool.
///
/// Returns True or False for boolean values, None for optional null,
/// and None for any other type.
///
/// Args:
///     x: The value to convert.
///
/// Returns:
///     The FuzzyBool representation.
pub fn fuzzyBool(x: anytype) FuzzyBool {
    return switch (@typeInfo(@TypeOf(x))) {
        .Optional => |opt| {
            if (opt.child == bool) x else null;
        },
        .Bool => @as(bool, x),
        else => null,
    };
}

/// Performs fuzzy AND operation.
/// Returns True if all args are True, False if any arg is False, else None.
///
/// Args:
///     args: A slice of FuzzyBool values.
///
/// Returns:
///     True if all args are true.
///     False if any arg is false.
///     None otherwise (mixture of True/False and None, or only None).
pub fn fuzzyAnd(args: []const FuzzyBool) FuzzyBool {
    var result: FuzzyBool = true;
    for (args) |a| {
        if (a) |val| {
            if (!val) return false;
        } else {
            result = null;
        }
    }
    return result;
}

/// Performs fuzzy NOT operation.
/// Returns None if `v` is None, else `!v`.
///
/// Args:
///     v: The FuzzyBool value.
///
/// Returns:
///     The negated FuzzyBool value.
pub fn fuzzyNot(v: FuzzyBool) FuzzyBool {
    return if (v) |val| !val else null;
}

/// Performs fuzzy OR operation.
/// Returns True if any arg is True, False if all args are False, else None.
///
/// Args:
///     args: A slice of FuzzyBool values.
///
/// Returns:
///     True if any arg is true.
///     False if all args are false.
///     None otherwise (mixture of True/False and None, or only None).
pub fn fuzzyOr(args: []const FuzzyBool) FuzzyBool {
    var result: FuzzyBool = false;
    for (args) |a| {
        if (a) |val| {
            if (val) return true;
        } else {
            if (result == false) result = null;
        }
    }
    return result;
}

/// Performs fuzzy XOR operation.
/// Returns None if any arg is None, else True (odd number of True) or False (even number of True).
///
/// Args:
///     args: A slice of FuzzyBool values.
///
/// Returns:
///     True if there's an odd number of true args and no None.
///     False if there's an even number of true args and no None.
///     None if any arg is None.
pub fn fuzzyXor(args: []const FuzzyBool) FuzzyBool {
    var count: u32 = 0;
    for (args) |a| {
        if (a) |val| {
            if (val) count += 1;
        } else {
            return null;
        }
    }
    return (count % 2) == 1;
}

/// Performs fuzzy NAND operation.
/// Equivalent to fuzzyNot(fuzzyAnd(args)).
///
/// Args:
///     args: A slice of FuzzyBool values.
///
/// Returns:
///     False if all args are true.
///     True if all args are false.
///     None otherwise.
pub fn fuzzyNand(args: []const FuzzyBool) FuzzyBool {
    return fuzzyNot(fuzzyAnd(args));
}

pub const Node = struct {
    logic_node: LogicNode,
    ref_count: std.atomic.Value(usize),

    pub fn acquire(self: *Node) *Node {
        _ = self.ref_count.fetchAdd(1, .monotonic);
        return self;
    }
    pub fn release(self: *Node, allocator: Allocator) void {
        if (self.ref_count.fetchSub(1, .release) == 1) {
            freeNodeContent(allocator, &self.logic_node);
            allocator.destroy(self);
        }
    }

    /// Helper function to get the variant tag as a comptime_int for sorting by type.
    pub fn getTagInt(node: *Node) u32 {
        return @intFromEnum(node.*);
    }

    /// Performs a structural comparison between two LogicNodes.
    /// Needed for equality checks in HashMaps and canonical sorting.
    /// Returns .lt if a < b, .gt if a > b, .eq if a == b.
    pub fn compareNodes(_: void, a: *const Node, b: *const Node) Order {
        if (a == b) return .eq;
        const tag_order = std.math.order(@intFromEnum(a.logic_node), @intFromEnum(b.logic_node));

        if (tag_order != .eq) return tag_order;

        return switch (a.logic_node) {
            .True, .False => .eq,
            .Symbol => |s1| std.mem.order(u8, s1, b.logic_node.Symbol),
            .Not => compareNodes({}, a.logic_node.Not, b.logic_node.Not),
            .And => |a_and| {
                const b_and = b.logic_node.And;
                const len_order = std.math.order(a_and.args.len, b_and.args.len);
                if (len_order != .eq) return len_order;
                for (a_and.args, 0..) |arg_a, i| {
                    const arg_order = compareNodes({}, arg_a, b_and.args[i]);
                    if (arg_order != .eq) return arg_order;
                }
                return .eq;
            },
            .Or => |a_or| {
                const b_or = b.logic_node.Or;
                const len_order = std.math.order(a_or.args.len, b_or.args.len);
                if (len_order != .eq) return len_order;
                for (a_or.args, 0..) |arg_a, i| {
                    const arg_order = compareNodes({}, arg_a, b_or.args[i]);
                    if (arg_order != .eq) return arg_order;
                }
                return .eq;
            },
        };
    }

    /// Adapter function for sorting functions like std.mem.sort that require a
    /// boolean "less than" comparator.
    /// Returns true if lhs is strictly less than rhs, false otherwise.
    fn lessThanNodes(context: void, lhs: *const Node, rhs: *const Node) bool {
        return compareNodes(context, lhs, rhs) == .lt;
    }

    /// Context for HashMap to use structural hashing and equality.
    pub const NodeContext = struct {
        pub fn hash(_: NodeContext, key: *const Node) u64 {
            var hasher = std.hash.Wyhash.init(0);
            key.deepHashNodes(&hasher);
            return hasher.final();
        }
        pub fn eql(_: NodeContext, a: *const Node, b: *const Node) bool {
            return a.eqlNodes(b);
        }
    };

    /// Performs a structural hash of a LogicNode.
    /// Needed for HashMap keys. Must be consistent with eqlNodes.
    pub fn deepHashNodes(self: *const Node, hasher: *std.hash.Wyhash) void {
        hasher.update(@tagName(self.logic_node));

        switch (self.logic_node) {
            .True, .False => {},
            .Symbol => |s| hasher.update(s),
            .Not => self.logic_node.Not.deepHashNodes(hasher),
            .And => |a| {
                for (a.args) |arg| {
                    arg.deepHashNodes(hasher);
                }
            },
            .Or => |o| {
                for (o.args) |arg| {
                    arg.deepHashNodes(hasher);
                }
            },
        }
    }

    /// Performs a structural comparison between two LogicNodes.
    /// Needed for sorting and equality checks in HashMaps.
    pub fn eqlNodes(self: *const Node, other: *const Node) bool {
        const tag_a = self.logic_node;
        const tag_b = other.logic_node;
        if (@intFromEnum(tag_a) != @intFromEnum(tag_b)) return false;

        return switch (tag_a) {
            .True, .False => true,
            .Symbol => |s_a| eql(u8, s_a, other.logic_node.Symbol),
            .Not => self.logic_node.Not.eqlNodes(other.logic_node.Not),
            .And => |a_and| {
                const b_and = other.logic_node.And;
                if (a_and.args.len != b_and.args.len) return false;
                for (a_and.args, 0..) |arg_a, i| {
                    if (!arg_a.eqlNodes(b_and.args[i])) return false;
                }
                return true;
            },
            .Or => |a_or| {
                const b_or = other.logic_node.Or;

                if (a_or.args.len != b_or.args.len) return false;
                for (a_or.args, 0..) |arg_a, i| {
                    if (!arg_a.eqlNodes(b_or.args[i])) return false;
                }
                return true;
            },
        };
    }

    /// Converts the LogicNode to a string representation.
    /// Allocates memory for the string using the provided allocator.
    pub fn toString(self: *const Node, allocator: Allocator) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure, InvalidSyntax }![]const u8 {
        return switch (self.logic_node) {
            .True => allocator.dupe(u8, "True"),
            .False => allocator.dupe(u8, "False"),
            // .Symbol => |s| s,
            .Symbol => allocator.dupe(u8, self.logic_node.Symbol),
            // .Not => |arg| try std.fmt.allocPrint(allocator, "{!s}", .{try arg.toString(allocator)}),
            .Not => |arg| {
                const arg_str = try arg.toString(allocator);
                defer allocator.free(arg_str);
                return std.fmt.allocPrint(allocator, "!{s}", .{arg_str});
            },
            .And => |args| {
                var parts = std.ArrayList([]const u8).init(allocator);
                defer parts.deinit();

                for (args.args) |arg| {
                    try parts.append(try arg.toString(allocator));
                }
                defer {
                    for (parts.items) |part| allocator.free(part);
                }

                const joined = std.mem.join(allocator, " & ", parts.items);
                defer allocator.free(joined);
                return std.fmt.allocPrint(allocator, "({s})", .{joined});
            },
            .Or => |args| {
                var parts = std.ArrayList([]const u8).init(allocator);
                defer parts.deinit();

                for (args.args) |arg| {
                    try parts.append(try arg.toString(allocator));
                }

                defer {
                    for (parts.items) |part| allocator.free(part);
                }

                const joined = std.mem.join(allocator, " | ", parts.items);
                defer allocator.free(joined);
                return std.fmt.allocPrint(allocator, "({s})", .{joined});
            },
        };
    }

    /// Applies the distributive property: (A | B) & C -> (A & C) | (B & C).
    /// This method is recursive and tries to push ORs up past ANDs.
    /// For other node types (Or, Not, Symbol, True, False), it returns the node itself.
    ///
    /// Args:
    ///     allocator: The allocator to use for creating new nodes.
    ///
    /// Returns:
    ///     A pointer to the resulting LogicNode. This node is owned by the caller
    ///     unless it is the original node or a global singleton.
    pub fn expand(self: *const Node, allocator: Allocator) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure, InvalidSyntax }!*Node {
        return switch (self.logic_node) {
            .Or, .Not, .Symbol, .True, .False => self.acquire(),
            .And => |and_node| {
                var expanded_children = std.ArrayList(*Node).init(allocator);
                defer {
                    for (expanded_children.items) |node| node.release(allocator);
                    expanded_children.deinit();
                }

                var any_child_expanded = false;
                var or_arg_index: ?usize = null;
                var or_node_to_distribute: ?*Node = null;

                for (and_node.args) |arg| {
                    const expanded_arg = try arg.expand(allocator);
                    if (expanded_arg != arg) any_child_expanded = true;
                    try expanded_children.append(expanded_arg);

                    if (expanded_arg.* == .Or and or_node_to_distribute == null) {
                        or_arg_index = expanded_children.items.len - 1;
                        or_node_to_distribute = expanded_arg;
                    }
                }

                if (or_node_to_distribute) |or_node_to_distribute_val| {
                    const or_index = or_arg_index.?;
                    var rest_arg_list = std.ArrayList(*Node).init(allocator);
                    defer {
                        for (rest_arg_list.items) |node| node.release(allocator);
                        rest_arg_list.deinit();
                    }

                    for (expanded_children.items, 0..) |exp_arg, i| {
                        if (i != or_index) {
                            try rest_arg_list.append(exp_arg.acquire());
                        }
                    }

                    expanded_children.items = &.{};

                    var distributed_or_args_list = std.ArrayList(*Node).init(allocator);
                    defer {
                        for (distributed_or_args_list.items) |node| node.release(allocator);
                        distributed_or_args_list.deinit();
                    }

                    for (or_node_to_distribute_val.logic_node.Or.args) |or_term| {
                        var new_and_arg_term_list = std.ArrayList(*Node).init(allocator);
                        defer {
                            for (new_and_arg_term_list.items) |node| node.release(allocator);
                            new_and_arg_term_list.deinit();
                        }

                        try new_and_arg_term_list.append(or_term.acquire());
                        for (rest_arg_list.items) |rest_arg| try new_and_arg_term_list.append(rest_arg.acquire());

                        const new_and_node = try createAnd(allocator, new_and_arg_term_list.items);
                        const expanded_new_and = try new_and_node.expand(allocator);

                        if (expanded_new_and != new_and_node) new_and_node.release(allocator);

                        try distributed_or_args_list.append(expanded_new_and);
                        new_and_arg_term_list.items = &.{};
                    }

                    self.release(allocator);
                    or_node_to_distribute_val.release(allocator);

                    const final_or_node = try createOr(allocator, distributed_or_args_list);
                    distributed_or_args_list.items = &.{};
                    return final_or_node;
                } else if (any_child_expanded) {
                    self.release(allocator);
                    const result = try createAnd(allocator, expanded_children.items);
                    expanded_children.items = &.{};
                    return result;
                } else {
                    return self.acquire();
                }
            },
        };
    }
};

/// Represents a logical expression node.
/// This is a tagged union representing the different types of nodes
/// in the logic expression tree.
pub const LogicNode = union(enum) {
    /// A conjunction (AND) of arguments. Arguments are sorted for canonical form.
    And: struct { args: []const *Node },
    /// A disjunction (OR) of arguments. Arguments are sorted for canonical form.
    Or: struct { args: []const *Node },
    /// A symbolic variable or proposition
    Symbol: []const u8,
    /// A negation (NOT) of a single argument.
    Not: *Node,
    True,
    False,
};

/// Helper to free memory *inside* LogicNode, but not the Node wrapper itself.
fn freeNodeContent(allocator: Allocator, logic_node: *LogicNode) void {
    switch (logic_node.*) {
        .Symbol => |s| allocator.free(s),
        .Not => |n| n.release(allocator),
        .And => |a| {
            for (a.args) |arg| arg.release(allocator);
            allocator.free(a.args);
        },
        .Or => |o| {
            for (o.args) |arg| arg.release(allocator);
            allocator.free(o.args);
        },
        .True, .False => {},
    }
}

/// Parses a logic expression string.
///
/// Accepts a simple format like `!a & b | c` with spaces around `&` and `|`,
/// and no space after `!`. Follows left-to-right operator precedence.
///
/// Args:
///     allocator: The allocator to use for creating nodes.
///     text: The input string.
///
/// Returns:
///     A pointer to the resulting LogicNode. The caller is responsible for freeing
///     this node using `freeNode`. Returns an error if parsing fails.
pub fn fromString(allocator: Allocator, text: []const u8) error{ OutOfMemory, InvalidSyntax, CustomAllocationFailure, InvalidArguments }!*Node {
    var tokens = std.mem.splitAny(u8, text, " &|()");
    var lexpr: ?*Node = null;
    var schedop: ?enum { And, Or } = null;

    while (tokens.next()) |token| {
        var current_node: ?*Node = null;

        if (eql(u8, token, "&")) {
            if (schedop == null) return error.InvalidSyntax;
            if (lexpr == null) return error.InvalidSyntax;
            schedop = .And;
            continue;
        } else if (eql(u8, token, "|")) {
            if (schedop == null) return error.InvalidSyntax;
            if (lexpr == null) return error.InvalidSyntax;
            schedop = .Or;
            continue;
        } else if (token.len > 0 and token[0] == '!') {
            if (token.len == 1) return error.InvalidSyntax;
            if (lexpr != null and schedop == null) return error.InvalidSyntax;

            const symbol_name = token[1..];
            const symbol_node = try createSymbol(allocator, symbol_name);

            const not_node = try createNot(allocator, symbol_node);
            current_node = not_node;
        } else {
            if (lexpr != null and schedop == null) return error.InvalidSyntax;
            const symbol_name = token;
            const symbol_node = try createSymbol(allocator, symbol_name);
            current_node = symbol_node;
        }

        if (schedop) |op| {
            if (lexpr == null or current_node == null) return error.InvalidSyntax;

            var new_expr: *Node = undefined;
            if (op == .And) {
                const args_slice = [_]*Node{ lexpr.?, current_node.? };
                new_expr = try createAnd(allocator, &args_slice);
            } else {
                const arg_slice = [_]*Node{ lexpr.?, current_node.? };
                new_expr = try createOr(allocator, &arg_slice);
            }

            lexpr.?.release(allocator);
            current_node.?.release(allocator);

            lexpr = new_expr;
            schedop = null;
        } else {
            if (lexpr != null) return error.InvalidSyntax;
            if (current_node == null) return error.InvalidSyntax;

            lexpr = current_node;
        }
    }

    if (schedop == null) return error.InvalidSyntax;
    if (lexpr != null) return error.InvalidSyntax;

    return lexpr.?;
}

/// Creates an And node, applying simplification and flattening rules.
/// Flattens nested Ands: And(A, And(B, C)) -> And(A, B, C)
/// Removes duplicates: And(A, A) -> A
/// Removes True: And(A, True) -> A
/// Handles False: And(A, False) -> False
/// Handles negation: And(A, !A) -> False
/// Sorts arguments canonically.
///
/// Args:
///     allocator: The allocator to use for new nodes and temporary structures.
///     args: A slice of nodes to conjoin. These nodes are NOT owned by this function;
///           they are expected to be either global singletons, original symbols,
///           or nodes already owned by the caller or another structure.
///
/// Returns:
///     A pointer to the resulting LogicNode. This node is owned by the caller
///     unless it is one of the global singletons (TrueNode, FalseNode).
pub fn createAnd(allocator: Allocator, args: []const *Node) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*Node {
    var flattened_list = std.ArrayList(*Node).init(allocator);
    defer {
        for (flattened_list.items) |node| node.release(allocator);
        flattened_list.deinit();
    }

    for (args) |arg| try flattenAndOr(allocator, arg, .{ .And = .{ .args = &.{} } }, &flattened_list);

    var unique_map = std.HashMapUnmanaged(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage){};

    for (flattened_list.items) |arg| {
        switch (arg.logic_node) {
            .False => {
                var it = unique_map.iterator();
                while (it.next()) |entry| entry.key_ptr.*.release(allocator);
                unique_map.deinit(allocator);
                return createFalse(allocator);
            },
            .True => {
                continue;
            },
            else => {},
        }

        const not_arg_for_check = try createNot(allocator, arg.acquire());
        defer not_arg_for_check.release(allocator);

        if (unique_map.contains(not_arg_for_check)) {
            var it = unique_map.iterator();
            while (it.next()) |entry| entry.key_ptr.*.release(allocator);
            unique_map.deinit(allocator);
            return try createFalse(allocator);
        }

        if (!unique_map.contains(arg)) {
            try unique_map.put(allocator, arg.acquire(), {});
        }
    }

    var unique_args_list = std.ArrayList(*Node).init(allocator);
    var it = unique_map.iterator();
    while (it.next()) |entry| {
        try unique_args_list.append(entry.key_ptr.*);
    }
    unique_map.deinit(allocator);

    if (unique_args_list.items.len == 0) {
        unique_args_list.deinit();
        return try createTrue(allocator);
    }
    if (unique_args_list.items.len == 1) {
        const result = unique_args_list.items[0];
        unique_args_list.deinit();
        return result;
    }

    std.mem.sort(*Node, unique_args_list.items, {}, Node.lessThanNodes);

    const final_args_slice = try unique_args_list.toOwnedSlice();

    const node_wrapper = try allocator.create(Node);
    errdefer {
        for (final_args_slice) |node| node.release(allocator);
        allocator.free(final_args_slice);
        allocator.destroy(node_wrapper);
    }
    node_wrapper.logic_node = .{ .And = .{ .args = final_args_slice } };
    node_wrapper.ref_count = std.atomic.Value(usize).init(1);
    return node_wrapper;
}

/// Creates an Or node, applying simplification and flattening rules.
/// Flattens nested Ors: Or(A, Or(B, C)) -> Or(A, B, C)
/// Removes duplicates: Or(A, A) -> A
/// Removes False: Or(A, False) -> A
/// Handles True: Or(A, True) -> True
/// Handles negation: Or(A, !A) -> True
/// Sorts arguments canonically.
///
/// Args:
///     allocator: The allocator to use for new nodes and temporary structures.
///     args: A slice of nodes to disjoin. These nodes are NOT owned by this function;
///           they are expected to be either global singletons, original symbols,
///           or nodes already owned by the caller or another structure.
///
/// Returns:
///     A pointer to the resulting LogicNode. This node is owned by the caller
///     unless it is one of the global singletons (TrueNode, FalseNode).
pub fn createOr(allocator: Allocator, args: []const *Node) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*Node {
    var flattened_list = std.ArrayList(*Node).init(allocator);
    defer {
        for (flattened_list.items) |node_items| node_items.release(allocator);
        flattened_list.deinit();
    }

    for (args) |arg| try flattenAndOr(allocator, arg, .{ .Or = .{ .args = &.{} } }, &flattened_list);

    var unique_map = std.HashMapUnmanaged(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage){};
    defer unique_map.deinit(allocator);

    for (flattened_list.items) |arg| {
        switch (arg.logic_node) {
            .True => {
                var it = unique_map.iterator();
                while (it.next()) |entry| entry.key_ptr.*.release(allocator);
                arg.release(allocator);
                return try createTrue(allocator);
            },
            .False => {
                arg.release(allocator);
                continue;
            },
            else => {},
        }

        const not_arg_for_check = try createNot(allocator, arg.acquire());
        defer not_arg_for_check.release(allocator);

        if (unique_map.contains(not_arg_for_check)) {
            var it = unique_map.iterator();
            while (it.next()) |entry| entry.key_ptr.*.release(allocator);
            arg.release(allocator);
            return try createTrue(allocator);
        }

        if (!unique_map.contains(arg)) try unique_map.put(allocator, arg.acquire(), {}) else arg.release(allocator);
    }
    flattened_list.items = &.{};

    var unique_args_list = std.ArrayList(*Node).init(allocator);
    defer unique_args_list.deinit();

    var it = unique_map.iterator();
    while (it.next()) |entry| try unique_args_list.append(entry.key_ptr.*);

    unique_map.clearAndFree(allocator);

    if (unique_args_list.items.len == 0) return try createFalse(allocator);
    if (unique_args_list.items.len == 1) {
        const result = unique_args_list.items[0];
        unique_args_list.items = &.{};
        return result;
    }
    std.mem.sort(*Node, unique_args_list.items, {}, Node.lessThanNodes);

    const final_args_slice = try allocator.dupe(*Node, unique_args_list.items);
    errdefer {
        for (final_args_slice) |node| node.release(allocator);
        allocator.free(final_args_slice);
    }

    unique_args_list.items = &.{};

    const node_wrapper = try allocator.create(Node);
    errdefer allocator.destroy(node_wrapper);
    node_wrapper.logic_node = .{ .Or = .{ .args = final_args_slice } };
    node_wrapper.ref_count = std.atomic.Value(usize).init(1);
    return node_wrapper;
}

/// Creates a Not node, applying simplification rules.
/// !True -> False
/// !False -> True
/// !!X -> X
/// !(A & B & ...) -> !A | !B | ... (De Morgan's)
/// !(A | B | ...) -> !A & !B & ... (De Morgan's)
///
/// Args:
///     allocator: The allocator to use for new nodes.
///     arg: The node to negate.
///
/// Returns:
///     A pointer to the resulting LogicNode. This node is owned by the caller
///     unless it is one of the global singletons (TrueNode, FalseNode) or
///     a direct reference to the original node's child (as in !!X -> X).
///     The caller should use recursiveFree if it determines the returned node is owned.
pub fn createNot(allocator: Allocator, arg: *Node) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*Node {
    defer arg.release(allocator);

    return switch (arg.logic_node) {
        .True => return try createFalse(allocator),
        .False => return try createTrue(allocator),
        .Not => {
            const child = arg.logic_node.Not;
            return child.acquire();
        },
        .And => |args| {
            var new_args_list = std.ArrayList(*Node).init(allocator);
            defer new_args_list.deinit();

            for (args.args) |child_args| {
                const negated_child = try createNot(allocator, child_args.acquire());
                try new_args_list.append(negated_child);
            }

            const result_or = try createOr(allocator, new_args_list.items);
            new_args_list.items = &.{};
            return result_or;
        },
        .Or => |args| {
            var new_and_args_list = std.ArrayList(*Node).init(allocator);
            defer new_and_args_list.deinit();

            for (args.args) |child_arg| {
                const negated_node = try createNot(allocator, child_arg.acquire());
                try new_and_args_list.append(negated_node);
            }

            const result_and = try createAnd(allocator, new_and_args_list.items);
            new_and_args_list.items = &.{};
            return result_and;
        },
        else => {
            const node = try allocator.create(Node);
            node.logic_node = .{ .Not = arg.acquire() };
            node.ref_count = std.atomic.Value(usize).init(1);
            return node;
        },
    };
}

/// Helper to recursively flatten And/Or nodes of the target type.
/// Adds non-matching nodes or flattened children to the result list.
/// Consumes `node` (releases its ref_count when done).
fn flattenAndOr(allocator: Allocator, node: *Node, target_logic: LogicNode, result_list: *std.ArrayList(*Node)) error{OutOfMemory}!void {
    defer node.release(allocator);

    const node_tag = @tagName(node.logic_node);
    const target_tag = @tagName(target_logic);

    if (std.mem.eql(u8, node_tag, target_tag)) {
        const children = switch (node.logic_node) {
            .And => node.logic_node.And.args,
            .Or => node.logic_node.Or.args,
            else => unreachable,
        };
        for (children) |child_arg| try flattenAndOr(allocator, child_arg.acquire(), target_logic, result_list);
    } else try result_list.append(node.acquire());
}

/// Creates a Symbol node.
/// Allocates memory for the node and duplicates the symbol name.
/// The caller is responsible for freeing the returned node using recursiveFree.
pub fn createSymbol(allocator: Allocator, name: []const u8) !*Node {
    const name_copy = try allocator.dupe(u8, name);
    errdefer allocator.free(name_copy);

    const node_wrapper = try allocator.create(Node);
    errdefer allocator.destroy(node_wrapper);

    node_wrapper.logic_node = .{ .Symbol = name_copy };
    node_wrapper.ref_count = std.atomic.Value(usize).init(1);
    return node_wrapper;
}

/// Creates a LogicNode representing True.
pub fn createTrue(allocator: Allocator) !*Node {
    const node = try allocator.create(Node);
    errdefer allocator.destroy(node);

    node.logic_node = .{ .True = {} };
    node.ref_count = std.atomic.Value(usize).init(1);
    return node;
}

/// Creates a LogicNode representing False.
pub fn createFalse(allocator: Allocator) !*Node {
    const node = try allocator.create(Node);
    errdefer allocator.destroy(node);
    node.logic_node = .{ .True = {} };
    node.ref_count = std.atomic.Value(usize).init(1);
    return node;
}
