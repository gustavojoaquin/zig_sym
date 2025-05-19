const std = @import("std");
const Allocator = std.mem.Allocator;
const eql = std.mem.eql;
const Order = std.math.Order;

const LogicError = error{ InvalidArguments, CustomAllocationFailure };

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

/// Represents a logical expression node.
/// This is a tagged union representing the different types of nodes
/// in the logic expression tree.
pub const LogicNode = union(enum) {
    /// A conjunction (AND) of arguments. Arguments are sorted for canonical form.
    And: struct { args: []const *const LogicNode },
    /// A disjunction (OR) of arguments. Arguments are sorted for canonical form.
    Or: struct { args: []const *const LogicNode },
    /// A symbolic variable or proposition
    Symbol: []const u8,
    /// A negation (NOT) of a single argument.
    Not: *const LogicNode,
    /// The boolean constant True.
    True,
    /// The boolean constant False
    False,

    /// Helper function to get the variant tag as a comptime_int for sorting by type.
    pub fn getTagInt(node: *const LogicNode) u32 {
        return @intFromEnum(node.*);
    }

    /// Performs a structural comparison between two LogicNodes.
    /// Needed for sorting and equality checks in HashMaps.
    pub fn eqlNodes(a: *const LogicNode, b: *const LogicNode) bool {
        const tag_a = a.*;
        const tag_b = b.*;
        if (@intFromEnum(tag_a) != @intFromEnum(tag_b)) return false;

        return switch (tag_a) {
            .True, .False => true,
            .Symbol => |s_a| eql(u8, s_a, b.Symbol),
            .Not => eqlNodes(a.Not, b.Not),
            .And => |a_and| {
                const b_and = b.And;
                if (a_and.args.len != b_and.args.len) return false;
                for (a_and.args, 0..) |arg_a, i| {
                    if (!eqlNodes(arg_a, b_and.args[i])) return false;
                }
                return true;
            },
            .Or => |a_or| {
                const b_or = b.Or;

                if (a_or.args.len != b_or.args.len) return false;
                for (a_or.args, 0..) |arg_a, i| {
                    if (!eqlNodes(arg_a, b_or.args[i])) return false;
                }
                return true;
            },
            // .S
        };
    }

    /// Performs a structural hash of a LogicNode.
    /// Needed for HashMap keys. Must be consistent with eqlNodes.
    pub fn deepHashNodes(hasher: *std.hash.Wyhash, node: *const LogicNode) void {
        hasher.update(@tagName(node.*));

        switch (node.*) {
            .True, .False => {},
            .Symbol => |s| hasher.update(s),
            .Not => deepHashNodes(hasher, node.Not),
            .And => |a| {
                for (a.args) |arg| {
                    deepHashNodes(hasher, arg);
                }
            },
            .Or => |o| {
                for (o.args) |arg| {
                    deepHashNodes(hasher, arg);
                }
            },
        }
    }

    /// Context for HashMap to use structural hashing and equality.
    const NodeContext = struct {
        pub fn hash(_: NodeContext, key: *const LogicNode) u64 {
            var hasher = std.hash.Wyhash.init(0);
            deepHashNodes(&hasher, key);
            return hasher.final();
        }
        pub fn eql(_: NodeContext, a: *const LogicNode, b: *const LogicNode) bool {
            return eqlNodes(a, b);
        }
    };

    /// Performs a structural comparison between two LogicNodes.
    /// Needed for equality checks in HashMaps and canonical sorting.
    /// Returns .lt if a < b, .gt if a > b, .eq if a == b.
    pub fn compareNodes(_: void, a: *const LogicNode, b: *const LogicNode) Order {
        if (a == b) return .eq;
        const tag_order = std.math.order(@intFromEnum(a.*), @intFromEnum(b.*));

        if (tag_order != .eq) return tag_order;

        return switch (a.*) {
            .True, .False => .eq,
            .Symbol => |s1| std.mem.order(u8, s1, b.Symbol),
            .Not => compareNodes({}, a.Not, b.Not),
            .And => |a_and| {
                const b_and = b.And;
                const len_order = std.math.order(a_and.args.len, b_and.args.len);
                if (len_order != .eq) return len_order;
                for (a_and.args, 0..) |arg_a, i| {
                    const arg_order = compareNodes({}, arg_a, b_and.args[i]);
                    if (arg_order != .eq) return arg_order;
                }
                return .eq;
            },
            .Or => |a_or| {
                const b_or = b.Or;
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
    fn lessThanNodes(context: void, lhs: *const LogicNode, rhs: *const LogicNode) bool {
        return compareNodes(context, lhs, rhs) == .lt;
    }
    /// Converts the LogicNode to a string representation.
    /// Allocates memory for the string using the provided allocator.
    pub fn toString(self: *const LogicNode, allocator: Allocator) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure, InvalidSyntax }![]const u8 {
        return switch (self.*) {
            .True => allocator.dupe(u8, "True"),
            .False => allocator.dupe(u8, "False"),
            // .Symbol => |s| s,
            .Symbol => allocator.dupe(u8, self.Symbol),
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
                // defer {
                //     for (parts.items) |part| allocator.free(part);
                //     parts.deinit();
                // }

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
    pub fn expand(self: *const LogicNode, allocator: Allocator) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure, InvalidSyntax }!*const LogicNode {
        // NOTE: Memory management in expand is tricky. If expansion creates a new
        // node different from `self`, and `self` was dynamically allocated,
        // `self` needs to be freed by the caller.
        // The nodes returned by recursive expand calls are owned by this scope
        // temporarily and either used in the final structure or discarded.
        // The create* functions handle freeing their immediate internal temps.
        return switch (self.*) {
            .Or, .Not, .Symbol, .True, .False => self,
            .And => |and_node| {
                var expanded_children = std.ArrayList(*const LogicNode).init(allocator);
                defer expanded_children.deinit();

                var any_child_expanded = false;
                var or_arg_index: ?usize = null;
                var or_node_to_distribute: ?*const LogicNode = null;

                for (and_node.args, 0..) |arg, i| {
                    const expanded_arg = try arg.expand(allocator);
                    if (expanded_arg != arg) any_child_expanded = true;
                    try expanded_children.append(expanded_arg);

                    if (expanded_arg.* == .Or and or_node_to_distribute == null) {
                        or_arg_index = i;
                        or_node_to_distribute = expanded_arg;
                    }
                }

                if (or_node_to_distribute) |or_node| {
                    const or_index = or_arg_index.?;
                    var rest_arg_list = std.ArrayList(*const LogicNode).init(allocator);
                    defer rest_arg_list.deinit();

                    for (expanded_children.items, 0..) |exp_arg, i| {
                        if (i != or_index) {
                            try rest_arg_list.append(exp_arg);
                        }
                    }

                    var distributed_or_args_list = std.ArrayList(*const LogicNode).init(allocator);
                    defer distributed_or_args_list.deinit();

                    for (or_node.Or.args) |or_term| {
                        var new_and_arg_term_list = std.ArrayList(*const LogicNode).init(allocator);
                        defer new_and_arg_term_list.deinit();

                        try new_and_arg_term_list.append(or_term);
                        try new_and_arg_term_list.appendSlice(rest_arg_list.items);

                        const new_and_node = try createAnd(allocator, new_and_arg_term_list.items);
                        const expanded_new_and = try new_and_node.expand(allocator);

                        try distributed_or_args_list.append(expanded_new_and);
                    }

                    const final_or_node = try createOr(allocator, distributed_or_args_list);
                    // TODO: If 'self' (the original AND node) was dynamically allocated
                    // and is different from 'final_or_node', free 'self'. This is complex.
                    return final_or_node;
                } else if (any_child_expanded) {
                    const result = try createAnd(allocator, expanded_children.items);
                    return result;
                } else {
                    return self;
                }
            },
        };
    }
};
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
pub fn fromString(allocator: Allocator, text: []const u8) error{ OutOfMemory, InvalidSyntax, CustomAllocationFailure, InvalidArguments }!*const LogicNode {
    var tokens = std.mem.splitAny(u8, text, " &|()");
    var lexpr: ?*const LogicNode = null;
    var schedop: ?enum { And, Or } = null;

    while (tokens.next()) |token| {
        var current_node: ?*const LogicNode = null;

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

            var new_expr: ?*const LogicNode = null;
            if (op == .And) {
                const args_slice = [_]*const LogicNode{ lexpr.?, current_node.? };
                new_expr = try createAnd(allocator, &args_slice);
            }
            // TODO: If lexpr was dynamically allocated AND not returned as new_expr, free lexpr.
            // This requires checking if new_expr is one of lexpr or current_node.
            // E.g., (a&b) & a -> a&b. Here new_expr is (a&b), lexpr was (a&b), current_node was a.
            // The old lexpr pointer is returned. Nothing to free here.
            // E.g., (a&b) & False -> False. Here new_expr is False. lexpr was (a&b). lexpr must be freed.
            // This implies tracking the origin of lexpr and current_node.
            // This is the hard part of manual memory for expression trees.

            lexpr = new_expr;
            schedop = null;
        } else {
            if (lexpr != null) return error.InvalidSyntax;
            if (current_node == null) return error.InvalidSyntax;

            lexpr = current_node;
        }
    }

    if (schedop == null) return error.InvalidSyntax;
    if (lexpr == null) return error.InvalidSyntax;

    return lexpr.?;
}

/// Recursively frees the memory owned by a LogicNode and its children.
/// This helper is simplistic and ASSUMES exclusive ownership of children.
/// Calling this on nodes with shared children (common in symbolic logic)
/// will lead to double frees. Use with caution, ideally with an arena allocator.
pub fn freeNode(allocator: Allocator, node: *const LogicNode) void {
    switch (node.*) {
        .True, .False => {
            allocator.destroy(node);
        },
        .Symbol => {
            allocator.free(node.Symbol);
            allocator.destroy(node);
        },
        .Not => {
            allocator.destroy(node);
        },
        .And => |compound| {
            allocator.free(compound.args);
            allocator.destroy(node);
        },
        .Or => |compound| {
            allocator.free(compound.args);
            allocator.destroy(node);
        },
    }
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
pub fn createAnd(allocator: Allocator, args: []const *const LogicNode) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*const LogicNode {
    var flattened_list = std.ArrayList(*const LogicNode).init(allocator);
    defer flattened_list.deinit();

    for (args) |arg| {
        const empty_and = LogicNode{
            .And = .{
                .args = &.{},
            },
        };

        try flattenAndOr(allocator, arg, &empty_and, &flattened_list);
    }

    var unique_map = std.AutoArrayHashMap(*const LogicNode, LogicNode.NodeContext).init(allocator);
    defer unique_map.deinit();

    for (flattened_list.items) |arg| {
        switch (arg.*) {
            .False => {
                return try createFalse(allocator);
            },
            .True => {
                continue;
            },
            else => {},
        }

        const not_arg = try createNot(allocator, arg);
        errdefer freeNode(allocator, not_arg);

        if (unique_map.contains(not_arg)) {
            return try createFalse(allocator);
        }

        try unique_map.put(arg, .{});

        freeNode(allocator, not_arg);
    }

    const unique_args = unique_map.keys();
    if (unique_args.len == 0) return try createTrue(allocator);
    if (unique_args.len == 1) return unique_args[0];

    var sorted_args_list = std.ArrayList(*const LogicNode).init(allocator);
    defer sorted_args_list.deinit();
    try sorted_args_list.appendSlice(unique_args);

    std.mem.sort(*const LogicNode, sorted_args_list.items, {}, LogicNode.lessThanNodes);

    const final_args_slice = try allocator.dupe(*const LogicNode, sorted_args_list.items);
    errdefer allocator.free(final_args_slice);

    const node = try allocator.create(LogicNode);
    errdefer allocator.destroy(node);

    node.* = .{ .And = .{ .args = final_args_slice } };
    return node;
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
pub fn createOr(allocator: Allocator, args: []const *const LogicNode) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*const LogicNode {
    var flattened_list = std.ArrayList(*const LogicNode).init(allocator);
    defer flattened_list.deinit();

    for (args) |arg| {
        const empty_or = LogicNode{
            .Or = .{
                .args = &.{},
            },
        };
        try flattenAndOr(allocator, arg, &empty_or, &flattened_list);
    }

    var unique_map = std.AutoArrayHashMap(*const LogicNode, LogicNode.NodeContext).init(allocator);
    defer unique_map.deinit();

    for (flattened_list.items) |arg| {
        switch (arg.*) {
            .True => {
                return try createTrue(allocator);
            },
            .False => {
                continue;
            },
            else => {},
        }

        const not_arg = try createNot(allocator, arg);
        errdefer freeNode(allocator, arg);

        if (unique_map.contains(not_arg)) {
            return try createTrue(allocator);
        }
        try unique_map.put(arg, .{});

        freeNode(allocator, not_arg);
    }

    const unique_args = unique_map.keys();
    if (unique_args.len == 0) return try createFalse(allocator);
    if (unique_args.len == 1) return unique_args[0];

    var sorted_args_list = std.ArrayList(*const LogicNode).init(allocator);
    defer sorted_args_list.deinit();
    try sorted_args_list.appendSlice(unique_args);

    std.mem.sort(*const LogicNode, sorted_args_list.items, {}, LogicNode.lessThanNodes);

    const final_args_slice = try allocator.dupe(*const LogicNode, sorted_args_list.items);
    errdefer allocator.free(final_args_slice);

    const node = try allocator.create(LogicNode);
    errdefer allocator.destroy(node);

    node.* = .{ .Or = .{ .args = final_args_slice } };
    return node;
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
pub fn createNot(allocator: Allocator, arg: *const LogicNode) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*const LogicNode {
    return switch (arg.*) {
        .True => return try createFalse(allocator),
        .False => return try createTrue(allocator),
        // .Not => arg.Not,
        .Not => {
            const child = arg.Not;
            freeNode(allocator, arg);
            return child;
        },
        .And => |args| {
            var new_args_list = std.ArrayList(*const LogicNode).init(allocator);
            defer new_args_list.deinit();

            var nodes_create_in_loop = std.ArrayList(*const LogicNode).init(allocator);
            defer nodes_create_in_loop.deinit();

            for (args.args) |a| {
                const negated_a = try createNot(allocator, a);
                try nodes_create_in_loop.append(negated_a);
                try new_args_list.append(negated_a);
            }

            const result_or = try createOr(allocator, new_args_list.items);

            switch (result_or.*) {
                .True, .False => {
                    for (nodes_create_in_loop.items) |node_to_free| {
                        switch (node_to_free.*) {
                            .Symbol => {},
                            .True, .False, .Not, .And, .Or => {
                                freeNode(allocator, node_to_free);
                            },
                        }
                    }
                },
                else => {},
            }
            return result_or;
        },
        .Or => |args| {
            var new_args_list = std.ArrayList(*const LogicNode).init(allocator);
            defer new_args_list.deinit();

            var nodes_returned_by_recursive_call = std.ArrayList(*const LogicNode).init(allocator);
            defer nodes_returned_by_recursive_call.deinit();

            for (args.args) |a| {
                const negated_a = try createNot(allocator, a);
                try nodes_returned_by_recursive_call.append(negated_a);
                try new_args_list.append(negated_a);
            }

            const result_and = try createAnd(allocator, new_args_list.items);
            switch (result_and.*) {
                .True, .False => {
                    for (nodes_returned_by_recursive_call.items) |node_to_free| {
                        switch (node_to_free.*) {
                            .Symbol => {},
                            .True, .False, .Not, .And, .Or => {
                                freeNode(allocator, node_to_free);
                            },
                        }
                    }
                },
                else => {},
            }
            return result_and;
        },
        else => {
            const node = try allocator.create(LogicNode);
            // defer allocator.destroy(node);
            node.* = .{ .Not = arg };
            return node;
        },
    };
}

/// Helper to recursively flatten And/Or nodes of the target type.
/// Adds non-matching nodes or flattened children to the result list.
fn flattenAndOr(allocator: Allocator, node: *const LogicNode, target: *const LogicNode, result_list: *std.ArrayList(*const LogicNode)) error{OutOfMemory}!void {
    const target_tag = @tagName(target.*);
    switch (node.*) {
        .And => |and_node| {
            if (std.mem.eql(u8, @tagName(node.*), target_tag)) {
                for (and_node.args) |sub_arg| {
                    try flattenAndOr(allocator, sub_arg, target, result_list);
                }
            } else {
                try result_list.append(node);
            }
        },
        .Or => |or_node| {
            if (std.mem.eql(u8, @tagName(node.*), target_tag)) {
                for (or_node.args) |sub_arg| {
                    try flattenAndOr(allocator, sub_arg, target, result_list);
                }
            } else {
                try result_list.append(node);
            }
        },
        else => {
            try result_list.append(node);
        },
    }
}

/// Creates a Symbol node.
/// Allocates memory for the node and duplicates the symbol name.
/// The caller is responsible for freeing the returned node using recursiveFree.
pub fn createSymbol(allocator: Allocator, name: []const u8) !*const LogicNode {
    const name_copy = try allocator.dupe(u8, name);
    errdefer allocator.free(name_copy);

    const node = try allocator.create(LogicNode);
    errdefer allocator.destroy(node);

    node.* = .{ .Symbol = name_copy };
    return node;
}

/// Creates a LogicNode representing True.
pub fn createTrue(allocator: Allocator) !*const LogicNode {
    const node = try allocator.create(LogicNode);
    node.* = .True;
    return node;
}

/// Creates a LogicNode representing False.
pub fn createFalse(allocator: Allocator) !*const LogicNode {
    const node = try allocator.create(LogicNode);
    node.* = .False;
    return node;
}
