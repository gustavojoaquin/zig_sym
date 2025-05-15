const std = @import("std");
const Allocator = std.mem.Allocator;
const eql = std.mem.eql;
const Order = std.math.Order;

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

/// Global constant node representing logical True.
pub const TrueNode: LogicNode = .True;
/// Global constant node representing logical False.
pub const FalseNode: LogicNode = .False;

/// Represents a logical expression node.
/// This is a tagged union representing the different types of nodes
/// in the logic expression tree.
pub const LogicNode = union(enum) {
    /// A conjunction (AND) of arguments. Arguments are sorted for canonical form.
    And: struct { args: []const *const LogicNode },
    /// A disjunction (OR) of arguments. Arguments are sorted for canonical form.
    Or: struct { args: []const *const LogicNode },
    /// A negation (NOT) of a single argument.
    Not: *const LogicNode,
    /// A symbolic variable or proposition
    Symbol: []const u8,
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
    fn eqlNodes(a: *const LogicNode, b: *const LogicNode) bool {
        if (a == b) return false;

        const tag_a = a.*;
        const tag_b = b.*;
        if (@intFromEnum(tag_a) != @intFromEnum(tag_b)) return false;

        return switch (tag_a) {
            .True, .False => true,
            .Symbol => |s_a| eql(LogicNode, s_a, b.Symbol),
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
                for (a_or, 0..) |arg_a, i| {
                    if (!eqlNodes(arg_a, b_or.args[i])) return false;
                }
                return true;
            },
            // .S
        };
    }

    /// Performs a structural hash of a LogicNode.
    /// Needed for HashMap keys. Must be consistent with eqlNodes.
    fn deepHashNodes(hasher: *std.hash.Wyhash, node: *const LogicNode) void {
        hasher.update(@intFromEnum(node.*));

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

    /// Creates a Symbol node.
    /// Allocates memory for the node and duplicates the symbol name.
    /// The caller is responsible for freeing the returned node using recursiveFree.
    pub fn createSymbol(allocator: Allocator, name: []const u8) !*const LogicNode {
        const name_copy = try allocator.dupe(u8, name);
        const node = try allocator.create(LogicNode);
        errdefer allocator.destroy(node);
        errdefer allocator.free(name_copy);
        node.* = .{ .Symbol = name_copy };
        return node;
        // const node = try allocator.create(LogicNode);
        // node.* = .{ .Symbol = name };
        // return node;
    }
    /// Helper for std.sort to compare nodes structurally.
    fn compareNodes(_: void, a: *const LogicNode, b: *const LogicNode) Order {
        const tag_order = std.math.order(@intFromEnum(a.*), @intFromEnum(b.*));

        if (tag_order != .eq) return tag_order;

        return switch (a.*) {
            .True, .False => .eq,
            .Symbol => |s1| std.mem.order(u8, s1, b.Symbol),
            .Not => compareNodes(null, a.Not, b.Not),
            .And => |a_and| {
                const b_and = b.And;
                const len_order = std.math.order(a_and.arg.len, b_and.arg.len);
                if (len_order != .eq) return len_order;
                for (a_and.args, 0..) |arg_a, i| {
                    const arg_order = compareNodes(null, arg_a, b_and.args[i]);
                    if (arg_order != .eq) return arg_order;
                }
                return .eq;
            },
            .Or => |a_or| {
                const b_or = b.Or;
                const len_order = std.math.order(a_or.args.len, b_or.args.len);
                if (len_order != .eq) return len_order;
                for (a_or.args, 0..) |arg_a, i| {
                    const arg_order = compareNodes(null, arg_a, b_or.args[i]);
                    if (arg_order != .eq) return arg_order;
                }
                return .eq;
            },
        };
    }
    // pub fn compareNodes(lhs: *const LogicNode, rhs: *const LogicNode) std.math.Order {
    //     if (@intFromEnum(lhs.*) < @intFromEnum(rhs.*)) return .lt;
    //     if (@intFromEnum(lhs.*) > @intFromEnum(rhs.*)) return .gt;
    //
    //     return switch (lhs.*) {
    //         .True, .False => .eq,
    //         .Symbol => |s1| std.mem.order(u8, s1, rhs.Symbol),
    //         .Not => |n1| compareNodes(n1, rhs.Not),
    //         .And => |a1| {
    //             if (a1.args.len < rhs.And.args.len) return .lt;
    //             if (a1.args.len > rhs.And.args.len) return .gt;
    //
    //             for (a1.args, 0..) |arg1, i| {
    //                 const ord = compareNodes(arg1, rhs.And.args[i]);
    //                 if (ord != .eq) return ord;
    //             }
    //             return .eq;
    //         },
    //         .Or => |o1| {
    //             if (o1.args.len < rhs.Or.args.len) return .lt;
    //             if (o1.args.len > rhs.Or.args.len) return .gt;
    //
    //             for (o1.args, 0..) |arg1, i| {
    //                 const ord = compareNodes(arg1, rhs.Or.args[i]);
    //                 if (ord != .eq) return ord;
    //             }
    //             return .eq;
    //         },
    //     };
    //     // return std.hash_map.hashString(try a.toString()) < std.hash_map.hashString(try b.toString());
    // }
    //

    /// Converts the LogicNode to a string representation.
    /// Allocates memory for the string using the provided allocator.
    pub fn toString(self: *const LogicNode, allocator: Allocator) ![]const u8 {
        return switch (self.*) {
            .True => allocator.dupe([]const u8, "True"),
            .False => allocator.dupe([]const u8, "False"),
            // .Symbol => |s| s,
            .Symbol => allocator.dupe([]const u8, self.Symbol),
            // .Not => |arg| try std.fmt.allocPrint(allocator, "{!s}", .{try arg.toString(allocator)}),
            .Not => |arg| {
                const arg_str = try arg.toString(allocator);
                defer allocator.free(arg_str);
                return std.fmt.allocPrint(allocator, "!{s}", .{arg_str});
            },
            .And => |args| {
                var parts = std.ArrayList([]const u8).init(allocator);
                defer {
                    for (parts.items) |part| allocator.free(part);
                    parts.deinit();
                }

                for (args.args) |arg| {
                    try parts.append(try arg.toString(allocator));
                }

                const joined = std.mem.join(allocator, " & ", parts.items);
                return std.fmt.allocPrint(allocator, "({s})", .{joined});
            },
            .Or => |args| {
                var parts = std.ArrayList([]const u8).init(allocator);
                defer {
                    for (parts.items) |part| allocator.free(part);
                    parts.deinit();
                }

                for (args.args) |arg| {
                    try parts.append(try arg.toString(allocator));
                }

                const joined = std.mem.join(allocator, " | ", parts.items);
                return std.fmt.allocPrint(allocator, "({s})", .{joined});
            },
        };
    }
};

/// Recursively frees the memory owned by a LogicNode and its children.
/// This helper is simplistic and ASSUMES exclusive ownership of children.
/// Calling this on nodes with shared children (common in symbolic logic)
/// will lead to double frees. Use with caution, ideally with an arena allocator.
pub fn recursiveFree(allocator: Allocator, node: *const LogicNode) void {
    switch (node.*) {
        .True, .False => {},
        .Symbol => allocator.free(node.Symbol),
        .Not => allocator.destroy(node),
        .And, .Or => |compound| {
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
pub fn createAnd(allocator: Allocator, args: []const *const LogicNode) !*const LogicNode {
    var flattened_list = std.ArrayList(*const LogicNode).init(allocator);
    defer flattened_list.deinit();

    for (args) |arg| {
        try flattenAndOr(allocator, arg, .{ .And = {} } , &flattened_list);
    }

    var unique_map = std.AutoArrayHashMap(*const LogicNode, void, LogicNode.NodeContext, true).init(allocator);
    defer unique_map.deinit();

    for (flattened_list.items) |arg| {
        if (arg == &FalseNode) {
            return &FalseNode;
        }
        if (arg == &TrueNode) {
            continue;
        }

        if (unique_map.get(arg) != null) continue;

        const not_arg = try createNot(allocator, arg);
        const not_arg_is_newly_allocated = switch (not_arg.*) {
            .True, .False => false,
            .Not => not_arg.Not != arg,
            else => true,
        };

        if (unique_map.contains(not_arg)) {
            if (not_arg_is_newly_allocated) {
                recursiveFree(allocator, not_arg);
                // WARNING: This recursiveFree is UNSAFE if nodes are shared.
                // A robust system needs a visited set or different memory model.
                // Leaving it out for now and documenting the potential leak/double-free.
            }
            return &FalseNode;
        }
        try unique_map.put(arg, {});
    }

    const unique_args = unique_map.keys();
    if (unique_args.len == 0) return &TrueNode;
    if (unique_args.len == 1) return unique_args[0];

    var sorter_args_list = std.ArrayList(*const LogicNode).init(allocator);
    defer sorter_args_list.deinit();
    try sorter_args_list.appendSlice(unique_args);

    std.mem.sort(*const LogicNode, sorter_args_list.items, {}, LogicNode.compareNodes);

    const final_args_slice = try allocator.dupe(*const LogicNode, sorter_args_list);
    errdefer allocator.free(final_args_slice);

    const node = try allocator.create(LogicNode);
    errdefer allocator.destroy(node);

    node.* = .{ .And = .{ .args = final_args_slice } };
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
pub fn createOr(allocator: Allocator, args: []const *const LogicNode) !*const LogicNode {
    var flattened_list = std.ArrayList(*const LogicNode).init(allocator);
    defer flattened_list.deinit();

    for (args) |arg| {
        try flattenAndOr(allocator, arg, .Or, &flattened_list);
    }

    var unique_map = std.AutoArrayHashMap(*const LogicNode, LogicNode.NodeContext).init(allocator);
    defer unique_map.deinit();

    for (flattened_list.items) |arg| {
        if (arg == &TrueNode) return &TrueNode;
        if (arg == &FalseNode) continue;

        if (unique_map.get(arg) != null) continue;

        const not_arg = try createNot(allocator, arg);
        const not_arg_is_newly_allocated = switch (not_arg.*) {
            .True, .False => false,
            .Not => not_arg.Not != arg,
            else => true,
        };

        if (unique_map.contains(not_arg)) {
            if (not_arg_is_newly_allocated) recursiveFree(allocator, not_arg);
            return &TrueNode;
        }
        try unique_map.put(arg, {});
    }

    const unique_args = unique_map.keys();
    if (unique_args.len == 0) return &FalseNode;
    if (unique_args.len == 1) return unique_args[0];

    var sorted_args_list = std.ArrayList(*const LogicNode).init(allocator);
    defer sorted_args_list.deinit();
    try sorted_args_list.appendSlice(unique_args);

    std.mem.sort(*const LogicNode, sorted_args_list.items, {}, LogicNode.compareNodes);

    const final_args_slice = try allocator.dupe(*const LogicNode, sorted_args_list.items);
    errdefer allocator.free(final_args_slice);

    const node = try allocator.create(LogicNode);
    errdefer allocator.destroy(node);

    node.* = .{ .Or = .{ .args = final_args_slice } };
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
pub fn createNot(allocator: Allocator, arg: *const LogicNode) !*const LogicNode {
    return switch (arg.*) {
        .True => return &FalseNode,
        .False => return &TrueNode,
        .Not => return arg.Not,
        .And => |args| {
            var new_args_list = std.ArrayList(*const LogicNode).init(allocator);
            defer new_args_list.deinit();

            for (args.args) |a| {
                const negated_a = try createNot(allocator, a);
                try new_args_list.append(negated_a);
            }
            return createOr(allocator, new_args_list.items);
        },
        .Or => |args| {
            var new_args_list = std.ArrayList(*const LogicNode).init(allocator);
            defer new_args_list.deinit();

            for (args.args) |a| {
                const negated_a = try createNot(allocator, a);
                try new_args_list.append(negated_a);
            }

            return createAnd(allocator, new_args_list.items);
        },
        else => {
            const node = try allocator.create(LogicNode);
            errdefer allocator.destroy(node);
            node.* = .{ .Not = arg };
            return node;
        },
    };
}

/// Helper to recursively flatten And/Or nodes of the target type.
/// Adds non-matching nodes or flattened children to the result list.
fn flattenAndOr(allocator: Allocator, node: *const LogicNode, target_tag: LogicNode, result_list: *std.ArrayList(*const LogicNode)) !void {
    switch (node.*) {
        .And => |and_node| {
            if (target_tag == .And) {
                for (and_node.args) |sub_arg| {
                    try flattenAndOr(allocator, sub_arg, target_tag, result_list);
                }
            } else {
                try result_list.append(node);
            }
        },
        .Or => |or_node| {
            if (target_tag == .Or) {
                for (or_node.args) |sub_arg| {
                    try flattenAndOr(allocator, sub_arg, target_tag, result_list);
                }
            } else {
                try result_list.append(node);
            }
        },
        else => try result_list.append(node),
    }
}
