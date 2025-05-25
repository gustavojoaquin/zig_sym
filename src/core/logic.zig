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

/// Represents a node in a logical expression tree.
///
/// `Node` is a reference-counted wrapper around a `LogicNode` union.
/// It handles memory management through `acquire` and `release` methods.
/// Nodes can represent boolean constants (True, False), symbolic variables,
/// or logical operations (Not, And, Or).
///
/// When a `Node` is created (e.g., via `createSymbol`, `createAnd`, etc.),
/// it typically starts with a reference count of 1, and the creator function
/// transfers ownership of this initial reference to the caller. The caller is
/// responsible for calling `release` when the node is no longer needed in that scope.
///
/// Internal structures (like an `And` node holding child `Node`s) also hold
/// references to their children, incrementing their `ref_count` accordingly.
pub const Node = struct {
    /// The underlying logical operation or value.
    logic_node: LogicNode,
    /// The atomic reference counter for managing the node's lifecycle.
    ref_count: std.atomic.Value(usize),

    /// Acquires an additional reference to this Node.
    ///
    /// This increments the node's reference count. It is the caller's responsibility
    /// to eventually call `release` for every `acquire` call to prevent memory leaks.
    ///
    /// Returns:
    ///     A pointer to self, for chaining or convenience.
    pub fn acquire(self: *Node) *Node {
        _ = self.ref_count.fetchAdd(1, .monotonic);
        return self;
    }

    /// Releases a reference to this Node.
    ///
    /// This decrements the node's reference count. If the reference count reaches zero,
    /// the node's internal content (e.g., symbol name, child nodes in And/Or/Not)
    /// is recursively released, and then the Node object itself is deallocated using
    /// the provided allocator.
    ///
    /// Args:
    ///     allocator: The allocator used to free the node and its content if
    ///                the reference count drops to zero. This must be the same
    ///                allocator used to create the node.
    pub fn release(self: *Node, allocator: Allocator) void {
        if (self.ref_count.fetchSub(1, .release) == 1) {
            freeNodeContent(allocator, &self.logic_node);
            allocator.destroy(self);
        }
    }

    /// Helper function to get the variant tag of the underlying `LogicNode`
    /// as a comptime_int, primarily for sorting nodes by their type.
    /// This function does not affect the reference count of the node.
    ///
    /// Args:
    ///     node: The node whose tag is to be retrieved.
    ///
    /// Returns:
    ///     An integer representing the enum tag of `node.logic_node`.
    pub fn getTagInt(node: *Node) u32 {
        return @intFromEnum(node.*);
    }

    /// Adapter function for sorting functions like `std.mem.sort` that require a
    /// boolean "less than" comparator.
    /// This function does not affect the reference counts of the nodes.
    ///
    /// Args:
    ///     context: Void context, unused.
    ///     lhs: The left-hand side node for comparison.
    ///     rhs: The right-hand side node for comparison.
    ///
    /// Returns:
    ///     `true` if `lhs` is strictly less than `rhs` based on `compareNodes`, `false` otherwise.
    fn lessThanNodes(context: void, lhs: *const Node, rhs: *const Node) bool {
        return compareNodes(context, lhs, rhs) == .lt;
    }

    /// Provides context for `std.HashMap` to use structural hashing and equality for `*Node` keys.
    ///
    /// When `*Node` pointers are used as keys in a `std.HashMap`, this context ensures
    /// that the map operates based on the logical structure of the nodes rather than
    /// their memory addresses. Hashing is performed via `deepHashNodes` and equality
    /// via `eqlNodes`.
    pub const NodeContext = struct {
        /// Computes a structural hash for the given `Node`.
        /// The hash is based on the node's type and content (recursively for complex nodes).
        /// This function does not affect the reference count of the key.
        ///
        /// Args:
        ///     _: NodeContext instance (unused).
        ///     key: The node to hash.
        ///
        /// Returns:
        ///     A u64 hash value.
        pub fn hash(_: NodeContext, key: *const Node) u64 {
            var hasher = std.hash.Wyhash.init(0);
            key.deepHashNodes(&hasher);
            return hasher.final();
        }

        /// Checks for structural equality between two `Node`s.
        /// Equality is based on the node's type and content (recursively for complex nodes).
        /// This function does not affect the reference counts of the nodes.
        ///
        /// Args:
        ///     _: NodeContext instance (unused).
        ///     a: The first node for comparison.
        ///     b: The second node for comparison.
        ///
        /// Returns:
        ///     `true` if `a` and `b` are structurally equivalent, `false` otherwise.
        pub fn eql(_: NodeContext, a: *const Node, b: *const Node) bool {
            return a.eqlNodes(b);
        }
    };

    /// Performs a deep structural hash of the `Node`.
    ///
    /// The hash is computed based on the node's type and its content. For composite
    /// nodes like `And`, `Or`, and `Not`, the hash includes the hashes of their children,
    /// ensuring that structurally identical (but potentially distinct in memory) nodes
    /// produce the same hash. This is consistent with `eqlNodes`.
    /// This function does not affect the reference count of the node.
    ///
    /// Args:
    ///     hasher: A pointer to a `std.hash.Wyhash` instance to update with the node's hash.
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

    /// Performs a deep structural equality check between this `Node` and another.
    ///
    /// Two nodes are considered structurally equal if they represent the same logical
    /// expression. This means they must be of the same type and their content
    /// (e.g., symbol name, or child nodes for And/Or/Not) must also be structurally equal.
    /// For `And` and `Or` nodes, the order of arguments matters for this check; canonical
    /// sorting during node creation (e.g., in `createAnd`, `createOr`) is essential
    /// for `eqlNodes` to correctly identify semantically equivalent but differently
    /// ordered expressions as equal.
    /// This function does not affect the reference counts of the nodes.
    ///
    /// Args:
    ///     other: The other node to compare against.
    ///
    /// Returns:
    ///     `true` if this node is structurally equivalent to `other`, `false` otherwise.
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
    ///
    /// Allocates memory for the string using the provided allocator. The caller is
    /// responsible for freeing the returned string slice. This function does not
    /// affect the reference count of the Node itself.
    ///
    /// Args:
    ///     allocator: The allocator to use for creating the string.
    ///
    /// Returns:
    ///     A newly allocated string representing the node, or an error.
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

    /// Applies the distributive property and other expansions to transform the expression,
    /// typically towards Disjunctive Normal Form (DNF).
    ///
    /// The `expand` function returns a node whose reference is owned by the caller.
    /// - If `self` is an `And` node and it is expanded (e.g., an `Or` child is distributed),
    ///   the original `self` node is released, and a new node representing the expanded
    ///   expression is returned. The caller owns this new node.
    /// - If `self` is an `And` node whose children are expanded but `self` itself is not
    ///   restructured, a new `And` node is created with the (potentially new) expanded
    ///   children, `self` is released, and this new `And` node is returned.
    /// - If `self` is an `And` node and no expansion occurs (neither `self` nor its children change),
    ///   `self.acquire()` is returned.
    /// - If `self` is not an `And` node (.Or, .Not, .Symbol, .True, .False), `self.acquire()` is returned.
    ///
    /// In all cases, the caller receives a node that it owns. It's recommended to always
    /// use the returned node as the authoritative version after the call. The original `self`
    /// reference passed to `expand` may have been consumed if a structural transformation
    /// replaced `self`.
    ///
    /// Args:
    ///     allocator: The allocator to use for creating new nodes during expansion.
    ///
    /// Returns:
    ///     A pointer to the resulting (potentially expanded) LogicNode. The caller owns this node.
    pub fn expand(self: *Node, allocator: Allocator) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure, InvalidSyntax }!*Node {
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

                    if (expanded_arg.logic_node == .Or and or_node_to_distribute == null) {
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

                    // expanded_children.items = &.{};

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
                        const expanded_result_node = try new_and_node.expand(allocator);

                        if (expanded_result_node == new_and_node) new_and_node.release(allocator);
                        try distributed_or_args_list.append(expanded_result_node);
                    }

                    self.release(allocator);

                    const final_or_node = try createOr(allocator, distributed_or_args_list.items);
                    return final_or_node;
                } else if (any_child_expanded) {
                    self.release(allocator);
                    const result = try createAnd(allocator, expanded_children.items);
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

/// Performs a structural comparison between two LogicNodes for ordering.
///
/// Nodes are compared first by their `LogicNode` type (e.g., Symbol < Not < And < Or),
/// then by their content (e.g., symbol names, children recursively).
/// This function is suitable for use in sorting algorithms.
/// This function does not affect the reference counts of the nodes.
///
/// Args:
///     _: Void context, unused.
///     a: The first node to compare.
///     b: The second node to compare.
///
/// Returns:
///     `std.math.Order.lt` if `a` is less than `b`.
///     `std.math.Order.gt` if `a` is greater than `b`.
///     `std.math.Order.eq` if `a` is structurally equivalent to `b`.
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
    var current_ixd: usize = 0;
    var lexpr: ?*Node = null;
    var schedop: ?enum { And, Or } = null;

    defer if (lexpr) |node| node.release(allocator);

    while (current_ixd < text.len) {
        while (current_ixd < text.len and std.ascii.isWhitespace(text[current_ixd])) current_ixd += 1;

        if (current_ixd == text.len) break;

        var current_node: ?*Node = null;

        defer if (current_node) |node| node.release(allocator);

        const char = text[current_ixd];
        if (char == '&') {
            current_ixd += 1;
            if (lexpr == null) return error.InvalidSyntax;
            if (schedop != null) return error.InvalidSyntax;
            schedop = .And;
            continue;
        } else if (char == '|') {
            current_ixd += 1;
            if (lexpr == null) return error.InvalidSyntax;
            if (schedop != null) return error.InvalidSyntax;
            schedop = .Or;
            continue;
        } else if (char == '!') {
            current_ixd += 1;
            if (lexpr != null and schedop == null) return error.InvalidSyntax;

            const start_sym_ixd = current_ixd;
            if (current_ixd < text.len and !std.ascii.isWhitespace(text[current_ixd]) and (std.mem.indexOfScalar(u8, "&|!()", text[current_ixd]) == null)) current_ixd += 1;

            const symbol_name = text[start_sym_ixd..current_ixd];
            if (symbol_name.len == 0) return error.InvalidSyntax;

            const temp_symbol = try createSymbol(allocator, symbol_name);
            defer temp_symbol.release(allocator);
            current_node = try createNot(allocator, temp_symbol);
        } else if (std.ascii.isAlphabetic(char)) {
            if (lexpr != null and schedop == null) return error.InvalidSyntax;

            const start_sym_ixd = current_ixd;
            if (current_ixd < text.len and !std.ascii.isWhitespace(text[current_ixd]) and (std.mem.indexOfScalar(u8, "&|!()", text[current_ixd]) == null)) current_ixd += 1;

            const symbol_name = text[start_sym_ixd..current_ixd];
            if (symbol_name.len == 0) return error.InvalidSyntax;

            if (eql(u8, symbol_name, "True")) {
                current_node = try createTrue(allocator);
            } else if (eql(u8, symbol_name, "False")) {
                current_node = try createFalse(allocator);
            } else {
                current_node = try createSymbol(allocator, symbol_name);
            }
        } else {
            return error.InvalidSyntax;
        }

        if (schedop) |op| {
            if (lexpr == null and current_node == null) return error.InvalidSyntax;

            const combined_args = [_]*Node{ lexpr.?, current_node.? };
            const new_combined_node = if (op == .And) try createAnd(allocator, &combined_args) else try createOr(allocator, &combined_args);

            lexpr.?.release(allocator);
            current_node.?.release(allocator);
            current_node = null;

            lexpr = new_combined_node;
            schedop = null;
        } else {
            if (lexpr != null) return error.InvalidSyntax;
            if (current_node == null) return error.InvalidSyntax;

            lexpr = current_node.?;
            current_node = null;
        }
    }

    if (lexpr == null) return error.InvalidSyntax;
    if (schedop != null) return error.InvalidSyntax;

    const result = lexpr.?;
    lexpr = null;
    return result;
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
        for (flattened_list.items) |node_items| node_items.release(allocator);
        flattened_list.deinit();
    }

    for (args) |arg| try flattenAndOr(allocator, arg.acquire(), .{ .And = .{ .args = &.{} } }, &flattened_list);

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

        const not_arg_for_check = try createNot(allocator, arg);
        defer not_arg_for_check.release(allocator);

        if (unique_map.contains(not_arg_for_check)) {
            var it = unique_map.iterator();
            while (it.next()) |entry| entry.key_ptr.*.release(allocator);
            unique_map.deinit(allocator);
            return try createFalse(allocator);
        }

        if (!unique_map.contains(arg))
            try unique_map.put(allocator, arg.acquire(), {});
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

    for (args) |arg| try flattenAndOr(allocator, arg.acquire(), .{ .Or = .{ .args = &.{} } }, &flattened_list);

    var unique_map = std.HashMapUnmanaged(*Node, void, Node.NodeContext, std.hash_map.default_max_load_percentage){};

    for (flattened_list.items) |arg| {
        switch (arg.logic_node) {
            .True => {
                var it = unique_map.iterator();
                while (it.next()) |entry| entry.key_ptr.*.release(allocator);
                unique_map.deinit(allocator);
                return try createTrue(allocator);
            },
            .False => {
                continue;
            },
            else => {},
        }

        const not_arg_for_check = try createNot(allocator, arg);
        defer not_arg_for_check.release(allocator);

        if (unique_map.contains(not_arg_for_check)) {
            var it = unique_map.iterator();
            while (it.next()) |entry| entry.key_ptr.*.release(allocator);
            unique_map.deinit(allocator);
            return try createTrue(allocator);
        }

        if (!unique_map.contains(arg)) try unique_map.put(allocator, arg.acquire(), {});
    }

    var unique_args_list = std.ArrayList(*Node).init(allocator);

    var it = unique_map.iterator();
    while (it.next()) |entry| try unique_args_list.append(entry.key_ptr.*);

    unique_map.deinit(allocator);

    if (unique_args_list.items.len == 0) {
        unique_args_list.deinit();
        return try createFalse(allocator);
    }
    if (unique_args_list.items.len == 1) {
        const result = unique_args_list.items[0];
        unique_args_list.deinit();
        return result;
    }
    std.mem.sort(*Node, unique_args_list.items, {}, Node.lessThanNodes);

    // const final_args_slice = try allocator.dupe(*Node, unique_args_list.items);
    const final_args_slice = try allocator.dupe(*Node, unique_args_list.items);
    unique_args_list.deinit();

    const node = try allocator.create(Node);
    errdefer {
        for (final_args_slice) |node_args| node_args.release(allocator);
        allocator.free(final_args_slice);
        allocator.destroy(node);
    }
    node.logic_node = .{ .Or = .{ .args = final_args_slice } };
    node.ref_count = std.atomic.Value(usize).init(1);
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
pub fn createNot(allocator: Allocator, arg: *Node) error{ OutOfMemory, InvalidArguments, CustomAllocationFailure }!*Node {
    return switch (arg.logic_node) {
        .True => return try createFalse(allocator),
        .False => return try createTrue(allocator),
        .Not => {
            const child = arg.logic_node.Not;
            return child.acquire();
        },
        .And => |args| {
            var new_args_list = std.ArrayList(*Node).init(allocator);
            defer {
                for (new_args_list.items) |node| node.release(allocator);
                new_args_list.deinit();
            }
            for (args.args) |child_args| {
                const negated_child = try createNot(allocator, child_args);
                try new_args_list.append(negated_child);
            }

            const result_or = try createOr(allocator, new_args_list.items);
            return result_or;
        },
        .Or => |args| {
            var new_and_args_list = std.ArrayList(*Node).init(allocator);
            defer {
                for (new_and_args_list.items) |node| node.release(allocator);
                new_and_args_list.deinit();
            }

            for (args.args) |child_arg| {
                const negated_node = try createNot(allocator, child_arg);
                try new_and_args_list.append(negated_node);
            }

            const result_and = try createAnd(allocator, new_and_args_list.items);
            return result_and;
        },
        else => {
            const node = try allocator.create(Node);
            errdefer allocator.destroy(node);
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
    node.logic_node = .{ .False = {} };
    node.ref_count = std.atomic.Value(usize).init(1);
    return node;
}
