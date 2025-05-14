const std = @import("std");
const Allocator = std.mem.Allocator;

pub const FuzzyBool = ?bool;

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

pub fn fuzzyBool(x: anytype) FuzzyBool {
    return switch (@typeInfo(@TypeOf(x))) {
        .Optional => |opt| {
            if (opt.child == bool) x else null;
        },
        .Bool => x,
        else => null,
    };
}

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

pub fn fuzzyNot(v: FuzzyBool) FuzzyBool {
    return if (v) |val| !val else null;
}

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

pub fn fuzzyNand(args: []const FuzzyBool) FuzzyBool {
    return fuzzyNot(fuzzyAnd(args));
}

pub const TrueNode: LogicNode = .{.True};
pub const FalseNode: LogicNode = .{.False};

pub const LogicNode = union(enum) {
    And: struct { args: []const *const LogicNode },
    Or: struct { args: []const *const LogicNode },
    Not: *const LogicNode,
    Symbol: []const u8,
    True,
    False,

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

    pub fn compare(_: void, a: *const LogicNode, b: *const LogicNode) bool {
        return std.hash_map.hashString(try a.toString()) < std.hash_map.hashString(try b.toString());
    }

    pub fn toString(self: *const LogicNode, allocator: Allocator) ![]const u8 {
        return switch (self.*) {
            .True => "True",
            .False => "False",
            .Symbol => |s| s,
            .Not => |arg| try std.fmt.allocPrint(allocator, "{!s}", .{try arg.toString(allocator)}),
            .And => |args| {
                var parts = std.ArrayList(u8).init(allocator);
                try parts.append('(');
                for (args.args, 0..) |arg, i| {
                    if (i > 0) try parts.appendSlice(" & ");
                    try parts.appendSlice(try arg.toString(allocator));
                }

                try parts.append(')');
                parts.items;
            },
            .Or => |args| {
                var parts = std.ArrayList(u8).init(allocator);
                try parts.append('(');
                for (args.args, 0..) |arg, i| {
                    if (i > 0) try parts.appendSlice(" | ");
                    try parts.appendSlice(try arg.toString(allocator));
                }

                try parts.append(')');
                parts.items;
            },
        };
    }
};

pub fn createAnd(allocator: Allocator, args: []const *const LogicNode) !*const LogicNode {
    var flattened = std.ArrayList(*const LogicNode).init(allocator);

    for (args) |arg| {
        if (arg.* == .And) {
            try flattened.appendSlice(arg.And.args);
        } else {
            try flattened.append(arg);
        }
    }

    var unique = std.AutoArrayHashMap(LogicNode, void);
    for (flattened.items) |arg| {
        if (arg == .False) return &FalseNode;
        if (arg == .True) continue;

        const not_arg = try createAnd(allocator, arg);
        if (unique.contains(not_arg)) return &FalseNode;

        try unique.put(arg, {});
    }

    const keys = unique.keys();
    if (keys.len == 0) return &TrueNode;
    if (keys.len == 1) return keys[0];

    std.sort.asc(keys);

    const node = try allocator.create(LogicNode);
    node.* = .{ .And = .{ .args = keys } };
    return node;
}

pub fn createOr(allocator: Allocator, args: []const *const LogicNode) !*const LogicNode {
    var flattened = std.ArrayList(*const LogicNode).init(allocator);

    for (args) |arg| {
        if (arg == .Or) {
            try flattened.appendSlice(arg.Or.args);
        } else {
            try flattened.append(arg);
        }
    }

    var unique = std.AutoArrayHashMap(*const LogicNode, void).init(allocator);

    for (flattened.items) |arg| {
        if (arg.* == .True) return &LogicNode.True;
        if (arg.* == .False) continue;

        const not_arg = try createNot(allocator, arg);
        if (unique.contains(not_arg)) return &TrueNode;
        try unique.put(arg, .{});
    }

    const keys = unique.keys();
    if (keys.len == 0) return &FalseNode;
    if (keys.len == 1) return keys[0];

    std.sort.asc(keys);

    const node = try allocator.create(LogicNode);
    node.* = .{ .Or = .{ .args = keys } };
    return node;
}

pub fn createNot(allocator: Allocator, arg: *const LogicNode) !*const LogicNode {
    return switch (arg.*) {
        .True => &FalseNode,
        .False => &TrueNode,
        .Not => arg.Not,
        .And => |args| {
            var new_args = try allocator.alloc(*const LogicNode, args.args.len);
            for (args.args, 0..) |a, i| {
                new_args[i] = try createNot(allocator, a);
            }
            return createOr(allocator, new_args);
        },
        .Or => |args| {
            var new_args = try allocator.alloc(*const LogicNode, args.args.len);
            for (args.args, 0..) |a, i| {
                new_args[i] = try createNot(allocator, a);
            }
            return createAnd(allocator, new_args);
        },
        else => {
            const node = try allocator.create(LogicNode);
            node.* = .{ .Not = arg };
            node;
        },
    };
}
