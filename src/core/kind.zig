const std = @import("std");
const Allocator = std.mem.Allocator;
const Mutex = std.Thread.Mutex;
const hash_map = std.hash_map;

// const Kind =  @This();

pub const Kind = union(enum) {
    undefined,
    number,
    boolean,
    matrix: *const Kind,

    pub const Undefined: Kind = .undefined;
    pub const Number: Kind = .number;
    pub const Boolean: Kind = .boolean;

    pub fn Matrix(allocator: Allocator, element_kind: Kind) !Kind {
        // return .{ .matrix = element_kind };
        const elem_ptr = try allocator.create(Kind);
        elem_ptr.* = element_kind;
        return .{ .matrix = elem_ptr };
    }

    pub fn equals(a: Kind, b: Kind) bool {
        const tag_a = @as(std.meta.Tag(Kind), a);
        const tag_b = @as(std.meta.Tag(Kind), b);

        if (tag_a != tag_b) return false;
        return switch (a) {
            // .matrix => |a_elem| {
            //     if (b.matrix == null or a_elem == null) return a_elem == b.matrix;
            //     return equals(a_elem.*, b.matrix.*);
            // },
            .matrix => |a_elem| a_elem.*.equals(b.matrix.*),
            else => true,
        };
    }
    pub fn deinit(self: Kind, allocator: Allocator) void {
        switch (self) {
            .matrix => |elem_ptr| {
                elem_ptr.deinit(allocator);
                // allocator.destroy(@ptrCast(*Kind)@alignCast(elem_ptr));
                // const align_cast_elem = @alignCast(elem_ptr);
                // const ptr_cast_elem = @ptrCast(align_cast_elem);
                allocator.destroy(elem_ptr);
            },
            else => {},
        }
    }
};

const DispatchKey = struct {
    tag1: std.meta.Tag(Kind),
    tag2: std.meta.Tag(Kind),

    pub fn hash(self: DispatchKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        std.hash.autoHash(&hasher, self.tag1);
        std.hash.autoHash(&hasher, self.tag2);
        return hasher.final();
    }
    pub fn eql(self: DispatchKey, other: DispatchKey) bool {
        return self.tag1 == other.tag1 and self.tag2 == other.tag2;
    }
};

pub const DispatchFn = *const fn (dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind;

pub fn numberNumberDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .number and b == .number);
    _ = dispatcher;

    return Kind.Number;
}

pub fn numberMatrixDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .number and b == .matrix);

    const b_elem_ptr = b.matrix.*;
    const final_elem_kind = try dispatcher.dispatchBinary(a, b_elem_ptr);
    const allocated_elem_ptr = try dispatcher.allocator.create(Kind);
    errdefer dispatcher.allocator.destroy(allocated_elem_ptr);
    allocated_elem_ptr.* = final_elem_kind;

    return Kind{ .matrix = allocated_elem_ptr };
}

pub fn undefinedDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    _ = dispatcher;
    _ = a;
    _ = b;
    return Kind.Undefined;
}

pub fn matrixMatrixDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .matrix and b == .matrix);

    const a_elem_ptr = a.matrix.*;
    const b_elem_ptr = a.matrix.*;

    const final_elem_kind = try dispatcher.dispatchBinary(a_elem_ptr, b_elem_ptr);

    const allocated_elem_ptr = try dispatcher.allocator.create(Kind);
    errdefer dispatcher.allocator.destroy(allocated_elem_ptr);

    allocated_elem_ptr.* = final_elem_kind;

    return Kind{ .matrix = allocated_elem_ptr };
}

pub fn booleanBooleanDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .boolean and b == .boolean);
    _ = dispatcher;
    return Kind.Boolean;
}
pub fn booleanMatrixDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .boolean and b == .matrix);
    const b_elem_ptr = b.matrix;
    const final_elem_kind = try dispatcher.dispatchBinary(a, b_elem_ptr.*);

    const allocated_elem_ptr = try dispatcher.allocator.create(Kind);
    errdefer dispatcher.allocator.destroy(allocated_elem_ptr);
    allocated_elem_ptr.* = final_elem_kind;

    return Kind{ .matrix = allocated_elem_ptr };
}

pub fn matrixBooleanDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .matrix and b == .boolean);
    // Just reuse the same logic as booleanMatrixDispatch
    return booleanMatrixDispatch(dispatcher, b, a);
}

pub const KindDispatcher = struct {
    name: []const u8,
    commutative: bool,
    allocator: Allocator,

    rules: hash_map.HashMap(DispatchKey, DispatchFn, hash_map.AutoContext(DispatchKey), 80),

    pub fn init(allocator: Allocator, name: []const u8, commutative: bool) KindDispatcher {
        return .{
            .allocator = allocator,
            .name = name,
            .commutative = commutative,
            .rules = hash_map.HashMap(DispatchKey, DispatchFn, hash_map.AutoContext(DispatchKey), 80).init(allocator),
        };
    }

    pub fn deinit(self: *KindDispatcher) void {
        // var cast_self_rules = @constCast(&self.rules);
        // cast_self_rules.deinit();
        self.rules.deinit();
    }

    /// Registers a dispatch function for a given pair of Kind tags.
    /// If commutative, also registers the reversed pair.
    pub fn register(self: *KindDispatcher, tag1: std.meta.Tag(Kind), tag2: std.meta.Tag(Kind), func: DispatchFn) !void {
        const key = DispatchKey{ .tag1 = tag1, .tag2 = tag2 };
        try self.rules.put(key, func);

        if (self.commutative and tag2 != tag2) {
            const reversed_key = DispatchKey{ .tag1 = tag2, .tag2 = tag1 };
            try self.rules.put(reversed_key, func);
        }
    }

    /// Dispatches based on a list of kinds.
    /// NOTE: The caller is responsible for calling .deinit() on the *returned* Kind
    /// if it might contain allocated data (i.e., if it's a matrix resulting from dispatch).
    pub fn dispatch(self: *KindDispatcher, kinds: []const Kind) Allocator.Error!Kind {
        if (kinds.len == 0) return Kind.Undefined;

        var current_result = kinds[0];
        var owns_current_result = false;

        for (kinds[1..]) |next_kind| {
            const next_result = try self.dispatchBinary(current_result, next_kind);
            const own_next_result = (next_result == .matrix);

            if (owns_current_result) {
                if (current_result == .matrix and next_result == .matrix) {
                    const changed = !current_result.matrix.*.equals(next_result);
                    if (changed) current_result.deinit(self.allocator);
                } else {
                    current_result.deinit(self.allocator);
                }
            }
            current_result = next_result;
            owns_current_result = own_next_result;
        }
        return current_result;
    }
    /// Performs binary dispatch using the registered rules.
    /// Returns an allocated Kind if the registered function allocates.
    pub fn dispatchBinary(self: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
        const tag_a = @as(std.meta.Tag(Kind), a);
        const tag_b = @as(std.meta.Tag(Kind), b);

        const key = DispatchKey{ .tag1 = tag_a, .tag2 = tag_b };

        if (self.rules.get(key)) |func| {
            return func(self, a, b);
        } else if (self.commutative) {
            const reversed_key = DispatchKey{ .tag1 = tag_b, .tag2 = tag_a };
            if (self.rules.get(reversed_key)) |func| {
                return func(self, b, a);
            }
        }

        return Kind.Undefined;
    }
};
