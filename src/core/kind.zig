const std = @import("std");
const Allocator = std.mem.Allocator;
const Mutex = std.Thread.Mutex;

// const Kind =  @This();

pub const Kind = union(enum) {
    undefined,
    number,
    boolean,
    matrix: *const Kind,

    pub const Undefined: Kind = .undefined;
    pub const Number: Kind = .number;
    pub const Boolean: Kind = .boolean;

    pub fn Matrix(element_kind: *const Kind) Kind {
        return .{ .matrix = element_kind };
    }

    pub fn equals(a: Kind, b: Kind) bool {
        const tag_a = @as(std.meta.Tag(Kind), a);
        const tag_b = @as(std.meta.Tag(Kind), b);

        if (tag_a != tag_b) return false;
        return switch (a) {
            .matrix => |a_elem| {
                if (b.matrix == null or a_elem == null) return a_elem == b.matrix;
                return equals(a_elem.*, b.matrix.*);
            },
            else => return true,
        };
    }
    pub fn deinit(self: Kind, allocator: Allocator) void {
        switch (self) {
            .matrix => |elem_ptr| {
                elem_ptr.*.deinit(allocator);
                allocator.destroy(@ptrCast(*Kind)@alignCast(elem_ptr));
            },
            .undefined,
            .number, boolean => {},
        }
    }
};

pub const KindDispatcher = struct {
    name: []const u8,
    commutative: bool,
    allocator: Allocator,

    pub fn init(allocator: Allocator, name: []const u8, commutative: bool) KindDispatcher {
        return .{
            .allocator = allocator,
            .name = name,
            .commutative = commutative,
        };
    }

    pub fn dispatch(self: *KindDispatcher, kinds: []const Kind) Allocator.Error!Kind {
        if (kinds.len == 0) return Kind.Undefined;

        var result = kinds[0];
        for (kinds[1..]) |kind| {
            result = try self.dispatchBinary(result, kind);
        }
        return result;
    }

    pub fn dispatchBinary(self: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
        if (self.commutative) {
            const a_order = KindOrder(a);
            const b_order = KindOrder(b);

            if (a_order > b_order) {
                return try self.dispatchBinary(b, a);
            }
        }

        return switch (a) {
            .number => switch (b) {
                .number => Kind.Number,
                .matrix => |b_elem| {
                    const elem_kind = try self.dispatchBinary(a, b_elem.*);
                    _ = elem_kind; // autofix
                    return Kind{ .matrix = try self.allocator.create(Kind) };
                },
                else => return Kind.Undefined,
            },
            .matrix => |a_elem| switch (b) {
                .number => {
                    const elem_kind = try self.dispatchBinary(a_elem.*, b);
                    _ = elem_kind; // autofix
                    return Kind{ .matrix = try self.allocator.create(Kind) };
                },
                .matrix => |b_elem| {
                    const elem_kind = try self.dispatchBinary(a_elem.*, b_elem.*);
                    _ = elem_kind; // autofix
                    return Kind{ .matrix = try self.allocator.create(Kind) };
                },
                else => return Kind.Undefined,
            },
            else => return Kind.Undefined,
        };
    }
};

fn KindOrder(k: Kind) usize {
    return switch (k) {
        .undefined => 0,
        .number => 1,
        .boolean => 2,
        .matrix => 3,
    };
}

// test "Number * Number results in Number" {
//     const allocator = std.testing.allocator;
//     var dispatcher = KindDispatcher.init(allocator, "test", true);
//     const result = try dispatcher.dispatch(&.{ Kind.Number, Kind.Number });
//     std.debug.print("All your {s} are belong to us.\n", .{"codebase"});
//     try std.testing.expect(Kind.equals(result, Kind.Number));
// }
//
// test "Number * Matrix(Number) result in Matrix(Number)" {
//     const allocator = std.testing.allocator;
//     const elem = &Kind.Number;
//     const matrix = Kind.Matrix(elem);
//     var dispatcher = KindDispatcher.init(allocator, "test", true);
//     const result = try dispatcher.dispatch(&.{ Kind.Number, matrix });
//     try std.testing.expect(result == .matrix and Kind.equals(result.matrix.*, Kind.Number));
// }
