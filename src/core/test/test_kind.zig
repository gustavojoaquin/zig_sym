const std = @import("std");
const kind = @import("../kind.zig");
const Kind = @import("../kind.zig").Kind;
const KindDispatcher = @import("../kind.zig").KindDispatcher;
const Allocator = std.mem.Allocator;

fn createTestDispatcher(allocator: Allocator) !KindDispatcher {
    var dispatcher = KindDispatcher.init(allocator, "test", true);
    try dispatcher.register(.number, .number, &kind.numberNumberDispatch);
    try dispatcher.register(.number, .matrix, &kind.numberMatrixDispatch);
    try dispatcher.register(.matrix, .matrix, &kind.matrixMatrixDispatch);
    try dispatcher.register(.undefined, .number, &kind.undefinedDispatch);
    try dispatcher.register(.undefined, .boolean, &kind.undefinedDispatch);
    try dispatcher.register(.undefined, .matrix, &kind.undefinedDispatch);
    try dispatcher.register(.undefined, .undefined, &kind.undefinedDispatch);
    return dispatcher;
}

test "Number * Number results in Number" {
    const allocator = std.testing.allocator;
    var dispatcher = try createTestDispatcher(allocator);
    defer dispatcher.deinit();

    const result = try dispatcher.dispatch(&.{ Kind.Number, Kind.Number });
    defer if (result == .matrix) result.deinit(allocator);

    try std.testing.expect(Kind.equals(result, Kind.Number));
}

test "Number * Matrix(Number) result in Matrix(Number)" {
    const allocator = std.testing.allocator;
    var dispatcher = try createTestDispatcher(allocator);
    defer dispatcher.deinit();

    // const input_elem = Kind.Number;
    const matrix = try Kind.Matrix(allocator, Kind.Number);
    defer if (matrix == .matrix) matrix.deinit(allocator);
    // std.debug.print("{}", .{matrix});

    const result = try dispatcher.dispatch(&.{ Kind.Number, matrix });
    defer result.deinit(allocator);

    try std.testing.expect(result == .matrix);
    switch (result) {
        .matrix => |elem_ptr| try std.testing.expect(elem_ptr.* == .number),
        else => try std.testing.expect(false),
    }
}

test "Matrix(Number) * Matrix(Number) result in Matrix(Number)" {
    const allocator = std.testing.allocator;
    var dispatcher = try createTestDispatcher(allocator);
    defer dispatcher.deinit();

    const input_elem = Kind.Number;
    const matrix1 = try Kind.Matrix(allocator, input_elem);
    const matrix2 = try Kind.Matrix(allocator, input_elem);

    defer if (matrix1 == .matrix) matrix1.deinit(allocator);
    defer if (matrix2 == .matrix) matrix2.deinit(allocator);

    const result = try dispatcher.dispatch(&.{ matrix1, matrix2 });
    defer result.deinit(allocator);

    try std.testing.expect(result == .matrix);

    switch (result) {
        .matrix => |elem_ptr| try std.testing.expect(elem_ptr.* == .number),
        else => try std.testing.expect(false),
    }
}

test "Number * Matrix(Matrix(Number)) results in Matrix(Matrix(Number))" {
    const allocator = std.testing.allocator;
    var dispatcher = try createTestDispatcher(allocator);
    defer dispatcher.deinit();

    const inner_elem = Kind.Number;
    const inner_matrix = try Kind.Matrix(allocator, inner_elem);
    const outer_matrix = try Kind.Matrix(allocator, inner_matrix);

    defer if (outer_matrix == .matrix) outer_matrix.deinit(allocator);

    const result = try dispatcher.dispatch(&.{ Kind.Number, outer_matrix });
    defer result.deinit(allocator);

    try std.testing.expect(result == .matrix);
    switch (result) {
        .matrix => |outer_elem_ptr| {
            try std.testing.expect(outer_elem_ptr.* == .matrix);
            switch (outer_elem_ptr.*) {
                .matrix => |inner_elem_ptr| {
                    try std.testing.expect(Kind.equals(inner_elem_ptr.*, Kind.Number));
                },
                else => {
                    try std.testing.expect(false);
                },
            }
        },
        else => {
            try std.testing.expect(false);
        },
    }
}

test "Unregistered dispatch results in Undefined" {
    const allocator = std.testing.allocator;
    var dispathcer = KindDispatcher.init(allocator, "test", true);
    defer dispathcer.deinit();

    const result = try dispathcer.dispatch(&.{ Kind.Number, Kind.Boolean });
    defer result.deinit(allocator);

    try std.testing.expect(result == .undefined);
}

// test "Number * Matrix(Number) result in Matrix(Number)" {
//     const allocator = std.testing.allocator;
//     const elem = &kind.Kind.Number;
//     const matrix = kind.Kind.Matrix(elem);
//     var dispatcher = kind.KindDispatcher.init(allocator, "test", true);
//     const result = try dispatcher.dispatch(&.{ kind.Kind.Number, matrix });
//     try std.testing.expect(result == .matrix and kind.Kind.equals(result.matrix.*, kind.Kind.Number));
// }
