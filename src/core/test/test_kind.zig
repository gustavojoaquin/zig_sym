const std = @import("std");
const kind = @import("../kind.zig");

test "Number * Number results in Number" {
    const allocator = std.testing.allocator;
    var dispatcher = kind.KindDispatcher.init(allocator, "test", true);
    const result = try dispatcher.dispatch(&.{ kind.Kind.Number, kind.Kind.Number });
    std.debug.print("All your {s} are belong to us.\n", .{"codebase"});
    try std.testing.expect(kind.Kind.equals(result, kind.Kind.Number));
}

test "Number * Matrix(Number) result in Matrix(Number)" {
    const allocator = std.testing.allocator;
    const elem = &kind.Kind.Number;
    const matrix = kind.Kind.Matrix(elem);
    var dispatcher = kind.KindDispatcher.init(allocator, "test", true);
    const result = try dispatcher.dispatch(&.{ kind.Kind.Number, matrix });
    try std.testing.expect(result == .matrix and kind.Kind.equals(result.matrix.*, kind.Kind.Number));
}
