const std = @import("std");
const logic = @import("../logic.zig");

test "test Logic Operators" {
    const allocator = std.testing.allocator;

    const a = try logic.LogicNode.createSymbol(allocator, "a");
    const b = try logic.LogicNode.createSymbol(allocator, "b");

    const not_not_a = try logic.createNot(allocator, try logic.createNot(allocator, a));
    try std.testing.expectEqual(a.*, not_not_a.*);

    const contradiction = try logic.createAnd(allocator, &.{ a, try logic.createNot(allocator, a) });
    try std.testing.expectEqual(logic.LogicNode.False, contradiction.*);

    const or_expr = try logic.createOr(allocator, &.{ a, b });
    const and_expr = try logic.createAnd(allocator, &.{ or_expr, or_expr });
    try std.testing.expectEqual(or_expr.*, and_expr.*);
}
