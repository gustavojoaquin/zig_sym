const std = @import("std");
const logic = @import("../logic.zig");

test "test Logic Operators" {
    const allocator = std.testing.allocator;

    const a = try logic.LogicNode.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a); // <-- Added defer free

    const b = try logic.LogicNode.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b); // <-- Added defer free

    // Inner createNot creates !a. Outer createNot(!!a) simplifies to 'a'
    // and *should* free the intermediate !a node.
    const not_not_a = try logic.createNot(allocator, try logic.createNot(allocator, a));
    try std.testing.expectEqual(a.*, not_not_a.*); // not_not_a is now the same pointer as a

    // createNot(a) creates !a. createAnd({a, !a}) simplifies to False.
    // createAnd *should* free the intermediate !a node passed to it.
    const not_a_contr = try logic.createNot(allocator, a); // Capture the intermediate !a
    const contradiction = try logic.createAnd(allocator, &.{ a, not_a_contr });
    try std.testing.expectEqual(logic.LogicNode.False, contradiction.*); // contradiction is &FalseNode

    const or_expr = try logic.createOr(allocator, &.{ a, b }); // Creates (a|b) node and slice
    defer logic.freeNode(allocator, or_expr); // <-- Added defer free

    // createAnd({or_expr, or_expr}) simplifies to or_expr.
    const and_expr = try logic.createAnd(allocator, &.{ or_expr, or_expr });
    try std.testing.expectEqual(or_expr.*, and_expr.*); // and_expr is now the same pointer as or_expr
}
