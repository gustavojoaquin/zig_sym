const std = @import("std");
const logic = @import("../logic.zig");
const FuzzyBool = logic.FuzzyBool;
const LogicNode = logic.LogicNode;

test "Fuzzy Torf" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    const values = [_]FuzzyBool{ T, F, U };
    for (values) |v1| {
        for (values) |v2| {
            for (values) |v3| {
                const args = [_]FuzzyBool{ v1, v2, v3 };
                const expected: FuzzyBool = if (v1 == true and v2 == true and v3 == true) true else if (v1 == false and v2 == false and v3 == false) false else null;
                try std.testing.expect(expected == logic.torf(&args));
            }
        }
    }

    try std.testing.expectEqual(null, logic.torf(&[_]FuzzyBool{ true, null }));
    try std.testing.expectEqual(null, logic.torf(&[_]FuzzyBool{ null, true }));
}

test "test Fuzzy Group" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    const values = [_]FuzzyBool{ T, F, U };
    for (values) |v1| {
        for (values) |v2| {
            for (values) |v3| {
                const args = [_]FuzzyBool{ v1, v2, v3 };

                const expected_group: FuzzyBool = if (v1 == null or v2 == null or v3 == null)
                    null
                else if (v1 == true and v2 == true and v3 == true)
                    true
                else
                    false;
                try std.testing.expectEqual(expected_group, logic.fuzzyGroup(&args, false));

                var false_count: usize = 0;
                if (v1 == false) false_count += 1;
                if (v2 == false) false_count += 1;
                if (v3 == false) false_count += 1;

                const expected_group_quick: FuzzyBool = if (v1 == null or v2 == null or v3 == null)
                    null
                else if (false_count > 1)
                    null
                else if (v1 == true and v2 == true and v3 == true)
                    true
                else
                    false;
                try std.testing.expectEqual(expected_group_quick, logic.fuzzyGroup(&args, true));
            }
        }
    }
}

test "test Fuzzy Not" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    try std.testing.expectEqual(F, logic.fuzzyNot(T));
    try std.testing.expectEqual(T, logic.fuzzyNot(F));
    try std.testing.expectEqual(U, logic.fuzzyNot(U));
}

test "test Fuzzy And" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    try std.testing.expectEqual(T, logic.fuzzyAnd(&[_]FuzzyBool{ T, T }));
    try std.testing.expectEqual(F, logic.fuzzyAnd(&[_]FuzzyBool{ T, F }));
    try std.testing.expectEqual(U, logic.fuzzyAnd(&[_]FuzzyBool{ T, U }));
    try std.testing.expectEqual(F, logic.fuzzyAnd(&[_]FuzzyBool{ F, F }));
    try std.testing.expectEqual(F, logic.fuzzyAnd(&[_]FuzzyBool{ F, U }));
    try std.testing.expectEqual(U, logic.fuzzyAnd(&[_]FuzzyBool{ U, U }));
    try std.testing.expectEqual(T, logic.fuzzyAnd(&[_]FuzzyBool{ T, T, T }));
    try std.testing.expectEqual(F, logic.fuzzyAnd(&[_]FuzzyBool{ T, F, U }));
    try std.testing.expectEqual(T, logic.fuzzyAnd(&[_]FuzzyBool{})); // Empty args -> True

    try std.testing.expectEqual(U, logic.fuzzyAnd(&[_]FuzzyBool{U}));
    try std.testing.expectEqual(T, logic.fuzzyAnd(&[_]FuzzyBool{T}));
    try std.testing.expectEqual(F, logic.fuzzyAnd(&[_]FuzzyBool{F}));
}

test "test Fuzzy Or" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    try std.testing.expectEqual(T, logic.fuzzyOr(&[_]FuzzyBool{ T, T }));
    try std.testing.expectEqual(T, logic.fuzzyOr(&[_]FuzzyBool{ T, F }));
    try std.testing.expectEqual(T, logic.fuzzyOr(&[_]FuzzyBool{ T, U }));
    try std.testing.expectEqual(F, logic.fuzzyOr(&[_]FuzzyBool{ F, F }));
    try std.testing.expectEqual(U, logic.fuzzyOr(&[_]FuzzyBool{ F, U }));
    try std.testing.expectEqual(U, logic.fuzzyOr(&[_]FuzzyBool{ U, U }));
    try std.testing.expectEqual(F, logic.fuzzyOr(&[_]FuzzyBool{ F, F, F }));
    try std.testing.expectEqual(T, logic.fuzzyOr(&[_]FuzzyBool{ T, F, U }));
    try std.testing.expectEqual(F, logic.fuzzyOr(&[_]FuzzyBool{})); // Empty args -> False

    try std.testing.expectEqual(U, logic.fuzzyOr(&[_]FuzzyBool{U}));
    try std.testing.expectEqual(T, logic.fuzzyOr(&[_]FuzzyBool{T}));
    try std.testing.expectEqual(F, logic.fuzzyOr(&[_]FuzzyBool{F}));
}

test "test Fuzzy Nand" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    try std.testing.expectEqual(logic.fuzzyNot(logic.fuzzyAnd(&[_]FuzzyBool{ T, F })), logic.fuzzyNand(&[_]FuzzyBool{ T, F })); // !(T & F) = !F = T
    try std.testing.expectEqual(logic.fuzzyNot(logic.fuzzyAnd(&[_]FuzzyBool{ T, T })), logic.fuzzyNand(&[_]FuzzyBool{ T, T })); // !(T & T) = !T = F
    try std.testing.expectEqual(logic.fuzzyNot(logic.fuzzyAnd(&[_]FuzzyBool{ F, F })), logic.fuzzyNand(&[_]FuzzyBool{ F, F })); // !(F & F) = !F = T
    try std.testing.expectEqual(logic.fuzzyNot(logic.fuzzyAnd(&[_]FuzzyBool{ T, U })), logic.fuzzyNand(&[_]FuzzyBool{ T, U })); // !(T & U) = !U = U
    try std.testing.expectEqual(logic.fuzzyNot(logic.fuzzyAnd(&[_]FuzzyBool{ F, U })), logic.fuzzyNand(&[_]FuzzyBool{ F, U })); // !(F & U) = !F = T
    try std.testing.expectEqual(logic.fuzzyNot(logic.fuzzyAnd(&[_]FuzzyBool{ U, U })), logic.fuzzyNand(&[_]FuzzyBool{ U, U })); // !(U & U) = !U = U
}

test "test Fuzzy Xor" {
    const T: FuzzyBool = true;
    const F: FuzzyBool = false;
    const U: FuzzyBool = null;

    try std.testing.expectEqual(U, logic.fuzzyXor(&[_]FuzzyBool{U}));
    try std.testing.expectEqual(U, logic.fuzzyXor(&[_]FuzzyBool{ U, T }));
    try std.testing.expectEqual(U, logic.fuzzyXor(&[_]FuzzyBool{ U, F }));
    try std.testing.expectEqual(T, logic.fuzzyXor(&[_]FuzzyBool{ T, F }));
    try std.testing.expectEqual(F, logic.fuzzyXor(&[_]FuzzyBool{ T, T }));
    try std.testing.expectEqual(F, logic.fuzzyXor(&[_]FuzzyBool{ T, T, F }));
    try std.testing.expectEqual(T, logic.fuzzyXor(&[_]FuzzyBool{ T, T, F, T }));
}

test "test Logic Cmp and Hash" {
    const allocator = std.testing.allocator;

    const a = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a);
    const b = try logic.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b);
    const c = try logic.createSymbol(allocator, "c");
    defer logic.freeNode(allocator, c);

    // Need raw !b for comparison, not one that will be immediately simplified if possible.
    // createNot on a Symbol creates a new .Not node.
    const not_b_raw = try logic.createNot(allocator, b);
    defer logic.freeNode(allocator, not_b_raw);

    const l1 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b
    defer logic.freeNode(allocator, l1);
    const l2 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b (same structure)
    defer logic.freeNode(allocator, l2);

    // Check structural equality
    try std.testing.expectEqual(true, LogicNode.eqlNodes(l1, l2));

    // Check structural hash (should be equal for equal nodes)
    var hasher1 = std.hash.Wyhash.init(0);
    LogicNode.deepHashNodes(&hasher1, l1);
    var hasher2 = std.hash.Wyhash.init(0);
    LogicNode.deepHashNodes(&hasher2, l2);
    try std.testing.expectEqual(hasher1.final(), hasher2.final());

    // Check sorting/comparison
    // Need raw !a and !b for comparison
    const not_a_raw = try logic.createNot(allocator, a);
    defer logic.freeNode(allocator, not_a_raw);
    const not_b_raw_again = try logic.createNot(allocator, b);
    defer logic.freeNode(allocator, not_b_raw_again);

    // .Not tag comes after .Symbol tag
    try std.testing.expectEqual(.lt, LogicNode.compareNodes({}, a, not_a_raw));
    try std.testing.expectEqual(.gt, LogicNode.compareNodes({}, not_a_raw, a));

    // Comparing two .Not nodes compares their children
    try std.testing.expectEqual(.lt, LogicNode.compareNodes({}, not_a_raw, not_b_raw_again)); // !a < !b because a < b
    try std.testing.expectEqual(.gt, LogicNode.compareNodes({}, not_b_raw_again, not_a_raw)); // !b > !a because b > a

    // And node sorting: by args, then element by element
    const and_abc = try logic.createAnd(allocator, &.{ a, b, c }); // canonical order a & b & c
    defer logic.freeNode(allocator, and_abc);
    const and_bac = try logic.createAnd(allocator, &.{ b, a, c }); // should simplify to a & b & c
    defer logic.freeNode(allocator, and_bac);
    const and_cba = try logic.createAnd(allocator, &.{ c, b, a }); // should simplify to a & b & c
    defer logic.freeNode(allocator, and_cba);

    try std.testing.expectEqual(true, LogicNode.eqlNodes(and_abc, and_bac));
    try std.testing.expectEqual(true, LogicNode.eqlNodes(and_abc, and_cba));
    try std.testing.expectEqual(true, LogicNode.eqlNodes(and_bac, and_cba));

    // Check comparing different And nodes
    const and_ab = try logic.createAnd(allocator, &.{ a, b });
    defer logic.freeNode(allocator, and_ab);
    try std.testing.expectEqual(.lt, LogicNode.compareNodes({}, and_ab, and_abc)); // a&b < a&b&c (fewer args)

    // Python test `(Not('a') < 2) is False` is not applicable in Zig due to static typing.
}

test "test Logic Operators" {
    const allocator = std.testing.allocator;

    const a = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a); // <-- Added defer free

    const b = try logic.createSymbol(allocator, "b");
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
