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

    const not_b_raw = try logic.createNot(allocator, b);
    defer logic.freeNode(allocator, not_b_raw);

    const l1 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b
    defer logic.freeNode(allocator, l1);
    const l2 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b (same structure)
    defer logic.freeNode(allocator, l2);

    try std.testing.expectEqual(true, LogicNode.eqlNodes(l1, l2));

    var hasher1 = std.hash.Wyhash.init(0);
    LogicNode.deepHashNodes(&hasher1, l1);
    var hasher2 = std.hash.Wyhash.init(0);
    LogicNode.deepHashNodes(&hasher2, l2);
    try std.testing.expectEqual(hasher1.final(), hasher2.final());

    // Check sorting/comparison - based on the new enum order (Symbol < Not)
    // Need raw !a and !b for comparison
    const not_a_raw = try logic.createNot(allocator, a);
    defer logic.freeNode(allocator, not_a_raw);
    const not_b_raw_again = try logic.createNot(allocator, b);
    defer logic.freeNode(allocator, not_b_raw_again);

    // .Symbol tag (index 2) comes before .Not tag (index 3) in the reordered enum
    try std.testing.expectEqual(.lt, LogicNode.compareNodes({}, a, not_a_raw)); // Symbol < Not
    try std.testing.expectEqual(.gt, LogicNode.compareNodes({}, not_a_raw, a)); // Not > Symbol

    // Comparing two .Not nodes compares their children
    // !a < !b because a < b (Symbol comparison handles this)
    try std.testing.expectEqual(.lt, LogicNode.compareNodes({}, not_a_raw, not_b_raw_again));
    try std.testing.expectEqual(.gt, LogicNode.compareNodes({}, not_b_raw_again, not_a_raw));

    // And node sorting: by args length, then element by element (already correct)
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

}

test "test Logic cmp" {
    const allocator = std.testing.allocator;

    const a_sym = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym);
    // defer allocator.free(a_sym.Symbol);
    // defer allocator.destroy(a_sym);
    const b_sym = try logic.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b_sym);
    // defer allocator.destroy(b_sym);
    const b_not = try logic.createNot(allocator, b_sym);
    defer logic.freeNode(allocator, b_not);
    // defer allocator.destroy(b_not);
    const l1 = try logic.createAnd(allocator, &[_]*const LogicNode{ a_sym, b_not });
    defer logic.freeNode(allocator, l1);

    const a_sym2 = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym2);
    const b_sym2 = try logic.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b_sym2);
    const not_b2 = try logic.createNot(allocator, b_sym2);
    defer logic.freeNode(allocator, not_b2);
    const l2 = try logic.createAnd(allocator, &[_]*const logic.LogicNode{ a_sym2, not_b2 });
    defer logic.freeNode(allocator, l2);

    const context = logic.LogicNode.NodeContext{};
    try std.testing.expectEqual(context.hash(l1), context.hash(l2));

    try std.testing.expect(logic.LogicNode.eqlNodes(l1, l2));
    try std.testing.expect(!logic.LogicNode.eqlNodes(l1, b_sym));

    const c_sym = try logic.createSymbol(allocator, "c");
    defer logic.freeNode(allocator, c_sym);
    const nodes_abc = [_]*const logic.LogicNode{ a_sym, b_sym, c_sym };
    // defer for (nodes_abc) |node_abc| logic.freeNode(allocator, node_abc);

    const and_abc = try logic.createAnd(allocator, &nodes_abc);
    defer logic.freeNode(allocator, and_abc);

    const a_sym3 = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym3);

    const b_sym3 = try logic.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b_sym3);

    const c_sym3 = try logic.createSymbol(allocator, "c");
    defer logic.freeNode(allocator, c_sym3);

    const node_b_a_c = [_]*const logic.LogicNode{ b_sym3, a_sym3, c_sym3 };
    // defer for (node_b_a_c) |node_bac| logic.freeNode(allocator, node_bac);

    const and_bac = try logic.createAnd(allocator, &node_b_a_c);
    defer logic.freeNode(allocator, and_bac);

    try std.testing.expect(logic.LogicNode.eqlNodes(and_abc, and_bac));

    const a_sym_cmp = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym_cmp);

    const b_sym_cmp = try logic.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b_sym_cmp);

    const not_a_sym_cmp = try logic.createNot(allocator, a_sym_cmp);
    defer logic.freeNode(allocator, not_a_sym_cmp);

    const not_b_sym_cmp = try logic.createNot(allocator, b_sym_cmp);
    defer logic.freeNode(allocator, not_b_sym_cmp);

    try std.testing.expect(logic.LogicNode.compareNodes({}, not_a_sym_cmp, not_b_sym_cmp) == .lt);
    try std.testing.expect(logic.LogicNode.compareNodes({}, not_b_sym_cmp, not_a_sym_cmp) == .gt);
}

test "test logic onearg" {
    const allocator = std.testing.allocator;

    const true_node = try logic.createTrue(allocator);
    const false_node = try logic.createFalse(allocator);

    // And() is True (empty args)
    const empty_and = try logic.createAnd(allocator, &.{});
    try std.testing.expect(logic.LogicNode.eqlNodes(empty_and, true_node));

    // Or() is False (empty args)
    const empty_or = try logic.createOr(allocator, &.{});
    try std.testing.expect(logic.LogicNode.eqlNodes(empty_or, false_node));

    // And(T) == T
    const and_t = try logic.createAnd(allocator, &.{true_node});
    try std.testing.expect(logic.LogicNode.eqlNodes(and_t, true_node));

    // And(F) == F
    const and_f = try logic.createAnd(allocator, &.{false_node});
    try std.testing.expect(logic.LogicNode.eqlNodes(and_f, false_node));

    // Or(T) == T
    const or_t = try logic.createOr(allocator, &.{true_node});
    try std.testing.expect(logic.LogicNode.eqlNodes(or_t, true_node));

    // Or(F) == F
    const or_f = try logic.createOr(allocator, &.{false_node});
    // defer logic.freeNode(allocator, or_f);
    try std.testing.expect(logic.LogicNode.eqlNodes(or_f, false_node));

    // And('a') == 'a' (simplification of single argument)
    const a_sym = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym);
    const and_a = try logic.createAnd(allocator, &.{a_sym});
    try std.testing.expect(logic.LogicNode.eqlNodes(and_a, a_sym));

    // Or('a') == 'a' (simplification of single argument)
    const or_a = try logic.createOr(allocator, &.{a_sym});
    try std.testing.expect(logic.LogicNode.eqlNodes(or_a, a_sym));
}

test "test logic xnotx" {
    const allocator = std.testing.allocator;

    const a_sym = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym);
    const not_a = try logic.createNot(allocator, a_sym);
    defer logic.freeNode(allocator, not_a);

    const true_node = try logic.createTrue(allocator);
    const false_node = try logic.createFalse(allocator);

    // And('a', Not('a')) == F
    const and_a_not_a = try logic.createAnd(allocator, &.{ a_sym, not_a });
    try std.testing.expect(logic.LogicNode.eqlNodes(and_a_not_a, false_node));

    // Or('a', Not('a')) == T
    const or_a_not_a = try logic.createOr(allocator, &.{ a_sym, not_a });
    try std.testing.expect(logic.LogicNode.eqlNodes(or_a_not_a, true_node));
}

test "test logic TF" {
    const allocator = std.testing.allocator;

    const true_node = try logic.createTrue(allocator);
    const false_node = try logic.createFalse(allocator);

    // And(F, F) == F
    var temp_and = try logic.createAnd(allocator, &.{ false_node, false_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_and, false_node));

    // And(F, T) == F
    temp_and = try logic.createAnd(allocator, &.{ false_node, true_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_and, false_node));

    // And(T, F) == F
    temp_and = try logic.createAnd(allocator, &.{ true_node, false_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_and, false_node));

    // And(T, T) == T
    temp_and = try logic.createAnd(allocator, &.{ true_node, true_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_and, true_node));

    // Or(F, F) == F
    var temp_or = try logic.createOr(allocator, &.{ false_node, false_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_or, false_node));

    // Or(F, T) == T
    temp_or = try logic.createOr(allocator, &.{ false_node, true_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_or, true_node));

    // Or(T, F) == T
    temp_or = try logic.createOr(allocator, &.{ true_node, false_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_or, true_node));

    // Or(T, T) == T
    temp_or = try logic.createOr(allocator, &.{ true_node, true_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_or, true_node));

    // And('a', T) == 'a'
    const a_sym = try logic.createSymbol(allocator, "a");
    defer logic.freeNode(allocator, a_sym);
    temp_and = try logic.createAnd(allocator, &.{ a_sym, true_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_and, a_sym));

    // And('b', F) == F
    const b_sym = try logic.createSymbol(allocator, "b");
    defer logic.freeNode(allocator, b_sym);
    temp_and = try logic.createAnd(allocator, &.{ b_sym, false_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_and, false_node));

    // Or('c', T) == T
    const c_sym = try logic.createSymbol(allocator, "c");
    defer logic.freeNode(allocator, c_sym);
    temp_or = try logic.createOr(allocator, &.{ c_sym, true_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_or, true_node));

    // Or('d', F) == 'd'
    const d_sym = try logic.createSymbol(allocator, "d");
    temp_or = try logic.createOr(allocator, &.{ d_sym, false_node });
    try std.testing.expect(logic.LogicNode.eqlNodes(temp_or, d_sym));
    logic.freeNode(allocator, temp_or);
}

test "test logic combine args"{
    const allocator = std.testing.allocator;

    const a1 = try logic.createSymbol(allocator, "a");
}
