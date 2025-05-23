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
    defer a.release(allocator);
    const b = try logic.createSymbol(allocator, "b");
    defer b.release(allocator);
    const c = try logic.createSymbol(allocator, "c");
    defer c.release(allocator);

    const not_b_raw = try logic.createNot(allocator, b);
    defer not_b_raw.release(allocator);

    const l1 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b
    defer l1.release(allocator);
    const l2 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b (same structure)
    defer l2.release(allocator);
    try std.testing.expect(l2.eqlNodes(l1));

    var hasher1 = std.hash.Wyhash.init(0);
    l1.deepHashNodes(&hasher1);
    var hasher2 = std.hash.Wyhash.init(0);
    l2.deepHashNodes(&hasher2);
    try std.testing.expectEqual(hasher1.final(), hasher2.final());

    // Check sorting/comparison - based on the new enum order (Symbol < Not)
    // Need raw !a and !b for comparison
    const not_a_raw = try logic.createNot(allocator, a);
    defer not_a_raw.release(allocator);
    const not_b_raw_again = try logic.createNot(allocator, b);
    defer not_b_raw_again.release(allocator);

    // .Symbol tag (index 2) comes before .Not tag (index 3) in the reordered enum
    try std.testing.expectEqual(.lt, logic.compareNodes({}, a, not_a_raw)); // Symbol < Not
    try std.testing.expectEqual(.gt, logic.compareNodes({}, not_a_raw, a)); // Not > Symbol

    // Comparing two .Not nodes compares their children
    // !a < !b because a < b (Symbol comparison handles this)
    try std.testing.expectEqual(.lt, logic.compareNodes({}, not_a_raw, not_b_raw_again));
    try std.testing.expectEqual(.gt, logic.compareNodes({}, not_b_raw_again, not_a_raw));

    // And node sorting: by args length, then element by element (already correct)
    const and_abc = try logic.createAnd(allocator, &.{ a, b, c }); // canonical order a & b & c
    defer and_abc.release(allocator);
    const and_bac = try logic.createAnd(allocator, &.{ b, a, c }); // should simplify to a & b & c
    defer and_bac.release(allocator);
    const and_cba = try logic.createAnd(allocator, &.{ c, b, a }); // should simplify to a & b & c
    defer and_cba.release(allocator);

    try std.testing.expectEqual(true, and_abc.eqlNodes(and_bac));
    try std.testing.expectEqual(true, and_abc.eqlNodes(and_cba));
    try std.testing.expectEqual(true, and_bac.eqlNodes(and_cba));

    // Check comparing different And nodes
    const and_ab = try logic.createAnd(allocator, &.{ a, b });
    defer and_ab.release(allocator);
    try std.testing.expectEqual(.lt, logic.compareNodes({}, and_ab, and_abc)); // a&b < a&b&c (fewer args)

}

test "test Logic cmp" {
    const allocator = std.testing.allocator;

    const a_sym = try logic.createSymbol(allocator, "a");
    defer a_sym.release(allocator);
    const b_sym = try logic.createSymbol(allocator, "b");
    defer b_sym.release(allocator);
    const b_not = try logic.createNot(allocator, b_sym);
    defer b_not.release(allocator);
    const l1 = try logic.createAnd(allocator, &[_]*logic.Node{ a_sym, b_not });
    defer l1.release(allocator);

    const a_sym2 = try logic.createSymbol(allocator, "a");
    defer a_sym2.release(allocator);
    const b_sym2 = try logic.createSymbol(allocator, "b");
    defer b_sym2.release(allocator);
    const not_b2 = try logic.createNot(allocator, b_sym2);
    defer not_b2.release(allocator);
    const l2 = try logic.createAnd(allocator, &[_]*logic.Node{ a_sym2, not_b2 });
    defer l2.release(allocator);

    const context = logic.Node.NodeContext{};
    try std.testing.expectEqual(context.hash(l1), context.hash(l2));

    try std.testing.expect(l1.eqlNodes(l2));
    try std.testing.expect(!l1.eqlNodes(b_sym));

    const c_sym = try logic.createSymbol(allocator, "c");
    defer c_sym.release(allocator);
    const nodes_abc = [_]*logic.Node{ a_sym, b_sym, c_sym };

    const and_abc = try logic.createAnd(allocator, &nodes_abc);
    defer and_abc.release(allocator);
    const a_sym3 = try logic.createSymbol(allocator, "a");
    defer a_sym3.release(allocator);
    const b_sym3 = try logic.createSymbol(allocator, "b");
    defer b_sym3.release(allocator);
    const c_sym3 = try logic.createSymbol(allocator, "c");
    defer c_sym3.release(allocator);
    const node_b_a_c = [_]*logic.Node{ b_sym3, a_sym3, c_sym3 };

    const and_bac = try logic.createAnd(allocator, &node_b_a_c);
    defer and_bac.release(allocator);

    try std.testing.expect(and_abc.eqlNodes(and_bac));

    const a_sym_cmp = try logic.createSymbol(allocator, "a");
    defer a_sym_cmp.release(allocator);
    const b_sym_cmp = try logic.createSymbol(allocator, "b");
    defer b_sym_cmp.release(allocator);
    const not_a_sym_cmp = try logic.createNot(allocator, a_sym_cmp);
    defer not_a_sym_cmp.release(allocator);
    const not_b_sym_cmp = try logic.createNot(allocator, b_sym_cmp);
    defer not_b_sym_cmp.release(allocator);

    try std.testing.expect(logic.compareNodes({}, not_a_sym_cmp, not_b_sym_cmp) == .lt);
    try std.testing.expect(logic.compareNodes({}, not_b_sym_cmp, not_a_sym_cmp) == .gt);
}

test "test logic onearg" {
    const allocator = std.testing.allocator;

    const true_node = try logic.createTrue(allocator);
    defer true_node.release(allocator);
    const false_node = try logic.createFalse(allocator);
    defer false_node.release(allocator);

    // And() is True (empty args)
    const empty_and = try logic.createAnd(allocator, &.{});
    defer empty_and.release(allocator);
    try std.testing.expect(empty_and.eqlNodes(true_node));

    // Or() is False (empty args)
    const empty_or = try logic.createOr(allocator, &.{});
    defer empty_or.release(allocator);
    try std.testing.expect(empty_or.eqlNodes(false_node));

    // And(T) == T
    const and_t = try logic.createAnd(allocator, &.{true_node});
    defer and_t.release(allocator);
    try std.testing.expect(and_t.eqlNodes(true_node));

    // And(F) == F
    const and_f = try logic.createAnd(allocator, &.{false_node});
    defer and_f.release(allocator);
    try std.testing.expect(and_f.eqlNodes(false_node));

    // Or(T) == T
    const or_t = try logic.createOr(allocator, &.{true_node});
    defer or_t.release(allocator);
    try std.testing.expect(or_t.eqlNodes(true_node));

    // Or(F) == F
    const or_f = try logic.createOr(allocator, &.{false_node});
    defer or_f.release(allocator);
    try std.testing.expect(or_f.eqlNodes(false_node));

    // And('a') == 'a' (simplification of single argument)
    const a_sym = try logic.createSymbol(allocator, "a");
    defer a_sym.release(allocator);
    const and_a = try logic.createAnd(allocator, &.{a_sym});
    defer and_a.release(allocator);
    try std.testing.expect(and_a.eqlNodes(a_sym));

    // Or('a') == 'a' (simplification of single argument)
    const or_a = try logic.createOr(allocator, &.{a_sym});
    defer or_a.release(allocator);
    try std.testing.expect(or_a.eqlNodes(a_sym));
}

test "test logic xnotx" {
    const allocator = std.testing.allocator;

    const a_sym = try logic.createSymbol(allocator, "a");
    defer a_sym.release(allocator);
    const not_a = try logic.createNot(allocator, a_sym);
    defer not_a.release(allocator);

    const true_node = try logic.createTrue(allocator);
    defer true_node.release(allocator);
    const false_node = try logic.createFalse(allocator);
    defer false_node.release(allocator);

    // And('a', Not('a')) == F
    const and_a_not_a = try logic.createAnd(allocator, &.{ a_sym, not_a });
    defer and_a_not_a.release(allocator);
    try std.testing.expect(and_a_not_a.eqlNodes(false_node));

    // Or('a', Not('a')) == T
    const or_a_not_a = try logic.createOr(allocator, &.{ a_sym, not_a });
    defer or_a_not_a.release(allocator);
    try std.testing.expect(or_a_not_a.eqlNodes(true_node));
}

test "test logic TF" {
    const allocator = std.testing.allocator;

    const true_node = try logic.createTrue(allocator);
    defer true_node.release(allocator);
    const false_node = try logic.createFalse(allocator);
    defer false_node.release(allocator);

    // And(F, F) == F
    var temp_and = try logic.createAnd(allocator, &.{ false_node, false_node });
    try std.testing.expect(temp_and.eqlNodes(false_node));
    temp_and.release(allocator);

    // And(F, T) == F
    temp_and = try logic.createAnd(allocator, &.{ false_node, true_node });
    try std.testing.expect(temp_and.eqlNodes(false_node));
    temp_and.release(allocator);

    // And(T, F) == F
    temp_and = try logic.createAnd(allocator, &.{ true_node, false_node });
    try std.testing.expect(temp_and.eqlNodes(false_node));
    temp_and.release(allocator);

    // And(T, T) == T
    temp_and = try logic.createAnd(allocator, &.{ true_node, true_node });
    try std.testing.expect(temp_and.eqlNodes(true_node));
    temp_and.release(allocator);

    // Or(F, F) == F
    var temp_or = try logic.createOr(allocator, &.{ false_node, false_node });
    try std.testing.expect(temp_or.eqlNodes(false_node));
    temp_or.release(allocator);

    // Or(F, T) == T
    temp_or = try logic.createOr(allocator, &.{ false_node, true_node });
    try std.testing.expect(temp_or.eqlNodes(true_node));
    temp_or.release(allocator);

    // Or(T, F) == T
    temp_or = try logic.createOr(allocator, &.{ true_node, false_node });
    try std.testing.expect(temp_or.eqlNodes(true_node));
    temp_or.release(allocator);

    // Or(T, T) == T
    temp_or = try logic.createOr(allocator, &.{ true_node, true_node });
    try std.testing.expect(temp_or.eqlNodes(true_node));
    temp_or.release(allocator);

    // And('a', T) == 'a'
    const a_sym = try logic.createSymbol(allocator, "a");
    defer a_sym.release(allocator);
    temp_and = try logic.createAnd(allocator, &.{ a_sym, true_node });
    try std.testing.expect(temp_and.eqlNodes(a_sym));
    temp_and.release(allocator);

    // And('b', F) == F
    const b_sym = try logic.createSymbol(allocator, "b");
    defer b_sym.release(allocator);
    temp_and = try logic.createAnd(allocator, &.{ b_sym, false_node });
    try std.testing.expect(temp_and.eqlNodes(false_node));
    temp_and.release(allocator);

    // Or('c', T) == T
    const c_sym = try logic.createSymbol(allocator, "c");
    defer c_sym.release(allocator);
    temp_or = try logic.createOr(allocator, &.{ c_sym, true_node });
    try std.testing.expect(temp_or.eqlNodes(true_node));
    temp_or.release(allocator);

    // Or('d', F) == 'd'
    const d_sym = try logic.createSymbol(allocator, "d");
    defer d_sym.release(allocator);
    temp_or = try logic.createOr(allocator, &.{ d_sym, false_node });
    try std.testing.expect(temp_or.eqlNodes(d_sym));
    temp_or.release(allocator);
}

test "test logic combine args" {
    const allocator = std.testing.allocator;

    const a1 = try logic.createSymbol(allocator, "a");
    defer a1.release(allocator);
    const b1 = try logic.createSymbol(allocator, "b");
    defer b1.release(allocator);
    const a2 = try logic.createSymbol(allocator, "a");
    defer a2.release(allocator);

    const and_aba = try logic.createAnd(allocator, &.{ a1, b1, a2 });
    defer and_aba.release(allocator);

    const a3 = try logic.createSymbol(allocator, "a");
    defer a3.release(allocator);
    const b2 = try logic.createSymbol(allocator, "b");
    defer b2.release(allocator);
    const and_ab = try logic.createAnd(allocator, &.{ a3, b2 });
    defer and_ab.release(allocator);

    // And('a', 'b', 'a') == And('a', 'b') (duplicate removal)
    try std.testing.expect(and_aba.eqlNodes(and_ab));

    // Or('a', 'b', 'a') == Or('a', 'b') (duplicate removal)
    const a4 = try logic.createSymbol(allocator, "a");
    defer a4.release(allocator);
    const b3 = try logic.createSymbol(allocator, "b");
    defer b3.release(allocator);
    const a5 = try logic.createSymbol(allocator, "a");
    defer a5.release(allocator);

    const or_aba = try logic.createOr(allocator, &.{ a4, b3, a5 });
    defer or_aba.release(allocator);

    const a6 = try logic.createSymbol(allocator, "a");
    defer a6.release(allocator);
    const b4 = try logic.createSymbol(allocator, "b");
    defer b4.release(allocator);

    const or_ab = try logic.createOr(allocator, &.{ a6, b4 });
    defer or_ab.release(allocator);

    try std.testing.expect(or_aba.eqlNodes(or_ab));

    // And(And('a', 'b'), And('c', 'd')) == And('a', 'b', 'c', 'd') (flattening)
    const a7 = try logic.createSymbol(allocator, "a");
    defer a7.release(allocator);
    const b5 = try logic.createSymbol(allocator, "b");
    defer b5.release(allocator);

    const and_ab_1 = try logic.createAnd(allocator, &.{ a7, b5 });
    defer and_ab_1.release(allocator);

    const c = try logic.createSymbol(allocator, "c");
    defer c.release(allocator);
    const d = try logic.createSymbol(allocator, "d");
    defer d.release(allocator);

    const and_cd = try logic.createAnd(allocator, &.{ c, d });
    defer and_cd.release(allocator);

    const and_ab_cd = try logic.createAnd(allocator, &.{ and_ab_1, and_cd });
    defer and_ab_cd.release(allocator);

    const a8 = try logic.createSymbol(allocator, "a");
    defer a8.release(allocator);
    const b6 = try logic.createSymbol(allocator, "b");
    defer b6.release(allocator);
    const c1 = try logic.createSymbol(allocator, "c");
    defer c1.release(allocator);
    const d1 = try logic.createSymbol(allocator, "d");
    defer d1.release(allocator);

    const and_abcd = try logic.createAnd(allocator, &.{ a8, b6, c1, d1 });
    defer and_abcd.release(allocator);

    try std.testing.expect(and_ab_cd.eqlNodes(and_abcd));

    // Or(Or('a', 'b'), Or('c', 'd')) == Or('a', 'b', 'c', 'd') (flattening)
    const a9 = try logic.createSymbol(allocator, "a");
    defer a9.release(allocator);
    const b7 = try logic.createSymbol(allocator, "b");
    defer b7.release(allocator);

    const or_ab_1 = try logic.createOr(allocator, &.{ a9, b7 });
    defer or_ab_1.release(allocator);

    const c2 = try logic.createSymbol(allocator, "c");
    defer c2.release(allocator);
    const d2 = try logic.createSymbol(allocator, "d");
    defer d2.release(allocator);

    const or_cd = try logic.createOr(allocator, &.{ c2, d2 });
    defer or_cd.release(allocator);

    const or_ab_cd = try logic.createOr(allocator, &.{ or_ab_1, or_cd });
    defer or_ab_cd.release(allocator);

    const a10 = try logic.createSymbol(allocator, "a");
    defer a10.release(allocator);
    const b8 = try logic.createSymbol(allocator, "b");
    defer b8.release(allocator);
    const c3 = try logic.createSymbol(allocator, "c");
    defer c3.release(allocator);
    const d3 = try logic.createSymbol(allocator, "d");
    defer d3.release(allocator);

    const or_abcd_1 = try logic.createOr(allocator, &.{ a10, b8, c3, d3 });
    defer or_abcd_1.release(allocator);

    try std.testing.expect(or_ab_cd.eqlNodes(or_abcd_1));

    // Or('t', And('n', 'p', 'r'), And('n', 'r'), And('n', 'p', 'r'), 't', And('n', 'r')) == Or('t', And('n', 'p', 'r'), And('n', 'r')) (complex simplification)
    const t_sym = try logic.createSymbol(allocator, "t");
    defer t_sym.release(allocator);
    const n_sym = try logic.createSymbol(allocator, "n");
    defer n_sym.release(allocator);
    const p_sym = try logic.createSymbol(allocator, "p");
    defer p_sym.release(allocator);
    const r_sym = try logic.createSymbol(allocator, "r");
    defer r_sym.release(allocator);

    const and_npr = try logic.createAnd(allocator, &.{ n_sym, p_sym, r_sym });
    defer and_npr.release(allocator);

    const and_nr = try logic.createAnd(allocator, &.{ n_sym, r_sym });
    defer and_nr.release(allocator);

    const complex_or_args = [_]*logic.Node{ t_sym, and_npr, and_nr, and_npr, t_sym, and_nr };
    const complex_or = try logic.createOr(allocator, &complex_or_args);
    defer complex_or.release(allocator);

    const expected_or_args = [_]*logic.Node{ t_sym, and_npr, and_nr };
    const expected_or = try logic.createOr(allocator, &expected_or_args);
    defer expected_or.release(allocator);

    try std.testing.expect(complex_or.eqlNodes(expected_or));
}
