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

    // l1 and l2 are created, they own their args slices but not the child nodes (a, not_b_raw).
    const l1 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b
    defer logic.freeNode(allocator, l1);
    const l2 = try logic.createAnd(allocator, &.{ a, not_b_raw }); // a & !b (same structure)
    defer logic.freeNode(allocator, l2);

    // Check structural equality using eqlNodes
    try std.testing.expectEqual(true, LogicNode.eqlNodes(l1, l2));

    // Check structural hash (should be equal for equal nodes)
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

// test "test Logic Operators" {
//     const allocator = std.testing.allocator;
//
//     const a = try logic.createSymbol(allocator, "a");
//     defer logic.freeNode(allocator, a); // Test owns original symbol 'a'
//     const b = try logic.createSymbol(allocator, "b");
//     defer logic.freeNode(allocator, b); // Test owns original symbol 'b'
//     const c = try logic.createSymbol(allocator, "c");
//     defer logic.freeNode(allocator, c); // Test owns original symbol 'c'
//
//     // Test !!a -> a simplification and memory cleanup
//     const not_a_intermediate = try logic.createNot(allocator, a); // Creates a .Not node wrapping 'a'. This node is dynamically allocated by createNot.
//     // When we call createNot on not_a_intermediate, it simplifies to 'a' and *frees* not_a_intermediate internally.
//     const not_not_a = try logic.createNot(allocator, not_a_intermediate); // Should return 'a' (the original 'a' node). createNot frees not_a_intermediate.
//     // The result not_not_a is the same pointer as 'a'. We don't free 'a' here, it's handled by its defer.
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(a, not_not_a)); // not_not_a structurally equals 'a'
//     try std.testing.expectEqual(a, not_not_a); // not_not_a *is* the same pointer as 'a'
//
//     // Test !(True) -> False
//     const true_node = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, true_node);
//     const not_true = try logic.createNot(allocator, true_node);
//     defer logic.freeNode(allocator, not_true); // not_true is a newly allocated False node
//
//     const expected_false = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, expected_false);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(not_true, expected_false)); // Compare structurally
//
//     // Test !(False) -> True
//     const false_node = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, false_node);
//     const not_false = try logic.createNot(allocator, false_node);
//     defer logic.freeNode(allocator, not_false); // not_false is a newly allocated True node
//
//     const expected_true = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, expected_true);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(not_false, expected_true)); // Compare structurally
//
//     // Test De Morgan's: !(a & b) -> !a | !b
//     const a_and_b = try logic.createAnd(allocator, &.{ a, b }); // Creates a & b. This node is dynamically allocated.
//     defer logic.freeNode(allocator, a_and_b); // Test owns a_and_b
//
//     const not_a_and_b = try logic.createNot(allocator, a_and_b); // Creates !(a & b) -> !a | !b. This node is dynamically allocated.
//     defer logic.freeNode(allocator, not_a_and_b); // Test owns not_a_and_b.
//
//     // Create the expected result !a | !b
//     const not_a_node = try logic.createNot(allocator, a); // Creates !a. Allocated by createNot.
//     defer logic.freeNode(allocator, not_a_node); // Test owns this intermediate !a node.
//     const not_b_node = try logic.createNot(allocator, b); // Creates !b. Allocated by createNot.
//     defer logic.freeNode(allocator, not_b_node); // Test owns this intermediate !b node.
//     const not_a_or_not_b = try logic.createOr(allocator, &.{ not_a_node, not_b_node }); // Creates !a | !b. Allocated by createOr.
//     defer logic.freeNode(allocator, not_a_or_not_b); // Test owns not_a_or_not_b.
//
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(not_a_and_b, not_a_or_not_b)); // Compare structurally
//
//     // Test De Morgan's: !(a | b) -> !a & !b
//     const a_or_b = try logic.createOr(allocator, &.{ a, b }); // Creates a | b. Allocated.
//     defer logic.freeNode(allocator, a_or_b); // Test owns a_or_b
//
//     const not_a_or_b = try logic.createNot(allocator, a_or_b); // Creates !(a | b) -> !a & !b. Allocated.
//     defer logic.freeNode(allocator, not_a_or_b); // Test owns not_a_or_b.
//
//     // We already have not_a_node and not_b_node from the previous test (if run sequentially).
//     // If tests are run in parallel, re-create them:
//     const not_a_node_2 = try logic.createNot(allocator, a);
//     defer logic.freeNode(allocator, not_a_node_2);
//     const not_b_node_2 = try logic.createNot(allocator, b);
//     defer logic.freeNode(allocator, not_b_node_2);
//     const not_a_and_not_b = try logic.createAnd(allocator, &.{ not_a_node_2, not_b_node_2 }); // Creates !a & !b. Allocated.
//     defer logic.freeNode(allocator, not_a_and_not_b); // Test owns not_a_and_not_b.
//
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(not_a_or_b, not_a_and_not_b)); // Compare structurally
//
//     // Test simplification: a & a -> a
//     const a_and_a_result = try logic.createAnd(allocator, &.{ a, a }); // Should return 'a' (the original a node)
//     // No defer freeNode on a_and_a_result because it *is* the original 'a' node.
//     try std.testing.expectEqual(a, a_and_a_result); // Check pointer equality here, as it should return the original.
//
//     // Test simplification: a | a -> a
//     const a_or_a_result = try logic.createOr(allocator, &.{ a, a }); // Should return 'a'
//     // No defer freeNode on a_or_a_result because it *is* the original 'a' node.
//     try std.testing.expectEqual(a, a_or_a_result); // Check pointer equality here.
//
//     // Test simplification: a & True -> a
//     const true_node_2 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, true_node_2);
//     const a_and_true_result = try logic.createAnd(allocator, &.{ a, true_node_2 }); // Should return 'a'
//     // No defer freeNode on a_and_true_result because it *is* the original 'a' node.
//     try std.testing.expectEqual(a, a_and_true_result); // Check pointer equality here.
//
//     // Test simplification: a | False -> a
//     const false_node_2 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, false_node_2);
//     const a_or_false_result = try logic.createOr(allocator, &.{ a, false_node_2 }); // Should return 'a'
//     // No defer freeNode on a_or_false_result because it *is* the original 'a' node.
//     try std.testing.expectEqual(a, a_or_false_result); // Check pointer equality here.
//
//     // Test contradiction: a & !a -> False
//     const not_a_contr_input = try logic.createNot(allocator, a); // Creates !a (a dynamically allocated .Not node wrapping 'a')
//     // This not_a_contr_input node is passed to createAnd. createAnd detects contradiction and frees it internally.
//     const a_and_not_a_result = try logic.createAnd(allocator, &.{ a, not_a_contr_input }); // Should return False node. createAnd frees not_a_contr_input.
//     defer logic.freeNode(allocator, a_and_not_a_result); // a_and_not_a_result is a newly allocated False node.
//
//     const expected_false_2 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, expected_false_2);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_false_2, a_and_not_a_result)); // Compare structurally
//
//     // Test contradiction: a | !a -> True
//     const not_a_contr_input_2 = try logic.createNot(allocator, a); // Creates !a (allocated .Not node)
//     // This node is passed to createOr. createOr detects contradiction and frees it internally.
//     const a_or_not_a_result = try logic.createOr(allocator, &.{ a, not_a_contr_input_2 }); // Should return True node. createOr frees not_a_contr_input_2.
//     defer logic.freeNode(allocator, a_or_not_a_result); // a_or_not_a_result is a newly allocated True node.
//
//     const expected_true_2 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, expected_true_2);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_true_2, a_or_not_a_result)); // Compare structurally
//
//     // Test simplification: And(True) -> True
//     const true_node_3 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, true_node_3);
//     const and_true_result = try logic.createAnd(allocator, &.{true_node_3}); // Should return True node
//     defer logic.freeNode(allocator, and_true_result); // and_true_result is a newly allocated True node. createAnd frees input true_node_3.
//
//     const expected_true_3 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, expected_true_3);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_true_3, and_true_result));
//
//     // Test simplification: And(False) -> False
//     const false_node_3 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, false_node_3);
//     const and_false_result = try logic.createAnd(allocator, &.{false_node_3}); // Should return False node
//     defer logic.freeNode(allocator, and_false_result); // and_false_result is a newly allocated False node. createAnd frees input false_node_3.
//
//     const expected_false_3 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, expected_false_3);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_false_3, and_false_result));
//
//     // Test simplification: Or(True) -> True
//     const true_node_4 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, true_node_4);
//     const or_true_result = try logic.createOr(allocator, &.{true_node_4}); // Should return True node
//     defer logic.freeNode(allocator, or_true_result); // or_true_result is a newly allocated True node. createOr frees input true_node_4.
//
//     const expected_true_4 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, expected_true_4);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_true_4, or_true_result));
//
//     // Test simplification: Or(False) -> False
//     const false_node_4 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, false_node_4);
//     const or_false_result = try logic.createOr(allocator, &.{false_node_4}); // Should return False node
//     defer logic.freeNode(allocator, or_false_result); // or_false_result is a newly allocated False node. createOr frees input false_node_4.
//
//     const expected_false_4 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, expected_false_4);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_false_4, or_false_result));
//
//     // Test simplification: And() -> True
//     const and_empty_result = try logic.createAnd(allocator, &.{}); // Should return True node
//     defer logic.freeNode(allocator, and_empty_result); // newly allocated True node
//     const expected_true_5 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, expected_true_5);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_true_5, and_empty_result));
//
//     // Test simplification: Or() -> False
//     const or_empty_result = try logic.createOr(allocator, &.{}); // Should return False node
//     defer logic.freeNode(allocator, or_empty_result); // newly allocated False node
//     const expected_false_5 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, expected_false_5);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_false_5, or_empty_result));
//
//     // Test De Morgan's resulting in singleton: !(a | !a) -> !(True) -> False
//     const not_a_contr_input_3_for_or = try logic.createNot(allocator, a); // Creates !a (allocated)
//     const a_or_not_a_intermediate_3 = try logic.createOr(allocator, &.{ a, not_a_contr_input_3_for_or }); // Simplifies to TrueNode. createOr frees not_a_contr_input_3_for_or.
//     defer logic.freeNode(allocator, a_or_not_a_intermediate_3); // a_or_not_a_intermediate_3 is newly allocated True node.
//
//     const not_a_or_not_a_result = try logic.createNot(allocator, a_or_not_a_intermediate_3); // Creates !(True) which simplifies to FalseNode. createNot frees a_or_not_a_intermediate_3.
//     defer logic.freeNode(allocator, not_a_or_not_a_result); // not_a_or_not_a_result is newly allocated False node.
//
//     const expected_false_6 = try logic.createFalse(allocator);
//     defer logic.freeNode(allocator, expected_false_6);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_false_6, not_a_or_not_a_result));
//
//     // Test De Morgan's resulting in singleton: !(a & !a) -> !(False) -> True
//     const not_a_contr_input_4_for_and = try logic.createNot(allocator, a); // Creates !a (allocated)
//     const a_and_not_a_intermediate_2 = try logic.createAnd(allocator, &.{ a, not_a_contr_input_4_for_and }); // Simplifies to FalseNode. createAnd frees not_a_contr_input_4_for_and.
//     defer logic.freeNode(allocator, a_and_not_a_intermediate_2); // a_and_not_a_intermediate_2 is newly allocated False node.
//
//     const not_a_and_not_a_result = try logic.createNot(allocator, a_and_not_a_intermediate_2); // Creates !(False) which simplifies to TrueNode. createNot frees a_and_not_a_intermediate_2.
//     defer logic.freeNode(allocator, not_a_and_not_a_result); // not_a_and_not_a_result is newly allocated True node.
//
//     const expected_true_6 = try logic.createTrue(allocator);
//     defer logic.freeNode(allocator, expected_true_6);
//     try std.testing.expectEqual(true, LogicNode.eqlNodes(expected_true_6, not_a_and_not_a_result));
//
//     // Test creating complex structure and freeing (using fromString)
//     const expr_str = "(!a & b) | c";
//     const expr_parsed = try logic.fromString(allocator, expr_str);
//     defer logic.freeNode(allocator, expr_parsed); // Test owns the result from fromString
//
//     // Test creating complex structure via calls
//     const not_a_complex = try logic.createNot(allocator, a);
//     defer logic.freeNode(allocator, not_a_complex); // Test owns !a
//     const not_a_and_b_complex = try logic.createAnd(allocator, &.{ not_a_complex, b });
//     defer logic.freeNode(allocator, not_a_and_b_complex); // Test owns (!a & b)
//     const expr_built = try logic.createOr(allocator, &.{ not_a_and_b_complex, c });
//     defer logic.freeNode(allocator, expr_built); // Test owns ((!a & b) | c)
//
//     // Note: The structural equality of expr_parsed and expr_built depends on the parser's
//     // ability to produce the same canonical form as the create* functions.
//     // This test primarily confirms that building complex structures and freeing works.
//
//     // Add checks for toString freeing intermediate strings
//     const simple_and = try logic.createAnd(allocator, &.{ a, b });
//     defer logic.freeNode(allocator, simple_and);
//     const simple_and_str = try simple_and.toString(allocator);
//     defer allocator.free(simple_and_str); // Caller frees the final string
//     try std.testing.expectEqualStrings("((a & b))", simple_and_str);
//
//     const simple_or = try logic.createOr(allocator, &.{ a, b });
//     defer logic.freeNode(allocator, simple_or);
//     const simple_or_str = try simple_or.toString(allocator);
//     defer allocator.free(simple_or_str); // Caller frees the final string
//     try std.testing.expectEqualStrings("((a | b))", simple_or_str);
//
//     const not_a_str = try not_a_complex.toString(allocator); // not_a_complex is !a
//     defer allocator.free(not_a_str);
//     try std.testing.expectEqualStrings("!a", not_a_str);
//
//     const a_str = try a.toString(allocator);
//     defer allocator.free(a_str);
//     try std.testing.expectEqualStrings("a", a_str);
// }
