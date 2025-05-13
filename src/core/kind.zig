//! This module provides a system for classifying objects by their "Kind,"
//! representing their mathematical or structural type, which may differ from their
//! specific data type. This is analogous to SymPy's kind system, allowing for
//! type-based dispatching for operations.
//!
//! Kinds can be simple (like Number, Boolean) or parameterized (like Matrix,
//! which has an element kind). The `KindDispatcher` allows registering rules
//! for how kinds combine under operations (e.g., Number + MatrixElementKind -> MatrixElementKind).
//!
//! Memory Management:
//! Parameterized Kinds like `Kind.Matrix` involve allocation. The creator of such
//! a Kind or the function returning it is responsible for ensuring `deinit` is eventually called.
//! The `KindDispatcher.dispatch` method, if it returns an allocated Kind (e.g., a new Matrix kind),
//! expects the caller to manage its deinitialization.

const std = @import("std");
const Allocator = std.mem.Allocator;
// const Mutex = std.Thread.Mutex;
const hash_map = std.hash_map;

/// Represents the mathematical or structural classification of an entity.
/// Kinds can be simple (e.g., number, boolean) or parameterized (e.g., a matrix
/// whose elements have a specific kind).
pub const Kind = union(enum) {
    undefined,
    number,
    boolean,
    /// A matrix kind, where the payload is a pointer to the Kind of its elements.
    /// This pointer is owned by this Kind instance if it was created via `Kind.Matrix`.
    matrix: *const Kind,

    /// Represents an undefined or unknown kind. Often used as a default or
    /// when a dispatch operation cannot determine a resulting kind.
    pub const Undefined: Kind = .undefined;
    /// Represents a numeric kind, encompasing scalars like integers, floats, complex numbers.
    pub const Number: Kind = .number;
    /// Represents a boolean kind.
    pub const Boolean: Kind = .boolean;

    /// Creates a `Kind.matrix` by allocating memory for its element kind.
    /// The caller is responsible for eventually calling `deinit` on the returned `Kind`
    /// to free the allocated `element_kind`.
    ///
    /// Parameters:
    ///   - allocator: The allocator to use for allocating the element kind.
    ///   - element_kind: The kind of the elements within the matrix.
    ///
    /// Returns:
    ///   A `Kind.matrix` variant, or an allocator error.
    pub fn Matrix(allocator: Allocator, element_kind: Kind) !Kind {
        // return .{ .matrix = element_kind };
        const elem_ptr = try allocator.create(Kind);
        elem_ptr.* = element_kind;
        return .{ .matrix = elem_ptr };
    }

    /// Checks if two Kinds are equal. For matrix kinds, it recursively checks
    /// the equality of their element kinds.
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

    /// Deinitializes a Kind, freeing any associated allocated memory.
    /// Currently, only `Kind.matrix` allocates memory for its element kind.
    /// This function is recursive for nested matrix kinds.
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

/// A key used for dispatching in the `KindDispatcher`. It's based on the tags
/// of two Kinds involved in a binary operation.
const DispatchKey = struct {
    tag1: std.meta.Tag(Kind),
    tag2: std.meta.Tag(Kind),

    /// Computes a hash for the 'DispatchKey'
    pub fn hash(self: DispatchKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        std.hash.autoHash(&hasher, self.tag1);
        std.hash.autoHash(&hasher, self.tag2);
        return hasher.final();
    }

    /// Check if this 'DispatchKey' is equal to another.
    pub fn eql(self: DispatchKey, other: DispatchKey) bool {
        return self.tag1 == other.tag1 and self.tag2 == other.tag2;
    }
};

/// A function pointer type for binary dispatch operations.
/// Implementations of this function determine the resulting Kind from two input Kinds.
/// If the resulting Kind is allocated (e.g., `Kind.Matrix`), the `DispatchFn` is responsible
/// for the allocation, and `KindDispatcher.dispatch` manages its lifecycle or passes
/// ownership to the caller.
pub const DispatchFn = *const fn (dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind;

// --- Specific Dispatch Functions ---

/// Dispatch function for (Number, Number) -> Number.
pub fn numberNumberDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .number and b == .number);
    _ = dispatcher;

    return Kind.Number;
}

/// Dispatch function for (Number, Matrix(ElemKind)) -> Matrix(dispatch(Number, ElemKind)).
/// Allocates a new Kind for the resulting matrix's element kind.
pub fn numberMatrixDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .number and b == .matrix);

    const b_elem_kind = b.matrix.*;
    const final_elem_kind = try dispatcher.dispatchBinary(a, b_elem_kind);

    // Note: Kind.Matrix allocates memory for final_elem_kind by copying it.
    // If final_elem_kind itself was a matrix (allocated), Kind.Matrix effectively
    // takes ownership of a *new* copy of that.
    return Kind.Matrix(dispatcher.allocator, final_elem_kind);
}
/// Dispatch function for (Undefined, Any) or (Any, Undefined) -> Undefined.
pub fn undefinedDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    _ = dispatcher;
    _ = a;
    _ = b;
    return Kind.Undefined;
}

/// Dispatch function for (Matrix(Elem1), Matrix(Elem2)) -> Matrix(dispatch(Elem1, Elem2)).
/// Allocates a new Kind for the resulting matrix's element kind.
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

/// Dispatch function for (Boolean, Boolean) -> Boolean.
pub fn booleanBooleanDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .boolean and b == .boolean);
    _ = dispatcher;
    return Kind.Boolean;
}

/// Dispatch function for (Boolean, Matrix(ElemKind)) -> Matrix(dispatch(Boolean, ElemKind)).
/// Allocates a new Kind for the resulting matrix's element kind.
pub fn booleanMatrixDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .boolean and b == .matrix);
    const b_elem_ptr = b.matrix;
    const final_elem_kind = try dispatcher.dispatchBinary(a, b_elem_ptr.*);

    const allocated_elem_ptr = try dispatcher.allocator.create(Kind);
    errdefer dispatcher.allocator.destroy(allocated_elem_ptr);
    allocated_elem_ptr.* = final_elem_kind;

    return Kind{ .matrix = allocated_elem_ptr };
}

/// Dispatch function for (Matrix(ElemKind), Boolean) -> Matrix(dispatch(ElemKind, Boolean)).
/// This often mirrors the (Boolean, Matrix) case if the underlying element operation is commutative.
pub fn matrixBooleanDispatch(dispatcher: *KindDispatcher, a: Kind, b: Kind) Allocator.Error!Kind {
    std.debug.assert(a == .matrix and b == .boolean);
    // Just reuse the same logic as booleanMatrixDispatch
    return booleanMatrixDispatch(dispatcher, b, a);
}

/// Manages and executes kind-based dispatching for operations.
/// It uses registered rules to determine the resulting Kind when an operation
/// is applied to objects of different Kinds.
pub const KindDispatcher = struct {
    name: []const u8,
    commutative: bool,
    allocator: Allocator,

    /// Stores the dispatch rules: (KindTag1, KindTag2) -> DispatchFn.
    rules: hash_map.HashMap(DispatchKey, DispatchFn, hash_map.AutoContext(DispatchKey), 80),

    /// Initializes a new KindDispatcher.
    ///
    /// Parameters:
    ///   - allocator: The allocator to be used by this dispatcher and its operations.
    ///   - name: A descriptive name for this dispatcher (e.g., "Add", "Mul").
    ///   - commutative: If true, registered rules (A, B) will automatically apply to (B, A)
    ///                  if a specific (B, A) rule is not found.
    pub fn init(allocator: Allocator, name: []const u8, commutative: bool) KindDispatcher {
        return .{
            .allocator = allocator,
            .name = name,
            .commutative = commutative,
            .rules = hash_map.HashMap(DispatchKey, DispatchFn, hash_map.AutoContext(DispatchKey), 80).init(allocator),
        };
    }

    /// Deinitializes the KindDispatcher, freeing its internal rule map.
    /// Note: This does not deinitialize Kinds that might have been returned by dispatch
    /// operations; callers are responsible for those.
    pub fn deinit(self: *KindDispatcher) void {
        // var cast_self_rules = @constCast(&self.rules);
        // cast_self_rules.deinit();
        self.rules.deinit();
    }

    /// Registers a dispatch function for a given pair of Kind tags.
    /// If `self.commutative` is true and `tag1` is different from `tag2`,
    /// the rule is also effectively registered for the reversed pair (`tag2`, `tag1`),
    /// unless a more specific rule for the reversed pair already exists.
    ///
    /// Parameters:
    ///   - tag1: The tag of the first Kind in the binary operation.
    ///   - tag2: The tag of the second Kind in the binary operation.
    ///   - func: The `DispatchFn` to call when these Kind tags are encountered.
    pub fn register(self: *KindDispatcher, tag1: std.meta.Tag(Kind), tag2: std.meta.Tag(Kind), func: DispatchFn) !void {
        const key = DispatchKey{ .tag1 = tag1, .tag2 = tag2 };
        try self.rules.put(key, func);
        // const key = DispatchKey{ .tag1 = tag1, .tag2 = tag2 };
        // try self.rules.put(key, func);
        //
        // if (self.commutative and tag2 != tag2) {
        //     const reversed_key = DispatchKey{ .tag1 = tag2, .tag2 = tag1 };
        //     try self.rules.put(reversed_key, func);
        // }
        // If commutative and tags are different, allow fallback to the same function for reversed order
        // This is handled in dispatchBinary by trying the reversed key if the direct key isn't found.
        // No need to add duplicate entries if the function is symmetrical.
        // If different functions are needed for (A,B) and (B,A) when commutative=true,
        // that would imply commutativity is only a fallback, not a strict property of the function.
        // The current dispatchBinary handles this by trying reversed if commutative.
    }

    /// Dispatches an operation across a sequence of Kinds, applying binary dispatch rules iteratively.
    /// `result_kind = op(op(kinds[0], kinds[1]), kinds[2])...`
    ///
    /// Memory Note:
    /// If the dispatch process results in an allocated `Kind` (e.g., `Kind.Matrix`),
    /// this function may perform intermediate allocations and deallocations.
    /// The *final returned Kind*, if it is an allocated type (like `Kind.Matrix`),
    /// becomes the responsibility of the caller to `deinit`.
    ///
    /// Parameters:
    ///   - kinds: A slice of Kinds to dispatch over.
    ///
    /// Returns:
    ///   The resulting `Kind` after all binary dispatches, or an error if any dispatch fails.
    ///   Returns `Kind.Undefined` if `kinds` is empty.
    pub fn dispatch(self: *KindDispatcher, kinds: []const Kind) Allocator.Error!Kind {
        if (kinds.len == 0) return Kind.Undefined;

        var current_result = kinds[0];
        // If kinds[0] was, for example, created by `Kind.Matrix()`, it's already "owned" externally.
        // This flag tracks if `current_result` is a Kind that *this dispatch function* allocated
        // and is thus responsible for deiniting if it's an intermediate result.
        var owns_current_result_internally: bool = false;

        for (kinds[1..]) |next_kind_in_sequence| {
            const prev_result_for_deinit = current_result;
            const prev_owned_internally = owns_current_result_internally;

            const dispatch_outcome = self.dispatchBinary(current_result, next_kind_in_sequence);

            // Handle error from dispatchBinary, ensuring cleanup of potentially owned current_result
            if (dispatch_outcome) |res| {
                current_result = res;
            } else |err| {
                if (prev_owned_internally) {
                    prev_result_for_deinit.deinit(self.allocator);
                }
                return err;
            }

            // The result of dispatchBinary could be a new allocation (e.g. new Matrix kind)
            owns_current_result_internally = switch (current_result) {
                .matrix => true, // Assume matrix kinds from dispatchBinary are new allocations
                else => false,
            };

            // If the previous current_result was owned internally by this loop iteration, deinit it.
            // But, be careful: if dispatchBinary returned its input (e.g. Undefined + Number -> Number),
            // current_result might point to the same thing as prev_result_for_deinit if it wasn't a matrix.
            // Or, if dispatchBinary reuses an allocation.
            // The most critical part is that if `prev_result_for_deinit` was a matrix allocated *in a previous iteration*,
            // and `current_result` is a *new* matrix (or not a matrix at all), `prev_result_for_deinit` must be freed.
            if (prev_owned_internally) {
                // If the new current_result is the *exact same allocated pointer* as the previous one,
                // then ownership just continues. Otherwise, the old one must be deinitialized.
                var deinit_previous = true;
                if (prev_result_for_deinit == .matrix and current_result == .matrix) {
                    if (prev_result_for_deinit.matrix == current_result.matrix) {
                        deinit_previous = false; // Same allocation, ownership effectively transferred.
                    }
                }
                if (deinit_previous) {
                    prev_result_for_deinit.deinit(self.allocator);
                }
            }
        }
        // The final current_result's ownership (if it's an allocated type) is transferred to the caller.
        return current_result;
    }
    /// Performs binary dispatch using registered rules for two Kinds.
    ///
    /// Memory Note:
    /// If the registered `DispatchFn` allocates a new `Kind` (e.g., `Kind.Matrix`),
    /// that newly allocated `Kind` is returned. The caller (`dispatch` or an external user)
    /// is responsible for its eventual deinitialization.
    ///
    /// Parameters:
    ///   - q: The first Kind.
    ///   - b: The second Kind.
    ///
    /// Returns:
    ///   The resulting `Kind` based on registered rules, or `Kind.Undefined` if no rule matches.
    ///   Can also return an allocator error if the dispatch function fails.
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
