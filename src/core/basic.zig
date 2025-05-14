const std = @import("std");
const Allocator = std.mem.Allocator;
const Hasher = std.hash.XxHash3;

const kind = @import("kind.zig");

const AssumptionsKB = struct {
    pub fn initDefault(allocator: Allocator) AssumptionsKB {
        _ = allocator;
        return .{};
    }

    pub fn deinit(self: *AssumptionsKB, allocator: Allocator) void {
        _ = self;
        _ = allocator;
    }
};

const S = struct {};

const traversal = struct {
    // pub fn preorderTraversal(root: *Const )
};

/// Defines the canonical sort order for SymPy class names.
/// Used by `Expr.compare` for establishing a consistent ordering.
const ordering_of_classes = &[_][]const u8{
    "Zero", "One", "Half", "Infinity", "NaN", "NegativeOne", "NegativeInfinity", // Singletons
    "Integer", "Rational", "Float", // Numbers
    "Exp1", "Pi", "ImaginaryUnit", // Number Symbols
    "Symbol", "Wild", "Dummy", // Symbols
    "Pow", "Mul", "Add", // Arithmetic
    "Derivative", "Integral", // Calculus
    "Abs", "Sign", "Sqrt", "Floor", "Ceiling", "Re", "Im", "Arg", "Conjugate", // Elementary Functions
    "Exp", "Log", // Exponentials
    "Sin", "Cos", "Tan", "Cot", "ASin", "ACos", "ATan", "ACot", // Trig
    "Sinh", "Cosh", "Tanh", "Coth", "ASinh", "ACosh", "ATanh", "ACoth", // Hyperbolic
    "RisingFactorial", "FallingFactorial", "factorial", "binomial", // Combinatorial
    "Gamma", "LowerGamma", "UpperGamma", "PolyGamma", // Gamma related
    "Erf", // Error functions
    "ChebyshevT", "ChebyshevU", // Polynomials (Note: Python uses Chebyshev, Chebyshev2)
    "Function", "AppliedUndef", "WildFunction", "Lambda", // General Functions
    "Order", // Landau Order
    "Equality", "Unequality", "StrictGreaterThan", "StrictLessThan", "GreaterThan", "LessThan", // Relations
    "BooleanTrue", "BooleanFalse", // Booleans
};

// --- VTable Definition ---

/// VTable for `Basic` enabling polymorphic behavior.
/// Each concrete SymPy type (Symbol, Add, etc.) will provide an implementation.
pub const BasicVTable = struct {
    destroy: *const fn (self: *Basic) void,
    clone: *const fn (self: *const Basic, allocator: Allocator) !Basic,

    hash_content: *const fn (self: *const Basic, hasher: *Hasher) void,
    eq_content: *const fn (self: *const Basic, other: *const Basic) bool,
    compare_content: *const fn (self: *const Basic, other: *const Basic) std.math.Order,

    get_func_name: *const fn (self: *const Basic) []const u8,
    get_args: *const fn (self: *const Basic) []*Basic,
    get_kind: *const fn (self: *const Basic) Kind,
    get_class_key: *const fn (self: *const Basic) struct { u32, u32, []const u8 },

    isAtom: *const fn (self: *const Basic) bool,
    isNumber: *const fn (self: *const Basic) bool,
    isSymbol: *const fn (self: *const Basic) bool,
    // TODO: add meny more type checks

    free_symbol: *const fn (self: *const Basic, allocator: Allocator) !std.ArrayList(*Basic),
    eval_subs: *const fn (self: *const Basic, old_expr: *const Basic, new_expr: *const Basic, allocator: Allocator) !?*Basic,
    doit: *const fn (self: *const Basic, hints: anytype, allocator: Allocator) !*Basic,

    recreate_with_args: *const fn (vtable_for_type: *const BasicVTable, args_list: []*Basic, allocator: Allocator, original_kind: kind.Kind) !*Basic,
};

/// Base struct for all SymPy objects in Zig.
///
/// Notes and conventions (adapted from Python):
/// 1. Always use `.args()`, when accessing parameters of some instance.
/// 2. In Zig, direct field access (like `_args`) is possible but typically done
///    within the module. Public API is via methods.
/// 3. Memory management is manual. `destroy()` must be called on heap-allocated `Basic` objects.
///    `Basic` instances typically own their `_args` (children), meaning they are cloned
///    upon creation and destroyed when the parent is destroyed.
pub const Basic = struct {
    vtable: *const BasicVTable,
    allocator: Allocator,
    _mhash: ?u64,
    _args: []*Basic,
    // _a
};
