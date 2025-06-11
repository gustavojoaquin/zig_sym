//! By convention, root.zig is the root source file when making a library. If
//! you are making an executable, the convention is to delete this file and
//! start with main.zig instead.
const std = @import("std");
const testing = std.testing;

pub fn add(a: i32, b: i32) i32 {
    return a + b;
}
pub const Kind = @import("core/kind.zig");
pub const logic = @import("core/logic.zig");

test "basic add functionality" {
    try testing.expect(add(3, 7) == 10);
}

test "Kind test" {
    @import("std").testing.refAllDecls(@This());
}
