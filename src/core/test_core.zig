const std = @import("std");
pub const test_kind = @import("test/test_kind.zig");
pub const test_logic = @import("test/test_logic.zig");

test {
    @import("std").testing.refAllDecls(@This());
}
