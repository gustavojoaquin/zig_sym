const std = @import("std");

const Shape = union(enum) {
    Circle: struct {
        radius: f32,
    },
    And: struct { args: []const *const Shape },
    Square: struct {
        side_length: f32,
    },
};

// Function to get the name of the current tag
fn getShapeName(shape: Shape) []const u8 {
    return @tagName(shape);
}

pub fn main() void {
    // Correct way to create union instances
    const circle = Shape{ .Circle = .{ .radius = 5.0 } };
    const square = Shape{ .Square = .{ .side_length = 4.0 } };
    const and_no = Shape{ .And = .{ .args = &.{} } };

    std.debug.print("Shape name: {s}\n", .{getShapeName(circle)});
    std.debug.print("Shape name: {s}\n", .{getShapeName(square)});
    std.debug.print("Shape name: {s}\n", .{getShapeName(and_no)});

    const MyEnum = enum { Foo, Bar };
    const val = MyEnum.Foo;

    const name = @tagName(val);
    const type_name = @typeInfo(name);
    std.debug.print("print some test: {s}", .{name});
    std.debug.print("print type name: {s}", .{type_name});

    // const str: *const [3:0]u8 = "foo";
    // Create a slice directly from the array literal
    // const slice_of_ptr: []*const u8 = &[_]*const u8{str.ptr};
    // or equivalently:
    // const slice_of_ptr = [_]*const u8{str.ptr}[0..];
    // const slice_of_ptr: []*const u8 = &[_]*const u8{&str[0]};
    // std.debug.print("xddd: {s}", .{str});
    // std.debug.print("xddd: {s}", .{slice_of_ptr});

}
