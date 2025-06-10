const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib_mod = b.addModule("zig_sym", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const test_core_mod = b.createModule(.{ .root_source_file = b.path("src/core/test_core.zig"), .target = target, .optimize = optimize });

    const lib = b.addLibrary(.{
        // .linkage = .dynamic,
        .name = "zig_sym",
        .root_module = lib_mod,
    });

    const test_core = b.addTest(.{ .name = "core", .root_module = test_core_mod });

    const test_root = b.addTest(.{ .name = "root", .root_module = lib_mod });
    b.installArtifact(lib);

    const run_core_tests = b.addRunArtifact(test_core);
    const run_root_tests = b.addRunArtifact(test_root);

    const core_step = b.step("test:core", "Run core tests");
    core_step.dependOn(&run_core_tests.step);
    const root_step = b.step("test:root", "Run root tests");
    root_step.dependOn(&run_root_tests.step);

    const test_step = b.step("test", "Run all tests");
    test_step.dependOn(core_step);
    test_step.dependOn(root_step);
}
