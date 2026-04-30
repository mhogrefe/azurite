#include <time.h>
#include <stdint.h>
#include <lean/lean.h>

/*
 * Lean FFI binding for: monoNanos : IO UInt64
 *
 * In the Lean runtime, IO UInt64 values are represented as functions
 * (lean_obj_arg → lean_obj_res) where the argument is the RealWorld token.
 * The result is a Lean IO.Result: lean_io_result_mk_ok(lean_box_uint64(v)).
 */
LEAN_EXPORT lean_obj_res azurite_mono_nanos(lean_obj_arg world) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    uint64_t ns = (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
    return lean_io_result_mk_ok(lean_box_uint64(ns));
}
