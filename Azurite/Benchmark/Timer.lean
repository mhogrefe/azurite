namespace Azurite.Benchmark

/-- Monotonic clock in nanoseconds via clock_gettime(CLOCK_MONOTONIC). -/
@[extern "azurite_mono_nanos"]
opaque monoNanos : IO UInt64

end Azurite.Benchmark
