/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace Azurite.Benchmark

/-- Monotonic clock in nanoseconds via clock_gettime(CLOCK_MONOTONIC). -/
@[extern "azurite_mono_nanos"]
opaque monoNanos : IO UInt64

end Azurite.Benchmark
