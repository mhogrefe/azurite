/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Test whether a `UInt64` is a positive power of two (i.e. `2^k` for some `k`).
Returns `false` for `0`. Uses the classical bit trick `u &&& (u - 1) == 0` for nonzero `u`. -/
@[inline]
def isPowerOfTwo (u : UInt64) : Bool := u != 0 && (u &&& (u - 1) == 0)

end UInt64
