/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Set the `i`-th bit of `u` (0-indexed, LSB first) to `1`. For `i ≥ 64` the original
value is returned; the operation is semantically invalid at those indices. -/
@[inline]
def setBit (u : UInt64) (i : Nat) : UInt64 :=
  if i < 64 then u ||| (1 <<< UInt64.ofNat i) else u

end UInt64
