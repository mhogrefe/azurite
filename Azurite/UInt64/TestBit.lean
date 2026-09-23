/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Return the `i`-th bit of `u` (0-indexed, LSB first). Returns `false` for `i ≥ 64`. -/
@[inline]
def testBit (u : UInt64) (i : Nat) : Bool :=
  if i < 64 then (u >>> UInt64.ofNat i) &&& 1 != 0 else false

end UInt64
