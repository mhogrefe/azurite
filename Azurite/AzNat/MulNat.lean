/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul

/-!
## Multiplication by a machine-sized natural

`x.mulNat a` is `x · a` for a `Nat` `a`: a single-limb multiplication (`mulUInt64`) when
`a < 2^63` — a scalar comparison, no boxing — and the general product otherwise.  For loops
whose small factors are computed in `Nat`.  The proof is in `Azurite/AzNat/Equiv/MulNat.lean`.
-/

namespace Azurite.AzNat

/-- `x · a` for a natural `a`: a single-limb multiplication when `a < 2^63`. -/
def mulNat (x : AzNat) (a : Nat) : AzNat :=
  if a ≤ 9223372036854775807 then mulUInt64 x a.toUInt64 else x * AzNat.ofNat a

end Azurite.AzNat
