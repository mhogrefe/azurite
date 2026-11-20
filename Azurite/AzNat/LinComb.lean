/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd.HalfBinary
import Azurite.AzNat.MulNat
import Azurite.AzNat.Add

/-!
## A linear combination with two machine-sized coefficients

`linComb x y s t` is `x · s + y · t` for naturals `s`, `t`.  When both are below `2^63` it is
one fused pass over the limbs (`linCombLimbs`, the pass of the half-binary GCD: two wide
multiplications and one addition with carry a limb) into one array, instead of two products
and a sum — three passes, three arrays.  For recurrences with small coefficients (the tangent
numbers).  The proof is in `Azurite/AzNat/Equiv/LinComb.lean`.
-/

namespace Azurite.AzNat

/-- `x · s + y · t`: one fused pass when `s, t < 2^63`.  (The pass runs over two limbs more
than the longer operand, so its carry flag is never set; the test only spares the proof.) -/
def linComb (x y : AzNat) (s t : Nat) : AzNat :=
  if s ≤ 9223372036854775807 ∧ t ≤ 9223372036854775807 then
    let r := linCombLimbs x.limbs y.limbs s.toUInt64 t.toUInt64 false
    if r.2 then x.mulNat s + y.mulNat t else ofLimbs r.1
  else x.mulNat s + y.mulNat t

end Azurite.AzNat
