/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.TanBracket

/-!
## The tangent

`tanPrecRound x p mode` is `tan x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `tan x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `tanApprox` (`AzFloat/TanBracket.lean`):
the quotient of the two components of the joint bracket of `sin |x|` and `cos x`
(`sinCosBracket`: one exact argument reduction, Algorithm 4.4 (SinCos) of *Modern Computer
Arithmetic*, three double-angle steps), the ends negated and swapped for `x < 0`.  A float is
never a pole of the tangent (`cos x` is irrational for `x ≠ 0`); at a working precision that does
not yet separate `x` from the nearest pole the bracket is a placeholder that the rounding test
rejects, and the loop raises the precision.  It terminates because `tan x` is irrational for
every nonzero float `x` (`irrational_tan_rat`).

**Extreme arguments.**  Tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) never reach the loop:
`tanTiny?` rounds from `|x| < tan |x| ≤ |x| + |x|³` by one test, at a cost independent of `e`.
For a huge `x` the reduction needs `π` to about `e` bits beyond the target precision; near a
multiple of `π` (small result) or an odd multiple of `π/2` (large result) the loop raises the
precision until the result is resolved.

Special values: `tan NaN = tan (±∞) = NaN`, `tan 0 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- `tan x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`). -/
def tanPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match tanTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        zivLoopCertified (tanApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (tanApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (finiteVal_neg_iff s e hv)
            (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `tan x` rounded to nearest at the precision of `x`. -/
def tan (x : AzFloat) : AzFloat := (tanPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
