/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiConstants
import Azurite.AzFloat.Equiv.AtanBracket

/-!
## The arctangent

`atanPrecRound x p mode` is `arctan x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `atan x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `atanApprox` (`AzFloat/AtanBracket.lean`):
for `|x| < 1` a Newton-like iteration of order five on `tan y = |x|` whose steps are certified
by the addition formula `arctan t = y + arctan ((t cos y − sin y)/(cos y + t sin y))`, the sine
and the cosine from Algorithm 4.4 (SinCos) of *Modern Computer Arithmetic*; for `|x| ≥ 1` the
same for `1/|x|` and `arctan |x| = π/2 − arctan (1/|x|)`; the ends negated and swapped for
`x < 0`.  The loop terminates because `arctan x` is irrational for every nonzero float `x`
(`irrational_arctan_rat`, from `irrational_tan_rat`).

**Extreme arguments.**  Tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) never reach the loop:
`atanTiny?` rounds from `|x| − |x|³ ≤ arctan |x| < |x|` by one test, at a cost independent of
`e`.  Small `x` above that threshold are computed with relative accuracy (the level of the
iteration grows with `−e`).  For a huge `x` the result is next to `π/2` and the loop works at
the absolute accuracy of the Ziv level, whatever the exponent.

Special values: `arctan NaN = NaN`, `arctan (±∞) = ±π/2` (correctly rounded), `arctan 0 = 0`
exactly.
-/

namespace Azurite.AzFloat

/-- `arctan x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`). -/
def atanPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity true => piDiv2PrecRound p mode
  | infinity false =>
    let r := piDiv2PrecRound p (-mode)
    (-r.1, r.2.swap)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match atanTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        zivLoopCertified (atanApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (atanApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (finiteVal_neg_iff s e hv)
            (abs_finiteVal_bounds s e hv).1 (abs_finiteVal_bounds s e hv).2
            (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `arctan x` rounded to nearest at the precision of `x`. -/
def atan (x : AzFloat) : AzFloat := (atanPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
