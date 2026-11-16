/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinhBracket

/-!
## The hyperbolic sine

`sinhPrecRound x p mode` is `sinh x = (e^x − e^(−x))/2` correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `sinh x` rounds to nearest at the
precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `sinhApprox`
(`AzFloat/SinhBracket.lean`): `sinh |x| = (u + u/(1 + u))/2` with `u = exp |x| − 1`, without
cancellation.  The loop terminates because `sinh q` is irrational for every rational `q ≠ 0`
(`irrational_sinh_rat`, from the transcendence of `e^q`).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) is rounded by one test
(`tanTiny?`: `|x| < sinh |x| ≤ |x| + |x|³`), at no cost; the Ziv loop would need about `2|e|`
bits to see the side of `x`.  A huge `x` costs what `exp x` costs — about `2^e` bits of
`ln 2` — and the result, of exponent about `x / ln 2`, never overflows.

Special values: `sinh NaN = NaN`, `sinh (±∞) = ±∞`, `sinh 0 = 0` exactly.  The function is odd:
`sinhPrecRound (−x) p mode` is the negation of `sinhPrecRound x p (−mode)`.
-/

namespace Azurite.AzFloat

/-- `sinh x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` and a finite `x ≠ 0`). -/
def sinhPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => (infinity s, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match tanTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
      zivLoopCertified (sinhApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
        (sinhApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `sinh x` rounded to nearest at the precision of `x`. -/
def sinh (x : AzFloat) : AzFloat := (sinhPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
