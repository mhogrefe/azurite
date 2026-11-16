/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CschBracket

/-!
## The hyperbolic cosecant

`cschPrecRound x p mode` is `csch x = 1 / sinh x = 2 / (e^x − e^(−x))` correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `csch x` rounds to
nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `cschApprox`
(`AzFloat/CschBracket.lean`), the reciprocal of the bracket of `sinh |x|`.  The loop terminates
because `sinh q`, hence `csch q`, is irrational for every rational `q ≠ 0`
(`irrational_sinh_rat`).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `2|e| ≥ p + 72`) gives a value within `|x|` of
`1/x`, inside, rounded by one test (`cschTiny?`); when `x` is a power of two, `1/x` is a float
and the Ziv loop would need about `2|e|` bits to see the side.  A huge `x` gives
`≈ ±2 e^(−|x|)`, with relative accuracy, at the cost of `exp x`; nothing underflows.

Special values: `csch NaN = NaN`, `csch (±∞) = 0` (there is no negative zero),
`csch 0 = +∞` (there is one zero only).  The function is odd: `cschPrecRound (−x) p mode` is
the negation of `cschPrecRound x p (−mode)`.
-/

namespace Azurite.AzFloat

/-- `csch x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` and a finite `x ≠ 0`). -/
def cschPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match cschTiny? s (finite s e q m hv) e p mode with
      | some r => r
      | none =>
      zivLoopCertified (cschApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
        (cschApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `csch x` rounded to nearest at the precision of `x`. -/
def csch (x : AzFloat) : AzFloat := (cschPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
