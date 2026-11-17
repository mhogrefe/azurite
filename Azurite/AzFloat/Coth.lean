/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CothBracket

/-!
## The hyperbolic cotangent

`cothPrecRound x p mode` is `coth x = 1 / tanh x = (e^x + e^(−x))/(e^x − e^(−x))` correctly
rounded to precision `p` in `mode`, with the comparison against the exact value; `coth x`
rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `cothApprox`
(`AzFloat/CothBracket.lean`): `coth |x| = 1 + 2/v` with `v = exp (2|x|) − 1`, without
cancellation.  The loop terminates because `tanh q`, hence `coth q`, is irrational for every
rational `q ≠ 0` (`irrational_tanh_rat`).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `2|e| ≥ p + 72`) gives a value within `|x|` of
`1/x`, outside, rounded by one test (`cscTiny?`).  A large `x` gives a value within
`4 e^(−2|x|)` of `±1`, outside, rounded by one test (`cothNearOne?`) as soon as `2^e ≥ p + 74`
for the exponent `e` of `x`: nothing is computed, so `coth (2^(2^30))` costs nothing.  In
between the loop needs at most a few times `p` bits.

Special values: `coth NaN = NaN`, `coth (±∞) = ±1`, `coth 0 = +∞` (there is one zero only).
The function is odd: `cothPrecRound (−x) p mode` is the negation of
`cothPrecRound x p (−mode)`.
-/

namespace Azurite.AzFloat

/-- `coth x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `x = 0`). -/
def cothPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if p = 0 then (nan, .eq) else setPrecRound (if s then one else -one) p mode
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match cscTiny? s (finite s e q m hv) e p mode with
      | some r => r
      | none =>
      match cothNearOne? s (tanhFloatN (finite s e q m hv) e) p mode with
      | some r => r
      | none =>
      zivLoopCertified (cothApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
        (cothApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `coth x` rounded to nearest at the precision of `x`. -/
def coth (x : AzFloat) : AzFloat := (cothPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
