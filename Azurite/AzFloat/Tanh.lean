/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.TanhBracket

/-!
## The hyperbolic tangent

`tanhPrecRound x p mode` is `tanh x = (e^x − e^(−x))/(e^x + e^(−x))` correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `tanh x` rounds to
nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `tanhApprox`
(`AzFloat/TanhBracket.lean`): `tanh |x| = v/(2 + v)` with `v = exp (2|x|) − 1`, without
cancellation.  The loop terminates because `tanh q` is irrational for every rational `q ≠ 0`
(`irrational_tanh_rat`).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) is rounded by one test
(`sinTiny?`: `|x| − |x|³ ≤ tanh |x| < |x|`).  A large `x` gives a value within `4 e^(−2|x|)` of
`±1`, rounded by one test (`tanhNearOne?`) as soon as `2^e ≥ p + 74` for the exponent `e` of
`x`: nothing is computed, so `tanh (2^(2^30))` costs nothing, although `exp` of that argument
is out of reach.  In between the loop needs at most a few times `p` bits.

Special values: `tanh NaN = NaN`, `tanh (±∞) = ±1`, `tanh 0 = 0` exactly.  The function is
odd: `tanhPrecRound (−x) p mode` is the negation of `tanhPrecRound x p (−mode)`.
-/

namespace Azurite.AzFloat

/-- `tanh x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `x = 0`). -/
def tanhPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if p = 0 then (nan, .eq) else setPrecRound (if s then one else -one) p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match sinTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
      match tanhNearOne? s (tanhFloatN (finite s e q m hv) e) p mode with
      | some r => r
      | none =>
      zivLoopCertified (tanhApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
        (tanhApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `tanh x` rounded to nearest at the precision of `x`. -/
def tanh (x : AzFloat) : AzFloat := (tanhPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
