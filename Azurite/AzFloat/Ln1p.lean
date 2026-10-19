/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnBracket

/-!
## `ln (1 + x)`

`ln1pPrecRound x p mode` is `ln (1 + x)` (MCA's `log1p`, §4.4.2 and Exercise 4.9) correctly
rounded to precision `p` in `mode`, with the comparison against the exact value; `ln1p x p` rounds
to nearest.  MCA evaluates `log1p` by argument reduction and a power series in `O(√n M(n))`; the
AGM logarithm of `LnBracket.lean` is `O(log n · M(n))`, so the bracket here is `ln` of the float
`y = ⌊1 + x⌋_w` (one rounded addition, one AGM run), the upper end widened by
`2^(2−w) ≥ ln ((1 + x)/y)` (`ln1pApprox`).  The point of `log1p` is small `|x|`: there `1 + x` loses
the leading zero bits of `x`, so for `|x| < 1` with exponent `e ≤ 0` the certified Ziv loop starts
at `p + 64 − e` instead of `p + 64`, and the first level already determines the rounding; the loop
needs no fuel since `ln (1 + x)` is irrational for every float `x ≠ 0` (`irrational_log_rat`).
Special values: `ln1p NaN = NaN`, `ln1p (+∞) = +∞`, `ln1p (−∞) = NaN`, `ln1p 0 = 0` exactly,
`ln1p (−1) = −∞`, `ln1p x = NaN` for `x < −1`.  The specification `ln1pPrecRound_eq_liftVal` is in
`Equiv/Ln1p.lean`.
-/

namespace Azurite.AzFloat

/-- The number of leading zero bits of a float of exponent `e` with `|x| < 1`: `−e` for `e ≤ 0`,
else `0` (only the start of the working precision depends on it). -/
def leadingZeroBits (e : AzInt) : Nat := if e.sign then 0 else e.abs.toUInt64.toNat

/-- `ln (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def ln1pPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite true e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (ln1pApprox (finite true e q m hv)) p mode
        (p + zivGuardBits + leadingZeroBits e)
        (ln1pApprox_isSome_exists p mode (toVal_finite true e q m hv)
          (by linarith [finiteVal_true_pos e hv]) (finiteVal_true_pos e hv).ne' _
          (by unfold zivGuardBits; omega))
  | finite false e q m hv =>
    if hneg : e.sign = true ∧ e.abs ≠ 0 then
      if eqIEEE (finite false e q m hv) (-one) then (infinity false, .eq) else (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (ln1pApprox (finite false e q m hv)) p mode
        (p + zivGuardBits + leadingZeroBits e)
        (ln1pApprox_isSome_exists p mode (toVal_finite false e q m hv)
          (finiteVal_false_gt_neg_one e hv hneg) (finiteVal_false_ne_zero e hv) _
          (by unfold zivGuardBits; omega))

/-- `ln (1 + x)` rounded to nearest at the precision of `x`. -/
def ln1p (x : AzFloat) : AzFloat := (ln1pPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
