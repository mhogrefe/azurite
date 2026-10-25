/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloatP1
import Azurite.AzFloat.LogBaseRatBase

/-!
## `log_b (1 + x)` in a rational base

`logBaseRatBaseP1PrecRound x b p mode` is `log_b (1 + x) = ln (1 + x) / ln b` for a float `x`
and a rational base `b`, correctly rounded to precision `p` in `mode`, with the comparison
against the exact value; `logBaseRatBaseP1 x b` rounds to nearest at the precision of `x`.  The
working precision starts at `p + 64 + leadingZeroBits e` as `lnP1` does.  For finite `x > −1`
and `b > 0`, `b ≠ 1`, the odd part and dyadic exponent of `1 + x` (`onePlusDyadic`) feed the
rational-base exactness test `logBaseRatBaseExact?`; otherwise the certified Ziv loop runs on
`logBaseRatBaseP1Approx`.  Special values: `b = 0` and `b = 1` delegate to
`logBaseFloatP1PrecRound` with the bases `zero` and `one`; `NaN` for `b < 0`, for `x` `NaN` or
`−∞` and below `−1`; `log_b ∞ = ±∞` and `log_b (1 − 1) = ∓∞` by the side of `b`;
`log_b (1 + 0) = 0`.  The specification `logBaseRatBaseP1PrecRound_eq` is in
`Equiv/LogBaseRatBaseP1.lean`.
-/

namespace Azurite.AzFloat

/-- The general case: finite `x > −1` and `b > 0`, `b ≠ 1`. -/
def logBaseRatBaseP1Finite (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) [NeZero p] (mode : RoundingMode) :
    AzFloat × Ordering :=
  match hx : logBaseRatBaseExact? (onePlusDyadic s (dyadicExp e m) (oddPart m)).2
      (onePlusDyadic s (dyadicExp e m) (oddPart m)).1 (ratDyadicExp b) (oddPart b.num)
      (oddPart b.den) with
  | some r => ofAzRatRound r p mode
  | none =>
    zivLoopCertified (logBaseRatBaseP1Approx (finite s e q m hv) b) p mode
      (p + zivGuardBits + leadingZeroBits e)
      (logBaseRatBaseP1Approx_isSome_exists p mode (toVal_finite s e q m hv) hgt b hb hb1
        (irrational_logBaseRatBaseP1_of_none s e hv hgt b (sign_eq_true_of_toRat_pos b hb)
          (num_ne_zero_of_toRat_pos b hb) hb1 hx)
        _ (by unfold zivGuardBits; omega))

/-- Finite `x > −1` and `b > 0`, `b ≠ 1`: the precision check. -/
def logBaseRatBaseP1Pos (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    logBaseRatBaseP1Finite s e hv hgt b hb hb1 p mode

/-- `b > 0`, `b ≠ 1`: dispatch on `x`. -/
def logBaseRatBaseP1Dispatch (x : AzFloat) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity false => (nan, .eq)
  | infinity true => if b.den < b.num then (infinity true, .eq) else (infinity false, .eq)
  | zero => (zero, .eq)
  | finite true e q m hv =>
    logBaseRatBaseP1Pos true e hv (by linarith [finiteVal_true_pos e hv]) b hb hb1 p mode
  | finite false e q m hv =>
    if hneg : e.sign = true ∧ e.abs ≠ 0 then
      if eqIEEE (finite false e q m hv) (-one) then
        if b.den < b.num then (infinity false, .eq) else (infinity true, .eq)
      else (nan, .eq)
    else logBaseRatBaseP1Pos false e hv (finiteVal_false_gt_neg_one e hv hneg) b hb hb1 p mode

/-- `log_b (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def logBaseRatBaseP1PrecRound (x : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : b.num = 0 then logBaseFloatP1PrecRound x zero p mode
  else if hs : b.sign = true then
    if h1 : b.num = 1 ∧ b.den = 1 then logBaseFloatP1PrecRound x one p mode
    else
      logBaseRatBaseP1Dispatch x b (toRat_pos_of_sign b hs h0) (toRat_ne_one_of_not_one b hs h1)
        p mode
  else (nan, .eq)

/-- `log_b (1 + x)` rounded to nearest at the precision of `x`. -/
def logBaseRatBaseP1 (x : AzFloat) (b : AzRat) : AzFloat :=
  (logBaseRatBaseP1PrecRound x b (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
