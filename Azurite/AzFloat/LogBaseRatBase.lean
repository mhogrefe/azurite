/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloat

/-!
## The logarithm in a rational base

`logBaseRatBasePrecRound x b p mode` is `log_b x = ln x / ln b` for a float `x` and a rational
base `b` (Malachite's `log_base_rational_base`), correctly rounded to precision `p` in `mode`,
with the comparison against the exact value; `logBaseRatBase x b` rounds to nearest at the
precision of `x`.  For a positive finite `x ≠ 1` and `b > 0`, `b ≠ 1`, with `b = (n / d) · 2^j`
for odd coprime `n`, `d`, `log_b x` is rational only through the float cases `d = 1` (base
`n · 2^j`) and `n = 1` (base `d · 2^(−j)`, negated) (`logBaseRatBaseExact?`), rounded once;
otherwise the certified Ziv loop runs on `logBaseRatBaseApprox`, the `ln x` bracket divided by
the sign-clamped rational bracket of `ln b`.  Special values: `b = 0` and `b = 1` delegate to
`logBaseFloatPrecRound` with the bases `zero` and `one`; `NaN` for `b < 0`, for `x` `NaN`, `−∞`
or negative; `log_b ∞ = ±∞` and `log_b 0 = ∓∞` by the side of `b`; `log_b 1 = 0`.  The
specification `logBaseRatBasePrecRound_eq` is in `Equiv/LogBaseRatBase.lean`.
-/

namespace Azurite.AzFloat

/-- The general case: a positive finite `x ≠ 1` and `b > 0`, `b ≠ 1`. -/
def logBaseRatBaseFinite (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (hx1 : finiteVal true ex mx ≠ 1) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) [NeZero p] (mode : RoundingMode) :
    AzFloat × Ordering :=
  match hx : logBaseRatBaseExact? (dyadicExp ex mx) (oddPart mx) (ratDyadicExp b)
      (oddPart b.num) (oddPart b.den) with
  | some r => ofAzRatRound r p mode
  | none =>
    zivLoopCertified (logBaseRatBaseApprox (finite true ex qx mx hvx) ex b) p mode
      (p + zivGuardBits)
      (logBaseRatBaseApprox_isSome_exists p mode ex hvx b hb hb1
        (irrational_logBaseRatBase_of_none ex hvx hx1 b (sign_eq_true_of_toRat_pos b hb)
          (num_ne_zero_of_toRat_pos b hb) hb1 hx)
        _ (by unfold zivGuardBits; omega))

/-- `b > 0`, `b ≠ 1`: dispatch on `x`. -/
def logBaseRatBasePos (x : AzFloat) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity false => (nan, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | infinity true => if b.den < b.num then (infinity true, .eq) else (infinity false, .eq)
  | zero => if b.den < b.num then (infinity false, .eq) else (infinity true, .eq)
  | finite true ex qx mx hvx =>
    if hx1 : eqIEEE (finite true ex qx mx hvx) one = true then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      logBaseRatBaseFinite ex hvx (finiteVal_ne_one_of_not_eqIEEE ex hvx hx1) b hb hb1 p mode

/-- `log_b x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def logBaseRatBasePrecRound (x : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : b.num = 0 then logBaseFloatPrecRound x zero p mode
  else if hs : b.sign = true then
    if h1 : b.num = 1 ∧ b.den = 1 then logBaseFloatPrecRound x one p mode
    else logBaseRatBasePos x b (toRat_pos_of_sign b hs h0) (toRat_ne_one_of_not_one b hs h1) p mode
  else (nan, .eq)

/-- `log_b x` rounded to nearest at the precision of `x`. -/
def logBaseRatBase (x : AzFloat) (b : AzRat) : AzFloat :=
  (logBaseRatBasePrecRound x b (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
