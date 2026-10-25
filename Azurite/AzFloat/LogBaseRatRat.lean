/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatFloat

/-!
## The logarithm of a rational in a rational base

`logBaseRatRatPrecRound q b p mode` is `log_b q = ln q / ln b` for rationals `q` and `b`
(Malachite's `log_base_rational_base` for a rational argument), returning a float correctly
rounded to precision `p` in `mode`, with the comparison against the exact value;
`logBaseRatRat q b p` rounds to nearest.  For `q > 0`, `q ≠ 1`, `b > 0`, `b ≠ 1`, with
`q = (n₁/d₁) · 2^i` and `b = (n₂/d₂) · 2^j` (odd coprime pairs), `log_b q` is rational only when
it is in one of the float cases (one of the four odd parts is `1`) or when
`log_{n₂} n₁ = log_{d₂} d₁` (crosswise for a negative value) and the 2-exponents agree
(`logBaseRatRatExact?`); otherwise the certified Ziv loop runs on `logBaseRatRatApprox`.
Special values: `b = 0` and `b = 1` delegate to `logBaseRatFloatPrecRound` with the bases
`zero` and `one`; `NaN` for `b < 0` or `q < 0`; `log_b 0 = ∓∞` by the side of `b`;
`log_b 1 = 0`.  The specification `logBaseRatRatPrecRound_eq` is in
`Equiv/LogBaseRatRat.lean`.
-/

namespace Azurite.AzFloat

/-- The general case: `q > 0`, `q ≠ 1`, `b > 0`, `b ≠ 1`. -/
def logBaseRatRatFinite (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) [NeZero p] (mode : RoundingMode) :
    AzFloat × Ordering :=
  match hx : logBaseRatRatExact? (ratDyadicExp q) (oddPart q.num) (oddPart q.den)
      (ratDyadicExp b) (oddPart b.num) (oddPart b.den) with
  | some r => ofAzRatRound r p mode
  | none =>
    zivLoopCertified (logBaseRatRatApprox q b) p mode (p + zivGuardBits)
      (logBaseRatRatApprox_isSome_exists p mode q hq b hb hb1
        (irrational_logBaseRatRat_of_none q (sign_eq_true_of_toRat_pos q hq)
          (num_ne_zero_of_toRat_pos q hq) hq1 b (sign_eq_true_of_toRat_pos b hb)
          (num_ne_zero_of_toRat_pos b hb) hb1 hx)
        _ (by unfold zivGuardBits; omega))

/-- `b > 0`, `b ≠ 1`: dispatch on `q`. -/
def logBaseRatRatPos (q b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hq0 : q.num = 0 then
    if b.den < b.num then (infinity false, .eq) else (infinity true, .eq)
  else if hqs : q.sign = true then
    if hq1 : q.num = 1 ∧ q.den = 1 then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      logBaseRatRatFinite q (toRat_pos_of_sign q hqs hq0) (toRat_ne_one_of_not_one q hqs hq1) b
        hb hb1 p mode
  else (nan, .eq)

/-- `log_b q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def logBaseRatRatPrecRound (q b : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : b.num = 0 then logBaseRatFloatPrecRound q zero p mode
  else if hs : b.sign = true then
    if h1 : b.num = 1 ∧ b.den = 1 then logBaseRatFloatPrecRound q one p mode
    else logBaseRatRatPos q b (toRat_pos_of_sign b hs h0) (toRat_ne_one_of_not_one b hs h1) p mode
  else (nan, .eq)

/-- `log_b q` rounded to nearest at precision `p`. -/
def logBaseRatRat (q b : AzRat) (p : Nat) : AzFloat := (logBaseRatRatPrecRound q b p .Nearest).1

end Azurite.AzFloat
