/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloat

/-!
## The logarithm of a rational in a float base

`logBaseRatFloatPrecRound q b p mode` is `log_b q = ln q / ln b` for a rational `q` and a float
`b` (Malachite's `log_base_rational_float_base`), correctly rounded to precision `p` in `mode`,
with the comparison against the exact value; `logBaseRatFloat q b p` rounds to nearest.  For
`q > 0`, `q ≠ 1` and a positive finite base `b ≠ 1`, `q = (n / d) · 2^i` with odd coprime `n`,
`d`, and `log_b q` is rational only through the float cases `d = 1` (on `n · 2^i`) and `n = 1`
(on `d · 2^(−i)`, negated) (`logBaseRatFloatExact?`), rounded once; otherwise the certified Ziv
loop runs on `logBaseRatFloatApprox`.  Special values: `NaN` for `q < 0`; `q = 0` and `q = 1`
delegate to `logBaseFloatPrecRound` at `0` and `1`; `b` `NaN`, `−∞` or negative gives `NaN`,
`b ∈ {∞, 0}` gives `0`, and `b = 1` gives `±∞` by the side of `q`.  The specification
`logBaseRatFloatPrecRound_eq` is in `Equiv/LogBaseRatFloat.lean`.
-/

namespace Azurite.AzFloat

/-- The general case: `q > 0`, `q ≠ 1`, and a positive finite base `b ≠ 1`. -/
def logBaseRatFloatFinite (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (p : Nat) [NeZero p] (mode : RoundingMode) :
    AzFloat × Ordering :=
  match hx : logBaseRatFloatExact? (ratDyadicExp q) (oddPart q.num) (oddPart q.den)
      (dyadicExp eb mb) (oddPart mb) with
  | some r => ofAzRatRound r p mode
  | none =>
    zivLoopCertified (logBaseRatFloatApprox q (finite true eb qb mb hvb) eb) p mode
      (p + zivGuardBits)
      (logBaseRatFloatApprox_isSome_exists p mode q hq eb hvb hb1
        (irrational_logBaseRatFloat_of_none q (sign_eq_true_of_toRat_pos q hq)
          (num_ne_zero_of_toRat_pos q hq) hq1 eb hvb hb1 hx)
        _ (by unfold zivGuardBits; omega))

/-- `q > 0`, `q ≠ 1`: dispatch on the base. -/
def logBaseRatFloatPos (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match b with
  | nan => (nan, .eq)
  | infinity false => (nan, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | infinity true => (zero, .eq)
  | zero => (zero, .eq)
  | finite true eb qb mb hvb =>
    if hb1 : eqIEEE (finite true eb qb mb hvb) one = true then
      if q.den < q.num then (infinity true, .eq) else (infinity false, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      logBaseRatFloatFinite q hq hq1 eb hvb (finiteVal_ne_one_of_not_eqIEEE eb hvb hb1) p mode

/-- `log_b q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def logBaseRatFloatPrecRound (q : AzRat) (b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then logBaseFloatPrecRound zero b p mode
  else if hs : q.sign = true then
    if h1 : q.num = 1 ∧ q.den = 1 then logBaseFloatPrecRound one b p mode
    else logBaseRatFloatPos q (toRat_pos_of_sign q hs h0) (toRat_ne_one_of_not_one q hs h1) b p mode
  else (nan, .eq)

/-- `log_b q` rounded to nearest at precision `p`. -/
def logBaseRatFloat (q : AzRat) (b : AzFloat) (p : Nat) : AzFloat :=
  (logBaseRatFloatPrecRound q b p .Nearest).1

end Azurite.AzFloat
