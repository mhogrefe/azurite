/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloat
import Azurite.AzFloat.LnP1

/-!
## `log_b (1 + x)` in a float base

`logBaseFloatP1PrecRound x b p mode` is `log_b (1 + x) = ln (1 + x) / ln b` for floats `x` and
`b`, correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`logBaseFloatP1 x b` rounds to nearest at the precision of `x`.  The working precision starts at
`p + 64 + leadingZeroBits e` as `lnP1` does.  For finite `x > −1` (so `1 + x > 0`, and
`1 + x ≠ 1`) and a positive finite base `b ≠ 1`, the odd part and dyadic exponent of `1 + x`
are computed directly from those of `x` (`onePlusDyadic`) and the common-root test
`logBaseFloatExact?` decides exactness; otherwise the certified Ziv loop runs on
`logBaseFloatP1Approx`, the `ln (1 + x)` bracket of `lnP1` divided by the clamped `ln b`
bracket.  The special values are those of `logBaseFloatPrecRound` at `1 + x`: `x = ∞`, `x = 0`
and `x = −1` delegate to it at `∞`, `1` and `0`; `NaN` for `NaN`, `−∞` and `x < −1`; `b = 1`
gives `+∞` for `x > 0` and `−∞` for `−1 < x < 0`.  The specification
`logBaseFloatP1PrecRound_eq_liftVal₂` is in `Equiv/LogBaseFloatP1.lean`.
-/

namespace Azurite.AzFloat

/-- The general case: finite `x > −1` and a positive finite base `b ≠ 1`. -/
def logBaseFloatP1Finite (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (p : Nat) [NeZero p] (mode : RoundingMode) :
    AzFloat × Ordering :=
  match hx : logBaseFloatExact? (onePlusDyadic s (dyadicExp e m) (oddPart m)).2
      (onePlusDyadic s (dyadicExp e m) (oddPart m)).1 (dyadicExp eb mb) (oddPart mb) with
  | some r => ofAzRatRound r p mode
  | none =>
    zivLoopCertified (logBaseFloatP1Approx (finite s e q m hv) (finite true eb qb mb hvb) eb)
      p mode (p + zivGuardBits + leadingZeroBits e)
      (logBaseFloatP1Approx_isSome_exists p mode (toVal_finite s e q m hv) hgt eb hvb hb1
        (irrational_logBaseFloatP1_of_none s e hv hgt eb hvb hb1 hx)
        _ (by unfold zivGuardBits; omega))

/-- Finite `x > −1`: dispatch on the base. -/
def logBaseFloatP1Pos (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match b with
  | nan => (nan, .eq)
  | infinity false => (nan, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | infinity true => (zero, .eq)
  | zero => (zero, .eq)
  | finite true eb qb mb hvb =>
    if hb1 : eqIEEE (finite true eb qb mb hvb) one = true then (infinity s, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      logBaseFloatP1Finite s e hv hgt eb hvb (finiteVal_ne_one_of_not_eqIEEE eb hvb hb1) p mode

/-- `log_b (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def logBaseFloatP1PrecRound (x b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity false => (nan, .eq)
  | infinity true => logBaseFloatPrecRound (infinity true) b p mode
  | zero => logBaseFloatPrecRound one b p mode
  | finite true e q m hv =>
    logBaseFloatP1Pos true e hv (by linarith [finiteVal_true_pos e hv]) b p mode
  | finite false e q m hv =>
    if hneg : e.sign = true ∧ e.abs ≠ 0 then
      if eqIEEE (finite false e q m hv) (-one) then logBaseFloatPrecRound zero b p mode
      else (nan, .eq)
    else logBaseFloatP1Pos false e hv (finiteVal_false_gt_neg_one e hv hneg) b p mode

/-- `log_b (1 + x)` rounded to nearest at the precision of `x`. -/
def logBaseFloatP1 (x b : AzFloat) : AzFloat :=
  (logBaseFloatP1PrecRound x b (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
