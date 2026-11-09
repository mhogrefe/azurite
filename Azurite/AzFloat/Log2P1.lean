/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Log2Bracket
import Azurite.AzFloat.LnP1

/-!
## `log₂ (1 + x)`

`log2P1PrecRound x p mode` is `log₂ (1 + x)` (C23's `log2P1`) correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `log2P1 x` rounds to nearest.  Exact
powers of two first: if `1 + x = 2^k` — detected by `onePlusPow2Exponent?` (the floor and the
ceiling of `1 + x` at the starting precision coincide and the significand is a power of two) —
the result is the integer `k`, exact.  Otherwise `log₂ (1 + x)` is irrational
(`irrational_logb_two_one_add_of_none`) and the certified Ziv loop runs on `log2P1Approx`, the
quotient of the `ln (1 + x)` bracket of `lnP1` by the bracket of `ln 2`, started at
`p + 64 + leadingZeroBits e` as `lnP1` does.  Special values as for `lnP1`: `NaN ↦ NaN`,
`+∞ ↦ +∞`, `−∞ ↦ NaN`, `0 ↦ 0` exactly, `−1 ↦ −∞`, `NaN` below `−1`.  The specification
`log2P1PrecRound_eq_liftVal` is in `Equiv/Log2P1.lean`.
-/

namespace Azurite.AzFloat

/-- `log2P1PrecRound` built on a bracket function `A` of `log₂ (1 + x)` with its Ziv certificate
`hA` (`log2P1Approx`, or `log2P1ApproxWith c` with precomputed constants). -/
def log2P1PrecRoundCore (A : AzFloat → Nat → Roundable × Roundable)
    (hA : ∀ (p : Nat) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ},
      x.toVal = some (xv : EReal) → -1 < xv → Irrational (Real.logb 2 (1 + xv)) →
      ∀ w₀ : Nat, 0 < w₀ →
      ∃ f : Nat, (roundingPossible (A x (w₀ * 2 ^ f)).1 (A x (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite true e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match h : onePlusPow2Exponent? (finite true e q m hv) (p + zivGuardBits + leadingZeroBits e)
        with
      | some k => setPrecRound (ofAzInt k) p mode
      | none =>
        zivLoopCertified (A (finite true e q m hv)) p mode
          (p + zivGuardBits + leadingZeroBits e)
          (hA p mode (toVal_finite true e q m hv)
            (by linarith [finiteVal_true_pos e hv])
            (irrational_logb_two_one_add_of_none (toVal_finite true e q m hv)
              (by unfold zivGuardBits; omega) (by linarith [finiteVal_true_pos e hv]) h)
            _ (by unfold zivGuardBits; omega))
  | finite false e q m hv =>
    if hneg : e.sign = true ∧ e.abs ≠ 0 then
      if eqIEEE (finite false e q m hv) (-one) then (infinity false, .eq) else (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match h : onePlusPow2Exponent? (finite false e q m hv) (p + zivGuardBits + leadingZeroBits e)
        with
      | some k => setPrecRound (ofAzInt k) p mode
      | none =>
        zivLoopCertified (A (finite false e q m hv)) p mode
          (p + zivGuardBits + leadingZeroBits e)
          (hA p mode (toVal_finite false e q m hv)
            (finiteVal_false_gt_neg_one e hv hneg)
            (irrational_logb_two_one_add_of_none (toVal_finite false e q m hv)
              (by unfold zivGuardBits; omega)
              (by linarith [finiteVal_false_gt_neg_one e hv hneg]) h)
            _ (by unfold zivGuardBits; omega))

/-- `log₂ (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def log2P1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  log2P1PrecRoundCore log2P1Approx @log2P1Approx_isSome_exists x p mode

/-- `log₂ (1 + x)` rounded to nearest at the precision of `x`. -/
def log2P1 (x : AzFloat) : AzFloat := (log2P1PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `log2P1PrecRound` with the constants `c`; the same result
(`log2P1PrecRoundWith_eq_log2P1PrecRound`).  (The Ziv loop starts at
`p + 64 + leadingZeroBits e`, so for small `|x|` the constants need a correspondingly finer `W`
to be used.) -/
def log2P1PrecRoundWith (c : LnConsts) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  log2P1PrecRoundCore (log2P1ApproxWith c) (@log2P1ApproxWith_isSome_exists c) x p mode

/-- `log₂ (1 + x)` rounded to nearest at the precision of `x`, with the constants `c`. -/
def log2P1With (c : LnConsts) (x : AzFloat) : AzFloat :=
  (log2P1PrecRoundWith c x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
