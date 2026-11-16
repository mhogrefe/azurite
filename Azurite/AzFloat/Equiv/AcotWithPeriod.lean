/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.Equiv.Acot
import Azurite.AzFloat.Equiv.AtanWithPeriod

/-!
# Equivalence: `arccot (x) u / (2π)`

`Spec.acotWithPeriod a u = (Spec.acot a) u / (2π)` (`u/4` at `0`, `0` at `±∞`) and
`acotWithPeriodPrecRound_eq :
  acotWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.acotWithPeriod · u))`
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arccot (a) u / (2π)`: `u/4` at `0`, `0` at `±∞`. -/
noncomputable def acotWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  (acot a).map fun θ => ((θ.toReal * u / (2 * π) : ℝ) : EReal)

theorem acotWithPeriod_coe {r : ℝ} (hr : r ≠ 0) (u : ℕ) :
    acotWithPeriod (r : EReal) u = some ((arctan r⁻¹ * u / (2 * π) : ℝ) : EReal) := by
  unfold acotWithPeriod
  rw [acot_coe hr, Option.map_some, EReal.toReal_coe]

theorem acotWithPeriod_zero (u : ℕ) :
    acotWithPeriod ((0 : ℝ) : EReal) u = some (((u : ℝ) / 4 : ℝ) : EReal) := by
  unfold acotWithPeriod
  rw [acot_zero, Option.map_some, EReal.toReal_coe]
  congr 2
  have hpi := pi_ne_zero
  field_simp
  ring

theorem acotWithPeriod_top (u : ℕ) : acotWithPeriod ⊤ u = some ((0 : ℝ) : EReal) := by
  unfold acotWithPeriod
  rw [acot_top, Option.map_some, EReal.toReal_coe, zero_mul, zero_div]

theorem acotWithPeriod_bot (u : ℕ) : acotWithPeriod ⊥ u = some ((0 : ℝ) : EReal) := by
  unfold acotWithPeriod
  rw [acot_bot, Option.map_some, EReal.toReal_coe, zero_mul, zero_div]

end Spec

/-- The rounded quarter turn is the value at `0`. -/
theorem quarterTurn_round (u : UInt64) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    setPrecRound (turnFraction true u 2) p mode
      = roundVal p mode (Spec.acotWithPeriod ((0 : ℝ) : EReal) u.toNat) := by
  rw [setPrecRound_eq_roundVal (toVal_turnFraction true u 2), Spec.acotWithPeriod_zero]
  simp only [↓reduceIte, one_mul]
  norm_num

/-- **`arccot (x) u / (2π)` is correctly rounded.** -/
theorem acotWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    acotWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.acotWithPeriod a u.toNat) := by
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [acotWithPeriodPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.acotWithPeriod_top, Spec.acotWithPeriod_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [acotWithPeriodPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero]
    exact quarterTurn_round u p mode
  | finite s e q m hv =>
    simp only [acotWithPeriodPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    have hy : (if s then one else -one).toVal
        = some (((if s then 1 else -1 : ℝ) : ℝ) : EReal) := by
      cases s with
      | true => simpa using toVal_one'
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [toVal_neg, toVal_one', Option.map_some, EReal.coe_neg]
    rw [atan2WithPeriodPrecRound_eq, hy, habs]
    simp only [Option.bind_some]
    rw [Spec.atan2WithPeriod_of (Spec.atan2_coe_coe _ _), Spec.acotWithPeriod_coe hx0]
    have hpos : 0 < |xv| := abs_pos.mpr hx0
    have harg : Complex.arg ⟨|xv|, if s then 1 else -1⟩ = arctan xv⁻¹ := by
      have h := arg_of_re_pos (z := (⟨|xv|, if s then 1 else -1⟩ : ℂ)) hpos
      rw [h]
      congr 1
      cases s with
      | true =>
        have := hsgn.mp rfl
        simp only [↓reduceIte]
        rw [abs_of_pos this, one_div]
      | false =>
        have hlt : xv < 0 := by
          rcases lt_or_gt_of_ne hx0 with h | h
          · exact h
          · exact absurd (hsgn.mpr h) (by simp)
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [abs_of_neg hlt, neg_div_neg_eq, one_div]
    rw [harg]

end Azurite.AzFloat
