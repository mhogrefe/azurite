/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.Equiv.Acsc
import Azurite.AzFloat.Equiv.AsinWithPeriod

/-!
# Equivalence: `arccsc (x) u / (2π)`

`Spec.acscWithPeriod a u = (Spec.acsc a) · u / (2π)` (so `0` at `±∞`, undefined inside
`(−1, 1)`), `acscPeriod_one`, `acscPeriod_two` (the values at `±1`, `±2`) and
`acscWithPeriodPrecRound_eq :
  acscWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.acscWithPeriod · u))`
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arccsc (a) u / (2π)`: `0` at `±∞`, undefined inside `(−1, 1)`. -/
noncomputable def acscWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  (acsc a).map fun θ => ((θ.toReal * u / (2 * π) : ℝ) : EReal)

theorem acscWithPeriod_coe {r : ℝ} (hr : 1 ≤ |r|) (u : ℕ) :
    acscWithPeriod (r : EReal) u = some ((arcsin r⁻¹ * u / (2 * π) : ℝ) : EReal) := by
  unfold acscWithPeriod
  rw [acsc_coe hr, Option.map_some, EReal.toReal_coe]

theorem acscWithPeriod_coe_of_lt_one {r : ℝ} (hr : |r| < 1) (u : ℕ) :
    acscWithPeriod (r : EReal) u = none := by
  unfold acscWithPeriod
  rw [acsc_coe_of_lt_one hr, Option.map_none]

theorem acscWithPeriod_top (u : ℕ) : acscWithPeriod ⊤ u = some ((0 : ℝ) : EReal) := by
  unfold acscWithPeriod
  rw [acsc_top, Option.map_some, EReal.toReal_coe, zero_mul, zero_div]

theorem acscWithPeriod_bot (u : ℕ) : acscWithPeriod ⊥ u = some ((0 : ℝ) : EReal) := by
  unfold acscWithPeriod
  rw [acsc_bot, Option.map_some, EReal.toReal_coe, zero_mul, zero_div]

end Spec

/-- The value at `±1`: a quarter turn. -/
theorem acscPeriod_one (pos : Bool) (U : ℝ) :
    arcsin (if pos then 1 else -1)⁻¹ * U / (2 * π) = (if pos then 1 else -1) * (U / 2 ^ 2) := by
  have h : (if pos then (1 : ℝ) else -1)⁻¹ = if pos then 1 else -1 := by
    cases pos <;> norm_num
  rw [h]
  exact asinPeriod_one pos U

/-- The value at `±2`: a twelfth of a turn. -/
theorem acscPeriod_two (pos : Bool) (U : ℝ) :
    arcsin (if pos then 2 else -2)⁻¹ * U / (2 * π) = (if pos then 1 else -1) * (U / 12) := by
  have h : (if pos then (2 : ℝ) else -2)⁻¹ = if pos then 1 / 2 else -(1 / 2) := by
    cases pos <;> norm_num
  rw [h]
  exact asinPeriod_half pos U

/-- **`arccsc (x) u / (2π)` is correctly rounded.** -/
theorem acscWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    acscWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.acscWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [acscWithPeriodPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.acscWithPeriod_top, Spec.acscWithPeriod_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [acscWithPeriodPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.acscWithPeriod_coe_of_lt_one (by simp), roundVal_none]
  | finite s e q m hv =>
    simp only [acscWithPeriodPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [dite_eq_left h1, setPrecRound_eq_roundVal (toVal_turnFraction s u 2)]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.acscWithPeriod_coe habs1.ge, eq_signed_of_abs_eq hsgn hx0 habs1,
        acscPeriod_one]
    · rw [dite_eq_right h1]
      have hne1 : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he]
        have hgt : 1 < |xv| := one_lt_abs_of_exponent hb.1 he hne1
        have hen := two_pow_le_of_exponent hb.1 he
        rw [Spec.acscWithPeriod_coe hgt.le]
        by_cases hu : u.toNat = 0
        · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
            roundVal_zero]
        · rw [dite_eq_right hu]
          have htwo : (one <<< AzInt.ofInt 1).toVal = some ((2 : ℝ) : EReal) := by
            rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
            norm_num
          by_cases h2 : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt 1) = true
          · rw [dite_eq_left h2, turnTwelfth_eq]
            obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h2
            rw [habs] at hv1
            rw [htwo] at hv2
            have habs2 : |xv| = 2 := by
              have := hv1.trans hv2.symm
              exact_mod_cast Option.some.inj this
            rw [eq_signed_of_abs_eq hsgn hx0 habs2, acscPeriod_two]
          · rw [dite_eq_right h2, dite_eq_right hp]
            have hne2 : |xv| ≠ 2 := fun h =>
              h2 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact htwo⟩)
            have hval := acscPeriod_eq_of_neg_iff hneg (u.toNat : ℝ)
            exact zivLoopCertified_eq_threshold' p mode _ (arcsin xv⁻¹ * u.toNat / (2 * π))
              (not_mem_floatSet_of_irrational p
                (irrational_acscPeriod_of_toVal (toVal_finite s e q m hv) hgt hne2 hu))
              _ (by unfold zivGuardBits; omega)
              (fun w _ => by
                obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := acscPeriodApprox_spec (!s)
                  (toVal_finite s e q m hv) hgt hen (AzNat.ofNat u.toNat) w
                rw [AzNat.toNat_ofNat, ← hval] at hlo hhi
                exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
      · rw [dite_eq_right he]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.acscWithPeriod_coe_of_lt_one hlt1, roundVal_none]

end Azurite.AzFloat
