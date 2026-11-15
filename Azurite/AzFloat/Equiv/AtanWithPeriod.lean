/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.Equiv.Atan
import Azurite.AzFloat.Equiv.Atan2WithPeriod

/-!
# Equivalence: `arctan (x) u / (2π)`

`Spec.atanWithPeriod : EReal → ℕ → Option EReal` (`±u/4` at `±∞`), `toVal_turnFraction`, and
`atanWithPeriodPrecRound_eq :
  atanWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.atanWithPeriod · u))`
for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `arctan (a) u / (2π)`: a quarter turn `±u/4` at `±∞`. -/
noncomputable def atanWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  some (if a = ⊤ then (((u : ℝ) / 4 : ℝ) : EReal)
    else if a = ⊥ then ((-((u : ℝ) / 4) : ℝ) : EReal)
    else ((Real.arctan a.toReal * u / (2 * Real.pi) : ℝ) : EReal))

theorem atanWithPeriod_coe (r : ℝ) (u : ℕ) :
    atanWithPeriod (r : EReal) u = some ((Real.arctan r * u / (2 * Real.pi) : ℝ) : EReal) := by
  unfold atanWithPeriod
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem atanWithPeriod_top (u : ℕ) :
    atanWithPeriod ⊤ u = some (((u : ℝ) / 4 : ℝ) : EReal) := by
  unfold atanWithPeriod
  rw [ite_eq_left rfl]

@[simp] theorem atanWithPeriod_bot (u : ℕ) :
    atanWithPeriod ⊥ u = some ((-((u : ℝ) / 4) : ℝ) : EReal) := by
  unfold atanWithPeriod
  rw [ite_eq_right (by simp), ite_eq_left rfl]

end Spec

/-- The value of `turnFraction`: `± u / 2^k`. -/
theorem toVal_turnFraction (pos : Bool) (u : UInt64) (k : ℕ) :
    (turnFraction pos u k).toVal
      = some (((if pos then 1 else -1) * ((u.toNat : ℝ) / 2 ^ k) : ℝ) : EReal) := by
  have h : (ofAzNat (AzNat.ofNat u.toNat) <<< AzInt.ofInt (-(k : Int))).toVal
      = some (((u.toNat : ℝ) / 2 ^ k : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat (AzNat.ofNat u.toNat))
      (AzInt.ofInt (-(k : Int)))
    rw [h, AzNat.toNat_ofNat, AzInt.toInt_ofInt, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  unfold turnFraction
  cases pos with
  | true => simp only [↓reduceIte, one_mul]; exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [toVal_neg, h, Option.map_some, EReal.coe_neg]

/-- **`arctan (x) u / (2π)` is correctly rounded.** -/
theorem atanWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    atanWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.atanWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  have hpi := Real.pi_pos
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [atanWithPeriodPrecRound, toVal_infinity, Option.bind_some]
    rw [setPrecRound_eq_roundVal (toVal_turnFraction s u 2)]
    cases s with
    | true =>
      simp only [↓reduceIte, Spec.atanWithPeriod_top, one_mul]
      norm_num
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Spec.atanWithPeriod_bot, neg_one_mul]
      norm_num
  | zero =>
    simp only [atanWithPeriodPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.atanWithPeriod_coe, Real.arctan_zero, zero_mul, zero_div,
      EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [atanWithPeriodPrecRound, toVal_finite, Option.bind_some,
      Spec.atanWithPeriod_coe]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases hu : u.toNat = 0
    · rw [ite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero, roundVal_zero]
    · rw [ite_eq_right hu]
      by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
      · rw [ite_eq_left h1, setPrecRound_eq_roundVal (toVal_turnFraction s u 3)]
        obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
        rw [habs] at hv1
        rw [toVal_one'] at hv2
        have habs1 : |xv| = 1 := by
          have := hv1.trans hv2.symm
          exact_mod_cast Option.some.inj this
        congr 3
        cases s with
        | true =>
          have hpos : 0 < xv := by
            rcases lt_or_gt_of_ne hx0 with h | h
            · exact absurd (hneg.mpr h) (by simp)
            · exact h
          rw [abs_of_pos hpos] at habs1
          simp only [↓reduceIte, one_mul]
          rw [habs1, Real.arctan_one]
          field_simp
          norm_num
        | false =>
          have hlt : xv < 0 := hneg.mp rfl
          rw [abs_of_neg hlt] at habs1
          have hx1 : xv = -1 := by linarith
          simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
          rw [hx1, Real.arctan_neg, Real.arctan_one]
          field_simp
          norm_num
      · rw [ite_eq_right h1, atan2WithPeriodPrecRound_eq]
        simp only [toVal_finite, toVal_one', Option.bind_some]
        rw [Spec.atan2WithPeriod_of (Spec.atan2_coe_coe _ _)]
        have harg : Complex.arg ⟨1, xv⟩ = Real.arctan xv := by
          have h := arg_of_re_pos (z := (⟨1, xv⟩ : ℂ)) (by norm_num)
          simpa using h
        rw [harg]

end Azurite.AzFloat
