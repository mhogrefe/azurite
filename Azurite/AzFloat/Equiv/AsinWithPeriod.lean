/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinWithPeriod
import Azurite.AzFloat.Equiv.Asin
import Azurite.AzFloat.Equiv.AtanWithPeriod
import Azurite.AzRat.Equiv.Construct

/-!
# Equivalence: `arcsin (x) u / (2π)`

`Spec.asinWithPeriod a u = (Spec.asin a) · u / (2π)` (undefined outside `[−1, 1]`),
`turnTwelfth_eq`, and
`asinWithPeriodPrecRound_eq :
  asinWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.asinWithPeriod · u))`
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arcsin (a) u / (2π)`: undefined outside `[−1, 1]`. -/
noncomputable def asinWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  (asin a).map fun θ => ((θ.toReal * u / (2 * π) : ℝ) : EReal)

theorem asinWithPeriod_coe {r : ℝ} (hr : |r| ≤ 1) (u : ℕ) :
    asinWithPeriod (r : EReal) u = some ((arcsin r * u / (2 * π) : ℝ) : EReal) := by
  unfold asinWithPeriod
  rw [asin_coe hr, Option.map_some, EReal.toReal_coe]

theorem asinWithPeriod_coe_of_one_lt {r : ℝ} (hr : 1 < |r|) (u : ℕ) :
    asinWithPeriod (r : EReal) u = none := by
  unfold asinWithPeriod
  rw [asin_coe_of_one_lt hr, Option.map_none]

@[simp] theorem asinWithPeriod_top (u : ℕ) : asinWithPeriod ⊤ u = none := by
  unfold asinWithPeriod
  rw [asin_top, Option.map_none]

@[simp] theorem asinWithPeriod_bot (u : ℕ) : asinWithPeriod ⊥ u = none := by
  unfold asinWithPeriod
  rw [asin_bot, Option.map_none]

end Spec

/-- A twelfth of a turn is returned correctly rounded. -/
theorem turnTwelfth_eq (pos : Bool) (u : UInt64) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    turnTwelfth pos u p mode
      = roundVal p mode
        (some (((if pos then 1 else -1) * ((u.toNat : ℝ) / 12) : ℝ) : EReal)) := by
  unfold turnTwelfth
  dsimp only
  rw [ofAzRatRound_eq_roundVal]
  congr 3
  cases pos with
  | true =>
    simp only [↓reduceIte, one_mul]
    rw [AzRat.toRat_ofAzNats, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
    push_cast
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [AzRat.toRat_neg, AzRat.toRat_ofAzNats, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
    push_cast
    rfl

/-- The value at `±1`: a quarter turn. -/
theorem asinPeriod_one (pos : Bool) (U : ℝ) :
    arcsin (if pos then 1 else -1) * U / (2 * π) = (if pos then 1 else -1) * (U / 2 ^ 2) := by
  have hpi := pi_ne_zero
  cases pos with
  | true =>
    simp only [↓reduceIte]
    rw [arcsin_one]
    field_simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [arcsin_neg_one]
    field_simp

/-- The value at `±1/2`: a twelfth of a turn. -/
theorem asinPeriod_half (pos : Bool) (U : ℝ) :
    arcsin (if pos then 1 / 2 else -(1 / 2)) * U / (2 * π)
      = (if pos then 1 else -1) * (U / 12) := by
  have hpi := pi_ne_zero
  cases pos with
  | true =>
    simp only [↓reduceIte]
    rw [arcsin_one_half]
    field_simp
    ring
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [arcsin_neg, arcsin_one_half]
    field_simp
    ring

/-- A float of sign bit `s` with `|x| = c > 0` is `± c`. -/
theorem eq_signed_of_abs_eq {s : Bool} {xv c : ℝ} (hsgn : s = true ↔ 0 < xv) (hx0 : xv ≠ 0)
    (habs : |xv| = c) : xv = if s then c else -c := by
  cases s with
  | true =>
    simp only [↓reduceIte]
    rw [← habs, abs_of_pos (hsgn.mp rfl)]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hlt : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact h
      · exact absurd (hsgn.mpr h) (by simp)
    rw [← habs, abs_of_neg hlt, neg_neg]

/-- **`arcsin (x) u / (2π)` is correctly rounded.** -/
theorem asinWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    asinWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.asinWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [asinWithPeriodPrecRound]
  | zero =>
    simp only [asinWithPeriodPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.asinWithPeriod_coe (by simp), arcsin_zero, zero_mul, zero_div,
      EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [asinWithPeriodPrecRound, toVal_finite, Option.bind_some]
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
    · rw [ite_eq_left h1, setPrecRound_eq_roundVal (toVal_turnFraction s u 2)]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.asinWithPeriod_coe habs1.le, eq_signed_of_abs_eq hsgn hx0 habs1,
        asinPeriod_one]
    · rw [ite_eq_right h1]
      have hne1 : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he]
        have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
        have h1e : 1 ≤ e.toInt := by
          rw [htoInt, he.1]
          simp only [↓reduceIte]
          have := he.2
          omega
        have hge : 1 ≤ |xv| := le_trans (one_le_zpow₀ (by norm_num) (by omega)) hb.1
        rw [Spec.asinWithPeriod_coe_of_one_lt (lt_of_le_of_ne hge (Ne.symm hne1)),
          roundVal_none]
      · rw [dite_eq_right he]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.asinWithPeriod_coe hlt1.le]
        by_cases hu : u.toNat = 0
        · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
            roundVal_zero]
        · rw [dite_eq_right hu]
          have hhalfv : (one <<< AzInt.ofInt (-1)).toVal = some ((1 / 2 : ℝ) : EReal) := by
            rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
            norm_num
          by_cases hh : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt (-1)) = true
          · rw [dite_eq_left hh, turnTwelfth_eq]
            obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp hh
            rw [habs] at hv1
            rw [hhalfv] at hv2
            have habsh : |xv| = 1 / 2 := by
              have := hv1.trans hv2.symm
              exact_mod_cast Option.some.inj this
            rw [eq_signed_of_abs_eq hsgn hx0 habsh, asinPeriod_half]
          · rw [dite_eq_right hh, dite_eq_right hp]
            have hneh : |xv| ≠ 1 / 2 := fun h =>
              hh ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact hhalfv⟩)
            have hval := asinPeriod_eq_of_neg_iff hneg (u.toNat : ℝ)
            exact zivLoopCertified_eq_threshold' p mode _ (arcsin xv * u.toNat / (2 * π))
              (not_mem_floatSet_of_irrational p
                (irrational_asinPeriod_of_toVal (toVal_finite s e q m hv) hx0 hlt1 hneh hu))
              _ (by unfold zivGuardBits; omega)
              (fun w _ => by
                obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := asinPeriodApprox_spec (!s)
                  (toVal_finite s e q m hv) hx0 hlt1 hb.2 (AzNat.ofNat u.toNat) w
                rw [AzNat.toNat_ofNat, ← hval] at hlo hhi
                exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _

end Azurite.AzFloat
