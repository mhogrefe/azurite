/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosWithPeriod
import Azurite.AzFloat.Equiv.Acos
import Azurite.AzRat.Equiv.Construct

/-!
# Equivalence: `arccos (x) u / (2π)`

`Spec.acosWithPeriod a u = (Spec.acos a) · u / (2π)` (undefined outside `[−1, 1]`),
`turnRatio_eq`, `acosPeriod_values` (the rational values), `orient_roundVal` (undoing the
orientation of the Ziv loop), and
`acosWithPeriodPrecRound_eq :
  acosWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.acosWithPeriod · u))`
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arccos (a) u / (2π)`: undefined outside `[−1, 1]`. -/
noncomputable def acosWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  (acos a).map fun θ => ((θ.toReal * u / (2 * π) : ℝ) : EReal)

theorem acosWithPeriod_coe {r : ℝ} (hr : |r| ≤ 1) (u : ℕ) :
    acosWithPeriod (r : EReal) u = some ((arccos r * u / (2 * π) : ℝ) : EReal) := by
  unfold acosWithPeriod
  rw [acos_coe hr, Option.map_some, EReal.toReal_coe]

theorem acosWithPeriod_coe_of_one_lt {r : ℝ} (hr : 1 < |r|) (u : ℕ) :
    acosWithPeriod (r : EReal) u = none := by
  unfold acosWithPeriod
  rw [acos_coe_of_one_lt hr, Option.map_none]

@[simp] theorem acosWithPeriod_top (u : ℕ) : acosWithPeriod ⊤ u = none := by
  unfold acosWithPeriod
  rw [acos_top, Option.map_none]

@[simp] theorem acosWithPeriod_bot (u : ℕ) : acosWithPeriod ⊥ u = none := by
  unfold acosWithPeriod
  rw [acos_bot, Option.map_none]

end Spec

/-- A rational fraction of a turn is returned correctly rounded. -/
theorem turnRatio_eq (u : UInt64) (n d : ℕ) (p : ℕ) [NeZero p] (mode : RoundingMode) {v : ℝ}
    (hv : v = (n : ℝ) * u.toNat / d) :
    turnRatio u n d p mode = roundVal p mode (some ((v : ℝ) : EReal)) := by
  unfold turnRatio
  rw [ofAzRatRound_eq_roundVal, hv, AzRat.toRat_ofAzNats, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  push_cast
  rfl

/-- `arccos (1/2) = π/3`. -/
theorem arccos_one_half : arccos (1 / 2) = π / 3 := by
  rw [arccos, arcsin_one_half]
  ring

/-- The rational values of `arccos (x) U / (2π)`: at `0`, `−1`, `1/2`, `−1/2`. -/
theorem acosPeriod_values (U : ℝ) :
    arccos 0 * U / (2 * π) = (1 : ℕ) * U / (4 : ℕ) ∧
      arccos (-1) * U / (2 * π) = (1 : ℕ) * U / (2 : ℕ) ∧
      arccos (1 / 2) * U / (2 * π) = (1 : ℕ) * U / (6 : ℕ) ∧
      arccos (-(1 / 2)) * U / (2 * π) = (1 : ℕ) * U / (3 : ℕ) := by
  have hpi := pi_ne_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [arccos_zero]
    push_cast
    field_simp
    ring
  · rw [arccos_neg_one]
    push_cast
    field_simp
  · rw [arccos_one_half]
    push_cast
    field_simp
    ring
  · rw [arccos_neg, arccos_one_half]
    push_cast
    field_simp
    ring

/-- Undoing the orientation: the rounding of `v` from the rounding of `± v` in the mode
`± mode`. -/
theorem orient_roundVal (o : Bool) (p : ℕ) [NeZero p] (mode : RoundingMode) (v : ℝ) :
    (if o then
        (-(roundVal p (if o then -mode else mode)
            (some (((if o then -1 else 1) * v : ℝ) : EReal))).1,
          (roundVal p (if o then -mode else mode)
            (some (((if o then -1 else 1) * v : ℝ) : EReal))).2.swap)
      else roundVal p (if o then -mode else mode)
        (some (((if o then -1 else 1) * v : ℝ) : EReal)))
      = roundVal p mode (some ((v : ℝ) : EReal)) := by
  cases o with
  | false => simp
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have h := roundVal_neg p mode (-v)
    rw [neg_neg] at h
    exact h.symm

/-- **`arccos (x) u / (2π)` is correctly rounded.** -/
theorem acosWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    acosWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.acosWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  obtain ⟨hv0, hvm1, hvh, hvmh⟩ := acosPeriod_values (u.toNat : ℝ)
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [acosWithPeriodPrecRound]
  | zero =>
    simp only [acosWithPeriodPrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right hp, ← EReal.coe_zero, Spec.acosWithPeriod_coe (by simp)]
    exact turnRatio_eq u 1 4 p mode hv0
  | finite s e q m hv =>
    simp only [acosWithPeriodPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [ite_eq_left h1]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.acosWithPeriod_coe habs1.le, eq_signed_of_abs_eq hsgn hx0 habs1]
      cases s with
      | true =>
        simp only [↓reduceIte]
        rw [arccos_one, zero_mul, zero_div, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right hp]
        exact turnRatio_eq u 1 2 p mode hvm1
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
        rw [Spec.acosWithPeriod_coe_of_one_lt (lt_of_le_of_ne hge (Ne.symm hne1)),
          roundVal_none]
      · rw [dite_eq_right he]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.acosWithPeriod_coe hlt1.le]
        by_cases hu : u.toNat = 0
        · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
            roundVal_zero]
        · rw [dite_eq_right hu, dite_eq_right hp]
          have hhalfv : (one <<< AzInt.ofInt (-1)).toVal = some ((1 / 2 : ℝ) : EReal) := by
            rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
            norm_num
          by_cases hh : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt (-1)) = true
          · rw [dite_eq_left hh]
            obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp hh
            rw [habs] at hv1
            rw [hhalfv] at hv2
            have habsh : |xv| = 1 / 2 := by
              have := hv1.trans hv2.symm
              exact_mod_cast Option.some.inj this
            rw [eq_signed_of_abs_eq hsgn hx0 habsh]
            cases s with
            | true =>
              simp only [↓reduceIte]
              exact turnRatio_eq u 1 6 p mode hvh
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact turnRatio_eq u 1 3 p mode hvmh
          · rw [dite_eq_right hh]
            have hneh : |xv| ≠ 1 / 2 := fun h =>
              hh ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact hhalfv⟩)
            have hirr := irrational_acosPeriod_of_toVal (toVal_finite s e q m hv) hx0 hlt1
              hneh hu
            set ψ := arccos xv * u.toNat / (2 * π) with hψ
            have key : ∀ (o : Bool) (m' : RoundingMode),
                zivLoopCertified
                  (acosPeriodApprox o s (finite s e q m hv) e (AzNat.ofNat u.toNat)) p m'
                  (p + zivGuardBits)
                  (acosPeriodApprox_isSome_exists p m' o (toVal_finite s e q m hv) hx0 hlt1
                    hneh hb.2 hsgn (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
                    (by unfold zivGuardBits; omega))
                = roundVal p m' (some (((if o then -1 else 1) * ψ : ℝ) : EReal)) :=
              fun o m' =>
              zivLoopCertified_eq_threshold' p m' _ _
                (not_mem_floatSet_of_irrational p (by
                  cases o with
                  | false => simpa using hirr
                  | true => simpa using hirr.neg)) _ (by unfold zivGuardBits; omega)
                (fun w _ => by
                  obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := acosPeriodApprox_spec o
                    (toVal_finite s e q m hv) hx0 hlt1 hb.2 hsgn (AzNat.ofNat u.toNat) w
                  rw [AzNat.toNat_ofNat] at hlo hhi
                  exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
            set o := acosPeriodOrientOf
              (le (finite s e q m hv).abs (one <<< AzInt.ofInt (-1))) s with hodef
            rw [key o (if o then -mode else mode)]
            exact orient_roundVal o p mode ψ

end Azurite.AzFloat
