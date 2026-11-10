/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosWithPeriod
import Azurite.AzFloat.Equiv.Cos

/-!
# Equivalence: `cos (2π x / u)`

`Spec.cosWithPeriod : EReal → ℕ → Option EReal` (`NaN` for `u = 0` and at `±∞`) and
`cosWithPeriodPrecRound_eq :
  cosWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.cosWithPeriod · u))`
for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `cos (2π a / u)`: undefined for `u = 0` and at `±∞`. -/
noncomputable def cosWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  if u = 0 ∨ a = ⊤ ∨ a = ⊥ then none
  else some ((Real.cos (2 * Real.pi * a.toReal / u) : ℝ) : EReal)

theorem cosWithPeriod_coe (r : ℝ) {u : ℕ} (hu : u ≠ 0) :
    cosWithPeriod r u = some ((Real.cos (2 * Real.pi * r / u) : ℝ) : EReal) := by
  unfold cosWithPeriod
  rw [ite_eq_right (not_or.mpr ⟨hu, not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩⟩),
    EReal.toReal_coe]

@[simp] theorem cosWithPeriod_zero_period (a : EReal) : cosWithPeriod a 0 = none := by
  unfold cosWithPeriod
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cosWithPeriod_top (u : ℕ) : cosWithPeriod ⊤ u = none := by
  unfold cosWithPeriod
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

@[simp] theorem cosWithPeriod_bot (u : ℕ) : cosWithPeriod ⊥ u = none := by
  unfold cosWithPeriod
  rw [ite_eq_left (Or.inr (Or.inr rfl))]

end Spec

theorem toVal_one_half : (one <<< AzInt.ofInt (-1)).toVal = some ((1 / 2 : ℝ) : EReal) := by
  rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
  norm_num

theorem toVal_neg_one_half :
    (-(one <<< AzInt.ofInt (-1))).toVal = some ((-1 / 2 : ℝ) : EReal) := by
  rw [toVal_neg, toVal_one_half, Option.map_some, ← EReal.coe_neg]
  norm_num

/-- `|finiteVal s e m| = m 2^(e − size m)`. -/
theorem abs_finiteVal_eq (s : Bool) (e : AzInt) (m : AzNat) :
    |finiteVal s e m| = (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size) := by
  cases s <;>
    simp only [finiteVal, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, abs_neg] <;>
    exact abs_of_nonneg (by positivity)

/-- **`cos (2π x / u)` is correctly rounded.** -/
theorem cosWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cosWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.cosWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  unfold cosWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu]
    cases x <;> simp
  · rw [dite_eq_right hu]
    cases x with
    | nan => rfl
    | infinity s => cases s <;> simp
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.cosWithPeriod_coe _ hu, ite_eq_right hp, mul_zero, zero_div,
        Real.cos_zero, setPrecRound_eq_roundVal toVal_one']
    | finite s e q m hv =>
      simp only [toVal_finite, Option.bind_some, Spec.cosWithPeriod_coe _ hu]
      rw [dite_eq_right hp]
      have hU' : (0 : ℝ) < u.toNat := by exact_mod_cast Nat.pos_of_ne_zero hu
      split
      · next r hT =>
        obtain ⟨hs, he⟩ := cosTiny?_cond hT
        have htoInt : (e + AzInt.ofInt 3).toInt
            = if (e + AzInt.ofInt 3).sign then ((e + AzInt.ofInt 3).abs.toNat : ℤ)
              else -((e + AzInt.ofInt 3).abs.toNat : ℤ) := rfl
        rw [hs] at htoInt
        simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
        have he3 : (e + AzInt.ofInt 3).toInt = e.toInt + 3 := by
          rw [AzInt.toInt_add, AzInt.toInt_ofInt]
        have hx := (abs_finiteVal_bounds s e hv).2
        set xv := finiteVal s e m with hxv
        have hpi4 := Real.pi_le_four
        have hpi0 := Real.pi_pos
        have ht3 : (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt = 8 * (2 : ℝ) ^ e.toInt := by
          rw [he3, zpow_add₀ two_ne_zero]; norm_num; ring
        have hsmall : (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt ≤ 1 / 2 := by
          rw [htoInt, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
          calc (1 / 2 : ℝ) ^ (e + AzInt.ofInt 3).abs.toNat ≤ (1 / 2 : ℝ) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 2 := by norm_num
        have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast Nat.pos_of_ne_zero hu
        have hax := abs_nonneg xv
        have hdiv : |xv| / u.toNat ≤ |xv| := div_le_self hax hU1
        have habs : |2 * Real.pi * xv / u.toNat| = 2 * Real.pi * (|xv| / u.toNat) := by
          rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
            abs_of_pos hU', mul_div_assoc]
        have hbound : |2 * Real.pi * xv / u.toNat| < (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt := by
          rw [habs, ht3]
          nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        refine cosTiny?_eq hbound ?_ hT
        obtain ⟨rx, hrx⟩ := finiteVal_rat s e hv
        have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
        have hr : |xv| / u.toNat = ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
          push_cast; rw [← hrx]
        rw [← Real.cos_abs, habs, hr]
        apply irrational_cos_two_pi_mul_rat_of_small
        · have h1 : (0 : ℝ) < ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
            rw [← hr]; exact div_pos (abs_pos.mpr hx0) hU'
          exact_mod_cast h1
        · have h1 : ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) < ((1 / 6 : ℚ) : ℝ) := by
            rw [← hr]; push_cast; linarith
          exact_mod_cast h1
      set E := e - (AzNat.ofNat m.size).toAzInt with hEdef
      set r := periodFrac m E (AzNat.ofNat u.toNat) with hr
      have hE : E.toInt = e.toInt - m.size := by
        rw [hEdef, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat]
      have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
        rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
      obtain ⟨k, hk, hr0, hr1⟩ := periodFrac_spec m E hun
      rw [AzNat.toNat_ofNat, hE] at hk
      have hU : (0 : ℝ) < u.toNat := by exact_mod_cast Nat.pos_of_ne_zero hu
      have hcos : Real.cos (2 * Real.pi * finiteVal s e m / u.toNat)
          = Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) := by
        calc Real.cos (2 * Real.pi * finiteVal s e m / u.toNat)
            = Real.cos |2 * Real.pi * finiteVal s e m / u.toNat| := (Real.cos_abs _).symm
          _ = Real.cos (2 * Real.pi * (|finiteVal s e m| / u.toNat)) := by
              rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
                abs_of_pos hU, mul_div_assoc]
          _ = Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ) + k * (2 * Real.pi)) := by
              rw [abs_finiteVal_eq, hk]
              congr 1
              ring
          _ = Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) := Real.cos_add_nat_mul_two_pi _ k
      rw [hcos]
      split_ifs with h1 h2 h4 h3 h6
      · rw [cos_two_pi_mul_rat_of_den_eq_one (den_toRat_eq h1),
          setPrecRound_eq_roundVal toVal_one']
      · rw [cos_two_pi_mul_rat_of_den_eq_two (den_toRat_eq h2),
          setPrecRound_eq_roundVal toVal_neg_one]
      · rw [cos_two_pi_mul_rat_of_den_eq_four (den_toRat_eq h4), EReal.coe_zero, roundVal_zero]
      · rw [cos_two_pi_mul_rat_of_den_eq_three (den_toRat_eq h3),
          setPrecRound_eq_roundVal toVal_neg_one_half]
      · rw [cos_two_pi_mul_rat_of_den_eq_six (den_toRat_eq h6),
          setPrecRound_eq_roundVal toVal_one_half]
      · exact zivLoopCertified_eq_threshold' p mode _ _
          (not_mem_floatSet_of_irrational p (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6))
          _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              cosPeriodApprox_spec r hr0 hr1 (w := w) (by unfold zivGuardBits at hw; omega)
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
