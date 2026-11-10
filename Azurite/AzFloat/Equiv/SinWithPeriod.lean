/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.Equiv.CosWithPeriod
import Azurite.AzFloat.Equiv.Sin

/-!
# Equivalence: `sin (2π x / u)`

`Spec.sinWithPeriod : EReal → ℕ → Option EReal` (`NaN` for `u = 0` and at `±∞`) and
`sinWithPeriodPrecRound_eq :
  sinWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.sinWithPeriod · u))`
for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `sin (2π a / u)`: undefined for `u = 0` and at `±∞`. -/
noncomputable def sinWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  if u = 0 ∨ a = ⊤ ∨ a = ⊥ then none
  else some ((Real.sin (2 * Real.pi * a.toReal / u) : ℝ) : EReal)

theorem sinWithPeriod_coe (r : ℝ) {u : ℕ} (hu : u ≠ 0) :
    sinWithPeriod r u = some ((Real.sin (2 * Real.pi * r / u) : ℝ) : EReal) := by
  unfold sinWithPeriod
  rw [ite_eq_right (not_or.mpr ⟨hu, not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩⟩),
    EReal.toReal_coe]

@[simp] theorem sinWithPeriod_zero_period (a : EReal) : sinWithPeriod a 0 = none := by
  unfold sinWithPeriod
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem sinWithPeriod_top (u : ℕ) : sinWithPeriod ⊤ u = none := by
  unfold sinWithPeriod
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

@[simp] theorem sinWithPeriod_bot (u : ℕ) : sinWithPeriod ⊥ u = none := by
  unfold sinWithPeriod
  rw [ite_eq_left (Or.inr (Or.inr rfl))]

end Spec

theorem signedPow2_zero_val (s : Bool) (c : Prop) [Decidable c] :
    ((if (s == decide c) = true then (1 : ℝ) else -1) * (2 : ℝ) ^ (0 : ℤ))
      = (if (!s) = true then -1 else 1) * (if c then 1 else -1) := by
  cases s <;> by_cases hc : c <;> simp [hc]

theorem signedPow2_neg_one_val (s : Bool) (c : Prop) [Decidable c] :
    ((if (s == decide c) = true then (1 : ℝ) else -1) * (2 : ℝ) ^ (-1 : ℤ))
      = (if (!s) = true then -1 else 1) * (if c then 1 / 2 else -1 / 2) := by
  cases s <;> by_cases hc : c <;> simp [hc] <;> norm_num

/-- **`sin (2π x / u)` is correctly rounded.** -/
theorem sinWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    sinWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.sinWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  unfold sinWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu]
    cases x <;> simp
  · rw [dite_eq_right hu]
    cases x with
    | nan => rfl
    | infinity s => cases s <;> simp
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.sinWithPeriod_coe _ hu, mul_zero, zero_div, Real.sin_zero,
        EReal.coe_zero, roundVal_zero]
    | finite s e q m hv =>
      simp only [toVal_finite, Option.bind_some, Spec.sinWithPeriod_coe _ hu]
      rw [dite_eq_right hp]
      have hUn : 0 < u.toNat := Nat.pos_of_ne_zero hu
      have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
      have hpi0 := Real.pi_pos
      set xv := finiteVal s e m with hxv
      have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
      set E := e - (AzNat.ofNat m.size).toAzInt with hEdef
      have hE : E.toInt = e.toInt - m.size := by
        rw [hEdef, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat]
      have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
        rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
      have habs : |2 * Real.pi * xv / u.toNat| = 2 * Real.pi * (|xv| / u.toNat) := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
          abs_of_pos hU, mul_div_assoc]
      have habsx : |xv| / u.toNat = (m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat := by
        rw [hxv, abs_finiteVal_eq, hE]
      have hsin : Real.sin (2 * Real.pi * xv / u.toNat)
          = (if (!s) = true then -1 else 1) * Real.sin (2 * Real.pi * (|xv| / u.toNat)) := by
        have hneg : (!s) = true ↔ 2 * Real.pi * xv / u.toNat < 0 := by
          rw [finiteVal_neg_iff s e hv]
          constructor
          · intro h
            exact div_neg_of_neg_of_pos (by nlinarith) hU
          · intro h
            by_contra hx
            push Not at hx
            have : 0 ≤ 2 * Real.pi * xv / u.toNat := by positivity
            linarith
        rw [sin_eq_of_neg_iff hneg, habs]
      rw [hsin]
      split
      · next r hT =>
        obtain ⟨hs, he⟩ := sinPeriodTiny?_cond hT
        unfold zivGuardBits at he
        have htoInt : (e + AzInt.ofInt 3).toInt
            = if (e + AzInt.ofInt 3).sign then ((e + AzInt.ofInt 3).abs.toNat : ℤ)
              else -((e + AzInt.ofInt 3).abs.toNat : ℤ) := rfl
        rw [hs] at htoInt
        simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
        have he3 : (e + AzInt.ofInt 3).toInt = e.toInt + 3 := by
          rw [AzInt.toInt_add, AzInt.toInt_ofInt]
        have hx := (abs_finiteVal_bounds s e hv).2
        rw [← hxv] at hx
        have hpi4 := Real.pi_le_four
        have ht3 : (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt = 8 * (2 : ℝ) ^ e.toInt := by
          rw [he3, zpow_add₀ two_ne_zero]; norm_num; ring
        have hsmall : (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt ≤ 1 / 2 := by
          rw [htoInt, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
          calc (1 / 2 : ℝ) ^ (e + AzInt.ofInt 3).abs.toNat ≤ (1 / 2 : ℝ) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 2 := by norm_num
        have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast hUn
        have hax := abs_pos.mpr hx0
        have hdiv : |xv| / u.toNat ≤ |xv| := div_le_self hax.le hU1
        have hbound : 2 * Real.pi * (|xv| / u.toNat) < (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt := by
          rw [ht3]
          nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        have hirr : Irrational (Real.sin (2 * Real.pi * (|xv| / u.toNat))) := by
          obtain ⟨rx, hrx⟩ := finiteVal_rat s e hv
          have hr : |xv| / u.toNat = ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
            push_cast; rw [← hrx]
          rw [hr]
          apply irrational_sin_two_pi_mul_rat_of_small
          · have h1 : (0 : ℝ) < ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
              rw [← hr]; exact div_pos hax hU
            exact_mod_cast h1
          · have h1 : ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) < ((1 / 12 : ℚ) : ℝ) := by
              rw [← hr]; push_cast; linarith
            exact_mod_cast h1
        have hm : 0 < m.toNat := by
          rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
          · rw [hxv, abs_finiteVal_eq, h0] at hax
            simp at hax
          · exact h0
        rw [habsx] at hbound hirr ⊢
        have key := sinPeriodTiny?_eq (m := m) (u := AzNat.ofNat u.toNat) hm
          (by rw [AzNat.toNat_ofNat]; exact hUn) (by rw [AzNat.toNat_ofNat]; exact hbound)
          (by rw [AzNat.toNat_ofNat]; exact hirr) hT
        rw [AzNat.toNat_ofNat] at key
        exact key
      set r := periodFrac m E (AzNat.ofNat u.toNat) with hr
      obtain ⟨k, hk, hr0, hr1⟩ := periodFrac_spec m E hun
      rw [AzNat.toNat_ofNat] at hk
      have hval : Real.sin (2 * Real.pi * (|xv| / u.toNat))
          = Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) := by
        rw [habsx, hk, show 2 * Real.pi * ((k : ℝ) + ((AzRat.toRat r : ℚ) : ℝ))
          = 2 * Real.pi * (AzRat.toRat r : ℝ) + k * (2 * Real.pi) by ring,
          Real.sin_add_nat_mul_two_pi]
      rw [hval]
      generalize hσ : (if (!s) = true then (-1 : ℝ) else 1) = σ
      split_ifs with h1 h2 h4 h12 <;> subst hσ
      · rw [sin_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h1]; norm_num), mul_zero,
          EReal.coe_zero, roundVal_zero]
      · rw [sin_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h2]), mul_zero,
          EReal.coe_zero, roundVal_zero]
      · rw [sin_two_pi_mul_toRat_of_den_eq_four hr0 hr1 h4,
          setPrecRound_eq_roundVal (toVal_signedPow2 _ _), signedPow2_zero_val]
      · rw [sin_two_pi_mul_toRat_of_den_eq_twelve hr0 hr1 h12,
          setPrecRound_eq_roundVal (toVal_signedPow2 _ _), signedPow2_neg_one_val]
      · exact zivLoopCertified_eq_threshold' p mode _ _
          (not_mem_floatSet_of_irrational p
            (irrational_sign_mul (irrational_sin_two_pi_mul_toRat r h1 h2 h4 h12) (!s)))
          _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              sinPeriodApprox_spec (!s) r hr0 hr1 (w := w)
                (by unfold zivGuardBits at hw; omega)
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
