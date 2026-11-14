/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanWithPeriod
import Azurite.AzFloat.Equiv.SinWithPeriod
import Azurite.AzFloat.Equiv.Tan

/-!
# Equivalence: `tan (2π x / u)`

`Spec.tanWithPeriod : EReal → ℕ → Option EReal` (`NaN` for `u = 0` and at `±∞`; the IEEE 754
poles of `Spec.tanPole`), `tanPeriodCore_eq`, `tanPole_two_pi_div_bool`, `tanPole_of_small`, and
`tanWithPeriodPrecRound_eq :
  tanWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.tanWithPeriod · u))`
for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `tan (2π a / u)` with the IEEE 754 poles: undefined for `u = 0` and at
`±∞`. -/
noncomputable def tanWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  if u = 0 ∨ a = ⊤ ∨ a = ⊥ then none else some (tanPole (2 * Real.pi * a.toReal / u))

theorem tanWithPeriod_coe (r : ℝ) {u : ℕ} (hu : u ≠ 0) :
    tanWithPeriod r u = some (tanPole (2 * Real.pi * r / u)) := by
  unfold tanWithPeriod
  rw [ite_eq_right (not_or.mpr ⟨hu, not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩⟩),
    EReal.toReal_coe]

@[simp] theorem tanWithPeriod_zero_period (a : EReal) : tanWithPeriod a 0 = none := by
  unfold tanWithPeriod
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem tanWithPeriod_top (u : ℕ) : tanWithPeriod ⊤ u = none := by
  unfold tanWithPeriod
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

@[simp] theorem tanWithPeriod_bot (u : ℕ) : tanWithPeriod ⊥ u = none := by
  unfold tanWithPeriod
  rw [ite_eq_left (Or.inr (Or.inr rfl))]

/-- The reduction to the fractional part with the sign as a Boolean. -/
theorem tanPole_two_pi_div_bool {xv U ρ : ℝ} {neg : Bool} (hneg : neg = true ↔ xv < 0) {k : ℕ}
    (hk : |xv| / U = k + ρ) :
    tanPole (2 * Real.pi * xv / U)
      = if neg = true then -tanPole (2 * Real.pi * ρ) else tanPole (2 * Real.pi * ρ) := by
  rw [tanPole_two_pi_div hk]
  by_cases hx : xv < 0
  · rw [ite_eq_left hx, ite_eq_left (hneg.mpr hx)]
  · rw [ite_eq_right hx, ite_eq_right fun h => hx (hneg.mp h)]

/-- For a small argument the value is the plain tangent, with the sign taken out. -/
theorem tanPole_of_small {xv U : ℝ} {neg : Bool} (hneg : neg = true ↔ xv < 0) (hU : 0 < U)
    (hb : 2 * Real.pi * (|xv| / U) < 1) :
    tanPole (2 * Real.pi * xv / U)
      = (((if neg then -1 else 1) * Real.tan (2 * Real.pi * (|xv| / U)) : ℝ) : EReal) := by
  have hy0 : 0 ≤ 2 * Real.pi * (|xv| / U) := by positivity
  have hpi := Real.pi_gt_three
  have hc : Real.cos (2 * Real.pi * (|xv| / U)) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  rw [tanPole_two_pi_div_bool hneg (k := 0) (ρ := |xv| / U) (by simp),
    tanPole_of_cos_ne_zero hc]
  cases neg <;> simp

end Spec

theorem negIf_top_bot (neg : Bool) (P : Prop) [Decidable P] :
    (if neg = true then -(if P then (⊤ : EReal) else ⊥) else (if P then (⊤ : EReal) else ⊥))
      = if (neg != decide P) = true then ⊤ else ⊥ := by
  cases neg <;> by_cases hP : P <;> simp [hP]

theorem signedPow2_zero_val_bne (neg : Bool) (P : Prop) [Decidable P] :
    ((if (neg != decide P) = true then (1 : ℝ) else -1) * (2 : ℝ) ^ (0 : ℤ))
      = (if neg = true then -1 else 1) * (if P then 1 else -1) := by
  cases neg <;> by_cases hP : P <;> simp [hP]

/-- **The case distinction after the reduction** computes the rounding of `± tanPole (2πr)`. -/
theorem tanPeriodCore_eq (neg : Bool) (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    tanPeriodCore neg r hr p mode
      = roundVal p mode (some (if neg = true
          then -Spec.tanPole (2 * Real.pi * (AzRat.toRat r : ℝ))
          else Spec.tanPole (2 * Real.pi * (AzRat.toRat r : ℝ)))) := by
  obtain ⟨hr0, hr1⟩ := hr
  have hne : ∀ {a b : ℕ}, a ≠ b → r.den = AzNat.ofNat a → r.den ≠ AzNat.ofNat b :=
    fun {a b} hab ha hb => hab (by
      have := congrArg AzNat.toNat (ha.symm.trans hb)
      rwa [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this)
  unfold tanPeriodCore
  by_cases h1 : r.den = AzNat.ofNat 1
  · rw [dite_eq_left h1]
    have hc := cos_two_pi_mul_toRat_ne_zero r (hne (by norm_num) h1)
    rw [Spec.tanPole_of_cos_ne_zero hc,
      tan_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h1]; norm_num)]
    cases neg <;> simp
  rw [dite_eq_right h1]
  by_cases h2 : r.den = AzNat.ofNat 2
  · rw [dite_eq_left h2]
    have hc := cos_two_pi_mul_toRat_ne_zero r (hne (by norm_num) h2)
    rw [Spec.tanPole_of_cos_ne_zero hc,
      tan_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h2])]
    cases neg <;> simp
  rw [dite_eq_right h2]
  by_cases h4 : r.den = AzNat.ofNat 4
  · rw [dite_eq_left h4, tanPole_two_pi_mul_toRat_of_den_eq_four hr0 hr1 h4, negIf_top_bot,
      roundVal_inf]
  rw [dite_eq_right h4]
  have hc := cos_two_pi_mul_toRat_ne_zero r h4
  rw [Spec.tanPole_of_cos_ne_zero hc]
  have hgoal : (if neg = true then -((Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ)) : ℝ) : EReal)
      else ((Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ)) : ℝ) : EReal))
      = (((if neg then -1 else 1) * Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ)) : ℝ)
        : EReal) := by
    cases neg <;> simp
  rw [hgoal]
  by_cases h8 : r.den = AzNat.ofNat 8
  · rw [dite_eq_left h8, tan_two_pi_mul_toRat_of_den_eq_eight hr0 hr1 h8,
      setPrecRound_eq_roundVal (toVal_signedPow2 _ _), signedPow2_zero_val_bne]
  rw [dite_eq_right h8]
  exact zivLoopCertified_eq_or_none p mode _ _
    (not_mem_floatSet_of_irrational p
      (irrational_sign_mul (irrational_tan_two_pi_mul_toRat r h1 h2 h4 h8) neg))
    _ (by unfold zivGuardBits; omega)
    (fun w hw => tanPeriodApprox_valid_or_none neg r hr0 hr1
      (by unfold zivGuardBits at hw; omega) p mode) _

/-- **`tan (2π x / u)` is correctly rounded**, with the IEEE 754 poles. -/
theorem tanWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    tanWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.tanWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  unfold tanWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu]
    cases x <;> simp
  · rw [dite_eq_right hu]
    cases x with
    | nan => rfl
    | infinity s => cases s <;> simp
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.tanWithPeriod_coe _ hu, mul_zero, zero_div,
        Spec.tanPole_of_cos_ne_zero (by rw [Real.cos_zero]; norm_num), Real.tan_zero,
        EReal.coe_zero, roundVal_zero]
    | finite s e q m hv =>
      simp only [toVal_finite, Option.bind_some, Spec.tanWithPeriod_coe _ hu]
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
      have habsx : |xv| / u.toNat = (m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat := by
        rw [hxv, abs_finiteVal_eq, hE]
      have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
      split
      · next r hT =>
        obtain ⟨hs, he⟩ := tanPeriodTiny?_cond hT
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
        have hirr : Irrational (Real.tan (2 * Real.pi * (|xv| / u.toNat))) := by
          obtain ⟨rx, hrx⟩ := finiteVal_rat s e hv
          have hr : |xv| / u.toNat = ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
            push_cast; rw [← hrx]
          rw [hr]
          apply irrational_tan_two_pi_mul_rat_of_small
          · have h1 : (0 : ℝ) < ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
              rw [← hr]; exact div_pos hax hU
            exact_mod_cast h1
          · have h1 : ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) < ((1 / 8 : ℚ) : ℝ) := by
              rw [← hr]; push_cast; linarith
            exact_mod_cast h1
        have hm : 0 < m.toNat := by
          rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
          · rw [hxv, abs_finiteVal_eq, h0] at hax
            simp at hax
          · exact h0
        rw [Spec.tanPole_of_small hneg hU (by linarith)]
        rw [habsx] at hbound hirr ⊢
        have key := tanPeriodTiny?_eq (m := m) (u := AzNat.ofNat u.toNat) hm
          (by rw [AzNat.toNat_ofNat]; exact hUn) (by rw [AzNat.toNat_ofNat]; exact hbound)
          (by rw [AzNat.toNat_ofNat]; exact hirr) hT
        rw [AzNat.toNat_ofNat] at key
        exact key
      obtain ⟨k, hk, hr0, hr1⟩ := periodFrac_spec m E hun
      rw [AzNat.toNat_ofNat, ← habsx] at hk
      rw [tanPeriodCore_eq, Spec.tanPole_two_pi_div_bool hneg hk]

end Azurite.AzFloat
