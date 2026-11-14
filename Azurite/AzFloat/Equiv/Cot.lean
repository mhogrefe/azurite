/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cot
import Azurite.AzFloat.Equiv.Csc
import Azurite.AzFloat.Equiv.TanWithPeriod

/-!
# Equivalence: the cotangent

`Spec.cot`, `Spec.cotWithPeriod`, `Spec.cotPi` (the poles of `Spec.cotSigned`: the infinity with
the sign of the argument times the sign of the cosine, `+∞` at `0`), `cotPeriodCore_eq`, and for
`p ≠ 0`:

* `cotPrecRound_eq_liftVal`, `cotRatPrecRound_eq`;
* `cotWithPeriodPrecRound_eq`, `cotRatWithPeriodPrecRound_eq`;
* `cotPiPrecRound_eq_liftVal`, `cotPiRatPrecRound_eq`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real cotangent: `cos a / sin a`, `+∞` at `0`; undefined (`NaN`) at `±∞`. -/
noncomputable def cot (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some (cotSigned a.toReal a.toReal)

theorem cot_coe (r : ℝ) : cot (r : EReal) = some (cotSigned r r) := by
  unfold cot
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem cot_top : cot ⊤ = none := by
  unfold cot
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cot_bot : cot ⊥ = none := by
  unfold cot
  rw [ite_eq_left (Or.inr rfl)]

open Classical in
/-- Extended-real `cot (2π a / u)` with the signed infinities of `cotSigned` at the poles:
undefined for `u = 0` and at `±∞`. -/
noncomputable def cotWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  if u = 0 ∨ a = ⊤ ∨ a = ⊥ then none
  else some (cotSigned a.toReal (2 * Real.pi * a.toReal / u))

theorem cotWithPeriod_coe (r : ℝ) {u : ℕ} (hu : u ≠ 0) :
    cotWithPeriod r u = some (cotSigned r (2 * Real.pi * r / u)) := by
  unfold cotWithPeriod
  rw [ite_eq_right (not_or.mpr ⟨hu, not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩⟩),
    EReal.toReal_coe]

@[simp] theorem cotWithPeriod_zero_period (a : EReal) : cotWithPeriod a 0 = none := by
  unfold cotWithPeriod
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cotWithPeriod_top (u : ℕ) : cotWithPeriod ⊤ u = none := by
  unfold cotWithPeriod
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

@[simp] theorem cotWithPeriod_bot (u : ℕ) : cotWithPeriod ⊥ u = none := by
  unfold cotWithPeriod
  rw [ite_eq_left (Or.inr (Or.inr rfl))]

open Classical in
/-- Extended-real `cot (π a)` with the signed infinities of `cotSigned` at the integers:
undefined (`NaN`) at `±∞`. -/
noncomputable def cotPi (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some (cotSigned a.toReal (Real.pi * a.toReal))

theorem cotPi_coe (r : ℝ) : cotPi (r : EReal) = some (cotSigned r (Real.pi * r)) := by
  unfold cotPi
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem cotPi_top : cotPi ⊤ = none := by
  unfold cotPi
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cotPi_bot : cotPi ⊥ = none := by
  unfold cotPi
  rw [ite_eq_left (Or.inr rfl)]

/-- `cot (π a)` is the period-`2` case of `cotWithPeriod`. -/
theorem cotWithPeriod_two (a : EReal) : cotWithPeriod a 2 = cotPi a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [cotWithPeriod_coe r (by norm_num), cotPi_coe]
    congr 2
    push_cast
    ring

/-- At a pole with a positive cosine the argument `0` gives `+∞`. -/
theorem cotSigned_zero (θ : ℝ) (hs : Real.sin θ = 0) (hc : 0 ≤ Real.cos θ) :
    cotSigned 0 θ = ⊤ := by
  unfold cotSigned
  rw [ite_eq_left hs, ite_eq_right (not_lt.mpr hc), ite_eq_right (lt_irrefl 0)]

/-- A pole with `cos θ = 1`. -/
theorem cotCore_of_cos_eq_one (neg : Bool) {θ : ℝ} (hs : Real.sin θ = 0)
    (hc : Real.cos θ = 1) : cotCore neg θ = if (!neg) = true then ⊤ else ⊥ := by
  unfold cotCore
  rw [ite_eq_left hs, ite_eq_right (by rw [hc]; norm_num)]
  cases neg <;> simp

/-- A pole with `cos θ = −1`. -/
theorem cotCore_of_cos_eq_neg_one (neg : Bool) {θ : ℝ} (hs : Real.sin θ = 0)
    (hc : Real.cos θ = -1) : cotCore neg θ = if neg = true then ⊤ else ⊥ := by
  unfold cotCore
  rw [ite_eq_left hs, ite_eq_left (by rw [hc]; norm_num)]

/-- A zero of the cotangent. -/
theorem cotCore_of_cos_eq_zero (neg : Bool) {θ : ℝ} (hs : Real.sin θ ≠ 0)
    (hc : Real.cos θ = 0) : cotCore neg θ = ((0 : ℝ) : EReal) := by
  unfold cotCore
  rw [ite_eq_right hs, hc, zero_div, mul_zero]

/-- The values `±1`. -/
theorem cotCore_of_tan_pm_one (neg : Bool) {θ : ℝ} {P : Prop} [Decidable P]
    (h : Real.tan θ = if P then 1 else -1) :
    cotCore neg θ
      = (((if neg = true then -1 else 1) * (if P then 1 else -1) : ℝ) : EReal) := by
  have hs : Real.sin θ ≠ 0 := fun hs => by
    rw [Real.tan_eq_sin_div_cos, hs, zero_div] at h
    split_ifs at h <;> norm_num at h
  unfold cotCore
  rw [ite_eq_right hs, cot_eq_inv_tan, h]
  by_cases hP : P <;> simp [hP]

end Spec

/-- **The case distinction after the reduction** computes the rounding of `± cot (2πr)`, with
the signed infinities at the poles. -/
theorem cotPeriodCore_eq (neg : Bool) (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cotPeriodCore neg r hr p mode
      = roundVal p mode (some (Spec.cotCore neg (2 * Real.pi * (AzRat.toRat r : ℝ)))) := by
  obtain ⟨hr0, hr1⟩ := hr
  unfold cotPeriodCore
  by_cases h1 : r.den = AzNat.ofNat 1
  · rw [dite_eq_left h1, Spec.cotCore_of_cos_eq_one neg
      (sin_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h1]; norm_num))
      (cos_two_pi_mul_rat_of_den_eq_one (den_toRat_eq h1)), roundVal_inf]
  rw [dite_eq_right h1]
  by_cases h2 : r.den = AzNat.ofNat 2
  · rw [dite_eq_left h2, Spec.cotCore_of_cos_eq_neg_one neg
      (sin_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h2]))
      (cos_two_pi_mul_rat_of_den_eq_two (den_toRat_eq h2)), roundVal_inf]
  rw [dite_eq_right h2]
  by_cases h4 : r.den = AzNat.ofNat 4
  · have hs : Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) ≠ 0 := by
      rw [sin_two_pi_mul_toRat_of_den_eq_four hr0 hr1 h4]
      split_ifs <;> norm_num
    rw [dite_eq_left h4, Spec.cotCore_of_cos_eq_zero neg hs
      (cos_two_pi_mul_rat_of_den_eq_four (den_toRat_eq h4)), EReal.coe_zero, roundVal_zero]
  rw [dite_eq_right h4]
  by_cases h8 : r.den = AzNat.ofNat 8
  · rw [dite_eq_left h8,
      Spec.cotCore_of_tan_pm_one neg (tan_two_pi_mul_toRat_of_den_eq_eight hr0 hr1 h8),
      setPrecRound_eq_roundVal (toVal_signedPow2 _ _), signedPow2_zero_val_bne]
  rw [dite_eq_right h8,
    Spec.cotCore_of_irrational (irrational_cot_two_pi_mul_toRat r h1 h2 h4 h8)]
  exact zivLoopCertified_eq_or_none p mode _ _
    (not_mem_floatSet_of_irrational p
      (irrational_sign_mul (irrational_cot_two_pi_mul_toRat r h1 h2 h4 h8) neg))
    _ (by unfold zivGuardBits; omega)
    (fun w hw => cotPeriodApprox_valid_or_none neg r hr0 hr1
      (by unfold zivGuardBits at hw; omega) p mode) _

/-- **`cot x` is correctly rounded**, `+∞` at `0`. -/
theorem cotPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cotPrecRound x p mode = liftVal Spec.cot x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [cotPrecRound, toVal_infinity, Option.bind_some]
    cases s <;> simp
  | zero =>
    simp only [cotPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.cot_coe,
      Spec.cotSigned_zero 0 Real.sin_zero (by rw [Real.cos_zero]; norm_num)]
    exact (roundVal_inf p mode true).symm
  | finite s e q m hv =>
    simp only [cotPrecRound, toVal_finite, Option.bind_some, Spec.cot_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx := toVal_finite s e q m hv
    have hx0 := finiteVal_ne_zero s e hv
    rw [Spec.cotSigned_self (finiteVal_neg_iff s e hv),
      Spec.cotCore_of_irrational (irrational_cot_abs_of_toVal hx hx0)]
    split
    · next r hT => exact cotTiny?_eq hv p mode hT
    exact zivLoopCertified_eq_or_none p mode _ _
      (not_mem_floatSet_of_irrational p
        (irrational_sign_mul (irrational_cot_abs_of_toVal hx hx0) (!s)))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => cotApprox_valid_or_none (!s) hx (abs_finiteVal_bounds s e hv).2
        (by unfold zivGuardBits at hw; omega) p mode) _

/-- **`cot q` of a rational is correctly rounded**, `+∞` at `0`. -/
theorem cotRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cotRatPrecRound q p mode
      = roundVal p mode (Spec.cot (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold cotRatPrecRound
  rw [Spec.cot_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.cotSigned_zero 0 Real.sin_zero (by rw [Real.cos_zero]; norm_num)]
    exact (roundVal_inf p mode true).symm
  · rw [dite_eq_right h0, dite_eq_right hp, Spec.cotSigned_self (not_sign_iff_toRat_neg q h0),
      Spec.cotCore_of_irrational (irrational_cot_abs_toRat q h0)]
    split
    · next r hT => exact cotTinyRat?_eq q h0 hT
    exact zivLoopCertified_eq_or_none p mode _ _
      (not_mem_floatSet_of_irrational p
        (irrational_sign_mul (irrational_cot_abs_toRat q h0) (!q.sign)))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => cotRatApprox_valid_or_none q (by unfold zivGuardBits at hw; omega) p mode) _

/-- The tiny path of the cotangent with a period. -/
theorem cotPeriodTiny?_eq_period {neg : Bool} {m u : AzNat} (hm : 0 < m.toNat)
    (hu : 0 < u.toNat) {E e' : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {xv U : ℝ} {ρ : ℚ} (hneg : neg = true ↔ xv < 0) (hU : 0 < U)
    (hxm : |xv| / U = (m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) (hρ : |xv| / U = (ρ : ℝ))
    (hρ0 : 0 < ρ) (hb : 2 * Real.pi * (|xv| / U) < (2 : ℝ) ^ e'.toInt)
    (hsmall : (2 : ℝ) ^ e'.toInt ≤ 1 / 2) (hT : cotPeriodTiny? neg m u E e' p mode = some r) :
    r = roundVal p mode (some (Spec.cotSigned xv (2 * Real.pi * xv / U))) := by
  have hpi0 := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hρ8 : ρ < 1 / 8 := by
    have h1 : (ρ : ℝ) < ((1 / 8 : ℚ) : ℝ) := by
      rw [← hρ]; push_cast
      nlinarith
    exact_mod_cast h1
  have hirr : Irrational (Real.cos (2 * Real.pi * (|xv| / U))
      / Real.sin (2 * Real.pi * (|xv| / U))) := by
    rw [cot_eq_inv_tan, hρ]
    exact (irrational_tan_two_pi_mul_rat_of_small hρ0 hρ8).inv
  rw [Spec.cotSigned_two_pi_div hneg hU (k := 0) (ρ := |xv| / U) (by simp),
    Spec.cotCore_of_irrational hirr]
  rw [hxm] at hb hirr ⊢
  exact cotPeriodTiny?_eq hm hu hb hirr hT

/-- **`cot (2π x / u)` is correctly rounded**, with the signed infinities at the poles and `+∞`
at `0`. -/
theorem cotWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cotWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.cotWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  unfold cotWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu]
    cases x <;> simp
  · rw [dite_eq_right hu]
    cases x with
    | nan => rfl
    | infinity s => cases s <;> simp
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.cotWithPeriod_coe _ hu,
        Spec.cotSigned_zero _ (by rw [mul_zero, zero_div, Real.sin_zero])
          (by rw [mul_zero, zero_div, Real.cos_zero]; norm_num)]
      exact (roundVal_inf p mode true).symm
    | finite s e q m hv =>
      simp only [toVal_finite, Option.bind_some, Spec.cotWithPeriod_coe _ hu]
      rw [dite_eq_right hp]
      have hUn : 0 < u.toNat := Nat.pos_of_ne_zero hu
      have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
      set xv := finiteVal s e m with hxv
      have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
      set E := e - (AzNat.ofNat m.size).toAzInt with hEdef
      have hE : E.toInt = e.toInt - m.size := by
        rw [hEdef, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat]
      have habsx : |xv| / u.toNat = (m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat := by
        rw [hxv, abs_finiteVal_eq, hE]
      have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
      have hax := abs_pos.mpr hx0
      split
      · next r hT =>
        obtain ⟨hs, he⟩ := cotTinyCore?_cond hT
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
        have hpi0 := Real.pi_pos
        have ht3 : (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt = 8 * (2 : ℝ) ^ e.toInt := by
          rw [he3, zpow_add₀ two_ne_zero]; norm_num; ring
        have hsmall : (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt ≤ 1 / 2 := by
          rw [htoInt, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
          calc (1 / 2 : ℝ) ^ (e + AzInt.ofInt 3).abs.toNat ≤ (1 / 2 : ℝ) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 2 := by norm_num
        have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast hUn
        have hdiv : |xv| / u.toNat ≤ |xv| := div_le_self hax.le hU1
        have hbound : 2 * Real.pi * (|xv| / u.toNat) < (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt := by
          rw [ht3]
          nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        obtain ⟨rx, hrx⟩ := finiteVal_rat s e hv
        have hr : |xv| / u.toNat = ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
          push_cast; rw [← hrx]
        have hm : 0 < m.toNat := by
          rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
          · rw [hxv, abs_finiteVal_eq, h0] at hax
            simp at hax
          · exact h0
        have hρ0 : (0 : ℚ) < |rx| / (u.toNat : ℚ) := by
          have h1 : (0 : ℝ) < ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
            rw [← hr]; exact div_pos hax hU
          exact_mod_cast h1
        refine cotPeriodTiny?_eq_period (u := AzNat.ofNat u.toNat) hm
          (by rw [AzNat.toNat_ofNat]; exact hUn) hneg hU ?_ hr hρ0 hbound hsmall hT
        rw [AzNat.toNat_ofNat]
        exact habsx
      have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
        rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
      obtain ⟨k, hk, hr0, hr1⟩ := periodFrac_spec m E hun
      rw [AzNat.toNat_ofNat, ← habsx] at hk
      rw [cotPeriodCore_eq, Spec.cotSigned_two_pi_div hneg hU hk]

/-- **`cot (2π q / u)` of a rational is correctly rounded**, with the signed infinities at the
poles and `+∞` at `0`. -/
theorem cotRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cotRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.cotWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold cotRatWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu, Spec.cotWithPeriod_zero_period, roundVal_none]
  rw [dite_eq_right hu, Spec.cotWithPeriod_coe _ hu]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.cotSigned_zero _ (by rw [mul_zero, zero_div, Real.sin_zero])
        (by rw [mul_zero, zero_div, Real.cos_zero]; norm_num)]
    exact (roundVal_inf p mode true).symm
  rw [dite_eq_right h0, dite_eq_right hp]
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  have hUn : 0 < u.toNat := Nat.pos_of_ne_zero hu
  have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
  have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast hUn
  have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  have hax := abs_pos.mpr hq0
  have hneg : (!q.sign) = true ↔ qv < 0 := not_sign_iff_toRat_neg q h0
  split
  · next r hT =>
    obtain ⟨hs, he⟩ := cotTinyCore?_cond hT
    unfold zivGuardBits at he
    set E := ratExpBound q + AzInt.ofInt 2 with hE
    have htoInt : E.toInt = if E.sign then (E.abs.toNat : ℤ) else -(E.abs.toNat : ℤ) := rfl
    rw [hs] at htoInt
    simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
    have he2 : E.toInt = (ratExpBound q).toInt + 2 := by
      rw [hE, AzInt.toInt_add, AzInt.toInt_ofInt]
    have hq := abs_toRat_lt_two_zpow q
    rw [← hqv] at hq
    have hpi4 := Real.pi_le_four
    have hpi0 := Real.pi_pos
    have ht : (2 : ℝ) ^ E.toInt = 8 * (2 : ℝ) ^ ((ratExpBound q).toInt - 1) := by
      rw [he2, show (ratExpBound q).toInt + 2 = ((ratExpBound q).toInt - 1) + 3 by ring,
        zpow_add₀ two_ne_zero]
      norm_num; ring
    have hsmall : (2 : ℝ) ^ E.toInt ≤ 1 / 2 := by
      rw [htoInt, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
      calc (1 / 2 : ℝ) ^ E.abs.toNat ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    have hdiv : |qv| / u.toNat ≤ |qv| := div_le_self hax.le hU1
    have hbound : 2 * Real.pi * (|qv| / u.toNat) < (2 : ℝ) ^ E.toInt := by
      rw [ht]
      nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have hr : |qv| / u.toNat = ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
      push_cast; rfl
    have hm : 0 < q.num.toNat :=
      Nat.pos_of_ne_zero fun h => h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
    have hD : 0 < (q.den * AzNat.ofNat u.toNat).toNat := by
      rw [AzNat.toNat_mul, AzNat.toNat_ofNat]
      exact Nat.mul_pos (AzRat.den_toNat_pos q) hUn
    have hy_eq : |qv| / u.toNat = (q.num.toNat : ℝ) * (2 : ℝ) ^ (AzInt.ofInt 0).toInt
        / ((q.den * AzNat.ofNat u.toNat).toNat : ℝ) := by
      rw [AzInt.toInt_ofInt, zpow_zero, mul_one, AzNat.toNat_mul, AzNat.toNat_ofNat, hqv,
        abs_coe_toRat, div_div]
      push_cast
      rfl
    have hρ0 : (0 : ℚ) < |AzRat.toRat q| / (u.toNat : ℚ) := by
      have h1 : (0 : ℝ) < ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
        rw [← hr]; exact div_pos hax hU
      exact_mod_cast h1
    exact cotPeriodTiny?_eq_period hm hD hneg hU hy_eq hr hρ0 hbound hsmall hT
  have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
    rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
  obtain ⟨k, hk, hr0, hr1⟩ := periodFracRat_spec q hun
  rw [AzNat.toNat_ofNat, ← hqv] at hk
  rw [cotPeriodCore_eq, Spec.cotSigned_two_pi_div hneg hU hk]

/-- **`cot (π x)` is correctly rounded**, with the signed infinities at the integers. -/
theorem cotPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cotPiPrecRound x p mode = liftVal Spec.cotPi x p mode := by
  unfold cotPiPrecRound liftVal
  rw [cotWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.cotWithPeriod_two a

/-- **`cot (π q)` of a rational is correctly rounded**, with the signed infinities at the
integers. -/
theorem cotPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cotPiRatPrecRound q p mode
      = roundVal p mode (Spec.cotPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold cotPiRatPrecRound
  rw [cotRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.cotWithPeriod_two _)

end Azurite.AzFloat
