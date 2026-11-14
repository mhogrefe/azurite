/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Csc
import Azurite.AzFloat.Equiv.SinWithPeriod
import Azurite.AzFloat.Equiv.SinRatWithPeriod
import Azurite.AzFloat.Equiv.Sec

/-!
# Equivalence: the cosecant

`Spec.csc`, `Spec.cscWithPeriod`, `Spec.cscPi` (the poles of `Spec.cscSigned`: the infinity with
the sign of the argument, `+∞` at `0`), `cscPeriodCore_eq`, and for `p ≠ 0`:

* `cscPrecRound_eq_liftVal`, `cscRatPrecRound_eq`;
* `cscWithPeriodPrecRound_eq`, `cscRatWithPeriodPrecRound_eq`;
* `cscPiPrecRound_eq_liftVal`, `cscPiRatPrecRound_eq`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real cosecant: `1 / sin a`, `+∞` at `0`; undefined (`NaN`) at `±∞`. -/
noncomputable def csc (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some (cscSigned a.toReal a.toReal)

theorem csc_coe (r : ℝ) : csc (r : EReal) = some (cscSigned r r) := by
  unfold csc
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem csc_top : csc ⊤ = none := by
  unfold csc
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem csc_bot : csc ⊥ = none := by
  unfold csc
  rw [ite_eq_left (Or.inr rfl)]

open Classical in
/-- Extended-real `csc (2π a / u)`, at the poles the infinity with the sign of `a` (`+∞` at
`0`): undefined for `u = 0` and at `±∞`. -/
noncomputable def cscWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  if u = 0 ∨ a = ⊤ ∨ a = ⊥ then none
  else some (cscSigned a.toReal (2 * Real.pi * a.toReal / u))

theorem cscWithPeriod_coe (r : ℝ) {u : ℕ} (hu : u ≠ 0) :
    cscWithPeriod r u = some (cscSigned r (2 * Real.pi * r / u)) := by
  unfold cscWithPeriod
  rw [ite_eq_right (not_or.mpr ⟨hu, not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩⟩),
    EReal.toReal_coe]

@[simp] theorem cscWithPeriod_zero_period (a : EReal) : cscWithPeriod a 0 = none := by
  unfold cscWithPeriod
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cscWithPeriod_top (u : ℕ) : cscWithPeriod ⊤ u = none := by
  unfold cscWithPeriod
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

@[simp] theorem cscWithPeriod_bot (u : ℕ) : cscWithPeriod ⊥ u = none := by
  unfold cscWithPeriod
  rw [ite_eq_left (Or.inr (Or.inr rfl))]

open Classical in
/-- Extended-real `csc (π a)`, at the integers the infinity with the sign of `a` (`+∞` at `0`):
undefined (`NaN`) at `±∞`. -/
noncomputable def cscPi (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some (cscSigned a.toReal (Real.pi * a.toReal))

theorem cscPi_coe (r : ℝ) : cscPi (r : EReal) = some (cscSigned r (Real.pi * r)) := by
  unfold cscPi
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem cscPi_top : cscPi ⊤ = none := by
  unfold cscPi
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cscPi_bot : cscPi ⊥ = none := by
  unfold cscPi
  rw [ite_eq_left (Or.inr rfl)]

/-- `csc (π a)` is the period-`2` case of `cscWithPeriod`. -/
theorem cscWithPeriod_two (a : EReal) : cscWithPeriod a 2 = cscPi a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [cscWithPeriod_coe r (by norm_num), cscPi_coe]
    congr 2
    push_cast
    ring

theorem cscSigned_zero (θ : ℝ) (h : Real.sin θ = 0) : cscSigned 0 θ = ⊤ := by
  unfold cscSigned
  rw [ite_eq_left h, ite_eq_right (lt_irrefl 0)]

theorem cscCore_of_sin_eq_zero (neg : Bool) {θ : ℝ} (h : Real.sin θ = 0) :
    cscCore neg θ = if (!neg) = true then ⊤ else ⊥ := by
  unfold cscCore
  rw [ite_eq_left h]
  cases neg <;> simp

theorem cscCore_of_sin_pm_one (neg : Bool) {θ : ℝ} {P : Prop} [Decidable P]
    (h : Real.sin θ = if P then 1 else -1) :
    cscCore neg θ
      = (((if (neg != decide P) = true then (1 : ℝ) else -1) * (2 : ℝ) ^ (0 : ℤ) : ℝ) : EReal) := by
  unfold cscCore
  rw [h]
  cases neg <;> by_cases hP : P <;> simp [hP]

theorem cscCore_of_sin_pm_half (neg : Bool) {θ : ℝ} {P : Prop} [Decidable P]
    (h : Real.sin θ = if P then 1 / 2 else -1 / 2) :
    cscCore neg θ
      = (((if (neg != decide P) = true then (1 : ℝ) else -1) * (2 : ℝ) ^ (1 : ℤ) : ℝ) : EReal) := by
  unfold cscCore
  rw [h]
  cases neg <;> by_cases hP : P <;> simp [hP] <;> norm_num

end Spec

/-- **The case distinction after the reduction** computes the rounding of `± csc (2πr)`, with
the signed infinity at the poles. -/
theorem cscPeriodCore_eq (neg : Bool) (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cscPeriodCore neg r hr p mode
      = roundVal p mode (some (Spec.cscCore neg (2 * Real.pi * (AzRat.toRat r : ℝ)))) := by
  obtain ⟨hr0, hr1⟩ := hr
  unfold cscPeriodCore
  by_cases h1 : r.den = AzNat.ofNat 1
  · rw [dite_eq_left h1, Spec.cscCore_of_sin_eq_zero neg
      (sin_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h1]; norm_num)), roundVal_inf]
  rw [dite_eq_right h1]
  by_cases h2 : r.den = AzNat.ofNat 2
  · rw [dite_eq_left h2, Spec.cscCore_of_sin_eq_zero neg
      (sin_two_pi_mul_rat_of_den_dvd_two (by rw [den_toRat_eq h2])), roundVal_inf]
  rw [dite_eq_right h2]
  by_cases h4 : r.den = AzNat.ofNat 4
  · rw [dite_eq_left h4,
      Spec.cscCore_of_sin_pm_one neg (sin_two_pi_mul_toRat_of_den_eq_four hr0 hr1 h4),
      setPrecRound_eq_roundVal (toVal_signedPow2 _ _)]
  rw [dite_eq_right h4]
  by_cases h12 : r.den = AzNat.ofNat 12
  · rw [dite_eq_left h12,
      Spec.cscCore_of_sin_pm_half neg (sin_two_pi_mul_toRat_of_den_eq_twelve hr0 hr1 h12),
      setPrecRound_eq_roundVal (toVal_signedPow2 _ _)]
  rw [dite_eq_right h12,
    Spec.cscCore_of_irrational (irrational_csc_two_pi_mul_toRat r h1 h2 h4 h12)]
  exact zivLoopCertified_eq_or_none p mode _ _
    (not_mem_floatSet_of_irrational p
      (irrational_sign_mul (irrational_csc_two_pi_mul_toRat r h1 h2 h4 h12) neg))
    _ (by unfold zivGuardBits; omega)
    (fun w hw => cscPeriodApprox_valid_or_none neg r hr0 hr1
      (by unfold zivGuardBits at hw; omega) p mode) _

/-- **`csc x` is correctly rounded**, `+∞` at `0`. -/
theorem cscPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cscPrecRound x p mode = liftVal Spec.csc x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [cscPrecRound, toVal_infinity, Option.bind_some]
    cases s <;> simp
  | zero =>
    simp only [cscPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.csc_coe, Spec.cscSigned_zero 0 Real.sin_zero]
    exact (roundVal_inf p mode true).symm
  | finite s e q m hv =>
    simp only [cscPrecRound, toVal_finite, Option.bind_some, Spec.csc_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx := toVal_finite s e q m hv
    have hx0 := finiteVal_ne_zero s e hv
    rw [Spec.cscSigned_self (finiteVal_neg_iff s e hv),
      Spec.cscCore_of_irrational (irrational_csc_abs_of_toVal hx hx0)]
    split
    · next r hT => exact cscTiny?_eq hv p mode hT
    exact zivLoopCertified_eq_or_none p mode _ _
      (not_mem_floatSet_of_irrational p
        (irrational_sign_mul (irrational_csc_abs_of_toVal hx hx0) (!s)))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => cscApprox_valid_or_none (!s) hx (abs_finiteVal_bounds s e hv).2
        (by unfold zivGuardBits at hw; omega) p mode) _

/-- The sign bit of a nonzero rational. -/
theorem not_sign_iff_toRat_neg (q : AzRat) (h0 : q.num ≠ 0) :
    (!q.sign) = true ↔ ((AzRat.toRat q : ℚ) : ℝ) < 0 := by
  have hpos := toRat_sign_iff q h0
  have hq0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hpos, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h hq0, le_of_lt⟩

/-- **`csc q` of a rational is correctly rounded**, `+∞` at `0`. -/
theorem cscRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cscRatPrecRound q p mode
      = roundVal p mode (Spec.csc (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold cscRatPrecRound
  rw [Spec.csc_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.cscSigned_zero 0 Real.sin_zero]
    exact (roundVal_inf p mode true).symm
  · rw [dite_eq_right h0, dite_eq_right hp, Spec.cscSigned_self (not_sign_iff_toRat_neg q h0),
      Spec.cscCore_of_irrational (irrational_csc_abs_toRat q h0)]
    split
    · next r hT => exact cscTinyRat?_eq q h0 hT
    exact zivLoopCertified_eq_or_none p mode _ _
      (not_mem_floatSet_of_irrational p
        (irrational_sign_mul (irrational_csc_abs_toRat q h0) (!q.sign)))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => cscRatApprox_valid_or_none q (by unfold zivGuardBits at hw; omega) p mode) _

/-- The tiny path of the cosecant with a period. -/
theorem cscPeriodTiny?_eq_period {neg : Bool} {m u : AzNat} (hm : 0 < m.toNat)
    (hu : 0 < u.toNat) {E e' : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {xv U : ℝ} {ρ : ℚ} (hneg : neg = true ↔ xv < 0)
    (hxm : |xv| / U = (m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) (hρ : |xv| / U = (ρ : ℝ))
    (hρ0 : 0 < ρ) (hb : 2 * Real.pi * (|xv| / U) < (2 : ℝ) ^ e'.toInt)
    (hsmall : (2 : ℝ) ^ e'.toInt ≤ 1 / 2) (hT : cscPeriodTiny? neg m u E e' p mode = some r) :
    r = roundVal p mode (some (Spec.cscSigned xv (2 * Real.pi * xv / U))) := by
  have hpi0 := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hρ12 : ρ < 1 / 12 := by
    have h1 : (ρ : ℝ) < ((1 / 12 : ℚ) : ℝ) := by
      rw [← hρ]; push_cast
      nlinarith
    exact_mod_cast h1
  have hirr : Irrational (1 / Real.sin (2 * Real.pi * (|xv| / U))) := by
    rw [one_div, hρ]
    exact (irrational_sin_two_pi_mul_rat_of_small hρ0 hρ12).inv
  rw [Spec.cscSigned_two_pi_div hneg (k := 0) (ρ := |xv| / U) (by simp),
    Spec.cscCore_of_irrational hirr]
  rw [hxm] at hb hirr ⊢
  exact cscPeriodTiny?_eq hm hu hb hirr hT

/-- **`csc (2π x / u)` is correctly rounded**, with `±∞` (the sign of `x`) at the poles and `+∞`
at `0`. -/
theorem cscWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cscWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.cscWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  unfold cscWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu]
    cases x <;> simp
  · rw [dite_eq_right hu]
    cases x with
    | nan => rfl
    | infinity s => cases s <;> simp
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.cscWithPeriod_coe _ hu,
        Spec.cscSigned_zero _ (by rw [mul_zero, zero_div, Real.sin_zero])]
      exact (roundVal_inf p mode true).symm
    | finite s e q m hv =>
      simp only [toVal_finite, Option.bind_some, Spec.cscWithPeriod_coe _ hu]
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
        obtain ⟨hs, he⟩ := cscTinyCore?_cond hT
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
        refine cscPeriodTiny?_eq_period (u := AzNat.ofNat u.toNat) hm
          (by rw [AzNat.toNat_ofNat]; exact hUn) hneg ?_ hr hρ0 hbound hsmall hT
        rw [AzNat.toNat_ofNat]
        exact habsx
      have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
        rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
      obtain ⟨k, hk, hr0, hr1⟩ := periodFrac_spec m E hun
      rw [AzNat.toNat_ofNat, ← habsx] at hk
      rw [cscPeriodCore_eq, Spec.cscSigned_two_pi_div hneg hk]

/-- **`csc (2π q / u)` of a rational is correctly rounded**, with `±∞` (the sign of `q`) at the
poles and `+∞` at `0`. -/
theorem cscRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cscRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.cscWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold cscRatWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu, Spec.cscWithPeriod_zero_period, roundVal_none]
  rw [dite_eq_right hu, Spec.cscWithPeriod_coe _ hu]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.cscSigned_zero _ (by rw [mul_zero, zero_div, Real.sin_zero])]
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
    obtain ⟨hs, he⟩ := cscTinyCore?_cond hT
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
    exact cscPeriodTiny?_eq_period hm hD hneg hy_eq hr hρ0 hbound hsmall hT
  have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
    rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
  obtain ⟨k, hk, hr0, hr1⟩ := periodFracRat_spec q hun
  rw [AzNat.toNat_ofNat, ← hqv] at hk
  rw [cscPeriodCore_eq, Spec.cscSigned_two_pi_div hneg hk]

/-- **`csc (π x)` is correctly rounded**, `±∞` with the sign of `x` at the integers. -/
theorem cscPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cscPiPrecRound x p mode = liftVal Spec.cscPi x p mode := by
  unfold cscPiPrecRound liftVal
  rw [cscWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.cscWithPeriod_two a

/-- **`csc (π q)` of a rational is correctly rounded**, `±∞` with the sign of `q` at the
integers. -/
theorem cscPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cscPiRatPrecRound q p mode
      = roundVal p mode (Spec.cscPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold cscPiRatPrecRound
  rw [cscRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.cscWithPeriod_two _)

end Azurite.AzFloat
