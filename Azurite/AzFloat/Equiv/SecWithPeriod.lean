/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SecWithPeriod
import Azurite.AzFloat.Equiv.CosWithPeriod
import Azurite.AzFloat.Equiv.CosRatWithPeriod
import Azurite.AzFloat.Equiv.CosRat
import Azurite.AzFloat.Equiv.Sec

/-!
# Equivalence: `sec (2π x / u)`, `sec q`, `sec (π x)`

`Spec.secWithPeriod`, `Spec.secPi` (with the pole value `+∞` of `Spec.secPole`),
`secPeriodCore_eq`, and for `p ≠ 0`:

* `secWithPeriodPrecRound_eq`, `secRatWithPeriodPrecRound_eq`;
* `secRatPrecRound_eq : secRatPrecRound q p mode = roundVal p mode (Spec.sec q)`;
* `secPiPrecRound_eq_liftVal`, `secPiRatPrecRound_eq`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `sec (2π a / u)`, `+∞` at the poles: undefined for `u = 0` and at `±∞`. -/
noncomputable def secWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  if u = 0 ∨ a = ⊤ ∨ a = ⊥ then none else some (secPole (2 * Real.pi * a.toReal / u))

theorem secWithPeriod_coe (r : ℝ) {u : ℕ} (hu : u ≠ 0) :
    secWithPeriod r u = some (secPole (2 * Real.pi * r / u)) := by
  unfold secWithPeriod
  rw [ite_eq_right (not_or.mpr ⟨hu, not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩⟩),
    EReal.toReal_coe]

@[simp] theorem secWithPeriod_zero_period (a : EReal) : secWithPeriod a 0 = none := by
  unfold secWithPeriod
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem secWithPeriod_top (u : ℕ) : secWithPeriod ⊤ u = none := by
  unfold secWithPeriod
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

@[simp] theorem secWithPeriod_bot (u : ℕ) : secWithPeriod ⊥ u = none := by
  unfold secWithPeriod
  rw [ite_eq_left (Or.inr (Or.inr rfl))]

open Classical in
/-- Extended-real `sec (π a)`, `+∞` at the half-integers: undefined (`NaN`) at `±∞`. -/
noncomputable def secPi (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some (secPole (Real.pi * a.toReal))

theorem secPi_coe (r : ℝ) : secPi (r : EReal) = some (secPole (Real.pi * r)) := by
  unfold secPi
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem secPi_top : secPi ⊤ = none := by
  unfold secPi
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem secPi_bot : secPi ⊥ = none := by
  unfold secPi
  rw [ite_eq_left (Or.inr rfl)]

/-- `sec (π a)` is the period-`2` case of `secWithPeriod`. -/
theorem secWithPeriod_two (a : EReal) : secWithPeriod a 2 = secPi a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [secWithPeriod_coe r (by norm_num), secPi_coe]
    congr 2
    push_cast
    ring

/-- With an irrational reciprocal the cosine does not vanish and the value is the plain
secant. -/
theorem secPole_of_irrational {θ : ℝ} (h : Irrational (1 / Real.cos θ)) :
    secPole θ = ((1 / Real.cos θ : ℝ) : EReal) := by
  refine secPole_of_cos_ne_zero fun hc => ?_
  rw [hc, div_zero] at h
  exact h ⟨0, by simp⟩

end Spec

theorem toVal_one_shl_one : (one <<< AzInt.ofInt 1).toVal = some ((2 : ℝ) : EReal) := by
  rw [toVal_shiftLeft_one toVal_one', mul_one]

theorem toVal_neg_one_shl_one : (-(one <<< AzInt.ofInt 1)).toVal = some ((-2 : ℝ) : EReal) := by
  rw [toVal_neg, toVal_one_shl_one, Option.map_some, ← EReal.coe_neg]

/-- **The case distinction after the reduction** computes the rounding of `secPole (2πr)`. -/
theorem secPeriodCore_eq (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    secPeriodCore r hr p mode
      = roundVal p mode (some (Spec.secPole (2 * Real.pi * (AzRat.toRat r : ℝ)))) := by
  obtain ⟨hr0, hr1⟩ := hr
  unfold secPeriodCore
  by_cases h1 : r.den = AzNat.ofNat 1
  · have hc := cos_two_pi_mul_rat_of_den_eq_one (den_toRat_eq h1)
    rw [dite_eq_left h1, Spec.secPole_of_cos_ne_zero (by rw [hc]; norm_num), hc, div_one,
      setPrecRound_eq_roundVal toVal_one']
  rw [dite_eq_right h1]
  by_cases h2 : r.den = AzNat.ofNat 2
  · have hc := cos_two_pi_mul_rat_of_den_eq_two (den_toRat_eq h2)
    rw [dite_eq_left h2, Spec.secPole_of_cos_ne_zero (by rw [hc]; norm_num), hc,
      show (1 : ℝ) / -1 = -1 by norm_num, setPrecRound_eq_roundVal toVal_neg_one_float]
  rw [dite_eq_right h2]
  by_cases h4 : r.den = AzNat.ofNat 4
  · rw [dite_eq_left h4,
      Spec.secPole_of_cos_eq_zero (cos_two_pi_mul_rat_of_den_eq_four (den_toRat_eq h4))]
    exact (roundVal_inf p mode true).symm
  rw [dite_eq_right h4]
  by_cases h3 : r.den = AzNat.ofNat 3
  · have hc := cos_two_pi_mul_rat_of_den_eq_three (den_toRat_eq h3)
    rw [dite_eq_left h3, Spec.secPole_of_cos_ne_zero (by rw [hc]; norm_num), hc,
      show (1 : ℝ) / (-1 / 2) = -2 by norm_num, setPrecRound_eq_roundVal toVal_neg_one_shl_one]
  rw [dite_eq_right h3]
  by_cases h6 : r.den = AzNat.ofNat 6
  · have hc := cos_two_pi_mul_rat_of_den_eq_six (den_toRat_eq h6)
    rw [dite_eq_left h6, Spec.secPole_of_cos_ne_zero (by rw [hc]; norm_num), hc,
      show (1 : ℝ) / (1 / 2) = 2 by norm_num, setPrecRound_eq_roundVal toVal_one_shl_one]
  rw [dite_eq_right h6,
    Spec.secPole_of_irrational (irrational_sec_two_pi_mul_toRat r h1 h2 h3 h4 h6)]
  exact zivLoopCertified_eq_or_none p mode _ _
    (not_mem_floatSet_of_irrational p (irrational_sec_two_pi_mul_toRat r h1 h2 h3 h4 h6))
    _ (by unfold zivGuardBits; omega)
    (fun w hw => secPeriodApprox_valid_or_none r hr0 hr1
      (by unfold zivGuardBits at hw; omega) p mode) _

/-- The tiny path of the secant with a period: for `0 < |x|/U` and `|2π x / U| < B ≤ 1/2`. -/
theorem secTiny?_eq_period {e : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {xv U : ℝ} {ρ : ℚ} (hU : 0 < U) (hρ : |xv| / U = (ρ : ℝ))
    (hρ0 : 0 < ρ) (hb : 2 * Real.pi * (|xv| / U) < (2 : ℝ) ^ e.toInt)
    (hsmall : (2 : ℝ) ^ e.toInt ≤ 1 / 2) (hT : secTiny? e p mode = some r) :
    r = roundVal p mode (some (Spec.secPole (2 * Real.pi * xv / U))) := by
  have hpi0 := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have habs : |2 * Real.pi * xv / U| = 2 * Real.pi * (|xv| / U) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hU,
      mul_div_assoc]
  have hρ6 : ρ < 1 / 6 := by
    have h1 : (ρ : ℝ) < ((1 / 6 : ℚ) : ℝ) := by
      rw [← hρ]; push_cast
      nlinarith
    exact_mod_cast h1
  have hirr : Irrational (1 / Real.cos (2 * Real.pi * xv / U)) := by
    rw [one_div, ← Real.cos_abs, habs, hρ]
    exact (irrational_cos_two_pi_mul_rat_of_small hρ0 hρ6).inv
  rw [Spec.secPole_of_irrational hirr]
  exact secTiny?_eq (by rw [habs]; exact hb) hirr hT

/-- **`sec (2π x / u)` is correctly rounded**, `+∞` at the poles. -/
theorem secWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    secWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.secWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  unfold secWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu]
    cases x <;> simp
  · rw [dite_eq_right hu]
    cases x with
    | nan => rfl
    | infinity s => cases s <;> simp
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.secWithPeriod_coe _ hu, ite_eq_right hp, mul_zero, zero_div,
        Spec.secPole_of_cos_ne_zero (by rw [Real.cos_zero]; norm_num), Real.cos_zero, div_one,
        setPrecRound_eq_roundVal toVal_one']
    | finite s e q m hv =>
      simp only [toVal_finite, Option.bind_some, Spec.secWithPeriod_coe _ hu]
      rw [dite_eq_right hp]
      have hUn : 0 < u.toNat := Nat.pos_of_ne_zero hu
      have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
      set xv := finiteVal s e m with hxv
      have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
      split
      · next r hT =>
        obtain ⟨hs, he⟩ := secTiny?_cond hT
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
                pow_le_pow_of_le_one (by norm_num) (by norm_num)
                  (by unfold zivGuardBits at he; omega)
            _ = 1 / 2 := by norm_num
        have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast hUn
        have hax := abs_pos.mpr hx0
        have hdiv : |xv| / u.toNat ≤ |xv| := div_le_self hax.le hU1
        have hbound : 2 * Real.pi * (|xv| / u.toNat) < (2 : ℝ) ^ (e + AzInt.ofInt 3).toInt := by
          rw [ht3]
          nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        obtain ⟨rx, hrx⟩ := finiteVal_rat s e hv
        have hr : |xv| / u.toNat = ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
          push_cast; rw [← hrx]
        refine secTiny?_eq_period hU hr ?_ hbound hsmall hT
        have h1 : (0 : ℝ) < ((|rx| / (u.toNat : ℚ) : ℚ) : ℝ) := by
          rw [← hr]; exact div_pos hax hU
        exact_mod_cast h1
      set E := e - (AzNat.ofNat m.size).toAzInt with hEdef
      have hE : E.toInt = e.toInt - m.size := by
        rw [hEdef, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat]
      have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
        rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
      obtain ⟨k, hk, hr0, hr1⟩ := periodFrac_spec m E hun
      rw [AzNat.toNat_ofNat, hE, ← abs_finiteVal_eq s e m, ← hxv] at hk
      rw [secPeriodCore_eq, Spec.secPole_two_pi_div hU hk]

/-- **`sec (2π q / u)` of a rational is correctly rounded**, `+∞` at the poles. -/
theorem secRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    secRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.secWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold secRatWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu, Spec.secWithPeriod_zero_period, roundVal_none]
  rw [dite_eq_right hu, dite_eq_right hp, Spec.secWithPeriod_coe _ hu]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, mul_zero, zero_div,
      Spec.secPole_of_cos_ne_zero (by rw [Real.cos_zero]; norm_num), Real.cos_zero, div_one,
      setPrecRound_eq_roundVal toVal_one']
  rw [dite_eq_right h0]
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  have hUn : 0 < u.toNat := Nat.pos_of_ne_zero hu
  have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
  have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast hUn
  have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  have hax := abs_pos.mpr hq0
  split
  · next r hT =>
    obtain ⟨hs, he⟩ := secTiny?_cond hT
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
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold zivGuardBits at he; omega)
        _ = 1 / 2 := by norm_num
    have hdiv : |qv| / u.toNat ≤ |qv| := div_le_self hax.le hU1
    have hbound : 2 * Real.pi * (|qv| / u.toNat) < (2 : ℝ) ^ E.toInt := by
      rw [ht]
      nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have hr : |qv| / u.toNat = ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
      push_cast; rfl
    refine secTiny?_eq_period hU hr ?_ hbound hsmall hT
    have h1 : (0 : ℝ) < ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
      rw [← hr]; exact div_pos hax hU
    exact_mod_cast h1
  have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
    rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
  obtain ⟨k, hk, hr0, hr1⟩ := periodFracRat_spec q hun
  rw [AzNat.toNat_ofNat, ← hqv] at hk
  rw [secPeriodCore_eq, Spec.secPole_two_pi_div hU hk]

/-- **`sec q` of a rational is correctly rounded.** -/
theorem secRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    secRatPrecRound q p mode
      = roundVal p mode (Spec.sec (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold secRatPrecRound
  rw [dite_eq_right hp, Spec.sec_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.cos_zero, div_one,
      setPrecRound_eq_roundVal toVal_one']
  · rw [dite_eq_right h0]
    split
    · next r hT =>
      refine secTiny?_eq (lt_of_lt_of_le (abs_toRat_lt_two_zpow q) ?_)
        (irrational_sec_toRat q h0) hT
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact zivLoopCertified_eq_or_none p mode _ (1 / Real.cos (AzRat.toRat q : ℝ))
      (not_mem_floatSet_of_irrational p (irrational_sec_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => secRatApprox_valid_or_none q (by unfold zivGuardBits at hw; omega) p mode) _

/-- **`sec (π x)` is correctly rounded**, `+∞` at the half-integers. -/
theorem secPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    secPiPrecRound x p mode = liftVal Spec.secPi x p mode := by
  unfold secPiPrecRound liftVal
  rw [secWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.secWithPeriod_two a

/-- **`sec (π q)` of a rational is correctly rounded**, `+∞` at the half-integers. -/
theorem secPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    secPiRatPrecRound q p mode
      = roundVal p mode (Spec.secPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold secPiRatPrecRound
  rw [secRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.secWithPeriod_two _)

end Azurite.AzFloat
