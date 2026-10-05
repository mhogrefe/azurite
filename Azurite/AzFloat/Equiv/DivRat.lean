/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DivRat
import Azurite.AzFloat.Equiv.MulRat

/-!
# Division between an `AzFloat` and an `AzRat` is a lift

`divRatPrecRound_eq_liftVal`: `divRatPrecRound x q p mode = liftVal (fun a => Spec.div a q) x
p mode`, and `ratDivPrecRound_eq_liftVal`: `ratDivPrecRound q x p mode = liftVal (fun a =>
Spec.div q a) x p mode`, where `q` stands for the value of the rational.  Both reduce to
`shift_ofFractionRound_eq` after the special values of `Spec.div`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- The value of `x / q`, for `q ≠ 0`, as the shifted fraction `± (m · den / num) · 2^(e − |m|)`. -/
theorem finiteVal_div_toRat (s : Bool) (e : AzInt) (m : AzNat) (q : AzRat) (hq : q.num ≠ 0) :
    finiteVal s e m / AzRat.toRat q
      = ((if (s == q.sign) then 1 else -1) * (((m * q.den).toNat : ℝ) / (q.num.toNat : ℝ)) : ℝ)
        * 2 ^ (e - (AzNat.ofNat m.size).toAzInt).toInt := by
  have hnum : (q.num.toNat : ℝ) ≠ 0 := by exact_mod_cast (AzRat.num_toNat_pos q hq).ne'
  have hden : (q.den.toNat : ℝ) ≠ 0 := by exact_mod_cast (AzRat.den_toNat_pos q).ne'
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_mul, coe_toRat_eq]
  unfold finiteVal
  cases s <;> cases q.sign <;> simp <;> field_simp

/-- The value of `q / x` as the shifted fraction `± (num / (den · m)) · 2^(|m| − e)`. -/
theorem toRat_div_finiteVal (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) (q : AzRat) :
    AzRat.toRat q / finiteVal s e m
      = ((if (q.sign == s) then 1 else -1) * ((q.num.toNat : ℝ) / ((q.den * m).toNat : ℝ)) : ℝ)
        * 2 ^ ((AzNat.ofNat m.size).toAzInt - e).toInt := by
  have hm'' : m.toNat ≠ 0 := fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hm' : (m.toNat : ℝ) ≠ 0 := by exact_mod_cast hm''
  have hden : (q.den.toNat : ℝ) ≠ 0 := by exact_mod_cast (AzRat.den_toNat_pos q).ne'
  have hpow : (2 : ℝ) ^ ((AzNat.ofNat m.size).toAzInt - e).toInt
      = (2 ^ (e.toInt - m.size))⁻¹ := by
    rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, ← zpow_neg]
    congr 1
    ring
  have h2 : (2 : ℝ) ^ (e.toInt - m.size) ≠ 0 := (zpow_pos (by norm_num) _).ne'
  rw [hpow, AzNat.toNat_mul, coe_toRat_eq]
  unfold finiteVal
  cases s <;> cases q.sign <;> simp <;> field_simp

/-- Division by a rational is the lift of `EReal` division by its value. -/
theorem divRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    divRatPrecRound x q p mode
      = liftVal (fun a => Spec.div a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  cases x with
  | nan => rfl
  | infinity s =>
    unfold liftVal
    rw [toVal_infinity, Option.bind_some]
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      rw [hq0, EReal.coe_zero, Spec.div_inf_zero, roundVal_inf]
      simp [divRatPrecRound, hq]
    · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
      rw [Spec.div_inf_coe s _ hq0, roundVal_inf]
      simp [divRatPrecRound, hq, sign_eq_decide_pos q hq]
  | zero =>
    unfold liftVal
    rw [toVal_zero, Option.bind_some]
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      simp [divRatPrecRound, hq, hq0, Spec.div]
    · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
      rw [Spec.div_zero_coe _ hq0, roundVal_zero]
      simp [divRatPrecRound, hq]
  | finite s e p' m hv =>
    unfold liftVal
    rw [toVal_finite, Option.bind_some]
    have hm0 : m ≠ 0 := by
      intro hm; rw [hm] at hv; exact absurd hv.size_eq (by simp; exact
        (lt_of_lt_of_le hv.pos (le_alignedBits p')).ne)
    have hx0 := finiteVal_ne_zero s e hv
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      rw [hq0, EReal.coe_zero, Spec.div_coe_zero _ hx0]
      simp only [divRatPrecRound, hq, ↓reduceIte]
      by_cases hpos : 0 < finiteVal s e m
      · have hs : s = true := (finiteVal_pos_iff s e m hm0).mp hpos
        rw [ite_eq_left hpos, roundVal_top, hs]
      · have hs : s = false := by
          cases s
          · rfl
          · exact absurd ((finiteVal_pos_iff true e m hm0).mpr rfl) hpos
        rw [ite_eq_right hpos, roundVal_bot, hs]
    · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
      rw [Spec.div_coe_coe _ _ hq0]
      simp only [divRatPrecRound, hq, ↓reduceIte]
      rw [shift_ofFractionRound_eq _ _ _ (fun h => hq h), finiteVal_div_toRat s e m q hq]

/-- Division of a rational by a float is the lift of `EReal` division of its value. -/
theorem ratDivPrecRound_eq_liftVal (q : AzRat) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ratDivPrecRound q x p mode
      = liftVal (fun a => Spec.div ((AzRat.toRat q : ℝ) : EReal) a) x p mode := by
  cases x with
  | nan => rfl
  | infinity t =>
    show (zero, Ordering.eq) = _
    unfold liftVal
    rw [toVal_infinity, Option.bind_some, Spec.div_coe_inf, roundVal_zero]
  | zero =>
    unfold liftVal
    rw [toVal_zero, Option.bind_some]
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      simp [ratDivPrecRound, hq, hq0, Spec.div]
    · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
      rw [Spec.div_coe_zero _ hq0]
      simp only [ratDivPrecRound, hq, ↓reduceIte]
      by_cases hpos : 0 < (AzRat.toRat q : ℝ)
      · have hs : q.sign = true := by rw [sign_eq_decide_pos q hq]; exact decide_eq_true hpos
        rw [ite_eq_left hpos, roundVal_top, hs]
      · have hs : q.sign = false := by rw [sign_eq_decide_pos q hq]; exact decide_eq_false hpos
        rw [ite_eq_right hpos, roundVal_bot, hs]
  | finite s e p' m hv =>
    unfold liftVal
    rw [toVal_finite, Option.bind_some]
    have hm0 : m ≠ 0 := by
      intro hm; rw [hm] at hv; exact absurd hv.size_eq (by simp; exact
        (lt_of_lt_of_le hv.pos (le_alignedBits p')).ne)
    have hx0 := finiteVal_ne_zero s e hv
    rw [Spec.div_coe_coe _ _ hx0]
    show ((ofFractionRound _ _ _ p mode).1 <<< _, (ofFractionRound _ _ _ p mode).2) = _
    have hdm : q.den * m ≠ 0 := by
      intro h
      have := congrArg AzNat.toNat h
      rw [AzNat.toNat_mul, AzNat.toNat_zero] at this
      rcases Nat.mul_eq_zero.mp this with h1 | h1
      · exact (AzRat.den_toNat_pos q).ne' h1
      · exact hm0 (AzNat.toNat_injective (h1.trans AzNat.toNat_zero.symm))
    rw [shift_ofFractionRound_eq _ _ _ hdm, toRat_div_finiteVal s e m hm0 q]

end Azurite.AzFloat
