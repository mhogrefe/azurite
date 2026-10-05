/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzFloat.Equiv.Div
import Azurite.AzFloat.Equiv.Mul
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzFloat.MulRat
import Azurite.AzNat.Equiv.Mul.Dispatch

/-!
# Multiplication of an `AzFloat` by an `AzRat` is a lift

`mulRatPrecRound_eq_liftVal`: `mulRatPrecRound x q p mode = liftVal (fun a => Spec.mul a q) x
p mode`, where `q` stands for the value of the rational.  `shift_ofFractionRound_eq` is the
shared step of the product and the two quotients: rounding an unreduced fraction and shifting
the result is `roundVal` of the fraction times the power of two (`ofFractionRound_eq` and
`roundVal_mul_two_zpow`).  `sign_eq_decide_pos` settles the sign of an infinite result.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- The sign of a nonzero rational is the sign of its value. -/
theorem sign_eq_decide_pos (q : AzRat) (hq : q.num ≠ 0) :
    q.sign = decide (0 < (AzRat.toRat q : ℝ)) := by
  have hnum : (0 : ℝ) < q.num.toNat := by exact_mod_cast AzRat.num_toNat_pos q hq
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  rw [coe_toRat_eq]
  cases hs : q.sign
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
    rw [eq_comm, decide_eq_false_iff_not, not_lt]
    exact (div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden).le
  · simp only [↓reduceIte, Int.cast_natCast]
    rw [eq_comm, decide_eq_true_iff]
    exact div_pos hnum hden

/-- Rounding an unreduced fraction and shifting the result exactly is `roundVal` of the fraction
times the power of two. -/
theorem shift_ofFractionRound_eq (sg : Bool) (N D : AzNat) (hD : D ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (k : AzInt) :
    ((ofFractionRound sg N D p mode).1 <<< k, (ofFractionRound sg N D p mode).2)
      = roundVal p mode (some ((((if sg then 1 else -1) * ((N.toNat : ℝ) / (D.toNat : ℝ)) : ℝ)
          * 2 ^ k.toInt : ℝ) : EReal)) := by
  rw [roundVal_mul_two_zpow, ofFractionRound_eq sg N D hD p mode]

/-- The value of `x · q` as the shifted fraction `± (m · num / den) · 2^(e − |m|)`. -/
theorem finiteVal_mul_toRat (s : Bool) (e : AzInt) (m : AzNat) (q : AzRat) :
    finiteVal s e m * AzRat.toRat q
      = ((if (s == q.sign) then 1 else -1) * (((m * q.num).toNat : ℝ) / (q.den.toNat : ℝ)) : ℝ)
        * 2 ^ (e - (AzNat.ofNat m.size).toAzInt).toInt := by
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_mul, coe_toRat_eq]
  unfold finiteVal
  cases s <;> cases q.sign <;> simp <;> ring

/-- Multiplication by a rational is the lift of `EReal` multiplication with its value. -/
theorem mulRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulRatPrecRound x q p mode
      = liftVal (fun a => Spec.mul a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  cases x with
  | nan => rfl
  | infinity s =>
    unfold liftVal
    rw [toVal_infinity, Option.bind_some]
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      cases s <;> simp [mulRatPrecRound, hq, hq0, Spec.mul]
    · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
      rw [Spec.mul_inf_coe s _ hq0, roundVal_inf]
      simp [mulRatPrecRound, hq, sign_eq_decide_pos q hq]
  | zero =>
    show (zero, Ordering.eq) = _
    unfold liftVal
    rw [toVal_zero, Option.bind_some]
    have : Spec.mul (0 : EReal) ((AzRat.toRat q : ℝ) : EReal) = some 0 := by
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) by simp, Spec.mul_coe_coe, zero_mul]
    rw [this, roundVal_zero]
  | finite s e p' m hv =>
    unfold liftVal
    rw [toVal_finite, Option.bind_some, Spec.mul_coe_coe]
    show ((ofFractionRound _ _ _ p mode).1 <<< _, (ofFractionRound _ _ _ p mode).2) = _
    rw [shift_ofFractionRound_eq _ _ _ q.den_nz, finiteVal_mul_toRat]

end Azurite.AzFloat
