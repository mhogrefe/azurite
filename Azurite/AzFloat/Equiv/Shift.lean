/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Shift
import Azurite.AzFloat.Equiv.Rounding
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Sub

/-!
# Correctness of the shifts

`toVal_shiftLeft`: the value is multiplied by `2^k` (`EReal` takes care of `±∞ · 2^k = ±∞`);
`shiftLeft_eq_liftE`: at the float's own precision the shift is the exact lift of
`v ↦ v · 2^k`.  `shiftRight` is `shiftLeft` by `-k`.
-/

namespace Azurite.AzFloat

@[simp] theorem shiftLeft_nan (k : AzInt) : shiftLeft nan k = nan := rfl
@[simp] theorem shiftLeft_infinity (s : Bool) (k : AzInt) : shiftLeft (infinity s) k = infinity s :=
  rfl
@[simp] theorem shiftLeft_zero (k : AzInt) : shiftLeft zero k = zero := rfl
@[simp] theorem shiftLeft_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat)
    (h : FiniteValid p m) (k : AzInt) :
    shiftLeft (finite s e p m h) k = finite s (e + k) p m h := rfl

theorem precision?_shiftLeft (x : AzFloat) (k : AzInt) :
    (shiftLeft x k).precision? = x.precision? := by
  cases x <;> rfl

theorem finiteVal_add (s : Bool) (e k : AzInt) (m : AzNat) :
    finiteVal s (e + k) m = finiteVal s e m * (2 : ℝ) ^ k.toInt := by
  unfold finiteVal
  have h2 : (2 : ℝ) ^ (e.toInt + k.toInt - m.size) = 2 ^ (e.toInt - m.size) * 2 ^ k.toInt := by
    rw [← zpow_add₀ (by norm_num)]; congr 1; ring
  rw [AzInt.toInt_add, h2]
  ring

/-- Shifting multiplies the value by `2^k`. -/
theorem toVal_shiftLeft (x : AzFloat) (k : AzInt) :
    (shiftLeft x k).toVal = x.toVal.map fun v => v * (((2 : ℝ) ^ k.toInt : ℝ) : EReal) := by
  have hpos : (0 : EReal) < (((2 : ℝ) ^ k.toInt : ℝ) : EReal) :=
    EReal.coe_pos.mpr (zpow_pos (by norm_num) _)
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [shiftLeft_infinity, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.map_some, EReal.bot_mul_of_pos hpos]
    · simp only [shiftLeft_infinity, toVal_infinity, ↓reduceIte, Option.map_some,
        EReal.top_mul_of_pos hpos]
  | zero => simp
  | finite s e p m h =>
    simp only [shiftLeft_finite, toVal_finite, Option.map_some, finiteVal_add, EReal.coe_mul]

theorem toVal_shiftRight (x : AzFloat) (k : AzInt) :
    (shiftRight x k).toVal = x.toVal.map fun v => v * (((2 : ℝ) ^ (-k.toInt) : ℝ) : EReal) := by
  unfold shiftRight
  rw [toVal_shiftLeft, AzInt.toInt_neg]

/-- At its own precision, the shift is the exact lift of `v ↦ v · 2^k`. -/
theorem shiftLeft_eq_liftE (p : ℕ) [NeZero p] (mode : RoundingMode) (x : AzFloat) (k : AzInt)
    (hx : x.precision? = some p ∨ x.precision? = none) :
    liftE (fun v => v * (((2 : ℝ) ^ k.toInt : ℝ) : EReal)) x p mode = (shiftLeft x k, .eq) := by
  have hx' : (shiftLeft x k).precision? = some p ∨ (shiftLeft x k).precision? = none := by
    rwa [precision?_shiftLeft]
  have h : x.toVal.bind (fun v => some (v * (((2 : ℝ) ^ k.toInt : ℝ) : EReal)))
      = (shiftLeft x k).toVal := by
    rw [toVal_shiftLeft]
    cases x.toVal <;> rfl
  unfold liftE liftVal
  rw [h]
  cases hv : (shiftLeft x k).toVal with
  | none =>
    cases x <;> simp at hv
    rfl
  | some v => exact roundVal_of_toVal p mode _ v hx' hv

end Azurite.AzFloat
