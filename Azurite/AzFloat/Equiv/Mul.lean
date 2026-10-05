/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzFloat.Mul
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Square.Dispatch

/-!
# Correctness of multiplication and squaring

`Spec.mul` is `EReal` multiplication with `0 · ∞` undefined; `mulPrecRound_eq_liftVal₂` and
`sqrPrecRound_eq_liftE` say the operations are the lifted specifications.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real multiplication, undefined (`NaN`) for `0 · (±∞)`. -/
noncomputable def mul (a b : EReal) : Option EReal :=
  if (a = 0 ∧ (b = ⊤ ∨ b = ⊥)) ∨ (b = 0 ∧ (a = ⊤ ∨ a = ⊥)) then none else some (a * b)

theorem mul_coe_coe (x y : ℝ) : mul (x : EReal) (y : EReal) = some ((x * y : ℝ) : EReal) := by
  unfold mul
  rw [ite_eq_right (by simp), EReal.coe_mul]

theorem mul_inf_coe (s : Bool) (r : ℝ) (hr : r ≠ 0) :
    mul (if s then ⊤ else ⊥) (r : EReal) = some (if (s == decide (0 < r)) then ⊤ else ⊥) := by
  unfold mul
  rw [ite_eq_right (by cases s <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero, hr])]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [decide_eq_false (not_lt.mpr h.le)]
    cases s
    · simp [EReal.bot_mul_coe_of_neg h]
    · simp [EReal.top_mul_coe_of_neg h]
  · rw [decide_eq_true h]
    cases s
    · simp [EReal.bot_mul_coe_of_pos h]
    · simp [EReal.top_mul_coe_of_pos h]

theorem mul_coe_inf (r : ℝ) (hr : r ≠ 0) (t : Bool) :
    mul (r : EReal) (if t then ⊤ else ⊥) = some (if (decide (0 < r) == t) then ⊤ else ⊥) := by
  unfold mul
  rw [ite_eq_right (by cases t <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero, hr])]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [decide_eq_false (not_lt.mpr h.le)]
    cases t
    · simp [EReal.coe_mul_bot_of_neg h]
    · simp [EReal.coe_mul_top_of_neg h]
  · rw [decide_eq_true h]
    cases t
    · simp [EReal.coe_mul_bot_of_pos h]
    · simp [EReal.coe_mul_top_of_pos h]

end Spec

theorem signed_mul (s t : Bool) :
    (if s then (1 : ℝ) else -1) * (if t then 1 else -1) = if (s == t) then 1 else -1 := by
  cases s <;> cases t <;> simp

/-- The exact product of two cores on the combined scale. -/
theorem mul_cores_scaled (e₁ : AzInt) {p₁ : ℕ} {m₁ : AzNat} (h₁ : FiniteValid p₁ m₁) (e₂ : AzInt)
    {p₂ : ℕ} {m₂ : AzNat} (h₂ : FiniteValid p₂ m₂) :
    (((coreSignificand p₁ m₁ * coreSignificand p₂ m₂).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (e₁ - (AzNat.ofNat p₁).toAzInt + (e₂ - (AzNat.ofNat p₂).toAzInt)).toInt
      = finiteVal true e₁ (coreSignificand p₁ m₁) * finiteVal true e₂ (coreSignificand p₂ m₂) := by
  rw [AzInt.toInt_add, AzInt.toInt_sub, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt,
    AzNat.toNat_ofNat, AzNat.toNat_ofNat, AzNat.toNat_mul, finiteVal_true_eq, finiteVal_true_eq,
    size_coreSignificand h₁, size_coreSignificand h₂, zpow_add₀ (by norm_num)]
  push_cast
  ring

/-- Multiplication is the float lift of `EReal` multiplication (`0 · (±∞)` being `NaN`). -/
theorem mulPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    mulPrecRound x y p mode = liftVal₂ Spec.mul x y p mode := by
  unfold liftVal₂
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t =>
      cases s <;> cases t <;>
        simp [mulPrecRound, Spec.mul, EReal.top_ne_zero, EReal.bot_ne_zero]
    | zero => cases s <;> simp [mulPrecRound, Spec.mul]
    | finite t e q m hv =>
      simp only [mulPrecRound, toVal_infinity, toVal_finite, Option.bind_some]
      rw [Spec.mul_inf_coe s _ (by
          rw [finiteVal_eq_core t e hv]
          exact finiteVal_ne_zero' t e _ (coreSignificand_ne_zero hv)),
        finiteVal_eq_core t e hv, decide_pos_finiteVal t e _ (coreSignificand_ne_zero hv),
        roundVal_inf]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t => cases t <;> simp [mulPrecRound, Spec.mul]
    | zero => simp [mulPrecRound, Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot]
    | finite t e q m hv => simp [mulPrecRound, Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot]
  | finite s e₁ p₁ m₁ h₁ =>
    cases y with
    | nan => rfl
    | infinity t =>
      simp only [mulPrecRound, toVal_infinity, toVal_finite, Option.bind_some]
      rw [Spec.mul_coe_inf _ (by
          rw [finiteVal_eq_core s e₁ h₁]
          exact finiteVal_ne_zero' s e₁ _ (coreSignificand_ne_zero h₁)) t,
        finiteVal_eq_core s e₁ h₁, decide_pos_finiteVal s e₁ _ (coreSignificand_ne_zero h₁),
        roundVal_inf]
    | zero => simp [mulPrecRound, Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot]
    | finite t e₂ p₂ m₂ h₂ =>
      simp only [mulPrecRound, toVal_finite, Option.bind_some, Spec.mul_coe_coe]
      rw [roundScaled_eq_roundVal, mul_assoc, mul_cores_scaled e₁ h₁ e₂ h₂,
        finiteVal_eq_core s e₁ h₁, finiteVal_eq_core t e₂ h₂, finiteVal_sign s e₁,
        finiteVal_sign t e₂, ← signed_mul, mul_mul_mul_comm]

/-- Squaring is the exact-value lift of `v ↦ v · v` (`EReal`'s `(±∞)² = ∞` needs no table). -/
theorem sqrPrecRound_eq_liftE (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrPrecRound x p mode = liftE (fun v => v * v) x p mode := by
  unfold liftE liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [sqrPrecRound]
  | zero => simp [sqrPrecRound]
  | finite s e q m hv =>
    simp only [sqrPrecRound, toVal_finite, Option.bind_some, ← EReal.coe_mul]
    have hS : (((AzNat.square (coreSignificand q m)).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (e - (AzNat.ofNat q).toAzInt + (e - (AzNat.ofNat q).toAzInt)).toInt
        = finiteVal s e m * finiteVal s e m := by
      rw [AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_square,
        finiteVal_eq_core s e hv, finiteVal_sign s e, finiteVal_true_eq, size_coreSignificand hv,
        zpow_add₀ (by norm_num)]
      push_cast
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
    rw [roundScaled_eq_roundVal, ite_eq_left rfl, one_mul, hS]

end Azurite.AzFloat
