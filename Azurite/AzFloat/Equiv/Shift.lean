/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Shift
import Azurite.AzFloat.Equiv.Precision
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

/-! ### Rounding commutes with exact shifts -/

/-- `⌊log₂ |r · 2^k|⌋ = ⌊log₂ |r|⌋ + k`. -/
theorem log_abs_mul_two_zpow (r : ℝ) (hr : r ≠ 0) (k : ℤ) :
    Int.log 2 |r * 2 ^ k| = Int.log 2 |r| + k := by
  have h2k : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) _
  have habs : |r * 2 ^ k| = |r| * 2 ^ k := by rw [abs_mul, abs_of_pos h2k]
  have hpos : 0 < |r| := abs_pos.mpr hr
  have hpos' : 0 < |r * 2 ^ k| := by rw [habs]; positivity
  apply le_antisymm
  · apply Int.lt_add_one_iff.mp
    apply (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos').mp
    push_cast
    rw [habs, show Int.log 2 |r| + k + 1 = (Int.log 2 |r| + 1) + k by ring,
      zpow_add₀ (by norm_num)]
    exact mul_lt_mul_of_pos_right (Int.lt_zpow_succ_log_self (by norm_num) |r|) h2k
  · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos').mp
    push_cast
    rw [habs, zpow_add₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_right (Int.zpow_log_le_self (by norm_num) hpos) h2k.le

/-- Rounding commutes with scaling by a power of two. -/
theorem val_round_mul_two_zpow (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ) (k : ℤ) :
    (RoundingTarget.round (floatSet p) mode (r * 2 ^ k)).val
      = (RoundingTarget.round (floatSet p) mode r).val * (((2 : ℝ) ^ k : ℝ) : EReal) := by
  rw [val_round_floatSet, val_round_floatSet]
  have h2k : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) _
  rcases eq_or_ne r 0 with rfl | hr
  · rw [zero_mul, RoundingTarget.val_round_of_mem _ mode (Or.inl (by simp))]
    simp
  · rw [RoundingTarget.val_round_precisionSet mode _ (mul_ne_zero hr h2k.ne'),
      RoundingTarget.val_round_precisionSet mode r hr]
    have hu : RoundingTarget.precScale 2 p (r * 2 ^ k)
        = RoundingTarget.precScale 2 p r * 2 ^ k := by
      unfold RoundingTarget.precScale
      rw [log_abs_mul_two_zpow r hr k]
      push_cast
      rw [show Int.log 2 |r| + k - p + 1 = (Int.log 2 |r| - p + 1) + k by ring,
        zpow_add₀ (by norm_num)]
    rw [hu, mul_div_mul_right _ _ h2k.ne', ← EReal.coe_mul]
    congr 1
    ring

/-- `roundVal` commutes with an exact shift: rounding `r · 2^k` is rounding `r` shifted, with
the same comparison tag. -/
theorem roundVal_mul_two_zpow (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ) (k : AzInt) :
    roundVal p mode (some ((r * 2 ^ k.toInt : ℝ) : EReal))
      = ((roundVal p mode (some (r : EReal))).1 <<< k, (roundVal p mode (some (r : EReal))).2) := by
  obtain ⟨h1, h2⟩ := roundVal_coe p mode (r * 2 ^ k.toInt)
  obtain ⟨h1', h2'⟩ := roundVal_coe p mode r
  have h2k : (0 : ℝ) < 2 ^ k.toInt := zpow_pos (by norm_num) _
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ((R : ℝ) : EReal) = (RoundingTarget.round (floatSet p) mode r).val := by
    rw [val_round_floatSet]
    exact RoundingTarget.precisionSet_exists_real _
  refine Prod.ext ?_ ?_
  · apply toVal_injective p
    · rw [fst_roundVal]; exact (ofEReal_spec p mode _).1
    · show (shiftLeft _ k).precision? = some p ∨ (shiftLeft _ k).precision? = none
      rw [precision?_shiftLeft, fst_roundVal]
      exact (ofEReal_spec p mode _).1
    · show toVal _ = toVal (shiftLeft _ k)
      rw [toVal_shiftLeft, h1, h1', Option.map_some, val_round_mul_two_zpow]
  · show (roundVal p mode (some ((r * 2 ^ k.toInt : ℝ) : EReal))).2 = _
    rw [h2, h2', val_round_mul_two_zpow, ← hR, ← EReal.coe_mul, compare_coe_coe, compare_coe_coe,
      compare_mul_right_pos _ _ _ h2k]

end Azurite.AzFloat
