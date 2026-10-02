/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Compare
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzInt.Equiv.Compare
import Azurite.AzNat.Equiv.Compare

/-!
# Correctness of the comparison

`partialCompare_eq`: `partialCompare x y` is the comparison of the values, `none` exactly when
a `NaN` is involved.  The finite case is `compareMagnitude_eq`: comparing exponents first is
sound because `2^(e−1) ≤ |v| < 2^e`, and at equal exponents padding the shorter significand
with zero limbs puts both on the same scale.
-/

namespace Azurite.AzFloat

theorem compare_natCast (a b : ℕ) : compare (a : ℝ) (b : ℝ) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by exact_mod_cast h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by exact_mod_cast h)]

theorem compare_neg_neg (a b : ℝ) : compare (-a) (-b) = (compare a b).swap := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (neg_lt_neg h)]; rfl
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]; rfl
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (neg_lt_neg h)]; rfl

theorem finiteVal_false (e : AzInt) (m : AzNat) : finiteVal false e m = -finiteVal true e m :=
  finiteVal_not true e m

theorem finiteVal_true_pos (e : AzInt) {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    0 < finiteVal true e m := by
  have hm : m ≠ 0 := ne_zero_of_size_pos (by
    rw [hv.size_eq]; exact lt_of_lt_of_le hv.pos (le_alignedBits p))
  exact (finiteVal_pos_iff true e m hm).mpr rfl

/-- Positive values of different exponents compare as their exponents. -/
theorem finiteVal_lt_of_exponent_lt (e₁ : AzInt) {p₁ : ℕ} {m₁ : AzNat} (h₁ : FiniteValid p₁ m₁)
    (e₂ : AzInt) {p₂ : ℕ} {m₂ : AzNat} (h₂ : FiniteValid p₂ m₂) (h : e₁.toInt < e₂.toInt) :
    finiteVal true e₁ m₁ < finiteVal true e₂ m₂ := by
  have hb₁ := (abs_finiteVal_bounds true e₁ h₁).2
  have hb₂ := (abs_finiteVal_bounds true e₂ h₂).1
  rw [abs_of_pos (finiteVal_true_pos e₁ h₁)] at hb₁
  rw [abs_of_pos (finiteVal_true_pos e₂ h₂)] at hb₂
  calc finiteVal true e₁ m₁ < (2 : ℝ) ^ e₁.toInt := hb₁
    _ ≤ (2 : ℝ) ^ (e₂.toInt - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ ≤ finiteVal true e₂ m₂ := hb₂

/-- At a common exponent, the aligned significands compare as the values. -/
theorem compare_aligned (e : AzInt) (m₁ m₂ : AzNat) (hs : m₁.size ≤ m₂.size) :
    AzNat.compare (m₁.shiftLeft (m₂.size - m₁.size)) m₂
      = compare (finiteVal true e m₁) (finiteVal true e m₂) := by
  rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_shiftLeft, ← compare_natCast]
  unfold finiteVal
  simp only [↓reduceIte, one_mul]
  conv_rhs => rw [← compare_mul_right_pos _ _ ((2 : ℝ) ^ ((m₂.size : ℤ) - e.toInt))
    (zpow_pos (by norm_num) _)]
  congr 1
  · push_cast
    rw [mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_natCast]
    congr 2
    rw [Nat.cast_sub hs]
    ring
  · rw [mul_assoc, ← zpow_add₀ (by norm_num)]
    simp

/-- The mirror image of `compare_aligned`. -/
theorem compare_aligned' (e : AzInt) (m₁ m₂ : AzNat) (hs : m₂.size ≤ m₁.size) :
    AzNat.compare m₁ (m₂.shiftLeft (m₁.size - m₂.size))
      = compare (finiteVal true e m₁) (finiteVal true e m₂) := by
  rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_shiftLeft, ← compare_natCast]
  unfold finiteVal
  simp only [↓reduceIte, one_mul]
  conv_rhs => rw [← compare_mul_right_pos _ _ ((2 : ℝ) ^ ((m₁.size : ℤ) - e.toInt))
    (zpow_pos (by norm_num) _)]
  congr 1
  · rw [mul_assoc, ← zpow_add₀ (by norm_num)]
    simp
  · push_cast
    rw [mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_natCast]
    congr 2
    rw [Nat.cast_sub hs]
    ring

theorem compareMagnitude_eq (e₁ : AzInt) {p₁ : ℕ} {m₁ : AzNat} (h₁ : FiniteValid p₁ m₁)
    (e₂ : AzInt) {p₂ : ℕ} {m₂ : AzNat} (h₂ : FiniteValid p₂ m₂) :
    compareMagnitude e₁ m₁ e₂ m₂ = compare (finiteVal true e₁ m₁) (finiteVal true e₂ m₂) := by
  unfold compareMagnitude
  rw [AzInt.compare_eq_compare_toInt]
  rcases lt_trichotomy e₁.toInt e₂.toInt with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    exact (compare_lt_iff_lt.mpr (finiteVal_lt_of_exponent_lt e₁ h₁ e₂ h₂ h)).symm
  · rw [compare_eq_iff_eq.mpr h]
    have he : e₁ = e₂ := by rw [← AzInt.ofInt_toInt e₁, ← AzInt.ofInt_toInt e₂, h]
    subst he
    by_cases hs : m₁.size ≤ m₂.size
    · rw [ite_eq_left hs]
      exact compare_aligned e₁ m₁ m₂ hs
    · rw [ite_eq_right hs]
      exact compare_aligned' e₁ m₁ m₂ (le_of_not_ge hs)
  · rw [compare_gt_iff_gt.mpr h]
    exact (compare_gt_iff_gt.mpr (finiteVal_lt_of_exponent_lt e₂ h₂ e₁ h₁ h)).symm

/-- `partialCompare` compares the values; `none` exactly when a `NaN` is involved. -/
theorem partialCompare_eq (x y : AzFloat) :
    partialCompare x y = match x.toVal, y.toVal with
      | some a, some b => some (compare a b)
      | _, _ => none := by
  have hT : ∀ r : ℝ, compare (⊤ : EReal) (r : EReal) = .gt := fun r =>
    compare_gt_iff_gt.mpr (EReal.coe_lt_top r)
  have hB : ∀ r : ℝ, compare (⊥ : EReal) (r : EReal) = .lt := fun r =>
    compare_lt_iff_lt.mpr (EReal.bot_lt_coe r)
  have hT' : ∀ r : ℝ, compare (r : EReal) (⊤ : EReal) = .lt := fun r =>
    compare_lt_iff_lt.mpr (EReal.coe_lt_top r)
  have hB' : ∀ r : ℝ, compare (r : EReal) (⊥ : EReal) = .gt := fun r =>
    compare_gt_iff_gt.mpr (EReal.bot_lt_coe r)
  have h0 : ((0 : ℝ) : EReal) = 0 := EReal.coe_zero
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t =>
      cases s <;> cases t <;> simp only [partialCompare, compareSigns, toVal_infinity,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Option.some.injEq]
      · rw [compare_eq_iff_eq.mpr rfl]
      · rw [compare_lt_iff_lt.mpr bot_lt_top]
      · rw [compare_gt_iff_gt.mpr bot_lt_top]
      · rw [compare_eq_iff_eq.mpr rfl]
    | zero =>
      cases s <;> simp only [partialCompare, toVal_infinity, toVal_zero, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq]
      · rw [← h0, hB]
      · rw [← h0, hT]
    | finite t e q m hv =>
      cases s <;> simp only [partialCompare, toVal_infinity, toVal_finite, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq]
      · rw [hB]
      · rw [hT]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t =>
      cases t <;> simp only [partialCompare, toVal_infinity, toVal_zero, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq]
      · rw [← h0, hB']
      · rw [← h0, hT']
    | zero =>
      simp only [partialCompare, toVal_zero, Option.some.injEq]
      rw [compare_eq_iff_eq.mpr rfl]
    | finite t e q m hv =>
      have hpos := finiteVal_true_pos e hv
      simp only [partialCompare, toVal_zero, toVal_finite, Option.some.injEq]
      rw [← h0, compare_coe_coe]
      cases t
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [finiteVal_false]
        exact (compare_gt_iff_gt.mpr (by linarith)).symm
      · simp only [↓reduceIte]
        exact (compare_lt_iff_lt.mpr hpos).symm
  | finite s e₁ q₁ m₁ h₁ =>
    cases y with
    | nan => rfl
    | infinity t =>
      cases t <;> simp only [partialCompare, toVal_infinity, toVal_finite, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq]
      · rw [hB']
      · rw [hT']
    | zero =>
      have hpos := finiteVal_true_pos e₁ h₁
      simp only [partialCompare, toVal_zero, toVal_finite, Option.some.injEq]
      rw [← h0, compare_coe_coe]
      cases s
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [finiteVal_false]
        exact (compare_lt_iff_lt.mpr (by linarith)).symm
      · simp only [↓reduceIte]
        exact (compare_gt_iff_gt.mpr hpos).symm
    | finite t e₂ q₂ m₂ h₂ =>
      have hpos₁ := finiteVal_true_pos e₁ h₁
      have hpos₂ := finiteVal_true_pos e₂ h₂
      simp only [partialCompare, toVal_finite]
      rw [compare_coe_coe]
      by_cases hst : s = t
      · subst hst
        rw [ite_eq_left rfl]
        cases s
        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
          rw [finiteVal_false, finiteVal_false, compare_neg_neg,
            compareMagnitude_eq e₁ h₁ e₂ h₂]
        · simp only [↓reduceIte, Option.some.injEq]
          exact compareMagnitude_eq e₁ h₁ e₂ h₂
      · rw [ite_eq_right hst]
        cases s <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
          at hst ⊢
        · exact absurd trivial hst
        · rw [finiteVal_false]
          exact (compare_lt_iff_lt.mpr (by linarith)).symm
        · rw [finiteVal_false]
          exact (compare_gt_iff_gt.mpr (by linarith)).symm
        · exact absurd trivial hst

theorem partialCompare_eq_none_iff (x y : AzFloat) :
    partialCompare x y = none ↔ x.isNaN = true ∨ y.isNaN = true := by
  rw [partialCompare_eq]
  cases x <;> cases y <;> simp [isNaN]

/-- IEEE equality is equality of values on non-`NaN` operands. -/
theorem eqIEEE_iff (x y : AzFloat) :
    eqIEEE x y = true ↔ ∃ v, x.toVal = some v ∧ y.toVal = some v := by
  unfold eqIEEE
  rw [partialCompare_eq]
  cases hx : x.toVal with
  | none => simp
  | some a =>
    cases hy : y.toVal with
    | none => simp
    | some b =>
      simp only [beq_iff_eq, Option.some.injEq, compare_eq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨a, rfl, rfl⟩
      · rintro ⟨v, hv, hv'⟩
        rw [hv, hv']

end Azurite.AzFloat
