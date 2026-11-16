/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscWithPeriodBracket
import Azurite.AzFloat.Equiv.AcscBracket
import Azurite.AzFloat.Equiv.AsinWithPeriodBracket

/-!
# Equivalence: the bracket of `arccsc (x) u / (2π)`

`irrational_acscPeriod_of_toVal` (`|x| > 1`, `|x| ≠ 2`), `acscPeriodApprox_spec` (width at
most `3U 2^(−w)`), `acscPeriod_eq_of_neg_iff`, `acscPeriodApprox_isSome_exists` (the Ziv
certificate).
-/

open Real

namespace Azurite.AzFloat

/-- `arccsc (x) U / (2π)` is irrational for a finite float `x` with `|x| > 1`, `|x| ≠ 2`. -/
theorem irrational_acscPeriod_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) (hx2 : |xv| ≠ 2) {U : ℕ} (hU : U ≠ 0) :
    Irrational (arcsin xv⁻¹ * U / (2 * π)) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hx0 : xv ≠ 0 := fun h => by
    rw [h, abs_zero] at hx1
    linarith
  have hinv : |xv⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hx1
  have hcast : xv⁻¹ = ((q⁻¹ : ℚ) : ℝ) := by rw [hq, Rat.cast_inv]
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  have hne : ∀ c : ℝ, |c| = 1 ∨ |c| = 1 / 2 → ((q⁻¹ : ℚ) : ℝ) ≠ c := by
    intro c hc h
    have h' : |xv⁻¹| = |c| := by rw [hcast, h]
    rcases hc with hc | hc
    · rw [hc] at h'
      linarith
    · rw [hc, abs_inv] at h'
      apply hx2
      have hpos : 0 < |xv| := by linarith
      field_simp at h'
      linarith
  rw [hcast]
  refine irrational_arcsin_rat_mul_div_two_pi (inv_ne_zero hq0) (hne 1 ?_) (hne (-1) ?_)
    (hne (1 / 2) ?_) (hne (-(1 / 2)) ?_) ?_ hU
  · left; norm_num
  · left; norm_num
  · right; norm_num
  · right
    rw [abs_neg]
    norm_num
  · rw [← hcast]
    exact hinv.le

/-- `acscPeriodApprox neg` as a pair of `Roundable`s bracketing `± arcsin (1/|x|) u / (2π)`. -/
theorem acscPeriodApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|) {en : ℕ}
    (hen : (2 : ℝ) ^ en ≤ 2 * |xv|) (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acscPeriodApprox neg x en u w).1 lv ∧
      Rounds (acscPeriodApprox neg x en u w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * (arcsin |xv|⁻¹ * u.toNat / (2 * π)) ∧
      (if neg then -1 else 1) * (arcsin |xv|⁻¹ * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (3 * (1 / 2 : ℝ) ^ w) := by
  have hθ : arcsin |xv|⁻¹ ≤ 2 := by
    have := arcsin_le_pi_div_two |xv|⁻¹
    linarith [pi_lt_four]
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    asinPeriodScale_spec (acscBracket_spec hx hx1 hen w) hθ u
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arccsc (x) U / (2π) = ± arcsin (1/|x|) U / (2π)` with the sign bit of `x`. -/
theorem acscPeriod_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) (U : ℝ) :
    arcsin xv⁻¹ * U / (2 * π) = (if neg then -1 else 1) * (arcsin |xv|⁻¹ * U / (2 * π)) := by
  rw [acsc_abs_eq hneg]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The Ziv certificate for `arccsc (x) u / (2π)`: `|x| > 1`, `|x| ≠ 2`, `u ≠ 0`. -/
theorem acscPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|)
    (hx2 : |xv| ≠ 2) (hneg : neg = true ↔ xv < 0) {en : ℕ} (hen : (2 : ℝ) ^ en ≤ 2 * |xv|)
    {u : AzNat} (hu : u.toNat ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acscPeriodApprox neg x en u (w₀ * 2 ^ f)).1
      (acscPeriodApprox neg x en u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (acscPeriodApprox neg x en u)
    (v := (if neg then -1 else 1) * (arcsin |xv|⁻¹ * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (3 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => acscPeriodApprox_spec neg hx hx1 hen u w) w₀ hw₀
  · rw [← acscPeriod_eq_of_neg_iff hneg]
    exact irrational_acscPeriod_of_toVal hx hx1 hx2 hu
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 3).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
