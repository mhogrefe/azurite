/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.Cos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Dottie number

The Dottie number `d = 0.739085…` is the unique real solution of `cos x = x`.

* `dottieNumber`, `cos_dottie`, `dottie_nonneg`, `dottie_le_one`, `eq_dottie_of_cos_eq`
  (uniqueness).
* `abs_sub_dottie_le`: `|x − d| ≤ |x − cos x|` for `x ∈ [0, 1]` (the residual bounds the error:
  `cos` decreases on `[0, 1]`, so `x − d` and `d − cos x` have the same sign).
* `abs_cos_sub_dottie_le`: `|cos x − d| ≤ (9/10) |x − d|` for `x ∈ [0, 1]` (the iteration
  `x ↦ cos x` contracts: `cos x − cos d = −2 sin ((x+d)/2) sin ((x−d)/2)` and `sin 1 ≤ 9/10`).
* `irrational_dottie`: a rational `d ≠ 0` would make `cos d = d` rational, against
  `irrational_cos_rat`.

For `AzFloat/Dottie.lean`.
-/

namespace Azurite

open Real

theorem exists_cos_eq_self : ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ Real.cos x = x := by
  have hcont : ContinuousOn (fun x : ℝ => Real.cos x - x) (Set.Icc 0 1) :=
    (Real.continuous_cos.sub continuous_id).continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc (Real.cos 1 - 1) (Real.cos 0 - 0) := by
    rw [Real.cos_zero]
    exact ⟨by linarith [Real.cos_le_one 1], by norm_num⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (zero_le_one) hcont h0
  exact ⟨x, hx, by simpa [sub_eq_zero] using hfx⟩

/-- The Dottie number: the solution of `cos x = x`. -/
noncomputable def dottieNumber : ℝ := exists_cos_eq_self.choose

theorem cos_dottie : Real.cos dottieNumber = dottieNumber := exists_cos_eq_self.choose_spec.2

theorem dottie_nonneg : 0 ≤ dottieNumber := exists_cos_eq_self.choose_spec.1.1

theorem dottie_le_one : dottieNumber ≤ 1 := exists_cos_eq_self.choose_spec.1.2

theorem dottie_ne_zero : dottieNumber ≠ 0 := by
  intro h
  have := cos_dottie
  rw [h, Real.cos_zero] at this
  norm_num at this

/-- The residual bounds the error on `[0, 1]`: `|x − d| ≤ |x − cos x|`. -/
theorem abs_sub_dottie_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    |x - dottieNumber| ≤ |x - Real.cos x| := by
  have hpi := Real.pi_gt_three
  rcases le_total dottieNumber x with h | h
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi dottie_nonneg (by linarith) h
    rw [cos_dottie] at hc
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [dottie_le_one]) h
    rw [cos_dottie] at hc
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem sin_one_le : Real.sin 1 ≤ 9 / 10 := by
  have h := Real.sin_bound (x := 1) (by norm_num)
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

theorem abs_sin_le_abs_self (t : ℝ) : |Real.sin t| ≤ |t| := by
  have := Real.abs_sin_sub_sin_le t 0
  simpa using this

/-- The iteration `x ↦ cos x` contracts toward the Dottie number on `[0, 1]`. -/
theorem abs_cos_sub_dottie_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    |Real.cos x - dottieNumber| ≤ 9 / 10 * |x - dottieNumber| := by
  have hpi := Real.pi_gt_three
  have hd0 := dottie_nonneg
  have hd1 := dottie_le_one
  have hm0 : 0 ≤ (x + dottieNumber) / 2 := by linarith
  have hm1 : (x + dottieNumber) / 2 ≤ 1 := by linarith
  have hs0 : 0 ≤ Real.sin ((x + dottieNumber) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hm0 (by linarith)
  have hs1 : Real.sin ((x + dottieNumber) / 2) ≤ 9 / 10 :=
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hm1).trans sin_one_le
  have hs2 := abs_sin_le_abs_self ((x - dottieNumber) / 2)
  have habs : |(x - dottieNumber) / 2| = |x - dottieNumber| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs] at hs2
  nth_rewrite 1 [← cos_dottie]
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg hs0]
  nlinarith [abs_nonneg (Real.sin ((x - dottieNumber) / 2)), abs_nonneg (x - dottieNumber),
    mul_le_mul hs1 hs2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 9 / 10)]

/-- The Dottie number is the only solution of `cos x = x`. -/
theorem eq_dottie_of_cos_eq {x : ℝ} (h : Real.cos x = x) : x = dottieNumber := by
  have hx1 : x ≤ 1 := by rw [← h]; exact Real.cos_le_one x
  have hxm1 : -1 ≤ x := by rw [← h]; exact Real.neg_one_le_cos x
  have hx0 : 0 ≤ x := by
    rw [← h]
    have hpi := Real.pi_gt_three
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have := abs_sub_dottie_le hx0 hx1
  rw [h, sub_self, abs_zero] at this
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))

/-- **The Dottie number is irrational.** -/
theorem irrational_dottie : Irrational dottieNumber := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact dottie_ne_zero (by rw [← hq, Rat.cast_zero])
  have := irrational_cos_rat hq0
  rw [hq, cos_dottie, ← hq] at this
  exact this ⟨q, rfl⟩

end Azurite
