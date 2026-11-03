/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3Equal

/-!
# DLMF §3.3(ii): the three- and four-point formulas

The cases `n = 2` and `n = 3` of `Section3Equal`.

* `dlmf_3_3_13_Ioo`: 3.3.13 for `t`-sets inside `(n₀, n₁)`, with `ξ ∈ [x_{n₀}, x_{n₁}]`.
* Three-point formula: `dlmf_3_3_16` (3.3.7 for `n = 2`, as a sum and written out with the
  coefficients), `dlmf_3_3_17` (`A_k^2`), `dlmf_3_3_18` (`c₂ = 1/(9√3)` on `|t| < 1`, attained at
  `t = 1/√3`), `dlmf_3_3_18_decimal` (`0.0641…`), `dlmf_3_3_18_bound`.
* Four-point formula: `dlmf_3_3_19`, `dlmf_3_3_20` (`A_k^3`), `dlmf_3_3_21_inner`
  (`c₃ = 3/128` on `0 < t < 1`, attained at `t = ½`), `dlmf_3_3_21_outer` (`c₃ = 1/24` on
  `−1 < t < 0` or `1 < t < 2`, attained at `t = (1 ± √5)/2`), `dlmf_3_3_21_decimal`,
  `dlmf_3_3_21_bound_inner`, `dlmf_3_3_21_bound_outer`.

The formulas 3.3.16 and 3.3.19 hold for every real `t` (with the cancelled coefficients
`lagCoeff'`); DLMF's ranges of `t` matter only for the bounds. The maxima `c_n` reduce, with
`s = t² − t` for `n = 3`, to elementary polynomial inequalities.
-/

namespace Azurite.DLMF

open Finset

/-- 3.3.13 for `t`-sets inside `(n₀, n₁)`, where `ξ ∈ [x_{n₀}, x_{n₁}]`. -/
theorem dlmf_3_3_13_Ioo {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) U) {J : Set ℝ}
    (hJ : J ⊆ Set.Ioo (eqN0 n : ℝ) (eqN1 n)) {t : ℝ} (ht : t ∈ J)
    (hI : Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h) ⊆ U) :
    ∃ ξ ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h),
      |lagrangeRem (eqNode x₀ h n) f (x₀ + t * h)| ≤
        eqBoundCoeff n J * h ^ (n + 1) * |iteratedDeriv (n + 1) f ξ| := by
  have ht' := hJ ht
  have hmin : min (x₀ + t * h) (x₀ + eqN0 n * h) = x₀ + eqN0 n * h :=
    min_eq_right (by nlinarith [mul_lt_mul_of_pos_right ht'.1 hh])
  have hmax : max (x₀ + t * h) (x₀ + eqN1 n * h) = x₀ + eqN1 n * h :=
    max_eq_right (by nlinarith [mul_lt_mul_of_pos_right ht'.2 hh])
  have h13 := dlmf_3_3_13 hh n f hU hd ((Metric.isBounded_Ioo _ _).subset hJ) ht
    (by rw [hmin, hmax]; exact hI)
  rwa [hmin, hmax] at h13

/-! ### Three-point formula 3.3.16–3.3.18 -/

theorem eqN0_two : eqN0 2 = -1 := by rw [eqN0_eq]; norm_num

theorem eqN1_two : eqN1 2 = 1 := by rw [eqN1_eq, eqN0_two]; norm_num

theorem Icc_eqN_two : Icc (eqN0 2) (eqN1 2) = {-1, 0, 1} := by
  rw [eqN0_two, eqN1_two]; decide

/-- **DLMF 3.3.17**: `A_{−1}^2 = ½t(t − 1)`, `A_0^2 = 1 − t²`, `A_1^2 = ½t(t + 1)`. -/
theorem dlmf_3_3_17 (t : ℝ) :
    lagCoeff' 2 (-1) t = 1 / 2 * t * (t - 1) ∧ lagCoeff' 2 0 t = 1 - t ^ 2 ∧
      lagCoeff' 2 1 t = 1 / 2 * t * (t + 1) := by
  simp only [lagCoeff', eqN0_two, eqN1_two]
  rw [show (Icc (-1 : ℤ) 1).erase (-1) = {0, 1} by decide,
    show (Icc (-1 : ℤ) 1).erase 0 = {-1, 1} by decide,
    show (Icc (-1 : ℤ) 1).erase 1 = {-1, 0} by decide]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [prod_pair, Nat.factorial] <;> ring

/-- **DLMF 3.3.16** with 3.3.17: `f_t = ∑_{k=−1}^{1} A_k^2 f_k + R_{2,t}` (valid for every real
`t`; DLMF states `|t| < 1`). -/
theorem dlmf_3_3_16 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (-1 : ℤ) 1, lagCoeff' 2 k t * f (x₀ + k * h) +
        lagrangeRem (eqNode x₀ h 2) f (x₀ + t * h) ∧
      f (x₀ + t * h) = 1 / 2 * t * (t - 1) * f (x₀ - h) + (1 - t ^ 2) * f x₀ +
        1 / 2 * t * (t + 1) * f (x₀ + h) + lagrangeRem (eqNode x₀ h 2) f (x₀ + t * h) := by
  have h7 := dlmf_3_3_7' (x₀ := x₀) hh 2 f t
  rw [← eqN0_two, ← eqN1_two]
  refine ⟨h7, ?_⟩
  rw [h7, Icc_eqN_two, sum_insert (by decide), sum_pair (by decide)]
  obtain ⟨h1, h2, h3⟩ := dlmf_3_3_17 t
  rw [h1, h2, h3]
  push_cast
  ring_nf

theorem prod_abs_eqN_two (t : ℝ) :
    ∏ k ∈ Icc (eqN0 2) (eqN1 2), |t - k| = |t * (t ^ 2 - 1)| := by
  rw [Icc_eqN_two, prod_insert (by decide), prod_pair (by decide)]
  push_cast
  rw [← abs_mul, ← abs_mul]
  congr 1
  ring

/-- **DLMF 3.3.18**: `c₂ = 1/(9√3)` on `|t| < 1`. -/
theorem dlmf_3_3_18 : eqBoundCoeff 2 (Set.Ioo (-1) 1) = 1 / (9 * √3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hg : IsGreatest ((fun t : ℝ => ∏ k ∈ Icc (eqN0 2) (eqN1 2), |t - k|) '' Set.Ioo (-1) 1)
      (2 * √3 / 9) := by
    refine ⟨⟨√3 / 3, ⟨by nlinarith, by nlinarith⟩, ?_⟩, ?_⟩
    · simp only [prod_abs_eqN_two]
      rw [show √3 / 3 * ((√3 / 3) ^ 2 - 1) = -(2 * √3 / 9) by
        rw [div_pow, h3]; ring, abs_neg, abs_of_pos (by positivity)]
    · rintro _ ⟨t, ht, rfl⟩
      simp only [prod_abs_eqN_two]
      have hsq : (t * (t ^ 2 - 1)) ^ 2 ≤ (2 * √3 / 9) ^ 2 := by
        rw [div_pow, mul_pow, mul_pow, h3]
        nlinarith [sq_nonneg (t ^ 2 - 1 / 3), sq_nonneg t, ht.1, ht.2,
          mul_nonneg (sq_nonneg (t ^ 2 - 1 / 3))
            (by nlinarith [ht.1, ht.2] : (0 : ℝ) ≤ 4 / 3 - t ^ 2)]
      exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
  rw [eqBoundCoeff, hg.csSup_eq]
  field_simp
  rw [show (Nat.factorial (2 + 1) : ℝ) = 6 by norm_num [Nat.factorial]]
  nlinarith [h3]

/-- **DLMF 3.3.18**, the decimal: `c₂ = 0.0641…`. -/
theorem dlmf_3_3_18_decimal : 0.0641 ≤ 1 / (9 * √3) ∧ 1 / (9 * √3) < 0.0642 := by
  have h1 : (1.732 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- 3.3.13 with 3.3.18: `|R_{2,t}| ≤ h³ |f'''(ξ)|/(9√3)` for `|t| < 1`, `ξ ∈ [x₀ − h, x₀ + h]`. -/
theorem dlmf_3_3_18_bound {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ 2, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - h) (x₀ + h) ⊆ U) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ ξ ∈ Set.Icc (x₀ - h) (x₀ + h), |lagrangeRem (eqNode x₀ h 2) f (x₀ + t * h)| ≤
      1 / (9 * √3) * h ^ 3 * |iteratedDeriv 3 f ξ| := by
  have e0 : x₀ + (eqN0 2 : ℝ) * h = x₀ - h := by rw [eqN0_two]; push_cast; ring
  have e1 : x₀ + (eqN1 2 : ℝ) * h = x₀ + h := by rw [eqN1_two]; push_cast; ring
  have hJ : Set.Ioo (-1 : ℝ) 1 ⊆ Set.Ioo (eqN0 2 : ℝ) (eqN1 2) := by
    rw [eqN0_two, eqN1_two]; push_cast; exact subset_rfl
  have := dlmf_3_3_13_Ioo hh 2 f hU hd hJ ht (by rw [e0, e1]; exact hI)
  rwa [e0, e1, dlmf_3_3_18] at this

/-! ### Four-point formula 3.3.19–3.3.21 -/

theorem eqN0_three : eqN0 3 = -1 := by rw [eqN0_eq]; norm_num

theorem eqN1_three : eqN1 3 = 2 := by rw [eqN1_eq, eqN0_three]; norm_num

theorem Icc_eqN_three : Icc (eqN0 3) (eqN1 3) = {-1, 0, 1, 2} := by
  rw [eqN0_three, eqN1_three]; decide

/-- **DLMF 3.3.20**: `A_{−1}^3 = −⅙t(t − 1)(t − 2)`, `A_0^3 = ½(t² − 1)(t − 2)`,
`A_1^3 = −½t(t + 1)(t − 2)`, `A_2^3 = ⅙t(t² − 1)`. -/
theorem dlmf_3_3_20 (t : ℝ) :
    lagCoeff' 3 (-1) t = -(1 / 6) * t * (t - 1) * (t - 2) ∧
      lagCoeff' 3 0 t = 1 / 2 * (t ^ 2 - 1) * (t - 2) ∧
      lagCoeff' 3 1 t = -(1 / 2) * t * (t + 1) * (t - 2) ∧
      lagCoeff' 3 2 t = 1 / 6 * t * (t ^ 2 - 1) := by
  simp only [lagCoeff', eqN0_three, eqN1_three]
  rw [show (Icc (-1 : ℤ) 2).erase (-1) = {0, 1, 2} by decide,
    show (Icc (-1 : ℤ) 2).erase 0 = {-1, 1, 2} by decide,
    show (Icc (-1 : ℤ) 2).erase 1 = {-1, 0, 2} by decide,
    show (Icc (-1 : ℤ) 2).erase 2 = {-1, 0, 1} by decide]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [prod_insert, prod_pair, Nat.factorial] <;> ring

/-- **DLMF 3.3.19** with 3.3.20: `f_t = ∑_{k=−1}^{2} A_k^3 f_k + R_{3,t}` (valid for every real
`t`; DLMF states `−1 < t < 2`). -/
theorem dlmf_3_3_19 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (-1 : ℤ) 2, lagCoeff' 3 k t * f (x₀ + k * h) +
        lagrangeRem (eqNode x₀ h 3) f (x₀ + t * h) ∧
      f (x₀ + t * h) = -(1 / 6) * t * (t - 1) * (t - 2) * f (x₀ - h) +
        1 / 2 * (t ^ 2 - 1) * (t - 2) * f x₀ + -(1 / 2) * t * (t + 1) * (t - 2) * f (x₀ + h) +
        1 / 6 * t * (t ^ 2 - 1) * f (x₀ + 2 * h) +
        lagrangeRem (eqNode x₀ h 3) f (x₀ + t * h) := by
  have h7 := dlmf_3_3_7' (x₀ := x₀) hh 3 f t
  rw [← eqN0_three, ← eqN1_three]
  refine ⟨h7, ?_⟩
  rw [h7, Icc_eqN_three, sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
  obtain ⟨h1, h2, h3, h4⟩ := dlmf_3_3_20 t
  rw [h1, h2, h3, h4]
  push_cast
  ring_nf

theorem prod_abs_eqN_three (t : ℝ) :
    ∏ k ∈ Icc (eqN0 3) (eqN1 3), |t - k| = |(t ^ 2 - t) * (t ^ 2 - t - 2)| := by
  rw [Icc_eqN_three, prod_insert (by decide), prod_insert (by decide), prod_pair (by decide)]
  push_cast
  rw [← abs_mul, ← abs_mul, ← abs_mul]
  congr 1
  ring

/-- **DLMF 3.3.21**, first case: `c₃ = 3/128` on `0 < t < 1`. -/
theorem dlmf_3_3_21_inner : eqBoundCoeff 3 (Set.Ioo 0 1) = 3 / 128 := by
  have hg : IsGreatest ((fun t : ℝ => ∏ k ∈ Icc (eqN0 3) (eqN1 3), |t - k|) '' Set.Ioo 0 1)
      (9 / 16) := by
    refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
    · simp only [prod_abs_eqN_three]; norm_num [abs_of_pos]
    · rintro _ ⟨t, ht, rfl⟩
      simp only [prod_abs_eqN_three]
      have hs0 : t ^ 2 - t ≤ 0 := by nlinarith [ht.1, ht.2]
      have hs1 : -(1 / 4) ≤ t ^ 2 - t := by nlinarith [sq_nonneg (t - 1 / 2)]
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
  rw [eqBoundCoeff, hg.csSup_eq]
  norm_num [Nat.factorial]

/-- **DLMF 3.3.21**, second case: `c₃ = 1/24` on `−1 < t < 0` or `1 < t < 2`. -/
theorem dlmf_3_3_21_outer :
    eqBoundCoeff 3 (Set.Ioo (-1) 0 ∪ Set.Ioo 1 2) = 1 / 24 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5a : 1 < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h5b : √5 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hg : IsGreatest ((fun t : ℝ => ∏ k ∈ Icc (eqN0 3) (eqN1 3), |t - k|) ''
      (Set.Ioo (-1) 0 ∪ Set.Ioo 1 2)) 1 := by
    refine ⟨⟨(1 - √5) / 2, Or.inl ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
    · simp only [prod_abs_eqN_three]
      rw [show ((1 - √5) / 2) ^ 2 - (1 - √5) / 2 = 1 by nlinarith]
      norm_num
    · rintro _ ⟨t, ht, rfl⟩
      simp only [prod_abs_eqN_three]
      have hs : 0 < t ^ 2 - t ∧ t ^ 2 - t < 2 := by
        rcases ht with ht | ht <;> constructor <;> nlinarith [ht.1, ht.2]
      rw [abs_of_nonpos (by nlinarith)]
      nlinarith [sq_nonneg (t ^ 2 - t - 1)]
  rw [eqBoundCoeff, hg.csSup_eq]
  norm_num [Nat.factorial]

/-- **DLMF 3.3.21**, the decimals: `3/128 = 0.0234…`, `1/24 = 0.0416…`. -/
theorem dlmf_3_3_21_decimal :
    (0.0234 ≤ (3 / 128 : ℝ) ∧ (3 / 128 : ℝ) < 0.0235) ∧
      (0.0416 ≤ (1 / 24 : ℝ) ∧ (1 / 24 : ℝ) < 0.0417) := by
  norm_num

/-- 3.3.13 with 3.3.21: `|R_{3,t}| ≤ (3/128) h⁴ |f⁗(ξ)|` for `0 < t < 1`,
`ξ ∈ [x₀ − h, x₀ + 2h]`. -/
theorem dlmf_3_3_21_bound_inner {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 3, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - h) (x₀ + 2 * h) ⊆ U) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.Icc (x₀ - h) (x₀ + 2 * h), |lagrangeRem (eqNode x₀ h 3) f (x₀ + t * h)| ≤
      3 / 128 * h ^ 4 * |iteratedDeriv 4 f ξ| := by
  have e0 : x₀ + (eqN0 3 : ℝ) * h = x₀ - h := by rw [eqN0_three]; push_cast; ring
  have e1 : x₀ + (eqN1 3 : ℝ) * h = x₀ + 2 * h := by rw [eqN1_three]; push_cast; ring
  have hJ : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioo (eqN0 3 : ℝ) (eqN1 3) := by
    rw [eqN0_three, eqN1_three]; push_cast
    exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
  have := dlmf_3_3_13_Ioo hh 3 f hU hd hJ ht (by rw [e0, e1]; exact hI)
  rwa [e0, e1, dlmf_3_3_21_inner] at this

/-- 3.3.13 with 3.3.21: `|R_{3,t}| ≤ h⁴ |f⁗(ξ)|/24` for `−1 < t < 0` or `1 < t < 2`,
`ξ ∈ [x₀ − h, x₀ + 2h]`. -/
theorem dlmf_3_3_21_bound_outer {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 3, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - h) (x₀ + 2 * h) ⊆ U) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 1 2) :
    ∃ ξ ∈ Set.Icc (x₀ - h) (x₀ + 2 * h), |lagrangeRem (eqNode x₀ h 3) f (x₀ + t * h)| ≤
      1 / 24 * h ^ 4 * |iteratedDeriv 4 f ξ| := by
  have e0 : x₀ + (eqN0 3 : ℝ) * h = x₀ - h := by rw [eqN0_three]; push_cast; ring
  have e1 : x₀ + (eqN1 3 : ℝ) * h = x₀ + 2 * h := by rw [eqN1_three]; push_cast; ring
  have hJ : Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 1 2 ⊆ Set.Ioo (eqN0 3 : ℝ) (eqN1 3) := by
    rw [eqN0_three, eqN1_three]; push_cast
    exact Set.union_subset (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
      (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
  have := dlmf_3_3_13_Ioo hh 3 f hU hd hJ ht (by rw [e0, e1]; exact hI)
  rwa [e0, e1, dlmf_3_3_21_outer] at this

end Azurite.DLMF
