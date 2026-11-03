/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3Points

/-!
# DLMF §3.3(ii): the five- and six-point formulas

The cases `n = 4` and `n = 5` of `Section3Equal`.

* `eqBoundCoeff_bounds`: two-sided bounds `m/(n+1)! ≤ c_n ≤ M/(n+1)!` from a witness and a
  uniform bound; `eqRem_le_of_coeff_le`: 3.3.13 with any upper bound for `c_n`.
* Five-point formula: `dlmf_3_3_22` (sum and written-out forms, every real `t`), `dlmf_3_3_23`
  (`A_k^4`), `dlmf_3_3_24_inner` (`0.0118 ≤ c₄ < 0.0119` on `|t| < 1`), `dlmf_3_3_24_outer`
  (`0.0302 ≤ c₄ < 0.0303` on `1 < |t| < 2`), remainder bounds `dlmf_3_3_24_bound_inner`,
  `dlmf_3_3_24_bound_outer`.
* Six-point formula: `dlmf_3_3_25`, `dlmf_3_3_26` (`A_k^5`), `dlmf_3_3_27_inner` (exactly
  `c₅ = 5/1024 = 0.00488…` on `0 < t < 1`, maximum at `t = ½`), `dlmf_3_3_27_mid`
  (`0.00701 ≤ c₅ < 0.00702`), `dlmf_3_3_27_outer` (`0.0234 ≤ c₅ < 0.0235`), remainder bounds
  `dlmf_3_3_27_bound_inner`, `_mid`, `_outer`.

DLMF gives `c₄` and the last two `c₅` only as decimals; their maxima are irrational (critical
points of `t⁵ − 5t³ + 4t`, resp. of a cubic in `v = (t − ½)²`). The decimals are proved as
two-sided bounds: below by a rational witness `t₀`, above by a polynomial inequality whose
certificate is the division by `(x − r)²`, `r` a rational approximation of the maximizer, with a
nonnegative quotient and a positive linear remainder on the interval (`quintic_le_inner`,
`quintic_le_outer`, `cubic_le_mid`, `cubic_le_outer`). The product `∏|t − k|` is even in `t` for
`n = 4` (`abs_quintic_abs`) and a cubic in `(t − ½)²` for `n = 5` (`prod_abs_eqN_five`).
-/

namespace Azurite.DLMF

open Finset

/-! ### Two-sided bounds for `c_n` and the resulting remainder bounds -/

/-- Bounds `m/(n+1)! ≤ c_n ≤ M/(n+1)!` from a witness `t₀ ∈ J` and a bound on `J`. -/
theorem eqBoundCoeff_bounds {n : ℕ} {J : Set ℝ} {m M t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hm : m ≤ ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t₀ - k|)
    (hM : ∀ t ∈ J, ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k| ≤ M) :
    m / (n + 1).factorial ≤ eqBoundCoeff n J ∧ eqBoundCoeff n J ≤ M / (n + 1).factorial := by
  have hbdd : BddAbove ((fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k|) '' J) :=
    ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM t ht⟩
  have hf : (0 : ℝ) ≤ 1 / (n + 1).factorial := by positivity
  rw [eqBoundCoeff, div_eq_mul_one_div m, div_eq_mul_one_div M, mul_comm m, mul_comm M]
  exact ⟨mul_le_mul_of_nonneg_left (le_csSup_of_le hbdd (Set.mem_image_of_mem _ ht₀) hm) hf,
    mul_le_mul_of_nonneg_left (csSup_le (Set.image_nonempty.mpr ⟨t₀, ht₀⟩)
      (by rintro _ ⟨t, ht, rfl⟩; exact hM t ht)) hf⟩

/-- 3.3.13 with an upper bound `C ≥ c_n`, for `t`-sets inside `(n₀, n₁)`. -/
theorem eqRem_le_of_coeff_le {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) U) {J : Set ℝ}
    (hJ : J ⊆ Set.Ioo (eqN0 n : ℝ) (eqN1 n)) {C : ℝ} (hC : eqBoundCoeff n J ≤ C) {t : ℝ}
    (ht : t ∈ J) (hI : Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h) ⊆ U) :
    ∃ ξ ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h),
      |lagrangeRem (eqNode x₀ h n) f (x₀ + t * h)| ≤
        C * h ^ (n + 1) * |iteratedDeriv (n + 1) f ξ| := by
  obtain ⟨ξ, hξ, hR⟩ := dlmf_3_3_13_Ioo hh n f hU hd hJ ht hI
  exact ⟨ξ, hξ, hR.trans (by gcongr)⟩

/-! ### Five-point formula 3.3.22–3.3.24 -/

theorem eqN0_four : eqN0 4 = -2 := by rw [eqN0_eq]; norm_num

theorem eqN1_four : eqN1 4 = 2 := by rw [eqN1_eq, eqN0_four]; norm_num

theorem Icc_eqN_four : Icc (eqN0 4) (eqN1 4) = {-2, -1, 0, 1, 2} := by
  rw [eqN0_four, eqN1_four]; decide

/-- **DLMF 3.3.23**: the coefficients `A_k^4`, `k = −2, …, 2`. -/
theorem dlmf_3_3_23 (t : ℝ) :
    lagCoeff' 4 (-2) t = 1 / 24 * t * (t ^ 2 - 1) * (t - 2) ∧
      lagCoeff' 4 (-1) t = -(1 / 6) * t * (t - 1) * (t ^ 2 - 4) ∧
      lagCoeff' 4 0 t = 1 / 4 * (t ^ 2 - 1) * (t ^ 2 - 4) ∧
      lagCoeff' 4 1 t = -(1 / 6) * t * (t + 1) * (t ^ 2 - 4) ∧
      lagCoeff' 4 2 t = 1 / 24 * t * (t ^ 2 - 1) * (t + 2) := by
  simp only [lagCoeff', eqN0_four, eqN1_four]
  rw [show (Icc (-2 : ℤ) 2).erase (-2) = {-1, 0, 1, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase (-1) = {-2, 0, 1, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase 0 = {-2, -1, 1, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase 1 = {-2, -1, 0, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase 2 = {-2, -1, 0, 1} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [prod_insert, prod_pair, Nat.factorial] <;> ring

/-- **DLMF 3.3.22** with 3.3.23: `f_t = ∑_{k=−2}^{2} A_k^4 f_k + R_{4,t}` (valid for every real
`t`; DLMF states `|t| < 2`). -/
theorem dlmf_3_3_22 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (-2 : ℤ) 2, lagCoeff' 4 k t * f (x₀ + k * h) +
        lagrangeRem (eqNode x₀ h 4) f (x₀ + t * h) ∧
      f (x₀ + t * h) = 1 / 24 * t * (t ^ 2 - 1) * (t - 2) * f (x₀ - 2 * h) +
        -(1 / 6) * t * (t - 1) * (t ^ 2 - 4) * f (x₀ - h) +
        1 / 4 * (t ^ 2 - 1) * (t ^ 2 - 4) * f x₀ +
        -(1 / 6) * t * (t + 1) * (t ^ 2 - 4) * f (x₀ + h) +
        1 / 24 * t * (t ^ 2 - 1) * (t + 2) * f (x₀ + 2 * h) +
        lagrangeRem (eqNode x₀ h 4) f (x₀ + t * h) := by
  have h7 := dlmf_3_3_7' (x₀ := x₀) hh 4 f t
  rw [← eqN0_four, ← eqN1_four]
  refine ⟨h7, ?_⟩
  rw [h7, Icc_eqN_four, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_pair (by decide)]
  obtain ⟨h1, h2, h3, h4, h5⟩ := dlmf_3_3_23 t
  rw [h1, h2, h3, h4, h5]
  push_cast
  ring_nf

theorem prod_abs_eqN_four (t : ℝ) :
    ∏ k ∈ Icc (eqN0 4) (eqN1 4), |t - k| = |t ^ 5 - 5 * t ^ 3 + 4 * t| := by
  rw [Icc_eqN_four, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_pair (by decide)]
  push_cast
  rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
  congr 1
  ring

theorem abs_quintic_abs (t : ℝ) :
    |t ^ 5 - 5 * t ^ 3 + 4 * t| = |(|t| ^ 5 - 5 * |t| ^ 3 + 4 * |t|)| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, show (-t) ^ 5 - 5 * (-t) ^ 3 + 4 * -t = -(t ^ 5 - 5 * t ^ 3 + 4 * t)
      by ring, abs_neg]

/-- `|t(t² − 1)(t² − 4)| ≤ 1.427` on `[0, 1]` (certificate: the quotient by `(s − 0.544)²`). -/
theorem quintic_le_inner {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |s ^ 5 - 5 * s ^ 3 + 4 * s| ≤ 1.427 := by
  have hg : 0 ≤ s ^ 5 - 5 * s ^ 3 + 4 * s := by
    nlinarith [mul_nonneg (mul_nonneg h0 (by nlinarith : (0 : ℝ) ≤ 1 - s ^ 2))
      (by nlinarith : (0 : ℝ) ≤ 4 - s ^ 2)]
  rw [abs_of_nonneg hg]
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have hq : 0 ≤ -s ^ 3 - 136 / 125 * s ^ 2 + 64253 / 15625 * s + 9367272 / 1953125 := by
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg (s - 544 / 1000)) hq]

/-- `|t(t² − 1)(t² − 4)| ≤ 3.635` on `[1, 2]` (certificate: the quotient by `(s − 1.6444)²`). -/
theorem quintic_le_outer {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    |s ^ 5 - 5 * s ^ 3 + 4 * s| ≤ 3.635 := by
  have h0 : 0 ≤ s := by linarith
  have hg : s ^ 5 - 5 * s ^ 3 + 4 * s ≤ 0 := by
    nlinarith [mul_nonneg (mul_nonneg h0 (by nlinarith : (0 : ℝ) ≤ s ^ 2 - 1))
      (by nlinarith : (0 : ℝ) ≤ 4 - s ^ 2)]
  rw [abs_of_nonpos hg]
  have hq : 0 ≤ s ^ 3 + 4111 / 1250 * s ^ 2 + 19450963 / 6250000 * s +
      5242844631 / 3906250000 := by
    nlinarith [pow_nonneg h0 3, sq_nonneg s]
  nlinarith [mul_nonneg (sq_nonneg (s - 16444 / 10000)) hq]

/-- **DLMF 3.3.24**, first case: `c₄ = 0.0118…` on `|t| < 1`. -/
theorem dlmf_3_3_24_inner :
    0.0118 ≤ eqBoundCoeff 4 (Set.Ioo (-1) 1) ∧ eqBoundCoeff 4 (Set.Ioo (-1) 1) < 0.0119 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 4) (J := Set.Ioo (-1) 1) (m := 1.416) (M := 1.427)
    (t₀ := 0.544)
    (by norm_num) (by rw [prod_abs_eqN_four, abs_of_pos (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_four, abs_quintic_abs]
      exact quintic_le_inner (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩))
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

/-- **DLMF 3.3.24**, second case: `c₄ = 0.0302…` on `1 < |t| < 2`. -/
theorem dlmf_3_3_24_outer :
    0.0302 ≤ eqBoundCoeff 4 (Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2) ∧
      eqBoundCoeff 4 (Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2) < 0.0303 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 4) (J := Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2)
    (m := 3.624) (M := 3.635) (t₀ := 1.6444)
    (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_four, abs_of_neg (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_four, abs_quintic_abs]
      have : 1 ≤ |t| ∧ |t| ≤ 2 := by
        rcases ht with ht | ht
        · rw [abs_of_neg (by linarith [ht.2])]; constructor <;> linarith [ht.1, ht.2]
        · rw [abs_of_pos (by linarith [ht.1])]; constructor <;> linarith [ht.1, ht.2]
      exact quintic_le_outer this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

/-- 3.3.13 with 3.3.24: `|R_{4,t}| ≤ 0.0119 h⁵ |f⁽⁵⁾(ξ)|` for `|t| < 1`,
`ξ ∈ [x₀ − 2h, x₀ + 2h]`. -/
theorem dlmf_3_3_24_bound_inner {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 4, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 2 * h) (x₀ + 2 * h) ⊆ U) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ ξ ∈ Set.Icc (x₀ - 2 * h) (x₀ + 2 * h),
      |lagrangeRem (eqNode x₀ h 4) f (x₀ + t * h)| ≤ 0.0119 * h ^ 5 * |iteratedDeriv 5 f ξ| := by
  have e0 : x₀ + (eqN0 4 : ℝ) * h = x₀ - 2 * h := by rw [eqN0_four]; push_cast; ring
  have e1 : x₀ + (eqN1 4 : ℝ) * h = x₀ + 2 * h := by rw [eqN1_four]; push_cast; ring
  have hJ : Set.Ioo (-1 : ℝ) 1 ⊆ Set.Ioo (eqN0 4 : ℝ) (eqN1 4) := by
    rw [eqN0_four, eqN1_four]; push_cast
    exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
  have := eqRem_le_of_coeff_le hh 4 f hU hd hJ dlmf_3_3_24_inner.2.le ht
    (by rw [e0, e1]; exact hI)
  rwa [e0, e1] at this

/-- 3.3.13 with 3.3.24: `|R_{4,t}| ≤ 0.0303 h⁵ |f⁽⁵⁾(ξ)|` for `1 < |t| < 2`,
`ξ ∈ [x₀ − 2h, x₀ + 2h]`. -/
theorem dlmf_3_3_24_bound_outer {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 4, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 2 * h) (x₀ + 2 * h) ⊆ U) {t : ℝ}
    (ht : t ∈ Set.Ioo (-2 : ℝ) (-1) ∪ Set.Ioo 1 2) :
    ∃ ξ ∈ Set.Icc (x₀ - 2 * h) (x₀ + 2 * h),
      |lagrangeRem (eqNode x₀ h 4) f (x₀ + t * h)| ≤ 0.0303 * h ^ 5 * |iteratedDeriv 5 f ξ| := by
  have e0 : x₀ + (eqN0 4 : ℝ) * h = x₀ - 2 * h := by rw [eqN0_four]; push_cast; ring
  have e1 : x₀ + (eqN1 4 : ℝ) * h = x₀ + 2 * h := by rw [eqN1_four]; push_cast; ring
  have hJ : Set.Ioo (-2 : ℝ) (-1) ∪ Set.Ioo 1 2 ⊆ Set.Ioo (eqN0 4 : ℝ) (eqN1 4) := by
    rw [eqN0_four, eqN1_four]; push_cast
    exact Set.union_subset (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
      (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
  have := eqRem_le_of_coeff_le hh 4 f hU hd hJ dlmf_3_3_24_outer.2.le ht
    (by rw [e0, e1]; exact hI)
  rwa [e0, e1] at this

/-! ### Six-point formula 3.3.25–3.3.27 -/

theorem eqN0_five : eqN0 5 = -2 := by rw [eqN0_eq]; norm_num

theorem eqN1_five : eqN1 5 = 3 := by rw [eqN1_eq, eqN0_five]; norm_num

theorem Icc_eqN_five : Icc (eqN0 5) (eqN1 5) = {-2, -1, 0, 1, 2, 3} := by
  rw [eqN0_five, eqN1_five]; decide

/-- **DLMF 3.3.26**: the coefficients `A_k^5`, `k = −2, …, 3`. -/
theorem dlmf_3_3_26 (t : ℝ) :
    lagCoeff' 5 (-2) t = -(1 / 120) * t * (t ^ 2 - 1) * (t - 2) * (t - 3) ∧
      lagCoeff' 5 (-1) t = 1 / 24 * t * (t - 1) * (t ^ 2 - 4) * (t - 3) ∧
      lagCoeff' 5 0 t = -(1 / 12) * (t ^ 2 - 1) * (t ^ 2 - 4) * (t - 3) ∧
      lagCoeff' 5 1 t = 1 / 12 * t * (t + 1) * (t ^ 2 - 4) * (t - 3) ∧
      lagCoeff' 5 2 t = -(1 / 24) * t * (t ^ 2 - 1) * (t + 2) * (t - 3) ∧
      lagCoeff' 5 3 t = 1 / 120 * t * (t ^ 2 - 1) * (t ^ 2 - 4) := by
  simp only [lagCoeff', eqN0_five, eqN1_five]
  rw [show (Icc (-2 : ℤ) 3).erase (-2) = {-1, 0, 1, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase (-1) = {-2, 0, 1, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 0 = {-2, -1, 1, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 1 = {-2, -1, 0, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 2 = {-2, -1, 0, 1, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 3 = {-2, -1, 0, 1, 2} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [prod_insert, prod_pair, Nat.factorial] <;> ring

/-- **DLMF 3.3.25** with 3.3.26: `f_t = ∑_{k=−2}^{3} A_k^5 f_k + R_{5,t}` (valid for every real
`t`; DLMF states `−2 < t < 3`). -/
theorem dlmf_3_3_25 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (-2 : ℤ) 3, lagCoeff' 5 k t * f (x₀ + k * h) +
        lagrangeRem (eqNode x₀ h 5) f (x₀ + t * h) ∧
      f (x₀ + t * h) = -(1 / 120) * t * (t ^ 2 - 1) * (t - 2) * (t - 3) * f (x₀ - 2 * h) +
        1 / 24 * t * (t - 1) * (t ^ 2 - 4) * (t - 3) * f (x₀ - h) +
        -(1 / 12) * (t ^ 2 - 1) * (t ^ 2 - 4) * (t - 3) * f x₀ +
        1 / 12 * t * (t + 1) * (t ^ 2 - 4) * (t - 3) * f (x₀ + h) +
        -(1 / 24) * t * (t ^ 2 - 1) * (t + 2) * (t - 3) * f (x₀ + 2 * h) +
        1 / 120 * t * (t ^ 2 - 1) * (t ^ 2 - 4) * f (x₀ + 3 * h) +
        lagrangeRem (eqNode x₀ h 5) f (x₀ + t * h) := by
  have h7 := dlmf_3_3_7' (x₀ := x₀) hh 5 f t
  rw [← eqN0_five, ← eqN1_five]
  refine ⟨h7, ?_⟩
  rw [h7, Icc_eqN_five, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_pair (by decide)]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := dlmf_3_3_26 t
  rw [h1, h2, h3, h4, h5, h6]
  push_cast
  ring_nf

/-- With `v = (t − ½)²`, `∏_{k=−2}^{3} |t − k| = |(v − ¼)(v − 9/4)(v − 25/4)|`. -/
theorem prod_abs_eqN_five (t : ℝ) :
    ∏ k ∈ Icc (eqN0 5) (eqN1 5), |t - k| =
      |((t - 1 / 2) ^ 2 - 1 / 4) * ((t - 1 / 2) ^ 2 - 9 / 4) * ((t - 1 / 2) ^ 2 - 25 / 4)| := by
  rw [Icc_eqN_five, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_pair (by decide)]
  push_cast
  rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
  congr 1
  ring

/-- `|(v − ¼)(v − 9/4)(v − 25/4)| ≤ 225/64` on `[0, ¼]`. -/
theorem cubic_le_inner {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4)| ≤ 225 / 64 := by
  rw [show (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) = -((1 / 4 - v) * (9 / 4 - v) * (25 / 4 - v))
    by ring, abs_neg, abs_of_nonneg (by
      apply mul_nonneg (mul_nonneg _ _) _ <;> linarith)]
  calc (1 / 4 - v) * (9 / 4 - v) * (25 / 4 - v) ≤ 1 / 4 * (9 / 4) * (25 / 4) := by
        apply mul_le_mul (mul_le_mul _ _ _ _) _ _ _ <;> norm_num <;> linarith
    _ = 225 / 64 := by norm_num

/-- `|(v − ¼)(v − 9/4)(v − 25/4)| ≤ 5.053` on `[¼, 9/4]` (quotient by `(v − 1.1528)²`). -/
theorem cubic_le_mid {v : ℝ} (h0 : 1 / 4 ≤ v) (h1 : v ≤ 9 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4)| ≤ 5.053 := by
  have hg : 0 ≤ (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) := by
    rw [show (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) = (v - 1 / 4) * ((9 / 4 - v) * (25 / 4 - v))
      by ring]
    apply mul_nonneg _ (mul_nonneg _ _) <;> linarith
  rw [abs_of_nonneg hg]
  nlinarith [mul_nonneg (sq_nonneg (v - 11528 / 10000)) (by linarith : (0 : ℝ) ≤ 16111 / 2500 - v)]

/-- `|(v − ¼)(v − 9/4)(v − 25/4)| ≤ 16.91` on `[9/4, 25/4]` (quotient by `(v − 4.6805)²`). -/
theorem cubic_le_outer {v : ℝ} (h0 : 9 / 4 ≤ v) (h1 : v ≤ 25 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4)| ≤ 16.91 := by
  have hg : (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) ≤ 0 := by
    rw [show (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) =
      -((v - 1 / 4) * (v - 9 / 4) * (25 / 4 - v)) by ring, neg_nonpos]
    apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
  rw [abs_of_nonpos hg]
  nlinarith [mul_nonneg (sq_nonneg (v - 46805 / 10000)) (by linarith : (0 : ℝ) ≤ v + 611 / 1000)]

/-- **DLMF 3.3.27**, first case: `c₅ = 5/1024 = 0.00488…` on `0 < t < 1` (the maximum is at
`t = ½`). -/
theorem dlmf_3_3_27_inner : eqBoundCoeff 5 (Set.Ioo 0 1) = 5 / 1024 := by
  have hg : IsGreatest ((fun t : ℝ => ∏ k ∈ Icc (eqN0 5) (eqN1 5), |t - k|) '' Set.Ioo 0 1)
      (225 / 64) := by
    refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
    · simp only [prod_abs_eqN_five]; norm_num [abs_of_neg]
    · rintro _ ⟨t, ht, rfl⟩
      simp only [prod_abs_eqN_five]
      exact cubic_le_inner (sq_nonneg _) (by nlinarith [ht.1, ht.2])
  rw [eqBoundCoeff, hg.csSup_eq]
  norm_num [Nat.factorial]

theorem dlmf_3_3_27_inner_decimal : 0.00488 ≤ (5 / 1024 : ℝ) ∧ (5 / 1024 : ℝ) < 0.00489 := by
  norm_num

/-- **DLMF 3.3.27**, second case: `c₅ = 0.00701…` on `−1 < t < 0` or `1 < t < 2`. -/
theorem dlmf_3_3_27_mid :
    0.00701 ≤ eqBoundCoeff 5 (Set.Ioo (-1) 0 ∪ Set.Ioo 1 2) ∧
      eqBoundCoeff 5 (Set.Ioo (-1) 0 ∪ Set.Ioo 1 2) < 0.00702 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 5) (J := Set.Ioo (-1) 0 ∪ Set.Ioo 1 2)
    (m := 5.0472) (M := 5.053) (t₀ := 1.5737)
    (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_five, abs_of_pos (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_five]
      have : 1 / 4 ≤ (t - 1 / 2) ^ 2 ∧ (t - 1 / 2) ^ 2 ≤ 9 / 4 := by
        rcases ht with ht | ht <;> constructor <;> nlinarith [ht.1, ht.2]
      exact cubic_le_mid this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

/-- **DLMF 3.3.27**, third case: `c₅ = 0.0234…` on `−2 < t < −1` or `2 < t < 3`. -/
theorem dlmf_3_3_27_outer :
    0.0234 ≤ eqBoundCoeff 5 (Set.Ioo (-2) (-1) ∪ Set.Ioo 2 3) ∧
      eqBoundCoeff 5 (Set.Ioo (-2) (-1) ∪ Set.Ioo 2 3) < 0.0235 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 5) (J := Set.Ioo (-2) (-1) ∪ Set.Ioo 2 3)
    (m := 16.848) (M := 16.91) (t₀ := 2.6634)
    (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_five, abs_of_neg (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_five]
      have : 9 / 4 ≤ (t - 1 / 2) ^ 2 ∧ (t - 1 / 2) ^ 2 ≤ 25 / 4 := by
        rcases ht with ht | ht <;> constructor <;> nlinarith [ht.1, ht.2]
      exact cubic_le_outer this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

theorem eqNode_five_ends (x₀ h : ℝ) :
    x₀ + (eqN0 5 : ℝ) * h = x₀ - 2 * h ∧ x₀ + (eqN1 5 : ℝ) * h = x₀ + 3 * h := by
  rw [eqN0_five, eqN1_five]; push_cast; constructor <;> ring

/-- 3.3.13 with 3.3.27: `|R_{5,t}| ≤ (5/1024) h⁶ |f⁽⁶⁾(ξ)|` for `0 < t < 1`,
`ξ ∈ [x₀ − 2h, x₀ + 3h]`. -/
theorem dlmf_3_3_27_bound_inner {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 5, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 2 * h) (x₀ + 3 * h) ⊆ U) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.Icc (x₀ - 2 * h) (x₀ + 3 * h), |lagrangeRem (eqNode x₀ h 5) f (x₀ + t * h)| ≤
      5 / 1024 * h ^ 6 * |iteratedDeriv 6 f ξ| := by
  obtain ⟨e0, e1⟩ := eqNode_five_ends x₀ h
  have hJ : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioo (eqN0 5 : ℝ) (eqN1 5) := by
    rw [eqN0_five, eqN1_five]; push_cast
    exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
  have := eqRem_le_of_coeff_le hh 5 f hU hd hJ dlmf_3_3_27_inner.le ht
    (by rw [e0, e1]; exact hI)
  rwa [e0, e1] at this

/-- 3.3.13 with 3.3.27: `|R_{5,t}| ≤ 0.00702 h⁶ |f⁽⁶⁾(ξ)|` for `−1 < t < 0` or `1 < t < 2`. -/
theorem dlmf_3_3_27_bound_mid {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 5, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 2 * h) (x₀ + 3 * h) ⊆ U) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 1 2) :
    ∃ ξ ∈ Set.Icc (x₀ - 2 * h) (x₀ + 3 * h), |lagrangeRem (eqNode x₀ h 5) f (x₀ + t * h)| ≤
      0.00702 * h ^ 6 * |iteratedDeriv 6 f ξ| := by
  obtain ⟨e0, e1⟩ := eqNode_five_ends x₀ h
  have hJ : Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 1 2 ⊆ Set.Ioo (eqN0 5 : ℝ) (eqN1 5) := by
    rw [eqN0_five, eqN1_five]; push_cast
    exact Set.union_subset (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
      (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
  have := eqRem_le_of_coeff_le hh 5 f hU hd hJ dlmf_3_3_27_mid.2.le ht
    (by rw [e0, e1]; exact hI)
  rwa [e0, e1] at this

/-- 3.3.13 with 3.3.27: `|R_{5,t}| ≤ 0.0235 h⁶ |f⁽⁶⁾(ξ)|` for `−2 < t < −1` or `2 < t < 3`. -/
theorem dlmf_3_3_27_bound_outer {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hd : ∀ k ≤ 5, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 2 * h) (x₀ + 3 * h) ⊆ U) {t : ℝ}
    (ht : t ∈ Set.Ioo (-2 : ℝ) (-1) ∪ Set.Ioo 2 3) :
    ∃ ξ ∈ Set.Icc (x₀ - 2 * h) (x₀ + 3 * h), |lagrangeRem (eqNode x₀ h 5) f (x₀ + t * h)| ≤
      0.0235 * h ^ 6 * |iteratedDeriv 6 f ξ| := by
  obtain ⟨e0, e1⟩ := eqNode_five_ends x₀ h
  have hJ : Set.Ioo (-2 : ℝ) (-1) ∪ Set.Ioo 2 3 ⊆ Set.Ioo (eqN0 5 : ℝ) (eqN1 5) := by
    rw [eqN0_five, eqN1_five]; push_cast
    exact Set.union_subset (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
      (Set.Ioo_subset_Ioo (by norm_num) (by norm_num))
  have := eqRem_le_of_coeff_le hh 5 f hU hd hJ dlmf_3_3_27_outer.2.le ht
    (by rw [e0, e1]; exact hI)
  rwa [e0, e1] at this

end Azurite.DLMF
