/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3PointsFiveSix

/-!
# DLMF §3.3(ii): the seven- and eight-point formulas

The cases `n = 6` and `n = 7` of `Section3Equal`, completing §3.3(ii).

* Seven-point formula: `dlmf_3_3_28` (sum and written-out forms, every real `t`), `dlmf_3_3_29`
  (`A_k^6`), `dlmf_3_3_30_inner` (`0.00245 ≤ c₆ < 0.00246` on `|t| < 1`), `dlmf_3_3_30_mid`
  (`0.00459 ≤ c₆ < 0.00460` on `1 < |t| < 2`), `dlmf_3_3_30_outer` (`0.0190 ≤ c₆ < 0.0191` on
  `2 < |t| < 3`), remainder bounds `dlmf_3_3_30_bound`.
* Eight-point formula: `dlmf_3_3_31`, `dlmf_3_3_32` (`A_k^7`), `dlmf_3_3_33_inner` (exactly
  `c₇ = 35/32768 = 0.00106…` on `0 < t < 1`, maximum at `t = ½`), `dlmf_3_3_33_mid`
  (`0.00139 ≤ c₇ < 0.00140`), `dlmf_3_3_33_third` (`0.00321 ≤ c₇ < 0.00322`),
  `dlmf_3_3_33_outer` (`0.0158 ≤ c₇ < 0.0159`), remainder bounds `dlmf_3_3_33_bound`.

As in `Section3PointsFiveSix`, the decimals are two-sided bounds from a rational witness and a
polynomial certificate. The product `∏|t − k|` is the odd septic `t(t² − 1)(t² − 4)(t² − 9)`
for `n = 6` (`abs_septic_abs` reduces to `|t|`) and a quartic in `v = (t − ½)²` for `n = 7`.
The certificate divides by `(x − r)²` (`r` near the maximizer); the quotient, of degree 5 resp.
2, has positive Bernstein coefficients on the interval `[a, b]`, so the hints
`(x − r)² (x − a)^i (b − x)^{d−i} ≥ 0` let `nlinarith` find the identity.
-/

namespace Azurite.DLMF

open Finset

/-! ### Seven-point formula 3.3.28–3.3.30 -/

theorem eqN0_six : eqN0 6 = -3 := by rw [eqN0_eq]; norm_num

theorem eqN1_six : eqN1 6 = 3 := by rw [eqN1_eq, eqN0_six]; norm_num

theorem Icc_eqN_six : Icc (eqN0 6) (eqN1 6) = {-3, -2, -1, 0, 1, 2, 3} := by
  rw [eqN0_six, eqN1_six]; decide

/-- **DLMF 3.3.29**: the coefficients `A_k^6`, `k = −3, …, 3`. -/
theorem dlmf_3_3_29 (t : ℝ) :
    lagCoeff' 6 (-3) t = 1 / 720 * t * (t ^ 2 - 1) * (t - 3) * (t ^ 2 - 4) ∧
      lagCoeff' 6 (-2) t = -(1 / 120) * t * (t ^ 2 - 1) * (t - 2) * (t ^ 2 - 9) ∧
      lagCoeff' 6 (-1) t = 1 / 48 * t * (t - 1) * (t ^ 2 - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 6 0 t = -(1 / 36) * (t ^ 2 - 1) * (t ^ 2 - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 6 1 t = 1 / 48 * t * (t + 1) * (t ^ 2 - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 6 2 t = -(1 / 120) * t * (t ^ 2 - 1) * (t + 2) * (t ^ 2 - 9) ∧
      lagCoeff' 6 3 t = 1 / 720 * t * (t ^ 2 - 1) * (t + 3) * (t ^ 2 - 4) := by
  simp only [lagCoeff', eqN0_six, eqN1_six]
  rw [show (Icc (-3 : ℤ) 3).erase (-3) = {-2, -1, 0, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase (-2) = {-3, -1, 0, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase (-1) = {-3, -2, 0, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 0 = {-3, -2, -1, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 1 = {-3, -2, -1, 0, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 2 = {-3, -2, -1, 0, 1, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 3 = {-3, -2, -1, 0, 1, 2} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [prod_insert, prod_pair, Nat.factorial] <;> ring

/-- **DLMF 3.3.28** with 3.3.29: `f_t = ∑_{k=−3}^{3} A_k^6 f_k + R_{6,t}` (valid for every real
`t`; DLMF states `|t| < 3`). -/
theorem dlmf_3_3_28 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (-3 : ℤ) 3, lagCoeff' 6 k t * f (x₀ + k * h) +
        lagrangeRem (eqNode x₀ h 6) f (x₀ + t * h) ∧
      f (x₀ + t * h) = 1 / 720 * t * (t ^ 2 - 1) * (t - 3) * (t ^ 2 - 4) * f (x₀ - 3 * h) +
        -(1 / 120) * t * (t ^ 2 - 1) * (t - 2) * (t ^ 2 - 9) * f (x₀ - 2 * h) +
        1 / 48 * t * (t - 1) * (t ^ 2 - 4) * (t ^ 2 - 9) * f (x₀ - h) +
        -(1 / 36) * (t ^ 2 - 1) * (t ^ 2 - 4) * (t ^ 2 - 9) * f x₀ +
        1 / 48 * t * (t + 1) * (t ^ 2 - 4) * (t ^ 2 - 9) * f (x₀ + h) +
        -(1 / 120) * t * (t ^ 2 - 1) * (t + 2) * (t ^ 2 - 9) * f (x₀ + 2 * h) +
        1 / 720 * t * (t ^ 2 - 1) * (t + 3) * (t ^ 2 - 4) * f (x₀ + 3 * h) +
        lagrangeRem (eqNode x₀ h 6) f (x₀ + t * h) := by
  have h7 := dlmf_3_3_7' (x₀ := x₀) hh 6 f t
  rw [← eqN0_six, ← eqN1_six]
  refine ⟨h7, ?_⟩
  rw [h7, Icc_eqN_six, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := dlmf_3_3_29 t
  rw [h1, h2, h3, h4, h5, h6, h7]
  push_cast
  ring_nf

theorem prod_abs_eqN_six (t : ℝ) :
    ∏ k ∈ Icc (eqN0 6) (eqN1 6), |t - k| = |t ^ 7 - 14 * t ^ 5 + 49 * t ^ 3 - 36 * t| := by
  rw [Icc_eqN_six, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_pair (by decide)]
  push_cast
  rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
  congr 1
  ring

theorem abs_septic_abs (t : ℝ) :
    |t ^ 7 - 14 * t ^ 5 + 49 * t ^ 3 - 36 * t| =
      |(|t| ^ 7 - 14 * |t| ^ 5 + 49 * |t| ^ 3 - 36 * |t|)| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, show (-t) ^ 7 - 14 * (-t) ^ 5 + 49 * (-t) ^ 3 - 36 * -t =
      -(t ^ 7 - 14 * t ^ 5 + 49 * t ^ 3 - 36 * t) by ring, abs_neg]

/-- `|t(t² − 1)(t² − 4)(t² − 9)| ≤ 12.37` on `[0, 1]`: the quotient by `(s − 0.5307)²` has
positive Bernstein coefficients on `[0, 1]`. -/
theorem septic_le_inner {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |s ^ 7 - 14 * s ^ 5 + 49 * s ^ 3 - 36 * s| ≤ 12.37 := by
  have hb : 0 ≤ 1 - s := by linarith
  have hg : s ^ 7 - 14 * s ^ 5 + 49 * s ^ 3 - 36 * s ≤ 0 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg h0 (by nlinarith : (0 : ℝ) ≤ 1 - s ^ 2))
      (by nlinarith : (0 : ℝ) ≤ 4 - s ^ 2)) (by nlinarith : (0 : ℝ) ≤ 9 - s ^ 2)]
  rw [abs_of_nonpos hg]
  have r := sq_nonneg (s - 5307 / 10000)
  nlinarith [mul_nonneg r (mul_nonneg (pow_nonneg h0 0) (pow_nonneg hb 5)),
    mul_nonneg r (mul_nonneg (pow_nonneg h0 1) (pow_nonneg hb 4)),
    mul_nonneg r (mul_nonneg (pow_nonneg h0 2) (pow_nonneg hb 3)),
    mul_nonneg r (mul_nonneg (pow_nonneg h0 3) (pow_nonneg hb 2)),
    mul_nonneg r (mul_nonneg (pow_nonneg h0 4) (pow_nonneg hb 1)),
    mul_nonneg r (mul_nonneg (pow_nonneg h0 5) (pow_nonneg hb 0))]

/-- `|t(t² − 1)(t² − 4)(t² − 9)| ≤ 23.17` on `[1, 2]` (quotient by `(s − 1.5958)²`). -/
theorem septic_le_mid {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    |s ^ 7 - 14 * s ^ 5 + 49 * s ^ 3 - 36 * s| ≤ 23.17 := by
  have ha : 0 ≤ s - 1 := by linarith
  have hb : 0 ≤ 2 - s := by linarith
  have hg : 0 ≤ s ^ 7 - 14 * s ^ 5 + 49 * s ^ 3 - 36 * s := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ s)
      (by nlinarith : (0 : ℝ) ≤ s ^ 2 - 1)) (by nlinarith : (0 : ℝ) ≤ 4 - s ^ 2))
      (by nlinarith : (0 : ℝ) ≤ 9 - s ^ 2)]
  rw [abs_of_nonneg hg]
  have r := sq_nonneg (s - 7979 / 5000)
  nlinarith [mul_nonneg r (mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 5)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 4)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 3)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 2)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 1)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 5) (pow_nonneg hb 0))]

/-- `|t(t² − 1)(t² − 4)(t² − 9)| ≤ 96` on `[2, 3]` (quotient by `(s − 2.678)²`). -/
theorem septic_le_outer {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) :
    |s ^ 7 - 14 * s ^ 5 + 49 * s ^ 3 - 36 * s| ≤ 96 := by
  have ha : 0 ≤ s - 2 := by linarith
  have hb : 0 ≤ 3 - s := by linarith
  have hg : s ^ 7 - 14 * s ^ 5 + 49 * s ^ 3 - 36 * s ≤ 0 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ s)
      (by nlinarith : (0 : ℝ) ≤ s ^ 2 - 1)) (by nlinarith : (0 : ℝ) ≤ s ^ 2 - 4))
      (by nlinarith : (0 : ℝ) ≤ 9 - s ^ 2)]
  rw [abs_of_nonpos hg]
  have r := sq_nonneg (s - 1339 / 500)
  nlinarith [mul_nonneg r (mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 5)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 4)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 3)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 2)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 1)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 5) (pow_nonneg hb 0))]

/-- **DLMF 3.3.30**, first case: `c₆ = 0.00245…` on `|t| < 1`. -/
theorem dlmf_3_3_30_inner :
    0.00245 ≤ eqBoundCoeff 6 (Set.Ioo (-1) 1) ∧ eqBoundCoeff 6 (Set.Ioo (-1) 1) < 0.00246 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 6) (J := Set.Ioo (-1) 1) (m := 12.348)
    (M := 12.37) (t₀ := 0.530655) (by norm_num)
    (by rw [prod_abs_eqN_six, abs_of_neg (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_six, abs_septic_abs]
      exact septic_le_inner (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩))
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

theorem abs_mem_of_mem_sym {t a b : ℝ} (ha : 0 ≤ a) (ht : t ∈ Set.Ioo (-b) (-a) ∪ Set.Ioo a b) :
    a ≤ |t| ∧ |t| ≤ b := by
  rcases ht with ht | ht
  · rw [abs_of_neg (by linarith [ht.2])]; constructor <;> linarith [ht.1, ht.2]
  · rw [abs_of_pos (by linarith [ht.1])]; constructor <;> linarith [ht.1, ht.2]

/-- **DLMF 3.3.30**, second case: `c₆ = 0.00459…` on `1 < |t| < 2`. -/
theorem dlmf_3_3_30_mid :
    0.00459 ≤ eqBoundCoeff 6 (Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2) ∧
      eqBoundCoeff 6 (Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2) < 0.00460 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 6) (J := Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2)
    (m := 23.1336) (M := 23.17) (t₀ := 1.59578) (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_six, abs_of_pos (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_six, abs_septic_abs]
      have := abs_mem_of_mem_sym (by norm_num) ht
      exact septic_le_mid this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

/-- **DLMF 3.3.30**, third case: `c₆ = 0.0190…` on `2 < |t| < 3`. -/
theorem dlmf_3_3_30_outer :
    0.0190 ≤ eqBoundCoeff 6 (Set.Ioo (-3) (-2) ∪ Set.Ioo 2 3) ∧
      eqBoundCoeff 6 (Set.Ioo (-3) (-2) ∪ Set.Ioo 2 3) < 0.0191 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 6) (J := Set.Ioo (-3) (-2) ∪ Set.Ioo 2 3)
    (m := 95.76) (M := 96) (t₀ := 2.67804) (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_six, abs_of_neg (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_six, abs_septic_abs]
      have := abs_mem_of_mem_sym (by norm_num) ht
      exact septic_le_outer this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

theorem eqNode_six_ends (x₀ h : ℝ) :
    x₀ + (eqN0 6 : ℝ) * h = x₀ - 3 * h ∧ x₀ + (eqN1 6 : ℝ) * h = x₀ + 3 * h := by
  rw [eqN0_six, eqN1_six]; push_cast; constructor <;> ring

/-- 3.3.13 with 3.3.30 on the three `t`-sets: `|R_{6,t}| ≤ C h⁷ |f⁽⁷⁾(ξ)|`,
`ξ ∈ [x₀ − 3h, x₀ + 3h]`, with `C = 0.00246`, `0.00460`, `0.0191`. -/
theorem dlmf_3_3_30_bound {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ 6, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 3 * h) (x₀ + 3 * h) ⊆ U) {t : ℝ} :
    (t ∈ Set.Ioo (-1 : ℝ) 1 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 3 * h),
      |lagrangeRem (eqNode x₀ h 6) f (x₀ + t * h)| ≤
        0.00246 * h ^ 7 * |iteratedDeriv 7 f ξ|) ∧
    (t ∈ Set.Ioo (-2 : ℝ) (-1) ∪ Set.Ioo 1 2 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 3 * h),
      |lagrangeRem (eqNode x₀ h 6) f (x₀ + t * h)| ≤
        0.00460 * h ^ 7 * |iteratedDeriv 7 f ξ|) ∧
    (t ∈ Set.Ioo (-3 : ℝ) (-2) ∪ Set.Ioo 2 3 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 3 * h),
      |lagrangeRem (eqNode x₀ h 6) f (x₀ + t * h)| ≤
        0.0191 * h ^ 7 * |iteratedDeriv 7 f ξ|) := by
  obtain ⟨e0, e1⟩ := eqNode_six_ends x₀ h
  have hI' : Set.Icc (x₀ + eqN0 6 * h) (x₀ + eqN1 6 * h) ⊆ U := by rw [e0, e1]; exact hI
  have hsub : ∀ {a b : ℝ}, -3 ≤ a → b ≤ 3 → Set.Ioo a b ⊆ Set.Ioo (eqN0 6 : ℝ) (eqN1 6) := by
    intro a b ha hb
    rw [eqN0_six, eqN1_six]; push_cast
    exact Set.Ioo_subset_Ioo ha hb
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · have := eqRem_le_of_coeff_le hh 6 f hU hd (hsub (by norm_num) (by norm_num))
      dlmf_3_3_30_inner.2.le ht hI'
    rwa [e0, e1] at this
  · have := eqRem_le_of_coeff_le hh 6 f hU hd
      (Set.union_subset (hsub (by norm_num) (by norm_num)) (hsub (by norm_num) (by norm_num)))
      dlmf_3_3_30_mid.2.le ht hI'
    rwa [e0, e1] at this
  · have := eqRem_le_of_coeff_le hh 6 f hU hd
      (Set.union_subset (hsub (by norm_num) (by norm_num)) (hsub (by norm_num) (by norm_num)))
      dlmf_3_3_30_outer.2.le ht hI'
    rwa [e0, e1] at this

/-! ### Eight-point formula 3.3.31–3.3.33 -/

theorem eqN0_seven : eqN0 7 = -3 := by rw [eqN0_eq]; norm_num

theorem eqN1_seven : eqN1 7 = 4 := by rw [eqN1_eq, eqN0_seven]; norm_num

theorem Icc_eqN_seven : Icc (eqN0 7) (eqN1 7) = {-3, -2, -1, 0, 1, 2, 3, 4} := by
  rw [eqN0_seven, eqN1_seven]; decide

/-- **DLMF 3.3.32**: the coefficients `A_k^7`, `k = −3, …, 4`. -/
theorem dlmf_3_3_32 (t : ℝ) :
    lagCoeff' 7 (-3) t = -(1 / 5040) * t * (t ^ 2 - 1) * (t - 3) * (t - 4) * (t ^ 2 - 4) ∧
      lagCoeff' 7 (-2) t = 1 / 720 * t * (t ^ 2 - 1) * (t - 2) * (t - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 7 (-1) t = -(1 / 240) * t * (t - 1) * (t - 4) * (t ^ 2 - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 7 0 t = 1 / 144 * (t ^ 2 - 1) * (t - 4) * (t ^ 2 - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 7 1 t = -(1 / 144) * t * (t + 1) * (t - 4) * (t ^ 2 - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 7 2 t = 1 / 240 * t * (t ^ 2 - 1) * (t + 2) * (t - 4) * (t ^ 2 - 9) ∧
      lagCoeff' 7 3 t = -(1 / 720) * t * (t ^ 2 - 1) * (t + 3) * (t - 4) * (t ^ 2 - 4) ∧
      lagCoeff' 7 4 t = 1 / 5040 * t * (t ^ 2 - 1) * (t ^ 2 - 4) * (t ^ 2 - 9) := by
  simp only [lagCoeff', eqN0_seven, eqN1_seven]
  rw [show (Icc (-3 : ℤ) 4).erase (-3) = {-2, -1, 0, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase (-2) = {-3, -1, 0, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase (-1) = {-3, -2, 0, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 0 = {-3, -2, -1, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 1 = {-3, -2, -1, 0, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 2 = {-3, -2, -1, 0, 1, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 3 = {-3, -2, -1, 0, 1, 2, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 4 = {-3, -2, -1, 0, 1, 2, 3} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [prod_insert, prod_pair, Nat.factorial] <;> ring

/-- **DLMF 3.3.31** with 3.3.32: `f_t = ∑_{k=−3}^{4} A_k^7 f_k + R_{7,t}` (valid for every real
`t`; DLMF states `−3 < t < 4`). -/
theorem dlmf_3_3_31 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (-3 : ℤ) 4, lagCoeff' 7 k t * f (x₀ + k * h) +
        lagrangeRem (eqNode x₀ h 7) f (x₀ + t * h) ∧
      f (x₀ + t * h) =
        -(1 / 5040) * t * (t ^ 2 - 1) * (t - 3) * (t - 4) * (t ^ 2 - 4) * f (x₀ - 3 * h) +
        1 / 720 * t * (t ^ 2 - 1) * (t - 2) * (t - 4) * (t ^ 2 - 9) * f (x₀ - 2 * h) +
        -(1 / 240) * t * (t - 1) * (t - 4) * (t ^ 2 - 4) * (t ^ 2 - 9) * f (x₀ - h) +
        1 / 144 * (t ^ 2 - 1) * (t - 4) * (t ^ 2 - 4) * (t ^ 2 - 9) * f x₀ +
        -(1 / 144) * t * (t + 1) * (t - 4) * (t ^ 2 - 4) * (t ^ 2 - 9) * f (x₀ + h) +
        1 / 240 * t * (t ^ 2 - 1) * (t + 2) * (t - 4) * (t ^ 2 - 9) * f (x₀ + 2 * h) +
        -(1 / 720) * t * (t ^ 2 - 1) * (t + 3) * (t - 4) * (t ^ 2 - 4) * f (x₀ + 3 * h) +
        1 / 5040 * t * (t ^ 2 - 1) * (t ^ 2 - 4) * (t ^ 2 - 9) * f (x₀ + 4 * h) +
        lagrangeRem (eqNode x₀ h 7) f (x₀ + t * h) := by
  have h7 := dlmf_3_3_7' (x₀ := x₀) hh 7 f t
  rw [← eqN0_seven, ← eqN1_seven]
  refine ⟨h7, ?_⟩
  rw [h7, Icc_eqN_seven, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := dlmf_3_3_32 t
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  push_cast
  ring_nf

/-- With `v = (t − ½)²`, `∏_{k=−3}^{4} |t − k| = |(v − ¼)(v − 9/4)(v − 25/4)(v − 49/4)|`. -/
theorem prod_abs_eqN_seven (t : ℝ) :
    ∏ k ∈ Icc (eqN0 7) (eqN1 7), |t - k| =
      |((t - 1 / 2) ^ 2 - 1 / 4) * ((t - 1 / 2) ^ 2 - 9 / 4) * ((t - 1 / 2) ^ 2 - 25 / 4) *
        ((t - 1 / 2) ^ 2 - 49 / 4)| := by
  rw [Icc_eqN_seven, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_pair (by decide)]
  push_cast
  rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
  congr 1
  ring

/-- `|(v − ¼)(v − 9/4)(v − 25/4)(v − 49/4)| ≤ 11025/256` on `[0, ¼]`. -/
theorem quartic_le_inner {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4)| ≤ 11025 / 256 := by
  rw [show (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4) =
    (1 / 4 - v) * (9 / 4 - v) * (25 / 4 - v) * (49 / 4 - v) by ring, abs_of_nonneg (by
      apply mul_nonneg (mul_nonneg (mul_nonneg _ _) _) _ <;> linarith)]
  calc (1 / 4 - v) * (9 / 4 - v) * (25 / 4 - v) * (49 / 4 - v) ≤
      1 / 4 * (9 / 4) * (25 / 4) * (49 / 4) := by
        apply mul_le_mul (mul_le_mul (mul_le_mul _ _ _ _) _ _ _) _ _ _ <;> norm_num <;>
          linarith
    _ = 11025 / 256 := by norm_num

/-- `|(v − ¼)(v − 9/4)(v − 25/4)(v − 49/4)| ≤ 56.3` on `[¼, 9/4]` (quotient by `(v − 1.1106)²`). -/
theorem quartic_le_mid {v : ℝ} (h0 : 1 / 4 ≤ v) (h1 : v ≤ 9 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4)| ≤ 56.3 := by
  have ha : 0 ≤ v - 1 / 4 := by linarith
  have hb : 0 ≤ 9 / 4 - v := by linarith
  have hg : (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4) ≤ 0 := by
    have : 0 ≤ (v - 1 / 4) * (9 / 4 - v) * (25 / 4 - v) * (49 / 4 - v) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg _ _) _) _ <;> linarith
    nlinarith
  rw [abs_of_nonpos hg]
  have r := sq_nonneg (v - 11106 / 10000)
  nlinarith [mul_nonneg r (mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 2)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 1)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 0))]

/-- `|(v − ¼)(v − 9/4)(v − 25/4)(v − 49/4)| ≤ 129.8` on `[9/4, 25/4]` (quotient by
`(v − 4.4651)²`). -/
theorem quartic_le_third {v : ℝ} (h0 : 9 / 4 ≤ v) (h1 : v ≤ 25 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4)| ≤ 129.8 := by
  have ha : 0 ≤ v - 9 / 4 := by linarith
  have hb : 0 ≤ 25 / 4 - v := by linarith
  have hg : 0 ≤ (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4) := by
    have : 0 ≤ (v - 1 / 4) * (v - 9 / 4) * (25 / 4 - v) * (49 / 4 - v) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg _ _) _) _ <;> linarith
    nlinarith
  rw [abs_of_nonneg hg]
  have r := sq_nonneg (v - 44651 / 10000)
  nlinarith [mul_nonneg r (mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 2)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 1)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 0))]

/-- `|(v − ¼)(v − 9/4)(v − 25/4)(v − 49/4)| ≤ 640.9` on `[25/4, 49/4]` (quotient by
`(v − 10.1743)²`). -/
theorem quartic_le_outer {v : ℝ} (h0 : 25 / 4 ≤ v) (h1 : v ≤ 49 / 4) :
    |(v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4)| ≤ 640.9 := by
  have ha : 0 ≤ v - 25 / 4 := by linarith
  have hb : 0 ≤ 49 / 4 - v := by linarith
  have hg : (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (v - 49 / 4) ≤ 0 := by
    have : 0 ≤ (v - 1 / 4) * (v - 9 / 4) * (v - 25 / 4) * (49 / 4 - v) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg _ _) _) _ <;> linarith
    nlinarith
  rw [abs_of_nonpos hg]
  have r := sq_nonneg (v - 101743 / 10000)
  nlinarith [mul_nonneg r (mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 2)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 1)),
    mul_nonneg r (mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 0))]

/-- **DLMF 3.3.33**, first case: `c₇ = 35/32768 = 0.00106…` on `0 < t < 1` (maximum at
`t = ½`). -/
theorem dlmf_3_3_33_inner : eqBoundCoeff 7 (Set.Ioo 0 1) = 35 / 32768 := by
  have hg : IsGreatest ((fun t : ℝ => ∏ k ∈ Icc (eqN0 7) (eqN1 7), |t - k|) '' Set.Ioo 0 1)
      (11025 / 256) := by
    refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
    · simp only [prod_abs_eqN_seven]; norm_num [abs_of_pos]
    · rintro _ ⟨t, ht, rfl⟩
      simp only [prod_abs_eqN_seven]
      exact quartic_le_inner (sq_nonneg _) (by nlinarith [ht.1, ht.2])
  rw [eqBoundCoeff, hg.csSup_eq]
  norm_num [Nat.factorial]

theorem dlmf_3_3_33_inner_decimal :
    0.00106 ≤ (35 / 32768 : ℝ) ∧ (35 / 32768 : ℝ) < 0.00107 := by
  norm_num

/-- **DLMF 3.3.33**, second case: `c₇ = 0.00139…` on `−1 < t < 0` or `1 < t < 2`. -/
theorem dlmf_3_3_33_mid :
    0.00139 ≤ eqBoundCoeff 7 (Set.Ioo (-1) 0 ∪ Set.Ioo 1 2) ∧
      eqBoundCoeff 7 (Set.Ioo (-1) 0 ∪ Set.Ioo 1 2) < 0.00140 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 7) (J := Set.Ioo (-1) 0 ∪ Set.Ioo 1 2)
    (m := 56.0448) (M := 56.3) (t₀ := 1.553845) (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_seven, abs_of_neg (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_seven]
      have : 1 / 4 ≤ (t - 1 / 2) ^ 2 ∧ (t - 1 / 2) ^ 2 ≤ 9 / 4 := by
        rcases ht with ht | ht <;> constructor <;> nlinarith [ht.1, ht.2]
      exact quartic_le_mid this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

/-- **DLMF 3.3.33**, third case: `c₇ = 0.00321…` on `−2 < t < −1` or `2 < t < 3`. -/
theorem dlmf_3_3_33_third :
    0.00321 ≤ eqBoundCoeff 7 (Set.Ioo (-2) (-1) ∪ Set.Ioo 2 3) ∧
      eqBoundCoeff 7 (Set.Ioo (-2) (-1) ∪ Set.Ioo 2 3) < 0.00322 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 7) (J := Set.Ioo (-2) (-1) ∪ Set.Ioo 2 3)
    (m := 129.4272) (M := 129.8) (t₀ := 2.61307) (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_seven, abs_of_pos (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_seven]
      have : 9 / 4 ≤ (t - 1 / 2) ^ 2 ∧ (t - 1 / 2) ^ 2 ≤ 25 / 4 := by
        rcases ht with ht | ht <;> constructor <;> nlinarith [ht.1, ht.2]
      exact quartic_le_third this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

/-- **DLMF 3.3.33**, fourth case: `c₇ = 0.0158…` on `−3 < t < −2` or `3 < t < 4`. -/
theorem dlmf_3_3_33_outer :
    0.0158 ≤ eqBoundCoeff 7 (Set.Ioo (-3) (-2) ∪ Set.Ioo 3 4) ∧
      eqBoundCoeff 7 (Set.Ioo (-3) (-2) ∪ Set.Ioo 3 4) < 0.0159 := by
  obtain ⟨h1, h2⟩ := eqBoundCoeff_bounds (n := 7) (J := Set.Ioo (-3) (-2) ∪ Set.Ioo 3 4)
    (m := 637.056) (M := 640.9) (t₀ := 3.689725) (Or.inr ⟨by norm_num, by norm_num⟩)
    (by rw [prod_abs_eqN_seven, abs_of_neg (by norm_num)]; norm_num)
    (fun t ht => by
      rw [prod_abs_eqN_seven]
      have : 25 / 4 ≤ (t - 1 / 2) ^ 2 ∧ (t - 1 / 2) ^ 2 ≤ 49 / 4 := by
        rcases ht with ht | ht <;> constructor <;> nlinarith [ht.1, ht.2]
      exact quartic_le_outer this.1 this.2)
  norm_num [Nat.factorial] at h1 h2
  constructor <;> linarith

theorem eqNode_seven_ends (x₀ h : ℝ) :
    x₀ + (eqN0 7 : ℝ) * h = x₀ - 3 * h ∧ x₀ + (eqN1 7 : ℝ) * h = x₀ + 4 * h := by
  rw [eqN0_seven, eqN1_seven]; push_cast; constructor <;> ring

/-- 3.3.13 with 3.3.33 on the four `t`-sets: `|R_{7,t}| ≤ C h⁸ |f⁽⁸⁾(ξ)|`,
`ξ ∈ [x₀ − 3h, x₀ + 4h]`, with `C = 35/32768`, `0.00140`, `0.00322`, `0.0159`. -/
theorem dlmf_3_3_33_bound {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ 7, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - 3 * h) (x₀ + 4 * h) ⊆ U) {t : ℝ} :
    (t ∈ Set.Ioo (0 : ℝ) 1 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 4 * h),
      |lagrangeRem (eqNode x₀ h 7) f (x₀ + t * h)| ≤
        35 / 32768 * h ^ 8 * |iteratedDeriv 8 f ξ|) ∧
    (t ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 1 2 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 4 * h),
      |lagrangeRem (eqNode x₀ h 7) f (x₀ + t * h)| ≤
        0.00140 * h ^ 8 * |iteratedDeriv 8 f ξ|) ∧
    (t ∈ Set.Ioo (-2 : ℝ) (-1) ∪ Set.Ioo 2 3 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 4 * h),
      |lagrangeRem (eqNode x₀ h 7) f (x₀ + t * h)| ≤
        0.00322 * h ^ 8 * |iteratedDeriv 8 f ξ|) ∧
    (t ∈ Set.Ioo (-3 : ℝ) (-2) ∪ Set.Ioo 3 4 → ∃ ξ ∈ Set.Icc (x₀ - 3 * h) (x₀ + 4 * h),
      |lagrangeRem (eqNode x₀ h 7) f (x₀ + t * h)| ≤
        0.0159 * h ^ 8 * |iteratedDeriv 8 f ξ|) := by
  obtain ⟨e0, e1⟩ := eqNode_seven_ends x₀ h
  have hI' : Set.Icc (x₀ + eqN0 7 * h) (x₀ + eqN1 7 * h) ⊆ U := by rw [e0, e1]; exact hI
  have hsub : ∀ {a b : ℝ}, -3 ≤ a → b ≤ 4 → Set.Ioo a b ⊆ Set.Ioo (eqN0 7 : ℝ) (eqN1 7) := by
    intro a b ha hb
    rw [eqN0_seven, eqN1_seven]; push_cast
    exact Set.Ioo_subset_Ioo ha hb
  have hu : ∀ {a b c d : ℝ}, -3 ≤ a → b ≤ 4 → -3 ≤ c → d ≤ 4 →
      Set.Ioo a b ∪ Set.Ioo c d ⊆ Set.Ioo (eqN0 7 : ℝ) (eqN1 7) :=
    fun ha hb hc hd => Set.union_subset (hsub ha hb) (hsub hc hd)
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · have := eqRem_le_of_coeff_le hh 7 f hU hd (hsub (by norm_num) (by norm_num))
      dlmf_3_3_33_inner.le ht hI'
    rwa [e0, e1] at this
  · have := eqRem_le_of_coeff_le hh 7 f hU hd (hu (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) dlmf_3_3_33_mid.2.le ht hI'
    rwa [e0, e1] at this
  · have := eqRem_le_of_coeff_le hh 7 f hU hd (hu (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) dlmf_3_3_33_third.2.le ht hI'
    rwa [e0, e1] at this
  · have := eqRem_le_of_coeff_le hh 7 f hU hd (hu (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) dlmf_3_3_33_outer.2.le ht hI'
    rwa [e0, e1] at this

end Azurite.DLMF
