/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Simpson

/-!
# DLMF §3.5(iii): Romberg integration

* 3.5.9: `rombergCoeff`, `dlmf_3_5_9`, for `f ∈ C^{2m+2}` on an open set containing `[a, b]`:
  `E_n(f) − ∑_{s=1}^{m} c_s h^{2s} = O(h^{2m+2})` uniformly in `n ≥ 1`, with
  `c_s = −B_{2s}/(2s)! (f^{(2s−1)}(b) − f^{(2s−1)}(a))` (Euler–Maclaurin `em_sum` of §2.10(i) with
  `periodicBernoulli_bound`); `contDiffOn_iterate_deriv`.
* 3.5.10: `rombergG` (`G_k(h)` from `G₀(h), …, G₀(h/2ᵏ)`, the convention of 3.5.11–3.5.13 and of the
  Example), `dlmf_3_5_10` in the corrected form `G_k(h) = G_{k−1}(½h) + …`;
  `dlmf_3_5_10_erratum` (`x⁴` on `[0, 1]`: `G₁(½) = 77/384 ≠ 5/24 = G₁(1)`).
* 3.5.11–3.5.12: `dlmf_3_5_11` (with `G₀(b − a) = ½(b − a)(f(a) + f(b))`), `dlmf_3_5_12` (halving
  the step adds the midpoints).
* Elimination: `rombergLambda`, `rombergLambda_eq_zero` (`λ_{k,s} = 0` for `1 ≤ s ≤ k`),
  `romberg_expansion` (`∫ − G_k(h) = ∑ λ_{k,s} c_s h^{2s} + O(h^{2m+2})`, by induction on `k`).
* 3.5.13: `rombergErrCoeff`, `dlmf_3_5_13_zero` (trapezoidal rule, from 3.5.3) and
  `dlmf_3_5_13_one` (`G₁` is Simpson's rule, from 3.5.8). The general case needs the
  definiteness of the Romberg Peano kernel (Bauer–Rutishauser–Stiefel) and is deferred.
* Example: `bernoulli'_six` … `bernoulli'_sixteen`, `bernoulli_sixteen`,
  `dlmf_3_5_iii_example_coeff` (the coefficient `(0.14…) × 10⁻¹³` for `b − a = 30`, `j = 2`,
  `k = 7`). The Laplace transform 3.5.14 of `J₀`, the 14 correct digits and the Gauss–Laguerre
  comparison need Bessel functions (Chapter 10) and are deferred.
-/

open Finset Filter Topology Set MeasureTheory intervalIntegral

namespace Azurite.DLMF

/-! ### The expansion of the trapezoidal error 3.5.9 -/

/-- Iterated derivatives of a `Cᴺ` function on an open set are `C^{N−l}`. -/
theorem contDiffOn_iterate_deriv {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) : ∀ l ≤ N, ContDiffOn ℝ (N - l : ℕ) (deriv^[l] f) U := by
  intro l
  induction l with
  | zero => intro _; simpa using hf
  | succ l ih =>
    intro hl
    rw [Function.iterate_succ_apply']
    exact (ih (by omega)).deriv_of_isOpen hU (by norm_cast; omega)

/-- The coefficients `c_s = −(B_{2s}/(2s)!) (f^{(2s−1)}(b) − f^{(2s−1)}(a))` of 3.5.9. -/
noncomputable def rombergCoeff (f : ℝ → ℝ) (a b : ℝ) (s : ℕ) : ℝ :=
  -((bernoulli (2 * s) : ℝ) / ((2 * s).factorial : ℝ)) *
    (iteratedDeriv (2 * s - 1) f b - iteratedDeriv (2 * s - 1) f a)

/-- **DLMF 3.5.9**: for `f ∈ C^{2m+2}` on an open set containing `[a, b]`,
`E_n(f) = c₁h² + c₂h⁴ + ⋯ + c_m h^{2m} + O(h^{2m+2})`, uniformly in `n ≥ 1`, `h = (b − a)/n`, with
the explicit coefficients `rombergCoeff` (from the Euler–Maclaurin formula `em_sum`). -/
theorem dlmf_3_5_9 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (m : ℕ) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ (2 * m + 2 : ℕ) f U) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → |trapError f a b n - ∑ s ∈ range m,
      rombergCoeff f a b (s + 1) * ((b - a) / n) ^ (2 * (s + 1))| ≤
        C * ((b - a) / n) ^ (2 * m + 2) := by
  have hsm := contDiffOn_iterate_deriv hU hf
  have hdiff : ∀ l < 2 * m + 2, ∀ x ∈ U, HasDerivAt (deriv^[l] f) (deriv^[l + 1] f x) x :=
    fun l hl x hx => by
      have := ((hsm l hl.le).differentiableOn (by norm_cast; omega)) x hx
      rw [Function.iterate_succ_apply']
      exact (this.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b)
    ((hsm (2 * m + 2) le_rfl).continuousOn.mono hIU)
  obtain ⟨β, hβ⟩ := periodicBernoulli_bound (2 * m + 2)
  refine ⟨|rombergCoeff f a b (m + 1)| + (b - a) * (M * β / (2 * m + 2).factorial),
    fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set h := (b - a) / n with hh
  have hpos : 0 < h := div_pos (by linarith) hn0
  have hnh : (n : ℝ) * h = b - a := by simp only [h]; field_simp
  set D : ℕ → ℝ → ℝ := fun l s => h ^ l * deriv^[l] f (a + s * h)
  have hxU : ∀ x ∈ Icc (0 : ℝ) (0 + n), a + x * h ∈ Icc a b := fun x hx => by
    constructor
    · nlinarith [hx.1]
    · nlinarith [hx.2, hnh]
  have hd : ∀ k < 2 * m + 2, ∀ x ∈ Icc (0 : ℝ) (0 + n), HasDerivAt (D k) (D (k + 1) x) x :=
    fun k hk x hx => by
      have := ((hdiff k hk _ (hIU (hxU x hx))).comp x
        (((hasDerivAt_id' x).mul_const h).const_add a)).const_mul (h ^ k)
      convert this using 1
      · simp only [D]; rfl
      · simp only [D, Function.iterate_succ_apply']; ring
  have hDc : ContinuousOn (D (2 * m + 2)) (Icc (0 : ℝ) (0 + n)) := by
    simp only [D]
    refine continuousOn_const.mul (((hsm (2 * m + 2) le_rfl).continuousOn.mono hIU).comp
      (by fun_prop) fun x hx => hxU x hx)
  have hem := em_sum (t := 0) (D := D) m n hd (hDc.intervalIntegrable_of_Icc (by linarith))
  set R := ∫ x in (0 : ℝ)..0 + n, D (2 * m + 2) x *
    (bernoulliFun (2 * m + 2) (Int.fract (x - 0)) / ((2 * m + 2).factorial : ℝ))
  have hD0 : ∀ s, D 0 s = f (a + s * h) := fun s => by simp [D]
  have hend : a + (n : ℝ) * h = b := by rw [hnh]; ring
  have hI : ∫ x in a..b, f x = h * ∫ x in (0 : ℝ)..0 + n, D 0 x := by
    have := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 0 + n) (f := f) hpos.ne' a
    simp only [mul_zero, zero_add] at this
    rw [show h * n + a = b by rw [mul_comm, hnh]; ring] at this
    simp only [hD0, zero_add]
    rw [show (fun s : ℝ => f (a + s * h)) = fun s => f (h * s + a) by ext s; ring_nf, this,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  have hT : trapezoidSum f a b n =
      h * (∑ i ∈ range (n + 1), D 0 (0 + i) - D 0 0 / 2 - D 0 (0 + n) / 2) := by
    simp only [trapezoidSum, hD0, zero_add, zero_mul, add_zero]
    rfl
  have hΔ : ∀ s : ℕ, D (2 * s + 1) (0 + n) - D (2 * s + 1) 0 =
      h ^ (2 * s + 1) * (iteratedDeriv (2 * s + 1) f b - iteratedDeriv (2 * s + 1) f a) :=
    fun s => by simp only [D, zero_add, zero_mul, add_zero, hend, iteratedDeriv_eq_iterate]; ring
  have herr : trapError f a b n = ∑ s ∈ range (m + 1),
      rombergCoeff f a b (s + 1) * h ^ (2 * (s + 1)) + h * R := by
    rw [trapError, hI, hT, hem]
    have hS : ∑ s ∈ range (m + 1), rombergCoeff f a b (s + 1) * h ^ (2 * (s + 1)) =
        -(h * ∑ s ∈ range (m + 1), (bernoulli (2 * s + 2) : ℝ) / ((2 * s + 2).factorial : ℝ) *
          (D (2 * s + 1) (0 + n) - D (2 * s + 1) 0)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [hΔ, rombergCoeff, show 2 * (s + 1) - 1 = 2 * s + 1 by omega,
        show 2 * (s + 1) = 2 * s + 2 by ring]
      ring
    rw [hS]; ring
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab.le⟩)
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ 0)
  have hRb : |R| ≤ h ^ (2 * m + 2) * (M * β / (2 * m + 2).factorial) * n := by
    have := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 0 + n)
      (C := h ^ (2 * m + 2) * (M * β / (2 * m + 2).factorial))
      (f := fun x => D (2 * m + 2) x *
        (bernoulliFun (2 * m + 2) (Int.fract (x - 0)) / ((2 * m + 2).factorial : ℝ)))
      fun x hx => by
        rw [uIoc_of_le (by linarith)] at hx
        have hm := hM _ (hxU x ⟨hx.1.le, hx.2⟩)
        have hb := hβ (x - 0)
        rw [Real.norm_eq_abs] at hm ⊢
        simp only [D]
        have hkf : (0 : ℝ) < (2 * m + 2).factorial := by positivity
        rw [abs_mul, abs_mul, abs_div, abs_of_pos (pow_pos hpos _), Nat.abs_cast]
        calc h ^ (2 * m + 2) * |deriv^[2 * m + 2] f (a + x * h)| *
              (|bernoulliFun (2 * m + 2) (Int.fract (x - 0))| / (2 * m + 2).factorial)
            ≤ h ^ (2 * m + 2) * M * (β / (2 * m + 2).factorial) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hm (pow_pos hpos _).le)
                (div_le_div_of_nonneg_right hb hkf.le) (by positivity)
                (mul_nonneg (pow_pos hpos _).le hM0)
          _ = h ^ (2 * m + 2) * (M * β / (2 * m + 2).factorial) := by ring
    rw [Real.norm_eq_abs, show (0 : ℝ) + n - 0 = n by ring, abs_of_pos hn0] at this
    exact this
  rw [herr, sum_range_succ]
  rw [show ∀ X Y Z : ℝ, X + Y + Z - X = Y + Z from fun X Y Z => by ring]
  calc |rombergCoeff f a b (m + 1) * h ^ (2 * (m + 1)) + h * R|
      ≤ |rombergCoeff f a b (m + 1)| * h ^ (2 * m + 2) + h * |R| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (pow_pos hpos _), show 2 * (m + 1) = 2 * m + 2 by ring]
        · rw [abs_mul, abs_of_pos hpos]
    _ ≤ |rombergCoeff f a b (m + 1)| * h ^ (2 * m + 2) +
        h * (h ^ (2 * m + 2) * (M * β / (2 * m + 2).factorial) * n) := by gcongr
    _ = (|rombergCoeff f a b (m + 1)| + (n * h) * (M * β / (2 * m + 2).factorial)) *
        h ^ (2 * m + 2) := by ring
    _ = _ := by rw [hnh]

/-! ### The Romberg scheme 3.5.10–3.5.12 -/

/-- `G_k(h)`, `h = (b − a)/n`, built from `G₀(h), G₀(h/2), …, G₀(h/2ᵏ)` (the convention
of 3.5.11–3.5.13 and of the Example). -/
noncomputable def rombergG (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℕ → ℝ
  | 0, n => trapezoidSum f a b n
  | k + 1, n => rombergG f a b k (2 * n) +
      (rombergG f a b k (2 * n) - rombergG f a b k n) / (4 ^ (k + 1) - 1)

/-- **DLMF 3.5.10** (corrected; see errata):
`G_k(h) = G_{k−1}(½h) + (G_{k−1}(½h) − G_{k−1}(h))/(4ᵏ − 1)`, `k ≥ 1`. -/
theorem dlmf_3_5_10 (f : ℝ → ℝ) (a b : ℝ) (k n : ℕ) :
    rombergG f a b (k + 1) n = rombergG f a b k (2 * n) +
      (rombergG f a b k (2 * n) - rombergG f a b k n) / (4 ^ (k + 1) - 1) := rfl

/-- **Erratum to 3.5.10**: as printed (`G_k(½h)` on the left) the formula would assert
`G_k(½h) = G_k(h)` in the convention of 3.5.11–3.5.13; for `f(x) = x⁴` on `[0, 1]`,
`G₁(½) = 77/384 ≠ 5/24 = G₁(1)`. -/
theorem dlmf_3_5_10_erratum :
    rombergG (fun x => x ^ 4) 0 1 1 2 = 77 / 384 ∧
      rombergG (fun x => x ^ 4) 0 1 1 1 = 5 / 24 := by
  constructor <;> norm_num [rombergG, trapezoidSum, sum_range_succ]

/-- **DLMF 3.5.11**: `G₀(h) = h(½f₀ + f₁ + ⋯ + f_{n−1} + ½fₙ)`, and the elementary start
`G₀(b − a) = ½(b − a)(f(a) + f(b))`. -/
theorem dlmf_3_5_11 (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    rombergG f a b 0 n = trapezoidSum f a b n ∧
      rombergG f a b 0 1 = 1 / 2 * (b - a) * (f a + f b) := by
  refine ⟨rfl, ?_⟩
  simp [rombergG, trapezoidSum, sum_range_succ]
  ring

/-- **DLMF 3.5.12**: `G₀(½h) = ½G₀(h) + ½h ∑_{k<n} f(x₀ + (k + ½)h)`, `h = (b − a)/n`. -/
theorem dlmf_3_5_12 (f : ℝ → ℝ) (a b : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    trapezoidSum f a b (2 * n) = 1 / 2 * trapezoidSum f a b n +
      1 / 2 * ((b - a) / n) * ∑ k ∈ range n, f (a + (k + 1 / 2) * ((b - a) / n)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set h := (b - a) / n
  have hh2 : (b - a) / ((2 * n : ℕ) : ℝ) = h / 2 := by simp only [h]; push_cast; field_simp
  rw [trapezoidSum, trapezoidSum, hh2, sum_range_succ,
    sum_range_even_odd (fun i => f (a + i * (h / 2))) n, sum_range_succ (n := n)]
  have he : ∀ j : ℕ, f (a + ((2 * j : ℕ) : ℝ) * (h / 2)) = f (a + j * h) := fun j => by
    congr 1; push_cast; ring
  have ho : ∀ j : ℕ, f (a + ((2 * j + 1 : ℕ) : ℝ) * (h / 2)) = f (a + (j + 1 / 2) * h) :=
    fun j => by congr 1; push_cast; ring
  have hl : f (a + ((2 * n : ℕ) : ℝ) * (h / 2)) = f (a + n * h) := by congr 1; push_cast; ring
  simp only [he, ho, sum_add_distrib]
  ring

/-! ### Elimination of the error terms -/

/-- The factor `λ_{k,s} = ∏_{i=1}^{k} (4^{i−s} − 1)/(4ⁱ − 1)` by which the Romberg scheme
multiplies `c_s h^{2s}`. -/
noncomputable def rombergLambda (k s : ℕ) : ℝ :=
  ∏ i ∈ Icc 1 k, ((4 : ℝ) ^ i / 4 ^ s - 1) / (4 ^ i - 1)

theorem rombergLambda_zero (s : ℕ) : rombergLambda 0 s = 1 := by simp [rombergLambda]

theorem rombergLambda_succ (k s : ℕ) : rombergLambda (k + 1) s =
    rombergLambda k s * (((4 : ℝ) ^ (k + 1) / 4 ^ s - 1) / (4 ^ (k + 1) - 1)) := by
  rw [rombergLambda, prod_Icc_succ_top (by omega)]; rfl

/-- The terms `c₁h², …, c_k h^{2k}` are eliminated: `λ_{k,s} = 0` for `1 ≤ s ≤ k`. -/
theorem rombergLambda_eq_zero {k s : ℕ} (h1 : 1 ≤ s) (hs : s ≤ k) : rombergLambda k s = 0 :=
  prod_eq_zero (mem_Icc.mpr ⟨h1, hs⟩) (by rw [div_self (by positivity), sub_self, zero_div])

/-- **The Romberg scheme eliminates successive error terms** (§3.5(iii)): for
`f ∈ C^{2m+2}`, `∫ₐᵇ f − G_k(h) = ∑_{s=1}^{m} λ_{k,s} c_s h^{2s} + O(h^{2m+2})` uniformly in
`n ≥ 1`, with `λ_{k,s} = 0` for `s ≤ k`. -/
theorem romberg_expansion {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (m : ℕ) {U : Set ℝ}
    (hU : IsOpen U) (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ (2 * m + 2 : ℕ) f U) :
    ∀ k : ℕ, ∃ C, ∀ n : ℕ, 1 ≤ n → |((∫ x in a..b, f x) - rombergG f a b k n) -
      ∑ s ∈ range m, rombergLambda k (s + 1) * rombergCoeff f a b (s + 1) *
        ((b - a) / n) ^ (2 * (s + 1))| ≤ C * ((b - a) / n) ^ (2 * m + 2) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨C, hC⟩ := dlmf_3_5_9 hab m hU hIU hf
    exact ⟨C, fun n hn => by simpa [rombergLambda_zero, rombergG, trapError] using hC n hn⟩
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    set q : ℝ := 4 ^ (k + 1)
    have hq : 1 < q := one_lt_pow₀ (by norm_num) (by omega)
    refine ⟨(|C| * q / 4 ^ (m + 1) + |C|) / (q - 1), fun n hn => ?_⟩
    have hq1 : q - 1 ≠ 0 := by linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (b - a) / n with hh
    have hpos : 0 < h := div_pos (by linarith) hn0
    have h2 : (b - a) / ((2 * n : ℕ) : ℝ) = h / 2 := by simp only [h]; push_cast; field_simp
    set P : ℝ → ℝ := fun x => ∑ s ∈ range m,
      rombergLambda k (s + 1) * rombergCoeff f a b (s + 1) * x ^ (2 * (s + 1))
    have hA := hC (2 * n) (by omega)
    have hB := hC n hn
    rw [h2] at hA
    set A := (∫ x in a..b, f x) - rombergG f a b k (2 * n) - P (h / 2)
    set B := (∫ x in a..b, f x) - rombergG f a b k n - P h
    have hP : ∑ s ∈ range m, rombergLambda (k + 1) (s + 1) * rombergCoeff f a b (s + 1) *
        h ^ (2 * (s + 1)) = (q * P (h / 2) - P h) / (q - 1) := by
      simp only [P, rombergLambda_succ, mul_sum, ← sum_sub_distrib, sum_div]
      refine sum_congr rfl fun s _ => ?_
      rw [show ((4 : ℝ) ^ (k + 1)) = q from rfl, div_pow h 2,
        show (2 : ℝ) ^ (2 * (s + 1)) = 4 ^ (s + 1) by rw [pow_mul]; norm_num]
      field_simp
    have hid : ((∫ x in a..b, f x) - rombergG f a b (k + 1) n) -
        ∑ s ∈ range m, rombergLambda (k + 1) (s + 1) * rombergCoeff f a b (s + 1) *
          h ^ (2 * (s + 1)) = (q * A - B) / (q - 1) := by
      rw [hP, dlmf_3_5_10, show ((4 : ℝ) ^ (k + 1)) = q from rfl]
      simp only [A, B]
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos (by linarith : (0 : ℝ) < q - 1)]
    rw [div_le_iff₀ (by linarith)]
    have hA' : |A| ≤ |C| * (h ^ (2 * m + 2) / 4 ^ (m + 1)) := by
      refine hA.trans ?_
      rw [div_pow, show (2 : ℝ) ^ (2 * m + 2) = 4 ^ (m + 1) by
        rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; norm_num]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hB' : |B| ≤ |C| * h ^ (2 * m + 2) :=
      hB.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    calc |q * A - B| ≤ q * |A| + |B| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          rw [abs_mul, abs_of_pos (by linarith)]
      _ ≤ q * (|C| * (h ^ (2 * m + 2) / 4 ^ (m + 1))) + |C| * h ^ (2 * m + 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hA' (by linarith)) hB'
      _ = _ := by field_simp

/-! ### The error formula 3.5.13 for `k = 0, 1` -/

/-- The coefficient `(b − a)^{2k+3} 2^{−k(k+1)} 4^{−j(k+1)} |B_{2k+2}|/(2k + 2)!` of 3.5.13. -/
noncomputable def rombergErrCoeff (L : ℝ) (j k : ℕ) : ℝ :=
  L ^ (2 * k + 3) / 2 ^ (k * (k + 1)) * ((4 : ℝ) ^ (j * (k + 1)))⁻¹ /
    ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)|

/-- **DLMF 3.5.13** for `k = 0` (the composite trapezoidal rule, 3.5.3). -/
theorem dlmf_3_5_13_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) (j : ℕ) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - rombergG f a b 0 (2 ^ j) =
      -rombergErrCoeff (b - a) j 0 * iteratedDeriv 2 f ξ := by
  obtain ⟨ξ, hξ, he⟩ := dlmf_3_5_3 hab (Nat.one_le_two_pow) hU hIU hf
  refine ⟨ξ, hξ, ?_⟩
  rw [show (∫ x in a..b, f x) - rombergG f a b 0 (2 ^ j) = trapError f a b (2 ^ j) from rfl, he,
    rombergErrCoeff, iteratedDeriv_succ, iteratedDeriv_one, bernoulli_two]
  push_cast
  rw [show ((4 : ℝ) ^ (j * (0 + 1))) = (2 ^ j) ^ 2 by
    rw [zero_add, mul_one, ← pow_mul, mul_comm, pow_mul]; norm_num]
  have : (0 : ℝ) < 2 ^ j := by positivity
  field_simp
  norm_num [abs_of_pos]
  ring

/-- **DLMF 3.5.13** for `k = 1`: `G₁(h)` is Simpson's rule with step `½h` (3.5.8). -/
theorem dlmf_3_5_13_one {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) (j : ℕ) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - rombergG f a b 1 (2 ^ j) =
      -rombergErrCoeff (b - a) j 1 * iteratedDeriv 4 f ξ := by
  obtain ⟨ξ, hξ, he⟩ := dlmf_3_5_8 hab (N := 2 ^ j) Nat.one_le_two_pow hU hIU hf
  refine ⟨ξ, hξ, ?_⟩
  have hG : rombergG f a b 1 (2 ^ j) = simpsonSum f a b (2 * 2 ^ j) := by
    rw [simpsonSum_eq_trapezoid f a b Nat.one_le_two_pow]
    simp only [rombergG]
    ring
  have hB4 : (bernoulli 4 : ℝ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; push_cast; ring
  rw [hG, show (∫ x in a..b, f x) - simpsonSum f a b (2 * 2 ^ j) = simpsonError f a b (2 * 2 ^ j)
    from rfl, he, rombergErrCoeff, hB4]
  push_cast
  rw [show ((4 : ℝ) ^ (j * (1 + 1))) = (2 ^ j) ^ 4 by
    rw [← pow_mul, show j * (1 + 1) = 2 * j by ring, pow_mul, mul_comm, pow_mul]; norm_num]
  have : (0 : ℝ) < 2 ^ j := by positivity
  field_simp
  norm_num [abs_div]
  ring

/-! ### The Example: the coefficient of `f^{(16)}(ξ)` -/

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5)]
  norm_num [Nat.choose]

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5),
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by norm_num : 1 < 7)]
  norm_num [Nat.choose]

theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six, bernoulli'_eight,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5),
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by norm_num : 1 < 7),
    bernoulli'_eq_zero_of_odd (by decide : Odd 9) (by norm_num : 1 < 9)]
  norm_num [Nat.choose]

theorem bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six, bernoulli'_eight, bernoulli'_ten,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5),
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by norm_num : 1 < 7),
    bernoulli'_eq_zero_of_odd (by decide : Odd 9) (by norm_num : 1 < 9),
    bernoulli'_eq_zero_of_odd (by decide : Odd 11) (by norm_num : 1 < 11)]
  norm_num [Nat.choose]

theorem bernoulli'_fourteen : bernoulli' 14 = 7 / 6 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six, bernoulli'_eight, bernoulli'_ten,
    bernoulli'_twelve, bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5),
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by norm_num : 1 < 7),
    bernoulli'_eq_zero_of_odd (by decide : Odd 9) (by norm_num : 1 < 9),
    bernoulli'_eq_zero_of_odd (by decide : Odd 11) (by norm_num : 1 < 11),
    bernoulli'_eq_zero_of_odd (by decide : Odd 13) (by norm_num : 1 < 13)]
  norm_num [Nat.choose]

theorem bernoulli'_sixteen : bernoulli' 16 = -3617 / 510 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six, bernoulli'_eight, bernoulli'_ten,
    bernoulli'_twelve, bernoulli'_fourteen,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5),
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by norm_num : 1 < 7),
    bernoulli'_eq_zero_of_odd (by decide : Odd 9) (by norm_num : 1 < 9),
    bernoulli'_eq_zero_of_odd (by decide : Odd 11) (by norm_num : 1 < 11),
    bernoulli'_eq_zero_of_odd (by decide : Odd 13) (by norm_num : 1 < 13),
    bernoulli'_eq_zero_of_odd (by decide : Odd 15) (by norm_num : 1 < 15)]
  norm_num [Nat.choose]

theorem bernoulli_sixteen : (bernoulli 16 : ℝ) = -3617 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_sixteen]; push_cast; ring

/-- The Example: with `b − a = 30`, `j = 2` and `k = 7`, the coefficient of `f^{(16)}(ξ)` in 3.5.13
is `(0.14…) × 10⁻¹³`. -/
theorem dlmf_3_5_iii_example_coeff :
    0.14e-13 ≤ rombergErrCoeff 30 2 7 ∧ rombergErrCoeff 30 2 7 < 0.15e-13 := by
  rw [rombergErrCoeff, show 2 * 7 + 2 = 16 by rfl, bernoulli_sixteen]
  norm_num [Nat.factorial, abs_div]

end Azurite.DLMF
