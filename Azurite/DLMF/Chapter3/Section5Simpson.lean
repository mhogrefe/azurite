/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5

/-!
# DLMF §3.5(ii): Simpson's rule

* `peano4`: for `P` with `P⁗ = 1`,
  `∫ P f⁽⁴⁾ = ∫ f + [P f‴ − P′ f″ + P″ f′ − P‴ f]` (an antiderivative identity); `C4Data`,
  `c4Data_of_contDiffOn` package the derivatives of `f ∈ C⁴` on an open set.
* 3.5.6: `dlmf_3_5_6`, for `f ∈ C⁴` on an open set containing `[a, b]` (`a < ξ < b`): `peano4` on
  `[a, m]` and `[m, b]` with the Peano kernel `K = (3w⁴ − 4hw³)/72`, `w = h − |x − m|`
  (`simpsonKernel_derivs`, `simpsonKernel_derivs'`), whose boundary terms at the midpoint cancel;
  `K ≤ 0`, `∫ K = −h⁵/90`; then the weighted mean value theorem with an interior point
  (`exists_mem_Ioo_integral_mul_eq` of §3.5(i)).
* 3.5.7–3.5.8: `simpsonWeight`, `simpsonSum`, `simpsonError`, `dlmf_3_5_7`, `sum_simpsonWeight`
  (the weights `1, 4, 2, …, 4, 1` as a sum of panels), `dlmf_3_5_8` (`n = 2N`; 3.5.6 on each panel,
  the average of the `f⁽⁴⁾(ξ_j)` by `exists_sum_eq_card_mul`).
* "a combination of two trapezoidal rules": `simpsonSum_eq_trapezoid`,
  `S_{2N} = (4 T_{2N} − T_N)/3` (step sizes `h` and `2h`).
-/

open Finset Filter Topology Set MeasureTheory intervalIntegral

namespace Azurite.DLMF

/-! ### The Peano-kernel identity of order 4 -/

/-- Derivatives of a `C⁴` function on an open set. -/
structure C4Data (f : ℝ → ℝ) (U : Set ℝ) : Prop where
  d0 : ∀ x ∈ U, HasDerivAt f (deriv f x) x
  d1 : ∀ x ∈ U, HasDerivAt (deriv f) (deriv (deriv f) x) x
  d2 : ∀ x ∈ U, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x
  d3 : ∀ x ∈ U, HasDerivAt (deriv (deriv (deriv f))) (deriv (deriv (deriv (deriv f))) x) x
  c4 : ContinuousOn (deriv (deriv (deriv (deriv f)))) U

theorem c4Data_of_contDiffOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 4 f U) :
    C4Data f U := by
  have h1 : ContDiffOn ℝ 3 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have h2 : ContDiffOn ℝ 2 (deriv (deriv f)) U := h1.deriv_of_isOpen hU (by norm_num)
  have h3 : ContDiffOn ℝ 1 (deriv (deriv (deriv f))) U := h2.deriv_of_isOpen hU (by norm_num)
  have h4 : ContDiffOn ℝ 0 (deriv (deriv (deriv (deriv f)))) U := h3.deriv_of_isOpen hU
    (by norm_num)
  have hd : ∀ {g : ℝ → ℝ} {n : WithTop ℕ∞}, ContDiffOn ℝ n g U → n ≠ 0 →
      ∀ x ∈ U, HasDerivAt g (deriv g x) x := fun hg hn x hx =>
    ((hg.differentiableOn hn) x hx).differentiableAt (hU.mem_nhds hx) |>.hasDerivAt
  exact ⟨hd hf (by norm_num), hd h1 (by norm_num), hd h2 (by norm_num), hd h3 (by norm_num),
    h4.continuousOn⟩

/-- `∫_p^q P f⁽⁴⁾ = ∫_p^q f + [P f‴ − P′ f″ + P″ f′ − P‴ f]_p^q` when `P⁗ = 1`. -/
theorem peano4 {f : ℝ → ℝ} {U : Set ℝ} (hf : C4Data f U) {p q : ℝ} (hpq : p ≤ q)
    (hI : Icc p q ⊆ U) {P P1 P2 P3 : ℝ → ℝ} (h0 : ∀ x, HasDerivAt P (P1 x) x)
    (h1 : ∀ x, HasDerivAt P1 (P2 x) x) (h2 : ∀ x, HasDerivAt P2 (P3 x) x)
    (h3 : ∀ x, HasDerivAt P3 1 x) (hPc : Continuous P) :
    ∫ x in p..q, P x * deriv (deriv (deriv (deriv f))) x = (∫ x in p..q, f x) +
      ((P q * deriv (deriv (deriv f)) q - P1 q * deriv (deriv f) q + P2 q * deriv f q -
          P3 q * f q) -
        (P p * deriv (deriv (deriv f)) p - P1 p * deriv (deriv f) p + P2 p * deriv f p -
          P3 p * f p)) := by
  have hφ : ∀ x ∈ uIcc p q, HasDerivAt
      (fun x => P x * deriv (deriv (deriv f)) x - P1 x * deriv (deriv f) x + P2 x * deriv f x -
        P3 x * f x) (P x * deriv (deriv (deriv (deriv f))) x - f x) x := by
    intro x hx
    rw [uIcc_of_le hpq] at hx
    have hU := hI hx
    have := ((((h0 x).fun_mul (hf.d3 x hU)).fun_sub ((h1 x).fun_mul (hf.d2 x hU))).fun_add
      ((h2 x).fun_mul (hf.d1 x hU))).fun_sub ((h3 x).fun_mul (hf.d0 x hU))
    convert this using 1
    ring
  have hfc : ContinuousOn f (Icc p q) := fun x hx =>
    (hf.d0 x (hI hx)).continuousAt.continuousWithinAt
  have h4c : ContinuousOn (fun x => P x * deriv (deriv (deriv (deriv f))) x) (Icc p q) :=
    hPc.continuousOn.mul (hf.c4.mono hI)
  have hFTC := integral_eq_sub_of_hasDerivAt hφ ((h4c.sub hfc).intervalIntegrable_of_Icc hpq)
  rw [intervalIntegral.integral_sub (h4c.intervalIntegrable_of_Icc hpq)
    (hfc.intervalIntegrable_of_Icc hpq)] at hFTC
  linarith

theorem iteratedDeriv_four_eq (f : ℝ → ℝ) :
    iteratedDeriv 4 f = deriv (deriv (deriv (deriv f))) := by
  rw [iteratedDeriv_eq_iterate]; rfl

/-! ### The elementary Simpson rule 3.5.6 -/

/-- Derivative chain of `(3u⁴ − 4hu³)/72`, `u = x − c`. -/
theorem simpsonKernel_derivs (c h : ℝ) (x : ℝ) :
    HasDerivAt (fun x => (3 * (x - c) ^ 4 - 4 * h * (x - c) ^ 3) / 72)
        ((12 * (x - c) ^ 3 - 12 * h * (x - c) ^ 2) / 72) x ∧
      HasDerivAt (fun x => (12 * (x - c) ^ 3 - 12 * h * (x - c) ^ 2) / 72)
        ((36 * (x - c) ^ 2 - 24 * h * (x - c)) / 72) x ∧
      HasDerivAt (fun x => (36 * (x - c) ^ 2 - 24 * h * (x - c)) / 72)
        ((72 * (x - c) - 24 * h) / 72) x ∧
      HasDerivAt (fun x => (72 * (x - c) - 24 * h) / 72) 1 x := by
  have hu : HasDerivAt (fun x => x - c) 1 x := (hasDerivAt_id' x).sub_const c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (((hu.pow 4).const_mul 3).fun_sub ((hu.pow 3).const_mul (4 * h))).div_const 72
    convert this using 1; norm_num; ring
  · have := (((hu.pow 3).const_mul 12).fun_sub ((hu.pow 2).const_mul (12 * h))).div_const 72
    convert this using 1; norm_num; ring
  · have := (((hu.pow 2).const_mul 36).fun_sub (hu.const_mul (24 * h))).div_const 72
    convert this using 1; norm_num; ring
  · have := ((hu.const_mul 72).sub_const (24 * h)).div_const 72
    convert this using 1; norm_num

/-- Derivative chain of `(3v⁴ − 4hv³)/72`, `v = c − x`. -/
theorem simpsonKernel_derivs' (c h : ℝ) (x : ℝ) :
    HasDerivAt (fun x => (3 * (c - x) ^ 4 - 4 * h * (c - x) ^ 3) / 72)
        (-((12 * (c - x) ^ 3 - 12 * h * (c - x) ^ 2) / 72)) x ∧
      HasDerivAt (fun x => -((12 * (c - x) ^ 3 - 12 * h * (c - x) ^ 2) / 72))
        ((36 * (c - x) ^ 2 - 24 * h * (c - x)) / 72) x ∧
      HasDerivAt (fun x => (36 * (c - x) ^ 2 - 24 * h * (c - x)) / 72)
        (-((72 * (c - x) - 24 * h) / 72)) x ∧
      HasDerivAt (fun x => -((72 * (c - x) - 24 * h) / 72)) 1 x := by
  have hv : HasDerivAt (fun x => c - x) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (((hv.pow 4).const_mul 3).fun_sub ((hv.pow 3).const_mul (4 * h))).div_const 72
    convert this using 1; norm_num; ring
  · have := ((((hv.pow 3).const_mul 12).fun_sub ((hv.pow 2).const_mul (12 * h))).div_const 72).neg
    convert this using 1; norm_num; ring
  · have := (((hv.pow 2).const_mul 36).fun_sub (hv.const_mul (24 * h))).div_const 72
    convert this using 1; norm_num; ring
  · have := (((hv.const_mul 72).sub_const (24 * h)).div_const 72).neg
    convert this using 1; norm_num

/-- **DLMF 3.5.6** (elementary Simpson's rule): for `f ∈ C⁴` on an open set containing `[a, b]`,
`h = ½(b − a)`, `∫ₐᵇ f = ⅓h(f(a) + 4f(½(a + b)) + f(b)) − (1/90) h⁵ f⁽⁴⁾(ξ)` with `a < ξ < b`. -/
theorem dlmf_3_5_6 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Ioo a b, ∫ x in a..b, f x = 1 / 3 * ((b - a) / 2) * (f a + 4 * f ((a + b) / 2) + f b) -
      1 / 90 * ((b - a) / 2) ^ 5 * iteratedDeriv 4 f ξ := by
  have hd := c4Data_of_contDiffOn hU hf
  set m := (a + b) / 2
  set h := (b - a) / 2
  have hh : 0 < h := by simp only [h]; linarith
  have hma : m - a = h := by simp only [m, h]; ring
  have hbm : b - m = h := by simp only [m, h]; ring
  have ham : a ≤ m := by linarith
  have hmb : m ≤ b := by linarith
  set f4 := deriv (deriv (deriv (deriv f)))
  -- the kernel `K = (3w⁴ − 4hw³)/72`, `w = h − |x − m|`
  set K : ℝ → ℝ := fun x => (3 * (h - |x - m|) ^ 4 - 4 * h * (h - |x - m|) ^ 3) / 72
  have hKL : EqOn (fun x => K x * f4 x)
      (fun x => (3 * (x - a) ^ 4 - 4 * h * (x - a) ^ 3) / 72 * f4 x) (uIcc a m) := fun x hx => by
    rw [uIcc_of_le ham] at hx
    simp only [K]
    rw [abs_of_nonpos (by linarith [hx.2]), show h - -(x - m) = x - a by linarith]
  have hKR : EqOn (fun x => K x * f4 x)
      (fun x => (3 * (b - x) ^ 4 - 4 * h * (b - x) ^ 3) / 72 * f4 x) (uIcc m b) := fun x hx => by
    rw [uIcc_of_le hmb] at hx
    simp only [K]
    rw [abs_of_nonneg (by linarith [hx.1]), show h - (x - m) = b - x by linarith]
  have hPL := peano4 hd ham ((Icc_subset_Icc_right hmb).trans hIU)
    (fun x => (simpsonKernel_derivs a h x).1) (fun x => (simpsonKernel_derivs a h x).2.1)
    (fun x => (simpsonKernel_derivs a h x).2.2.1) (fun x => (simpsonKernel_derivs a h x).2.2.2)
    (by fun_prop)
  have hPR := peano4 hd hmb ((Icc_subset_Icc_left ham).trans hIU)
    (fun x => (simpsonKernel_derivs' b h x).1) (fun x => (simpsonKernel_derivs' b h x).2.1)
    (fun x => (simpsonKernel_derivs' b h x).2.2.1) (fun x => (simpsonKernel_derivs' b h x).2.2.2)
    (by fun_prop)
  have hfc : ContinuousOn f (Icc a b) := fun x hx =>
    (hd.d0 x (hIU hx)).continuousAt.continuousWithinAt
  have h4c : ContinuousOn f4 (Icc a b) := hd.c4.mono hIU
  have hKc : Continuous K := by simp only [K]; fun_prop
  have hKf4 : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b →
      IntervalIntegrable (fun x => K x * f4 x) volume p q := fun hap hpq hqb =>
    (hKc.continuousOn.mul (h4c.mono (Icc_subset_Icc hap hqb))).intervalIntegrable_of_Icc hpq
  have hfi : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → IntervalIntegrable f volume p q :=
    fun hap hpq hqb => (hfc.mono (Icc_subset_Icc hap hqb)).intervalIntegrable_of_Icc hpq
  -- `∫ K f⁽⁴⁾ = ∫ f − ⅓h(f(a) + 4f(m) + f(b))`
  have hsplit : ∫ x in a..b, K x * f4 x =
      (∫ x in a..m, (3 * (x - a) ^ 4 - 4 * h * (x - a) ^ 3) / 72 * f4 x) +
        ∫ x in m..b, (3 * (b - x) ^ 4 - 4 * h * (b - x) ^ 3) / 72 * f4 x := by
    rw [← integral_add_adjacent_intervals (hKf4 le_rfl ham hmb) (hKf4 ham hmb le_rfl),
      integral_congr hKL, integral_congr hKR]
  have hfsplit : ∫ x in a..b, f x = (∫ x in a..m, f x) + ∫ x in m..b, f x :=
    (integral_add_adjacent_intervals (hfi le_rfl ham hmb) (hfi ham hmb le_rfl)).symm
  have hkey : ∫ x in a..b, K x * f4 x =
      (∫ x in a..b, f x) - 1 / 3 * h * (f a + 4 * f m + f b) := by
    rw [hsplit, hPL, hPR, hfsplit]
    simp only [hma, hbm, sub_self]
    ring
  -- `∫ K = −h⁵/90`
  have hKL' : EqOn K (fun x => (3 * (x - a) ^ 4 - 4 * h * (x - a) ^ 3) / 72) (uIcc a m) :=
    fun x hx => by
      rw [uIcc_of_le ham] at hx
      simp only [K]
      rw [abs_of_nonpos (by linarith [hx.2]), show h - -(x - m) = x - a by linarith]
  have hKR' : EqOn K (fun x => (3 * (b - x) ^ 4 - 4 * h * (b - x) ^ 3) / 72) (uIcc m b) :=
    fun x hx => by
      rw [uIcc_of_le hmb] at hx
      simp only [K]
      rw [abs_of_nonneg (by linarith [hx.1]), show h - (x - m) = b - x by linarith]
  have hAL : ∀ x ∈ uIcc a m, HasDerivAt (fun x => (3 / 5 * (x - a) ^ 5 - h * (x - a) ^ 4) / 72)
      ((3 * (x - a) ^ 4 - 4 * h * (x - a) ^ 3) / 72) x := fun x _ => by
    have hu := (hasDerivAt_id' x).sub_const a
    have := (((hu.pow 5).const_mul (3 / 5)).fun_sub ((hu.pow 4).const_mul h)).div_const 72
    convert this using 1; norm_num; ring
  have hAR : ∀ x ∈ uIcc m b, HasDerivAt (fun x => -((3 / 5 * (b - x) ^ 5 - h * (b - x) ^ 4) / 72))
      ((3 * (b - x) ^ 4 - 4 * h * (b - x) ^ 3) / 72) x := fun x _ => by
    have hv : HasDerivAt (fun x => b - x) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub b
    have := ((((hv.pow 5).const_mul (3 / 5)).fun_sub ((hv.pow 4).const_mul h)).div_const 72).neg
    convert this using 1; norm_num; ring
  have hKint : ∫ x in a..b, K x = -(h ^ 5 / 90) := by
    rw [← integral_add_adjacent_intervals (hKc.intervalIntegrable a m)
      (hKc.intervalIntegrable m b), integral_congr hKL', integral_congr hKR',
      integral_eq_sub_of_hasDerivAt hAL ((show Continuous fun x =>
        (3 * (x - a) ^ 4 - 4 * h * (x - a) ^ 3) / 72 by fun_prop).intervalIntegrable _ _),
      integral_eq_sub_of_hasDerivAt hAR ((show Continuous fun x =>
        (3 * (b - x) ^ 4 - 4 * h * (b - x) ^ 3) / 72 by fun_prop).intervalIntegrable _ _)]
    simp only [hma, hbm, sub_self]
    ring
  -- the mean value theorem with the weight `−K ≥ 0`
  have hw : ∀ x ∈ Icc a b, 0 ≤ h - |x - m| := fun x hx => by
    rw [sub_nonneg, abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hnegK : ∀ x, -K x = (h - |x - m|) ^ 3 * (4 * h - 3 * (h - |x - m|)) / 72 := fun x => by
    simp only [K]; ring
  obtain ⟨ξ, hξ, hmv⟩ := exists_mem_Ioo_integral_mul_eq (f := f4) (g := fun x => -K x) hab h4c
    hKc.neg.continuousOn
    (fun x hx => by
      rw [hnegK]
      have := hw x hx
      exact div_nonneg (mul_nonneg (pow_nonneg this 3) (by linarith [abs_nonneg (x - m)]))
        (by norm_num))
    (fun x hx => by
      rw [hnegK]
      have : 0 < h - |x - m| := by
        rw [sub_pos, abs_lt]; constructor <;> linarith [hx.1, hx.2]
      exact div_pos (mul_pos (pow_pos this 3) (by linarith [abs_nonneg (x - m)])) (by norm_num))
  have hneg : ∫ x in a..b, K x * f4 x = -∫ x in a..b, f4 x * -K x := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext x; ring
  have hKneg : ∫ x in a..b, -K x = h ^ 5 / 90 := by
    rw [intervalIntegral.integral_neg, hKint, neg_neg]
  refine ⟨ξ, hξ, ?_⟩
  rw [iteratedDeriv_four_eq]
  rw [hneg, hmv, hKneg] at hkey
  linarith

/-! ### The composite Simpson rule 3.5.7–3.5.8 -/

/-- The weights `1, 4, 2, 4, 2, …, 4, 1` of 3.5.7. -/
def simpsonWeight (n k : ℕ) : ℝ := if k = 0 ∨ k = n then 1 else if k % 2 = 1 then 4 else 2

/-- The composite Simpson sum `⅓h(f₀ + 4f₁ + 2f₂ + ⋯ + 4f_{n−1} + fₙ)`, `h = (b − a)/n`. -/
noncomputable def simpsonSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  1 / 3 * ((b - a) / n) * ∑ k ∈ range (n + 1), simpsonWeight n k * f (a + k * ((b - a) / n))

/-- The error `E_n(f)` of the composite Simpson rule. -/
noncomputable def simpsonError (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (∫ x in a..b, f x) - simpsonSum f a b n

/-- **DLMF 3.5.7**: `∫ₐᵇ f = ⅓h(f₀ + 4f₁ + 2f₂ + ⋯ + 4f_{n−1} + fₙ) + E_n(f)`. -/
theorem dlmf_3_5_7 (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    ∫ x in a..b, f x = simpsonSum f a b n + simpsonError f a b n := by
  rw [simpsonError]; ring

/-- The weighted sum over `2N + 1` nodes is the sum of the `N` panels. -/
theorem sum_simpsonWeight (g : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range (2 * N + 1), simpsonWeight (2 * N) k * g k =
      ∑ j ∈ range N, (g (2 * j) + 4 * g (2 * j + 1) + g (2 * j + 2)) := by
  set c : ℕ → ℝ := fun k => if k = 0 then 1 else if k % 2 = 1 then 4 else 2
  have hw : ∀ k < 2 * N, simpsonWeight (2 * N) k = c k := fun k hk => by
    simp only [simpsonWeight, c]
    by_cases h0 : k = 0
    · simp [h0]
    · simp only [h0, false_or, show k ≠ 2 * N by omega, ↓reduceIte]
  have hlast : simpsonWeight (2 * N) (2 * N) = 1 := by simp [simpsonWeight]
  rw [sum_range_succ, hlast, sum_congr rfl fun k hk => by rw [hw k (mem_range.mp hk)], one_mul]
  clear hw hlast
  induction N, hN using Nat.le_induction with
  | base => simp [c, sum_range_succ]
  | succ N hN ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ]
    have h2N : c (2 * N) = 2 := by simp only [c]; simp [show 2 * N ≠ 0 by omega]
    have h2N1 : c (2 * N + 1) = 4 := by simp only [c]; simp [Nat.add_mod]
    rw [h2N, h2N1, ← ih]
    ring

/-- **DLMF 3.5.8**: for `f ∈ C⁴` on an open set containing `[a, b]` and `n = 2N` even,
`E_n(f) = −((b − a)/180) h⁴ f⁽⁴⁾(ξ)` with `a < ξ < b`, `h = (b − a)/n`. -/
theorem dlmf_3_5_8 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 1 ≤ N) {U : Set ℝ}
    (hU : IsOpen U) (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Ioo a b, simpsonError f a b (2 * N) =
      -((b - a) / 180) * ((b - a) / (2 * N : ℕ)) ^ 4 * iteratedDeriv 4 f ξ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (b - a) / (2 * N : ℕ) with hh
  have hpos : 0 < h := div_pos (by linarith) (by positivity)
  have h2Nh : 2 * (N : ℝ) * h = b - a := by simp only [h]; push_cast; field_simp
  set x : ℕ → ℝ := fun k => a + k * h
  have hxs : ∀ k : ℕ, x (k + 1) = x k + h := fun k => by simp only [x]; push_cast; ring
  have hxe : x (2 * N) = b := by simp only [x]; push_cast; linarith
  have hxI : ∀ k ≤ 2 * N, x k ∈ Icc a b := fun k hk => by
    have hk' : (k : ℝ) ≤ 2 * N := by exact_mod_cast hk
    refine ⟨by simp only [x]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], ?_⟩
    simp only [x]; nlinarith
  have hsub : ∀ j ∈ range N, Icc (x (2 * j)) (x (2 * j + 2)) ⊆ Icc a b := fun j hj =>
    Icc_subset_Icc (hxI _ (by have := mem_range.mp hj; omega)).1
      (hxI _ (by have := mem_range.mp hj; omega)).2
  have hx2 : ∀ j : ℕ, x (2 * j + 2) = x (2 * j) + 2 * h := fun j => by
    rw [show 2 * j + 2 = 2 * j + 1 + 1 by ring, hxs, hxs]; ring
  have hloc : ∀ j ∈ range N, ∃ ξ ∈ Ioo (x (2 * j)) (x (2 * j + 2)),
      ∫ t in x (2 * j)..x (2 * j + 2), f t = 1 / 3 * h * (f (x (2 * j)) +
        4 * f (x (2 * j + 1)) + f (x (2 * j + 2))) - 1 / 90 * h ^ 5 * iteratedDeriv 4 f ξ :=
    fun j hj => by
      obtain ⟨ξ, hξ, he⟩ := dlmf_3_5_6 (by rw [hx2]; linarith) hU ((hsub j hj).trans hIU) hf
      refine ⟨ξ, hξ, ?_⟩
      rw [he, hx2, show (x (2 * j) + (x (2 * j) + 2 * h)) / 2 = x (2 * j + 1) by rw [hxs]; ring,
        show (x (2 * j) + 2 * h - x (2 * j)) / 2 = h by ring]
  choose! ξ hξ hloc using hloc
  have hfc : ContinuousOn f (Icc a b) := hf.continuousOn.mono hIU
  have hint : ∫ t in a..b, f t = ∑ j ∈ range N, ∫ t in x (2 * j)..x (2 * j + 2), f t := by
    have := sum_integral_adjacent_intervals (a := fun j : ℕ => x (2 * j)) (n := N) (f := f)
      (μ := volume) fun j hj => (hfc.mono (hsub j (mem_range.mpr hj))).intervalIntegrable_of_Icc
        (by rw [show 2 * (j + 1) = 2 * j + 2 by ring, hx2]; linarith)
    simp only [show ∀ j : ℕ, 2 * (j + 1) = 2 * j + 2 from fun j => by ring, mul_zero] at this
    rw [this]
    simp only [x, Nat.cast_zero, zero_mul, add_zero]
    rw [← hxe]
  have hξI : ∀ j ∈ range N, ξ j ∈ Ioo a b := fun j hj =>
    ⟨lt_of_le_of_lt (hxI _ (by have := mem_range.mp hj; omega)).1 (hξ j hj).1,
      lt_of_lt_of_le (hξ j hj).2 (hxI _ (by have := mem_range.mp hj; omega)).2⟩
  have hd4 : ContinuousOn (iteratedDeriv 4 f) (Icc a b) := by
    rw [iteratedDeriv_four_eq]; exact (c4Data_of_contDiffOn hU hf).c4.mono hIU
  obtain ⟨η, hη, hsum⟩ := exists_sum_eq_card_mul hd4 hN hξI
  refine ⟨η, hη, ?_⟩
  have hS : simpsonSum f a b (2 * N) = ∑ j ∈ range N, 1 / 3 * h * (f (x (2 * j)) +
      4 * f (x (2 * j + 1)) + f (x (2 * j + 2))) := by
    rw [simpsonSum, ← mul_sum, sum_simpsonWeight (fun k => f (x k)) hN]
  rw [simpsonError, hint, hS, sum_congr rfl hloc, sum_sub_distrib,
    ← Finset.mul_sum (range N) (fun j => iteratedDeriv 4 f (ξ j)) (1 / 90 * h ^ 5), hsum]
  rw [show 1 / 90 * h ^ 5 * (N * iteratedDeriv 4 f η) = (2 * N * h) / 180 * h ^ 4 *
    iteratedDeriv 4 f η by ring, h2Nh]
  ring

/-! ### Simpson's rule from two trapezoidal rules -/

theorem sum_range_even_odd (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range (2 * N), g k = ∑ j ∈ range N, (g (2 * j) + g (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- "Simpson's rule can be regarded as a combination of two trapezoidal rules": with `2N`
subintervals, `S_{2N} = (4 T_{2N} − T_N)/3` (step sizes `h` and `2h`). -/
theorem simpsonSum_eq_trapezoid (f : ℝ → ℝ) (a b : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    simpsonSum f a b (2 * N) =
      (4 * trapezoidSum f a b (2 * N) - trapezoidSum f a b N) / 3 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  set h := (b - a) / (2 * N : ℕ)
  set g : ℕ → ℝ := fun k => f (a + k * h)
  have hG : ∀ j : ℕ, f (a + j * ((b - a) / N)) = g (2 * j) := fun j => by
    simp only [g, h]; congr 1; push_cast; field_simp
  rw [simpsonSum, trapezoidSum, trapezoidSum, sum_simpsonWeight (fun k => g k) hN]
  simp only [hG]
  have hT1 : ∑ k ∈ range (2 * N + 1), f (a + k * ((b - a) / (2 * N : ℕ))) =
      ∑ j ∈ range N, (g (2 * j) + g (2 * j + 1)) + g (2 * N) := by
    rw [sum_range_succ, sum_range_even_odd (fun k => g k)]
  have hT2 : ∑ j ∈ range (N + 1), g (2 * j) = ∑ j ∈ range N, g (2 * j) + g (2 * N) :=
    sum_range_succ _ _
  have hshift : ∑ j ∈ range N, g (2 * j + 2) = ∑ j ∈ range N, g (2 * j) - g 0 + g (2 * N) := by
    have := sum_range_succ (fun j => g (2 * j)) N
    rw [sum_range_succ'] at this
    simp only [mul_zero, show ∀ j : ℕ, 2 * (j + 1) = 2 * j + 2 from fun j => by ring] at this
    linarith
  rw [hT1, hT2, sum_add_distrib, sum_add_distrib, sum_add_distrib, hshift, ← mul_sum]
  simp only [g, h, Nat.cast_zero, zero_mul, add_zero]
  have hb : a + ((2 * N : ℕ) : ℝ) * ((b - a) / (2 * N : ℕ)) = a + (N : ℝ) * ((b - a) / N) := by
    push_cast; field_simp
  rw [hb]
  rw [show (b - a) / (N : ℝ) = 2 * ((b - a) / (2 * N : ℕ)) by push_cast; field_simp]
  ring

end Azurite.DLMF
