/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Romberg
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DLMF §3.5(iv): Interpolatory quadrature rules

* 3.5.15: `quadError` (`E_n(f) = ∫ₐᵇ f w − ∑ₖ wₖ f(xₖ)`), `IsInterpolatory` (`E_n(p) = 0` for
  every polynomial of degree `≤ n − 1`), `interpWeight` (`wₖ = ∫ₐᵇ ℓₖ w`, Mathlib's
  `Lagrange.basis`), `dlmf_3_5_15` (these weights give an interpolatory rule),
  `isInterpolatory_iff` (and they are the only ones), `quadError_interpWeight`
  (`E_n(f) = ∫ₐᵇ (f − Lₙf) w`), `isInterpolatory_of_pow` (exactness on `1, x, …, x^{n−1}`).
* Closed and open rules: `IsClosedRule`, `IsOpenRule`. Newton–Cotes: the trapezoidal rule
  (`trapezoid_isInterpolatory`, `trapezoid_isClosedRule`, `trapezoidSum_one_eq`) and Simpson's rule
  (`simpson_isInterpolatory`, `simpson_isClosedRule`, `simpsonSum_two_eq`); the midpoint rule
  (`midpoint_isInterpolatory`, `midpoint_isOpenRule`).
* Fejér's rule: nodes `ccNode n k = cos(kπ/n)`, `0 < k < n`, are the extrema of `T_n`
  (`fejer_nodes_isLocalExtr_iff`, from Mathlib's `isLocalExtr_T_real_iff`); `fejer_isOpenRule`,
  `fejer_isInterpolatory`.
* Clenshaw–Curtis 3.5.16–3.5.17: `ccG`, `ccB`, `ccWeight`; `range_eq_insert_fejer` (Fejér's nodes
  plus `±1`), `ccNode_isClosedRule`, `ccWeight_pos` (`∑_{j=1}^{J} 2/(4j² − 1) = 1 − 1/(2J + 1)`),
  `dlmf_3_5_16` (the rule is interpolatory and the weights are `∫₋₁¹ ℓₖ`). Proof: the discrete
  cosine sums `sum_range_two_mul_cos`, `sum_ccG_mul_cos` (`∑ₖ g_k cos(akπ/n) = 2n [2n ∣ a]`),
  `ccWeight_mul_cos` (the rule on `T_m`, `m ≤ n`), `integral_T_real`
  (`∫₋₁¹ T_m = 2/(1 − m²)` or `0`, via `x = cos θ`), and the basis `T₀, …, Tₙ` of polynomials of
  degree `≤ n` (`integral_eq_sum_ccWeight`).
-/

open Polynomial Finset Set MeasureTheory intervalIntegral Real

namespace Azurite.DLMF

variable {ι : Type*} [DecidableEq ι]

/-! ### Interpolatory rules 3.5.15 -/

/-- The error `E_n(f) = ∫ₐᵇ f w − ∑ₖ wₖ f(xₖ)` of the rule with nodes `v i` (`i ∈ s`) and weights
`c i` (3.5.15). -/
noncomputable def quadError (w : ℝ → ℝ) (a b : ℝ) (s : Finset ι) (v c : ι → ℝ) (f : ℝ → ℝ) :
    ℝ :=
  (∫ t in a..b, f t * w t) - ∑ i ∈ s, c i * f (v i)

/-- A rule is **interpolatory** when `E_n(f) = 0` for every polynomial of degree `≤ n − 1`,
`n = #s`. -/
def IsInterpolatory (w : ℝ → ℝ) (a b : ℝ) (s : Finset ι) (v c : ι → ℝ) : Prop :=
  ∀ p : ℝ[X], p.degree < #s → quadError w a b s v c (fun t => p.eval t) = 0

/-- The weights obtained by integrating the Lagrange basis polynomials against `w`:
`wₖ = ∫ₐᵇ ℓₖ(x) w(x) dx`. -/
noncomputable def interpWeight (w : ℝ → ℝ) (a b : ℝ) (s : Finset ι) (v : ι → ℝ) (i : ι) : ℝ :=
  ∫ t in a..b, (Lagrange.basis s v i).eval t * w t

theorem intervalIntegrable_eval_mul {w : ℝ → ℝ} {a b : ℝ} (hw : IntervalIntegrable w volume a b)
    (p : ℝ[X]) : IntervalIntegrable (fun t => p.eval t * w t) volume a b :=
  hw.continuousOn_mul p.continuous.continuousOn

/-- Integrating the Lagrange interpolation polynomial against `w`:
`∫ₐᵇ Lₙ(f) w = ∑ₖ wₖ f(xₖ)`. -/
theorem integral_interpolate_mul {w : ℝ → ℝ} {a b : ℝ} (hw : IntervalIntegrable w volume a b)
    (s : Finset ι) (v r : ι → ℝ) :
    ∫ t in a..b, (Lagrange.interpolate s v r).eval t * w t =
      ∑ i ∈ s, interpWeight w a b s v i * r i := by
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, sum_mul]
  rw [integral_finsetSum fun i _ => by
    simpa [mul_assoc] using (intervalIntegrable_eval_mul hw (Lagrange.basis s v i)).const_mul (r i)]
  refine sum_congr rfl fun i _ => ?_
  rw [interpWeight, ← intervalIntegral.integral_mul_const]
  congr 1; ext t; ring

/-- **DLMF 3.5.15**: with the weights `wₖ = ∫ ℓₖ w` the rule is interpolatory (exact for
polynomials of degree `≤ n − 1`). -/
theorem dlmf_3_5_15 {w : ℝ → ℝ} {a b : ℝ} (hw : IntervalIntegrable w volume a b)
    {s : Finset ι} {v : ι → ℝ} (hv : Set.InjOn v s) :
    IsInterpolatory w a b s v (interpWeight w a b s v) := by
  intro p hp
  rw [quadError, sub_eq_zero]
  conv_lhs => rw [Lagrange.eq_interpolate hv hp]
  rw [integral_interpolate_mul hw]

/-- The weights of an interpolatory rule are unique: they are `wₖ = ∫ ℓₖ w`. -/
theorem isInterpolatory_iff {w : ℝ → ℝ} {a b : ℝ} (hw : IntervalIntegrable w volume a b)
    {s : Finset ι} {v c : ι → ℝ} (hv : Set.InjOn v s) :
    IsInterpolatory w a b s v c ↔ ∀ i ∈ s, c i = interpWeight w a b s v i := by
  constructor
  · intro h i hi
    have := h (Lagrange.basis s v i) (by
      rw [Lagrange.degree_basis hv hi]
      exact_mod_cast Nat.sub_lt (card_pos.mpr ⟨i, hi⟩) one_pos)
    rw [quadError, sub_eq_zero, sum_eq_single_of_mem i hi fun j hj hji => by
      rw [Lagrange.eval_basis_of_ne hji.symm hj, mul_zero],
      Lagrange.eval_basis_self hv hi, mul_one] at this
    exact this.symm
  · intro h p hp
    have := dlmf_3_5_15 hw hv p hp
    rw [quadError] at this ⊢
    rwa [sum_congr rfl fun i hi => by rw [h i hi]]

/-- The error term is found by integrating the product of `f − Lₙ(f)` and `w`, `Lₙ(f)` the
Lagrange interpolation polynomial of degree `n − 1`. -/
theorem quadError_interpWeight {w f : ℝ → ℝ} {a b : ℝ} (hw : IntervalIntegrable w volume a b)
    (hf : IntervalIntegrable (fun t => f t * w t) volume a b) (s : Finset ι) (v : ι → ℝ) :
    quadError w a b s v (interpWeight w a b s v) f =
      ∫ t in a..b, (f t - (Lagrange.interpolate s v (fun i => f (v i))).eval t) * w t := by
  simp only [sub_mul]
  rw [integral_sub hf (intervalIntegrable_eval_mul hw _), integral_interpolate_mul hw, quadError]

/-! ### Closed and open rules -/

/-- A **closed** rule: the extreme members of the set of nodes are the endpoints `a` and `b`. -/
def IsClosedRule (a b : ℝ) (s : Finset ι) (v : ι → ℝ) : Prop :=
  (∀ i ∈ s, v i ∈ Icc a b) ∧ (∃ i ∈ s, v i = a) ∧ ∃ i ∈ s, v i = b

/-- An **open** rule: the nodes lie in the open interval `(a, b)`. -/
def IsOpenRule (a b : ℝ) (s : Finset ι) (v : ι → ℝ) : Prop :=
  ∀ i ∈ s, v i ∈ Ioo a b

omit [DecidableEq ι] in
/-- A rule that is exact for the monomials `1, x, …, x^{n−1}` is interpolatory. -/
theorem isInterpolatory_of_pow {w : ℝ → ℝ} {a b : ℝ} (hw : IntervalIntegrable w volume a b)
    {s : Finset ι} {v c : ι → ℝ}
    (h : ∀ m < #s, (∫ t in a..b, t ^ m * w t) = ∑ i ∈ s, c i * v i ^ m) :
    IsInterpolatory w a b s v c := by
  intro p hp
  by_cases hp0 : p = 0
  · subst hp0; simp [quadError]
  have hnd : p.natDegree < #s := (natDegree_lt_iff_degree_lt hp0).mpr hp
  rw [quadError, sub_eq_zero]
  simp only [eval_eq_sum_range' hnd, sum_mul]
  rw [integral_finsetSum fun m _ => by
    simpa [mul_assoc] using
      (intervalIntegrable_eval_mul hw (X ^ m)).const_mul (p.coeff m)]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  have := h m (mem_range.mp hm)
  rw [show (fun x => p.coeff m * x ^ m * w x) = fun x => p.coeff m * (x ^ m * w x) by
    ext; ring, intervalIntegral.integral_const_mul, this, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-! ### Newton–Cotes (closed) and midpoint (open) rules -/

/-- The elementary trapezoidal rule 3.5.1 is the closed interpolatory rule with nodes `a, b`. -/
theorem trapezoid_isInterpolatory (a b : ℝ) :
    IsInterpolatory (fun _ => 1) a b (range 2) (fun i => a + i * (b - a))
      (fun _ => (b - a) / 2) := by
  refine isInterpolatory_of_pow intervalIntegrable_const fun m hm => ?_
  rw [card_range] at hm
  simp only [mul_one, integral_pow]
  interval_cases m <;> simp [sum_range_succ] <;> ring

theorem trapezoid_isClosedRule {a b : ℝ} (hab : a ≤ b) :
    IsClosedRule a b (range 2) (fun i => a + i * (b - a)) :=
  ⟨fun i hi => by
    simp only [Finset.mem_range] at hi
    interval_cases i <;> simp [hab],
   ⟨0, by simp⟩, ⟨1, by simp⟩⟩

theorem trapezoidSum_one_eq (f : ℝ → ℝ) (a b : ℝ) :
    trapezoidSum f a b 1 = ∑ i ∈ range 2, (b - a) / 2 * f (a + i * (b - a)) := by
  simp [trapezoidSum, sum_range_succ]
  ring

/-- Simpson's rule 3.5.6 is the closed interpolatory rule with nodes `a, ½(a + b), b`. -/
theorem simpson_isInterpolatory (a b : ℝ) :
    IsInterpolatory (fun _ => 1) a b (range 3) (fun i => a + i * ((b - a) / 2))
      (fun i => 1 / 3 * ((b - a) / 2) * simpsonWeight 2 i) := by
  refine isInterpolatory_of_pow intervalIntegrable_const fun m hm => ?_
  rw [card_range] at hm
  simp only [mul_one, integral_pow]
  interval_cases m <;> simp [sum_range_succ, simpsonWeight] <;> ring

theorem simpson_isClosedRule {a b : ℝ} (hab : a ≤ b) :
    IsClosedRule a b (range 3) (fun i => a + i * ((b - a) / 2)) :=
  ⟨fun i hi => by
    simp only [Finset.mem_range] at hi
    interval_cases i <;> simp only [Set.mem_Icc] <;> constructor <;> push_cast <;> linarith,
   ⟨0, by simp⟩, ⟨2, by simp; ring⟩⟩

theorem simpsonSum_two_eq (f : ℝ → ℝ) (a b : ℝ) :
    simpsonSum f a b 2 = ∑ i ∈ range 3,
      1 / 3 * ((b - a) / 2) * simpsonWeight 2 i * f (a + i * ((b - a) / 2)) := by
  rw [simpsonSum, mul_sum]
  push_cast
  exact sum_congr rfl fun i _ => by ring

/-- The midpoint rule `∫ₐᵇ f ≈ (b − a) f(½(a + b))` is an open interpolatory rule. -/
theorem midpoint_isInterpolatory (a b : ℝ) :
    IsInterpolatory (fun _ => 1) a b (range 1) (fun _ => (a + b) / 2) (fun _ => b - a) := by
  refine isInterpolatory_of_pow intervalIntegrable_const fun m hm => ?_
  rw [card_range] at hm
  interval_cases m
  simp

theorem midpoint_isOpenRule {a b : ℝ} (hab : a < b) :
    IsOpenRule a b (range 1) (fun _ => (a + b) / 2) :=
  fun _ _ => ⟨by linarith, by linarith⟩

/-! ### Fejér and Clenshaw–Curtis: discrete cosine sums -/

/-- The nodes `x_k = cos(kπ/n)`. -/
noncomputable def ccNode (n k : ℕ) : ℝ := Real.cos (k * π / n)

/-- `g_k` of 3.5.17. -/
noncomputable def ccG (n k : ℕ) : ℝ := if k = 0 ∨ k = n then 1 else 2

/-- `b_j` of 3.5.17 (`b_j = 1` when `j = ½n`). -/
noncomputable def ccB (n j : ℕ) : ℝ := if 2 * j = n then 1 else 2

theorem sum_range_two_mul_cos {n : ℕ} (hn : 0 < n) (a : ℤ) :
    ∑ k ∈ range (2 * n), Real.cos (a * k * π / n) =
      if (2 * n : ℤ) ∣ a then (2 * n : ℝ) else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    rw [sum_congr rfl fun (k : ℕ) _ => show Real.cos (((2 * n * t : ℤ) : ℝ) * k * π / n) = 1 by
      rw [show ((2 * n * t : ℤ) : ℝ) * k * π / n = ((t * k : ℤ) : ℝ) * (2 * π) by
        push_cast; field_simp]
      exact Real.cos_int_mul_two_pi _]
    simp
  · set ζ := Complex.exp (a * π / n * Complex.I)
    have hζ : ζ ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
      apply h
      refine ⟨m, ?_⟩
      have : (a : ℂ) = 2 * n * m := by
        have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
        have := hm
        field_simp at this
        linear_combination this
      exact_mod_cast this
    have hζn : ζ ^ (2 * n) = 1 := by
      have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      rw [← Complex.exp_nat_mul, show ((2 * n : ℕ) : ℂ) * (a * π / n * Complex.I) =
        (a : ℂ) * (2 * π * Complex.I) by push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I a
    have hterm : ∀ k : ℕ, Real.cos (a * k * π / n) = (ζ ^ k).re := fun k => by
      rw [← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
      congr 2
      push_cast; ring
    rw [sum_congr rfl fun k _ => hterm k, ← Complex.re_sum, geom_sum_eq hζ, hζn]
    simp

theorem sum_ccG_mul_cos {n : ℕ} (hn : 0 < n) (a : ℤ) :
    ∑ k ∈ range (n + 1), ccG n k * Real.cos (a * k * π / n) =
      if (2 * n : ℤ) ∣ a then (2 * n : ℝ) else 0 := by
  rw [← sum_range_two_mul_cos hn a]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set c : ℕ → ℝ := fun k => Real.cos (a * k * π / n) with hc
  have hrefl : ∀ k < n, c (n + k) = c (n - k) := fun k hk => by
    simp only [hc]
    rw [show ((n - k : ℕ) : ℝ) = n - k by push_cast [hk.le]; ring,
      show (a : ℝ) * ((n - k : ℝ)) * π / n = -((a : ℝ) * ((n + k : ℕ) : ℝ) * π / n) + a * (2 * π) by
        push_cast; field_simp; ring,
      Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have h2 : ∑ k ∈ range (2 * n), c k = ∑ k ∈ range n, c k + ∑ k ∈ range n, c (k + 1) := by
    rw [two_mul, sum_range_add, sum_congr rfl fun k hk => hrefl k (mem_range.mp hk),
      ← sum_range_reflect (fun k => c (k + 1)) n]
    congr 1
    exact sum_congr rfl fun k hk => by congr 1; have := mem_range.mp hk; omega
  rw [h2]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ, sum_range_succ', sum_range_succ' (fun k => c k), sum_range_succ]
  have hg : ∀ k ∈ range m, ccG (m + 1) (k + 1) = 2 := fun k hk => by
    have := mem_range.mp hk
    simp only [ccG, show ¬ (k + 1 = 0 ∨ k + 1 = m + 1) by omega, ↓reduceIte]
  rw [sum_congr rfl fun k hk => by rw [hg k hk]]
  simp only [ccG, ↓reduceIte, true_or, or_true]
  rw [← mul_sum]
  ring

/-! ### Clenshaw–Curtis weights 3.5.16–3.5.17 -/

/-- **DLMF 3.5.16**: the Clenshaw–Curtis weights
`w_k = (g_k/n)(1 − ∑_{j=1}^{⌊n/2⌋} b_j/(4j² − 1) cos(2jkπ/n))`. -/
noncomputable def ccWeight (n k : ℕ) : ℝ :=
  ccG n k / n * (1 - ∑ j ∈ Icc 1 (n / 2),
    ccB n j / (4 * j ^ 2 - 1) * Real.cos (2 * j * k * π / n))

/-- `∫₋₁¹ T_m(x) dx`. -/
noncomputable def chebInt (m : ℕ) : ℝ := if Even m then 2 / (1 - m ^ 2) else 0

theorem dvd_two_mul_iff_eq_zero {n : ℕ} {x : ℤ} (h1 : -(2 * n : ℤ) < x) (h2 : x < 2 * n) :
    (2 * n : ℤ) ∣ x ↔ x = 0 :=
  ⟨fun h => Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨h1, h2⟩), fun h => h ▸ dvd_zero _⟩

theorem ccWeight_mul_cos {n : ℕ} (hn : 0 < n) {m : ℕ} (hm : m ≤ n) :
    ∑ k ∈ range (n + 1), ccWeight n k * Real.cos (m * (k * π / n)) = chebInt m := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set β : ℕ → ℝ := fun j => ccB n j / (4 * j ^ 2 - 1)
  set D : ℤ → ℝ := fun a => ∑ k ∈ range (n + 1), ccG n k * Real.cos (a * k * π / n)
  have hexp : ∀ k, ccWeight n k * Real.cos (m * (k * π / n)) = 1 / n * (ccG n k *
      Real.cos (((m : ℤ) : ℝ) * k * π / n) - ∑ j ∈ Icc 1 (n / 2), β j * (1 / 2) *
        (ccG n k * Real.cos (((2 * j + m : ℤ) : ℝ) * k * π / n) +
          ccG n k * Real.cos (((2 * j - m : ℤ) : ℝ) * k * π / n))) := fun k => by
    have hprod : ∀ j : ℕ, Real.cos (((2 * j + m : ℤ) : ℝ) * k * π / n) +
        Real.cos (((2 * j - m : ℤ) : ℝ) * k * π / n) =
          2 * (Real.cos (2 * j * k * π / n) * Real.cos (m * (k * π / n))) := fun j => by
      rw [show ((2 * j + m : ℤ) : ℝ) * k * π / n = 2 * j * k * π / n + m * (k * π / n) by
          push_cast; ring,
        show ((2 * j - m : ℤ) : ℝ) * k * π / n = 2 * j * k * π / n - m * (k * π / n) by
          push_cast; ring, Real.cos_add, Real.cos_sub]
      ring
    rw [show Real.cos (((m : ℤ) : ℝ) * k * π / n) = Real.cos (m * (k * π / n)) by
      congr 1; push_cast; ring]
    simp only [← mul_add, hprod]
    rw [show ∑ j ∈ Icc 1 (n / 2), β j * (1 / 2) * (ccG n k * (2 * (Real.cos (2 * j * k * π / n) *
        Real.cos (m * (k * π / n))))) = ccG n k * Real.cos (m * (k * π / n)) *
          ∑ j ∈ Icc 1 (n / 2), β j * Real.cos (2 * j * k * π / n) by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring]
    simp only [ccWeight, β]
    ring
  rw [sum_congr rfl fun k _ => hexp k, ← mul_sum, sum_sub_distrib, sum_comm]
  simp only [← mul_sum, mul_add, sum_add_distrib]
  have hD : ∀ a : ℤ, ∑ k ∈ range (n + 1), ccG n k * Real.cos (a * k * π / n) =
      if (2 * n : ℤ) ∣ a then (2 * n : ℝ) else 0 := sum_ccG_mul_cos hn
  simp only [hD]
  have hsum : ∀ j ∈ Finset.Icc 1 (n / 2),
      β j * (1 / 2) * (if (2 * n : ℤ) ∣ (2 * j + m : ℤ) then (2 * n : ℝ) else 0) +
        β j * (1 / 2) * (if (2 * n : ℤ) ∣ (2 * j - m : ℤ) then (2 * n : ℝ) else 0) =
      if 2 * j = m then (2 * n : ℝ) / (4 * (j : ℝ) ^ 2 - 1) else 0 := fun j hj => by
    have hj := Finset.mem_Icc.mp hj
    have h2j : 2 * j ≤ n := by omega
    have hA : (2 * n : ℤ) ∣ (2 * j + m : ℤ) ↔ 2 * j + m = 2 * n := by
      rw [← dvd_sub_self_right, dvd_two_mul_iff_eq_zero (by omega) (by omega)]; omega
    have hB : (2 * n : ℤ) ∣ (2 * j - m : ℤ) ↔ 2 * j = m := by
      rw [dvd_two_mul_iff_eq_zero (by omega) (by omega)]; omega
    simp only [hA, hB, β, ccB]
    split_ifs <;> first | omega | (field_simp; ring)
  rw [← sum_add_distrib, sum_congr rfl hsum]
  have hDm : (2 * n : ℤ) ∣ (m : ℤ) ↔ m = 0 := by
    rw [dvd_two_mul_iff_eq_zero (by omega) (by omega)]; omega
  simp only [hDm, chebInt]
  rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · subst ht
      rw [sum_eq_zero fun j hj => by
        have := (Finset.mem_Icc.mp hj).1; simp only [ite_eq_right_iff]; omega]
      simp; field_simp
    · rw [sum_eq_single_of_mem t (Finset.mem_Icc.mpr ⟨ht0, by omega⟩) fun j _ hjt => by
        simp only [ite_eq_right_iff]; omega]
      simp only [show 2 * t = m by omega, ↓reduceIte, show m ≠ 0 by omega,
        show Even m from ⟨t, ht⟩]
      subst ht
      push_cast
      have : (4 * (t : ℝ) ^ 2 - 1) ≠ 0 := by
        have : (1 : ℝ) ≤ t := by exact_mod_cast ht0
        nlinarith
      rw [show (1 : ℝ) - ((t : ℝ) + t) ^ 2 = -(4 * (t : ℝ) ^ 2 - 1) by ring]
      field_simp
      ring
  · rw [sum_eq_zero fun j _ => by simp only [ite_eq_right_iff]; omega]
    simp only [show m ≠ 0 by omega, ↓reduceIte, show ¬ Even m from Nat.not_even_iff_odd.mpr ⟨t, ht⟩]
    simp

theorem integral_sin_mul_zero_pi (c : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.sin (c * θ) = c⁻¹ * (1 - Real.cos (c * π)) := by
  by_cases hc : c = 0
  · simp [hc]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin, smul_eq_mul,
    mul_zero, Real.cos_zero]

/-- `∫₋₁¹ g(x) dx = ∫₀^π g(cos θ) sin θ dθ`. -/
theorem integral_neg_one_one_eq {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x in (-1 : ℝ)..1, g x = ∫ θ in (0 : ℝ)..π, g (Real.cos θ) * Real.sin θ := by
  have hsub := integral_comp_mul_deriv (a := 0) (b := π) (f := Real.cos)
    (f' := fun x => -Real.sin x) (fun x _ => Real.hasDerivAt_cos x)
    Real.continuous_sin.neg.continuousOn hg
  rw [Real.cos_zero, Real.cos_pi] at hsub
  rw [integral_symm, ← hsub]
  simp only [Function.comp, mul_neg, intervalIntegral.integral_neg, neg_neg]

/-- `∫₋₁¹ T_m(x) dx = 2/(1 − m²)` for even `m` and `0` for odd `m`. -/
theorem integral_T_real (m : ℕ) : ∫ x in (-1 : ℝ)..1, (Chebyshev.T ℝ m).eval x = chebInt m := by
  rw [integral_neg_one_one_eq (Polynomial.continuous _)]
  simp only [Chebyshev.T_real_cos, Int.cast_natCast]
  have hprod : ∀ θ : ℝ, Real.cos (m * θ) * Real.sin θ =
      1 / 2 * Real.sin ((1 + m) * θ) + 1 / 2 * Real.sin ((1 - m) * θ) := fun θ => by
    rw [add_mul, sub_mul, one_mul, Real.sin_add, Real.sin_sub]; ring
  simp only [hprod]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_mul_zero_pi, integral_sin_mul_zero_pi,
    show (1 + (m : ℝ)) * π = m * π + π by ring, show (1 - (m : ℝ)) * π = π - m * π by ring,
    Real.cos_add_pi, Real.cos_pi_sub, Real.cos_nat_mul_pi, chebInt]
  rcases Nat.even_or_odd m with hm | hm
  · simp only [hm, ↓reduceIte, hm.neg_one_pow]
    have h1 : (1 + (m : ℝ)) ≠ 0 := by positivity
    have h2 : (1 - (m : ℝ)) ≠ 0 := by
      intro h
      have : m = 1 := by exact_mod_cast (by linarith : (m : ℝ) = 1)
      exact Nat.not_even_one (this ▸ hm)
    have h3 : (1 - (m : ℝ) ^ 2) ≠ 0 := by
      rw [show (1 - (m : ℝ) ^ 2) = (1 + m) * (1 - m) by ring]; exact mul_ne_zero h1 h2
    field_simp
    ring
  · simp only [Nat.not_even_iff_odd.mpr hm, ↓reduceIte, hm.neg_one_pow]
    ring

/-- The Clenshaw–Curtis rule integrates polynomials of degree `≤ n` exactly (via the basis
`T₀, …, Tₙ`). -/
theorem integral_eq_sum_ccWeight {n : ℕ} (hn : 0 < n) {P : ℝ[X]} (hP : P.degree < (n + 1 : ℕ)) :
    ∫ x in (-1 : ℝ)..1, P.eval x = ∑ k ∈ range (n + 1), ccWeight n k * P.eval (ccNode n k) := by
  have hmem : P ∈ degreeLT ℝ (n + 1) := mem_degreeLT.mpr hP
  rw [← Sequence.span_degreeLT (Chebyshev.chebyshevTsequence ℝ) (by simp)] at hmem
  clear hP
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [Set.mem_Iio] at hm
    change ∫ x in (-1 : ℝ)..1, (Chebyshev.T ℝ m).eval x =
      ∑ k ∈ range (n + 1), ccWeight n k * (Chebyshev.T ℝ m).eval (ccNode n k)
    rw [integral_T_real, ← ccWeight_mul_cos hn (by omega)]
    refine sum_congr rfl fun k _ => ?_
    rw [ccNode, Chebyshev.T_real_cos]
    push_cast
    ring_nf
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [eval_add, mul_add, sum_add_distrib]
    rw [intervalIntegral.integral_add ((Polynomial.continuous _).intervalIntegrable _ _)
      ((Polynomial.continuous _).intervalIntegrable _ _), hx, hy]
  | smul c x _ hx =>
    simp only [eval_smul, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul, hx, mul_sum]
    exact sum_congr rfl fun k _ => by ring

theorem ccNode_mem_Icc_zero_pi {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (k : ℝ) * π / n ∈ Icc 0 π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn0, mul_comm π]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) pi_pos.le

theorem ccNode_injOn {n : ℕ} (hn : 0 < n) : Set.InjOn (ccNode n) (range (n + 1) : Finset ℕ) := by
  intro i hi j hj h
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have := Real.injOn_cos (ccNode_mem_Icc_zero_pi hn (by omega : i ≤ n))
    (ccNode_mem_Icc_zero_pi hn (by omega : j ≤ n)) h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [div_left_inj' hn0, mul_left_inj' pi_ne_zero] at this
  exact_mod_cast this

/-- **DLMF 3.5.16–3.5.17**: the Clenshaw–Curtis rule with nodes `x_k = cos(kπ/n)`,
`k = 0, 1, …, n`, and weights `ccWeight` is interpolatory on `[−1, 1]` (weight `1`), so its
weights are the interpolatory weights `∫₋₁¹ ℓₖ`. -/
theorem dlmf_3_5_16 {n : ℕ} (hn : 0 < n) :
    IsInterpolatory (fun _ => 1) (-1) 1 (range (n + 1)) (ccNode n) (ccWeight n) ∧
      ∀ k ∈ range (n + 1),
        ccWeight n k = interpWeight (fun _ => 1) (-1) 1 (range (n + 1)) (ccNode n) k := by
  have h : IsInterpolatory (fun _ => 1) (-1) 1 (range (n + 1)) (ccNode n) (ccWeight n) := by
    intro p hp
    rw [card_range] at hp
    rw [quadError, sub_eq_zero]
    simp only [mul_one]
    exact integral_eq_sum_ccWeight hn hp
  exact ⟨h, (isInterpolatory_iff intervalIntegrable_const (ccNode_injOn hn)).mp h⟩

theorem sum_two_div_four_sq_sub_one (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (2 : ℝ) / (4 * j ^ 2 - 1) = 1 - 1 / (2 * (J : ℝ) + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1), ih]
    have h1 : (2 * (J : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (4 * ((J + 1 : ℕ) : ℝ) ^ 2 - 1) ≠ 0 := by
      push_cast; have : (0 : ℝ) ≤ J := J.cast_nonneg; nlinarith
    have h3 : (2 * ((J + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- The Clenshaw–Curtis weights are positive. -/
theorem ccWeight_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < ccWeight n k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : 0 < ccG n k := by unfold ccG; split_ifs <;> norm_num
  refine mul_pos (div_pos hG hn0) (sub_pos.mpr ?_)
  have hbound : ∀ j ∈ Finset.Icc 1 (n / 2), |ccB n j / (4 * (j : ℝ) ^ 2 - 1) *
      Real.cos (2 * j * k * π / n)| ≤ 2 / (4 * (j : ℝ) ^ 2 - 1) := fun j hj => by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hd : 0 < 4 * (j : ℝ) ^ 2 - 1 := by nlinarith
    have hB : 0 < ccB n j ∧ ccB n j ≤ 2 := by unfold ccB; split_ifs <;> norm_num
    rw [abs_mul, abs_div, abs_of_pos hB.1, abs_of_pos hd]
    calc ccB n j / (4 * (j : ℝ) ^ 2 - 1) * |Real.cos (2 * j * k * π / n)|
        ≤ ccB n j / (4 * (j : ℝ) ^ 2 - 1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (div_pos hB.1 hd).le
      _ ≤ 2 / (4 * (j : ℝ) ^ 2 - 1) := by
          rw [mul_one]; exact div_le_div_of_nonneg_right hB.2 hd.le
  calc ∑ j ∈ Finset.Icc 1 (n / 2), ccB n j / (4 * (j : ℝ) ^ 2 - 1) * Real.cos (2 * j * k * π / n)
      ≤ ∑ j ∈ Finset.Icc 1 (n / 2), 2 / (4 * (j : ℝ) ^ 2 - 1) :=
        sum_le_sum fun j hj => (le_abs_self _).trans (hbound j hj)
    _ = 1 - 1 / (2 * ((n / 2 : ℕ) : ℝ) + 1) := sum_two_div_four_sq_sub_one _
    _ < 1 := by
        have : 0 < 1 / (2 * ((n / 2 : ℕ) : ℝ) + 1) := by positivity
        linarith

/-- The Clenshaw–Curtis rule is closed: its extreme nodes are `x_n = −1` and `x₀ = 1`. -/
theorem ccNode_isClosedRule {n : ℕ} (hn : 0 < n) :
    IsClosedRule (-1) 1 (range (n + 1)) (ccNode n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  refine ⟨fun k _ => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩, ⟨n, by simp, ?_⟩,
    ⟨0, by simp, by simp [ccNode]⟩⟩
  rw [ccNode, show (n : ℝ) * π / n = π by field_simp, Real.cos_pi]

/-! ### Fejér's rule -/

/-- The nodes of Fejér's rule, `cos(kπ/n)` for `0 < k < n`, are the extrema of `T_n` (the
critical points in `(−1, 1)`). -/
theorem fejer_nodes_isLocalExtr_iff {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    IsLocalExtr (Chebyshev.T ℝ n).eval x ↔ ∃ k ∈ Finset.Ioo 0 n, x = ccNode n k :=
  Chebyshev.isLocalExtr_T_real_iff hn x

/-- Fejér's rule is open: its nodes lie in `(−1, 1)`. -/
theorem fejer_isOpenRule {n : ℕ} : IsOpenRule (-1) 1 (Finset.Ioo 0 n) (ccNode n) := by
  intro k hk
  obtain ⟨hk0, hkn⟩ := Finset.mem_Ioo.mp hk
  have hn : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have h1 : 0 < (k : ℝ) * π / n := by positivity
  have h2 : (k : ℝ) * π / n < π := by
    rw [div_lt_iff₀ hn0, mul_comm π]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hkn) pi_pos
  constructor
  · rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h1.le le_rfl h2
  · rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl h2.le h1

/-- Fejér's rule (interpolatory weights `∫₋₁¹ ℓₖ`) is an open interpolatory rule. -/
theorem fejer_isInterpolatory {n : ℕ} (hn : 0 < n) :
    IsInterpolatory (fun _ => 1) (-1) 1 (Finset.Ioo 0 n) (ccNode n)
      (interpWeight (fun _ => 1) (-1) 1 (Finset.Ioo 0 n) (ccNode n)) :=
  dlmf_3_5_15 intervalIntegrable_const ((ccNode_injOn hn).mono fun k hk => by
    simp only [Finset.coe_Ioo, Set.mem_Ioo] at hk
    simp only [Finset.coe_range, Set.mem_Iio]; omega)

/-- Adding `−1` and `1` (`k = n` and `k = 0`) to Fejér's nodes gives the Clenshaw–Curtis
nodes. -/
theorem range_eq_insert_fejer {n : ℕ} (hn : 0 < n) :
    range (n + 1) = insert 0 (insert n (Finset.Ioo 0 n)) := by
  ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]; omega

end Azurite.DLMF
