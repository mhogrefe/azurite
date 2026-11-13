/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Bounds

/-!
# Explicit bounds for the Stirling remainder integrals `K_{2n}`

Supplement to DLMF §5.11 (for §5.21, computation of `Γ`): the existential constant of
`norm_stirlingK_le` made explicit for even index.

* `abs_bernoulliFun_two_mul_le`, `abs_periodicBernoulli_two_mul_le`: `|B̃_{2n}(t)| ≤ |B_{2n}|`
  (from the cosine Fourier series of the Bernoulli polynomials, all cosines `≤ 1`).
* `norm_stirlingK_two_mul_le`: `|K_{2n}(z)| ≤ |B_{2n}| / (sin^{2n}(½δ) (2n − 1)|z|^{2n−1})` in
  `|ph z| ≤ π − δ`.
* `norm_stirlingJ_sub_sum_le`: the remainder of Stirling's series after the `B_{2n}` term is at
  most `|B_{2n}| / (2n(2n − 1) sin^{2n}(½δ) |z|^{2n−1})`, i.e. the last included term times
  `sin^{−2n}(½δ)`. (The sharper "first neglected term" bounds are `dlmf_5_11_ii_real` and
  `dlmf_5_11_ii_complex`.)
-/

open Complex MeasureTheory Set
open scoped Real Nat

namespace Azurite.DLMF

/-- `|B_{2n}(x)| ≤ |B_{2n}|` on `[0, 1]`. -/
theorem abs_bernoulliFun_two_mul_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * n) x| ≤ |(bernoulli (2 * n) : ℝ)| := by
  have hx' := hasSum_one_div_nat_pow_mul_cos (k := n) (by omega) hx
  have h0 := hasSum_one_div_nat_pow_mul_cos (k := n) (by omega) (left_mem_Icc.mpr zero_le_one)
  have hle := hx'.norm_le_of_bounded h0 fun k => by
    rw [mul_zero, Real.cos_zero, mul_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ) ^ (2 * n))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval x =
      bernoulliFun (2 * n) x := rfl
  have hb0 : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval 0 =
      bernoulli (2 * n) := bernoulliFun_eval_zero _
  rw [hb, hb0, Real.norm_eq_abs] at hle
  set c : ℝ := (-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)! with hc
  have hc0 : 0 < |c| := by
    rw [hc, abs_div, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    positivity
  have hr : c * (bernoulli (2 * n) : ℝ) ≤ |c| * |(bernoulli (2 * n) : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  rw [abs_mul] at hle
  exact le_of_mul_le_mul_left (hle.trans hr) hc0

/-- `|B̃_{2n}(t)| ≤ |B_{2n}|` for the periodic Bernoulli functions. -/
theorem abs_periodicBernoulli_two_mul_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    |periodicBernoulli (2 * n) t| ≤ |(bernoulli (2 * n) : ℝ)| :=
  abs_bernoulliFun_two_mul_le hn ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- `|K_{2n}(z)| ≤ |B_{2n}| / (sin^{2n}(½δ) (2n − 1)|z|^{2n−1})` for `|ph z| ≤ π − δ`. -/
theorem norm_stirlingK_two_mul_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ ≤ π) (harg : |arg z| ≤ π - δ) :
    ‖stirlingK (2 * n) z‖ ≤
      |(bernoulli (2 * n) : ℝ)| /
        (Real.sin (δ / 2) ^ (2 * n) * ((2 * n - 1) * ‖z‖ ^ (2 * n - 1))) := by
  have h := (integrableOn_div_add_pow (measurable_periodicBernoulli (2 * n))
    (C := |(bernoulli (2 * n) : ℝ)|) (abs_periodicBernoulli_two_mul_le hn) hz hδ hδπ harg
    (m := 2 * n) (by omega)).2
  push_cast at h
  exact h

/-- Stirling's series 5.11.1 with the explicit remainder bound: after the terms up to `B_{2n}`,
`|J(z) − ∑_{j ≤ 2n−2} B_{j+2}/((j + 2)(j + 1)z^{j+1})| ≤
|B_{2n}| / (2n(2n − 1) sin^{2n}(½δ) |z|^{2n−1})` for `|ph z| ≤ π − δ`. -/
theorem norm_stirlingJ_sub_sum_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ ≤ π) (harg : |arg z| ≤ π - δ) :
    ‖stirlingJ z - ∑ j ∈ Finset.range (2 * n - 1),
        (bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1) * z ^ (j + 1))‖ ≤
      |(bernoulli (2 * n) : ℝ)| /
        (2 * n * (2 * n - 1) * Real.sin (δ / 2) ^ (2 * n) * ‖z‖ ^ (2 * n - 1)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := stirlingJ_eq_sum hz (2 * n - 2)
  rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega, show 2 * n - 2 + 2 = 2 * n by omega] at h
  have hK := norm_stirlingK_two_mul_le hn (slitPlane_ne_zero hz) hδ hδπ harg
  have hc : ((2 * n - 2 : ℕ) : ℂ) + 2 = ((2 * n : ℝ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h, sub_sub_cancel_left, norm_neg, hc, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 : (0 : ℝ) < 2 * n - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 (slitPlane_ne_zero hz)
  calc ‖stirlingK (2 * n) z‖ / (2 * n)
      ≤ |(bernoulli (2 * n) : ℝ)| / (Real.sin (δ / 2) ^ (2 * n) *
          ((2 * n - 1) * ‖z‖ ^ (2 * n - 1))) / (2 * n) := by gcongr
    _ = _ := by field_simp

end Azurite.DLMF
