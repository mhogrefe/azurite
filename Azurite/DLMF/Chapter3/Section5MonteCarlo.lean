/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Probability.Moments.Variance

/-!
# DLMF §3.5(x): the Monte Carlo method

"With `N` function values, the Monte Carlo method aims at an error of order `1/√N`,
independently of the dimension of the domain of integration." For samples `Xᵢ = f(Uᵢ)` (any
probability space, hence any dimension), pairwise independent, square integrable, with common mean
`m` and variance `σ²`, the estimate `(1/N) ∑ Xᵢ` (`mcMean`) is unbiased (`integral_mcMean`), has
variance `σ²/N` (`variance_mcMean`), standard deviation `σ/√N` (`sqrt_variance_mcMean`), and
`P(|mean − m| ≥ ε) ≤ σ²/(N ε²)` (`dlmf_3_5_x_monteCarlo`, Chebyshev).
-/

open MeasureTheory ProbabilityTheory Finset

namespace Azurite.DLMF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Monte Carlo estimate `(1/N) ∑_{i<N} Xᵢ`. -/
noncomputable def mcMean (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω

omit [IsProbabilityMeasure μ] in
theorem memLp_mcMean {X : ℕ → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (N : ℕ) :
    MemLp (mcMean X N) 2 μ := by
  unfold mcMean
  have := (memLp_finsetSum' (range N) fun i _ => hX i).const_mul (N : ℝ)⁻¹
  simpa [Finset.sum_apply] using this

/-- The estimate is unbiased. -/
theorem integral_mcMean {X : ℕ → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) {m : ℝ}
    (hm : ∀ i, ∫ ω, X i ω ∂μ = m) {N : ℕ} (hN : 0 < N) : ∫ ω, mcMean X N ω ∂μ = m := by
  unfold mcMean
  rw [integral_const_mul, integral_finsetSum _ fun i _ => (hX i).integrable one_le_two]
  simp only [hm, sum_const, card_range, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

omit [IsProbabilityMeasure μ] in
/-- `Var[(1/N) ∑ Xᵢ] = σ²/N`. -/
theorem variance_mcMean {X : ℕ → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ) {σ2 : ℝ}
    (hvar : ∀ i, variance (X i) μ = σ2) (N : ℕ) : variance (mcMean X N) μ = σ2 / N := by
  unfold mcMean
  rw [variance_const_mul]
  have hs := IndepFun.variance_sum (μ := μ) (s := range N) (fun i _ => hX i)
    (fun i _ j _ hij => hind hij)
  rw [show (fun ω => ∑ i ∈ range N, X i ω) = ∑ i ∈ range N, X i by
    ext ω; simp [Finset.sum_apply], hs, sum_congr rfl fun i _ => hvar i, sum_const, card_range,
    nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

omit [IsProbabilityMeasure μ] in
/-- The standard deviation is `σ/√N`: error of order `1/√N`. -/
theorem sqrt_variance_mcMean {X : ℕ → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ) {σ2 : ℝ}
    (hvar : ∀ i, variance (X i) μ = σ2) (N : ℕ) :
    √(variance (mcMean X N) μ) = √σ2 / √N := by
  rw [variance_mcMean hX hind hvar, Real.sqrt_div' _ (Nat.cast_nonneg N)]

/-- **DLMF §3.5(x)**, Monte Carlo: `P(|(1/N) ∑ Xᵢ − m| ≥ ε) ≤ σ²/(N ε²)`, for any probability
space (independently of the dimension). -/
theorem dlmf_3_5_x_monteCarlo {X : ℕ → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ) {m σ2 : ℝ}
    (hm : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ2) {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |mcMean X N ω - m|} ≤ ENNReal.ofReal (σ2 / (N * ε ^ 2)) := by
  have h := meas_ge_le_variance_div_sq (memLp_mcMean hX N) hε
  rw [variance_mcMean hX hind hvar, integral_mcMean hX hm hN, div_div] at h
  exact h

end Azurite.DLMF
