/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Holomorphic parametric integrals

If `z ↦ F(z, t)` is holomorphic for every `t` and `‖F(z, t)‖ ≤ g(t)` with `g` integrable,
uniformly for `z` near `z₀`, then `z ↦ ∫ F(z, t) dμ(t)` is holomorphic near `z₀`. The derivative
bound needed by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` comes from Cauchy's estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), so only `F` itself has to be bounded.
Used for the analytic continuations in §5.12.
-/

open Complex Filter Topology Set MeasureTheory

namespace Azurite.DLMF

/-- **Holomorphy of a parametric integral** from a bound on the integrand alone. -/
theorem hasDerivAt_integral_of_holo {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F F' : ℂ → α → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {g : α → ℝ} (hg : Integrable g μ)
    (hm : ∀ z ∈ Metric.ball z₀ r, AEStronglyMeasurable (F z) μ)
    (hm' : AEStronglyMeasurable (F' z₀) μ)
    (hd : ∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ (2 * r), HasDerivAt (F · t) (F' z t) z)
    (hb : ∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ (2 * r), ‖F z t‖ ≤ g t) :
    HasDerivAt (fun z => ∫ t, F z t ∂μ) (∫ t, F' z₀ t ∂μ) z₀ := by
  have hz₀ : z₀ ∈ Metric.closedBall z₀ (2 * r) := Metric.mem_closedBall_self (by linarith)
  have hint : Integrable (F z₀) μ :=
    hg.mono' (hm z₀ (Metric.mem_ball_self hr)) (hb.mono fun t ht => ht z₀ hz₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := z₀) (bound := fun t => g t / r) (Metric.ball_mem_nhds z₀ hr)
    (eventually_nhds_iff.mpr ⟨Metric.ball z₀ r, hm, Metric.isOpen_ball, Metric.mem_ball_self hr⟩)
    hint hm' ?_ (hg.div_const r) ?_
  · exact key.2
  · filter_upwards [hd, hb] with t hdt hbt z hz
    have hsub : Metric.closedBall z r ⊆ Metric.closedBall z₀ (2 * r) := by
      intro w hw
      rw [Metric.mem_closedBall] at hw ⊢
      have := Metric.mem_ball.mp hz
      linarith [dist_triangle w z z₀]
    have hdc : DiffContOnCl ℂ (F · t) (Metric.ball z r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hr.ne']
      exact fun w hw => (hdt w (hsub hw)).differentiableAt.differentiableWithinAt
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
      (fun w hw => hbt w (hsub (Metric.sphere_subset_closedBall hw)))
    rwa [(hdt z (hsub (Metric.mem_closedBall_self hr.le))).deriv] at h
  · filter_upwards [hd] with t hdt z hz
    refine hdt z ?_
    have := Metric.mem_ball.mp hz
    rw [Metric.mem_closedBall]
    linarith

/-- `z ↦ ∫ F(z, t) dμ(t)` is holomorphic on an open set `U` when every point of `U` has a
neighborhood ball on which `F` is holomorphic and dominated by an integrable function. -/
theorem differentiableOn_integral_of_holo {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F F' : ℂ → α → ℂ} {U : Set ℂ}
    (hm : ∀ z ∈ U, AEStronglyMeasurable (F z) μ) (hm' : ∀ z ∈ U, AEStronglyMeasurable (F' z) μ)
    (hloc : ∀ z₀ ∈ U, ∃ r > 0, Metric.ball z₀ r ⊆ U ∧ ∃ g : α → ℝ, Integrable g μ ∧
      (∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ (2 * r), HasDerivAt (F · t) (F' z t) z) ∧
      ∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ (2 * r), ‖F z t‖ ≤ g t) :
    DifferentiableOn ℂ (fun z => ∫ t, F z t ∂μ) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hU, g, hg, hd, hb⟩ := hloc z₀ hz₀
  exact (hasDerivAt_integral_of_holo hr hg (fun z hz => hm z (hU hz)) (hm' z₀ hz₀) hd hb)
    |>.differentiableAt.differentiableWithinAt

/-- Entire version of `differentiableOn_integral_of_holo`. -/
theorem differentiable_integral_of_holo {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F F' : ℂ → α → ℂ} (hm : ∀ z, AEStronglyMeasurable (F z) μ)
    (hm' : ∀ z, AEStronglyMeasurable (F' z) μ)
    (hloc : ∀ z₀, ∃ g : α → ℝ, Integrable g μ ∧
      (∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ 2, HasDerivAt (F · t) (F' z t) z) ∧
      ∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ 2, ‖F z t‖ ≤ g t) :
    Differentiable ℂ (fun z => ∫ t, F z t ∂μ) := by
  intro z₀
  obtain ⟨g, hg, hd, hb⟩ := hloc z₀
  exact (hasDerivAt_integral_of_holo (r := 1) one_pos hg (fun z _ => hm z) (hm' z₀)
    (by simpa using hd) (by simpa using hb)).differentiableAt

/-- `b ↦ ∫ w(t) e^{bℓ(t)} dμ(t)` is entire when `w` is integrable and `ℓ` is bounded. -/
theorem differentiable_integral_mul_cexp_of_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w ℓ : α → ℂ} (hw : Integrable w μ) (hℓ : AEStronglyMeasurable ℓ μ)
    {M : ℝ} (hM : ∀ᵐ t ∂μ, ‖ℓ t‖ ≤ M) :
    Differentiable ℂ (fun b => ∫ t, w t * cexp (b * ℓ t) ∂μ) := by
  refine differentiable_integral_of_holo (F' := fun b t => w t * (cexp (b * ℓ t) * ℓ t))
    (fun b => hw.aestronglyMeasurable.mul (continuous_exp.comp_aestronglyMeasurable
      (hℓ.const_mul b)))
    (fun b => hw.aestronglyMeasurable.mul ((continuous_exp.comp_aestronglyMeasurable
      (hℓ.const_mul b)).mul hℓ)) fun b₀ => ?_
  refine ⟨fun t => ‖w t‖ * Real.exp ((‖b₀‖ + 2) * M), hw.norm.mul_const _, ?_, ?_⟩
  · refine ae_of_all _ fun t b _ => ?_
    have := ((hasDerivAt_id b).mul_const (ℓ t)).cexp.const_mul (w t)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · filter_upwards [hM] with t ht b hb
    have hb' : ‖b‖ ≤ ‖b₀‖ + 2 := by
      have := Metric.mem_closedBall.mp hb
      rw [dist_eq_norm] at this
      linarith [norm_le_insert' b b₀]
    rw [norm_mul]
    gcongr
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    exact mul_le_mul hb' ht (norm_nonneg _) (by positivity)

end Azurite.DLMF
