/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9CauchyJordan
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# DLMF §3.4(ii): differentiation of analytic functions

* 3.4.17: `dlmf_3_4_17` (analytic `F`, Jordan contour, from `dlmf_1_9_31_jordan`) and
  `dlmf_3_4_17_real` for a real `f` that extends analytically: `ofReal_iteratedDeriv_eq` shows
  that the real derivatives of `f` are the complex derivatives of its extension on `ℝ`
  (`HasDerivAt.real_of_complex`, `HasDerivAt.ofReal_comp`, induction on `k`).
* 3.4.18: `dlmf_3_4_18`, the circle `C(x₀, r)` parametrized by `θ`, from Mathlib's
  `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`.
* Example: `dlmf_3_4_19` (the real part of 3.4.18 for `e^z` at `0`, any `r > 0`),
  `dlmf_3_4_19_dominant` (with `r = k` the integrand is `e^k` at `θ = 0, 2π`),
  `dlmf_3_4_19_bound` (the "rough approximation": `1/k! ≤ e^k/k^k`).

The composite trapezoidal rule (3.5.2) and the saddle-point motivation are pointers to §3.5 and
§2.4(iv).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace Azurite.DLMF

open Azurite.JordanCurve

variable {c : ℝ → ℂ} {a b : ℝ}

/-! ### Cauchy's formula for derivatives 3.4.17 -/

/-- **DLMF 3.4.17** for an analytic `F`:
`F^{(k)}(x₀)/k! = (1/(2πi)) ∮_C F(ζ)/(ζ − x₀)^{k+1} dζ` on a positively oriented Jordan
contour `C` enclosing `x₀`, `F` continuous within and on `C` and
analytic within `C`. -/
theorem dlmf_3_4_17 (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {F : ℂ → ℂ}
    (hfc : ContinuousOn F (jordanInterior c a b ∪ c '' Icc a b))
    (hfd : DifferentiableOn ℂ F (jordanInterior c a b)) {x₀ : ℂ}
    (hx₀ : x₀ ∈ jordanInterior c a b) (k : ℕ) :
    iteratedDeriv k F x₀ / k.factorial =
      1 / (2 * π * I) * contourIntegral (fun ζ => F ζ / (ζ - x₀) ^ (k + 1)) c a b := by
  rw [dlmf_1_9_31_jordan P hJ hpos hfc hfd hx₀ k]
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 := two_pi_I_ne_zero
  field_simp

/-- The real derivatives of `f` are the complex derivatives of an analytic extension `F`: if `F`
is analytic on an open `U` and `f(x) = F(x)` for real `x ∈ U`, then `f^{(k)}(x) = F^{(k)}(x)`
there. -/
theorem ofReal_iteratedDeriv_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {f : ℝ → ℝ} (hf : ∀ x : ℝ, (x : ℂ) ∈ U → (f x : ℂ) = F x) :
    ∀ (k : ℕ) (x : ℝ), (x : ℂ) ∈ U → ((iteratedDeriv k f x : ℝ) : ℂ) = iteratedDeriv k F x := by
  have hA := hF.analyticOnNhd hU
  intro k
  induction k with
  | zero => intro x hx; simpa using hf x hx
  | succ k ih =>
    intro x hx
    set G := iteratedDeriv k F
    have hG : AnalyticOnNhd ℂ G U := by
      simp only [G, iteratedDeriv_eq_iterate]; exact hA.iterated_deriv k
    have hGd : HasDerivAt G (deriv G x) x := (hG x hx).differentiableAt.hasDerivAt
    have hev : ∀ᶠ y in 𝓝 x, ((iteratedDeriv k f y : ℝ) : ℂ) = G y :=
      Filter.eventually_of_mem (continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds hx))
        fun y hy => ih y hy
    have h1 : HasDerivAt (fun y : ℝ => ((iteratedDeriv k f y : ℝ) : ℂ)) (deriv G x) x :=
      hGd.comp_ofReal.congr_of_eventuallyEq hev
    have hre : HasDerivAt (iteratedDeriv k f) (deriv G x).re x :=
      hGd.real_of_complex.congr_of_eventuallyEq (hev.mono fun y hy => by
        show _ = (G y).re; rw [← hy, ofReal_re])
    have heq : ((deriv G x).re : ℂ) = deriv G x := hre.ofReal_comp.unique h1
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hre.deriv, heq]

/-- **DLMF 3.4.17** for a real `f` that extends analytically: if `F` is analytic on an open `U`
containing `C` and its interior, `f = F` on `U ∩ ℝ`, and `x₀ ∈ ℝ` lies inside `C`, then
`f^{(k)}(x₀)/k! = (1/(2πi)) ∮_C F(ζ)/(ζ − x₀)^{k+1} dζ`. -/
theorem dlmf_3_4_17_real (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hsub : jordanInterior c a b ∪ c '' Icc a b ⊆ U)
    {f : ℝ → ℝ} (hf : ∀ x : ℝ, (x : ℂ) ∈ U → (f x : ℂ) = F x) {x₀ : ℝ}
    (hx₀ : (x₀ : ℂ) ∈ jordanInterior c a b) (k : ℕ) :
    ((iteratedDeriv k f x₀ / k.factorial : ℝ) : ℂ) =
      1 / (2 * π * I) * contourIntegral (fun ζ => F ζ / (ζ - x₀) ^ (k + 1)) c a b := by
  push_cast
  rw [ofReal_iteratedDeriv_eq hU hF hf k x₀ (hsub (Or.inl hx₀))]
  exact dlmf_3_4_17 P hJ hpos (hF.continuousOn.mono hsub)
    (hF.mono (subset_union_left.trans hsub)) hx₀ k

/-! ### The circle 3.4.18 -/

/-- **DLMF 3.4.18**: with `C` the circle of radius `r` about `x₀`,
`F^{(k)}(x₀)/k! = (1/(2π r^k)) ∫₀^{2π} F(x₀ + r e^{iθ}) e^{−ikθ} dθ`, for `F` analytic on the
closed disk. -/
theorem dlmf_3_4_18 {F : ℂ → ℂ} {x₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.closedBall x₀ r)) (k : ℕ) :
    iteratedDeriv k F x₀ / k.factorial = 1 / (2 * π * r ^ k) *
      ∫ θ in (0 : ℝ)..2 * π, F (x₀ + r * cexp (θ * I)) * cexp (-(k * θ * I)) := by
  have h := hF.circleIntegral_one_div_sub_center_pow_smul hr k
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hint : (∮ z in C(x₀, r), (1 / (z - x₀) ^ (k + 1)) • F z) = I / (r : ℂ) ^ k *
      ∫ θ in (0 : ℝ)..2 * π, F (x₀ + r * cexp (θ * I)) * cexp (-(k * θ * I)) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, circleMap, smul_eq_mul, zero_add, add_sub_cancel_left]
    have he : cexp (θ * I) ≠ 0 := Complex.exp_ne_zero _
    rw [show cexp (-(k * θ * I)) = (cexp (θ * I) ^ k)⁻¹ by
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; ring_nf]
    field_simp
    ring
  rw [hint, smul_eq_mul] at h
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 := two_pi_I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc iteratedDeriv k F x₀ / k.factorial
      = 1 / (2 * π * I) * (2 * π * I / k.factorial * iteratedDeriv k F x₀) := by
        field_simp
    _ = 1 / (2 * π * I) * (I / (r : ℂ) ^ k *
          ∫ θ in (0 : ℝ)..2 * π, F (x₀ + r * cexp (θ * I)) * cexp (-(k * θ * I))) := by
        rw [h]
    _ = _ := by rw [← mul_assoc]; congr 1; field_simp

/-! ### Example 3.4.19 -/

/-- **DLMF 3.4.19**: for `f(z) = e^z`, `x₀ = 0`, and any `r > 0`,
`1/k! = (1/(2π r^k)) ∫₀^{2π} e^{r cos θ} cos(r sin θ − kθ) dθ` (the real part of 3.4.18). -/
theorem dlmf_3_4_19 (k : ℕ) {r : ℝ} (hr : 0 < r) :
    1 / (k.factorial : ℝ) = 1 / (2 * π * r ^ k) *
      ∫ θ in (0 : ℝ)..2 * π, Real.exp (r * Real.cos θ) * Real.cos (r * Real.sin θ - k * θ) := by
  have h := dlmf_3_4_18 (F := cexp) (x₀ := 0) hr Complex.differentiable_exp.differentiableOn k
  rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero] at h
  have hcont : Continuous fun θ : ℝ => cexp (0 + r * cexp (θ * I)) * cexp (-(k * θ * I)) := by
    fun_prop
  have key : ∀ θ : ℝ, (cexp (0 + r * cexp (θ * I)) * cexp (-(k * θ * I))).re =
      Real.exp (r * Real.cos θ) * Real.cos (r * Real.sin θ - k * θ) := fun θ => by
    rw [← Complex.exp_add, Complex.exp_re]
    congr 2
    · simp [Complex.exp_ofReal_mul_I_re]
    · simp [Complex.exp_ofReal_mul_I_im]; ring
  have hre := congrArg Complex.re h
  rw [show (1 : ℂ) / (k.factorial : ℂ) = ((1 / (k.factorial : ℝ) : ℝ) : ℂ) by push_cast; rfl,
    show (1 : ℂ) / (2 * π * (r : ℂ) ^ k) = ((1 / (2 * π * r ^ k) : ℝ) : ℂ) by push_cast; rfl,
    ofReal_re, re_ofReal_mul] at hre
  have hcomm :=
    intervalIntegral.intervalIntegral_re (hcont.intervalIntegrable (μ := volume) 0 (2 * π))
  simp only [RCLike.re_to_complex, key] at hcomm
  rw [← hcomm] at hre
  exact hre

/-- With `r = k`, the integrand of 3.4.19 equals `e^k` at the dominant points `θ = 0, 2π`. -/
theorem dlmf_3_4_19_dominant (k : ℕ) :
    Real.exp (k * Real.cos 0) * Real.cos (k * Real.sin 0 - k * 0) = Real.exp k ∧
      Real.exp (k * Real.cos (2 * π)) * Real.cos (k * Real.sin (2 * π) - k * (2 * π)) =
        Real.exp k := by
  refine ⟨by simp, ?_⟩
  rw [Real.cos_two_pi, Real.sin_two_pi, mul_zero, zero_sub, Real.cos_neg,
    Real.cos_nat_mul_two_pi, mul_one, mul_one]

/-- The "rough approximation" with `r = k`: the integrand of 3.4.19 is at most `e^k`, so
`1/k! ≤ e^k/k^k`. -/
theorem dlmf_3_4_19_bound {k : ℕ} (hk : 1 ≤ k) :
    1 / (k.factorial : ℝ) ≤ Real.exp k / (k : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [dlmf_3_4_19 k hkpos]
  have hcont : Continuous fun θ : ℝ =>
      Real.exp (k * Real.cos θ) * Real.cos (k * Real.sin θ - k * θ) := by fun_prop
  have hle : ∫ θ in (0 : ℝ)..2 * π, Real.exp (k * Real.cos θ) * Real.cos (k * Real.sin θ - k * θ)
      ≤ ∫ θ in (0 : ℝ)..2 * π, Real.exp k := by
    refine intervalIntegral.integral_mono_on (by positivity) (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => ?_
    calc Real.exp (k * Real.cos θ) * Real.cos (k * Real.sin θ - k * θ)
        ≤ Real.exp (k * Real.cos θ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.exp_pos _).le
      _ ≤ Real.exp k := by
          rw [mul_one, Real.exp_le_exp]
          exact mul_le_of_le_one_right hkpos.le (Real.cos_le_one θ)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
  have hpos : (0 : ℝ) < 2 * π * (k : ℝ) ^ k := by positivity
  calc 1 / (2 * π * (k : ℝ) ^ k) *
        ∫ θ in (0 : ℝ)..2 * π, Real.exp (k * Real.cos θ) * Real.cos (k * Real.sin θ - k * θ)
      ≤ 1 / (2 * π * (k : ℝ) ^ k) * (2 * π * Real.exp k) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.exp k / (k : ℝ) ^ k := by field_simp

end Azurite.DLMF
