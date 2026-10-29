/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section10
import Azurite.DLMF.Chapter1.Section10Laurent
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# DLMF §1.10(vii): Inverse Functions

Formalizations of <https://dlmf.nist.gov/1.10.vii>.

* Lagrange inversion theorem:
  * 1.10.12: `dlmf_1_10_12` (an analytic local inverse `F` exists, from Mathlib's inverse function
    theorem `HasStrictFDerivAt.toOpenPartialHomeomorph`) and `dlmf_1_10_12_unique` (any solution
    continuous at `w₀` with `F(w₀) = z₀` agrees with it near `w₀`).
  * 1.10.13: `dlmf_1_10_13`, with `inversionCoeff` (`n Fₙ` is the residue of `1/(f − f(z₀))ⁿ`).
  * 1.10.14: `dlmf_1_10_14`, with `lagrangeCoeff` (`n Gₙ` is the residue of `g′/(f − f(z₀))ⁿ`).
  * Proof: `hasSum_lagrange`, by
    * Cauchy's formula `g(z₁) = (2πi)⁻¹ ∮ g f′/(f − f(z₁))` (`circleIntegral_inverse_cauchy`, via
      `dslope`);
    * the geometric expansion of `1/(f − w)` in powers of `w − w₀` under the integral
      (`hasSum_circleIntegral_div_sub`);
    * integration by parts on the circle (`circleIntegral_by_parts`), which turns
      `∮ g f′/(f − w₀)^{n+1}` into `n⁻¹ ∮ g′/(f − w₀)ⁿ`.
* Extended inversion theorem:
  * 1.10.15: `f(z) = f(z₀) + (z − z₀)^μ φ(z)` with `φ(z₀) = f₀ ≠ 0`. Its values over all branches
    of `(z − z₀)^μ` form `extPowMV`.
  * Branch: a logarithm `L₀` of `f₀` fixes the branch `ψ = extBranch` of `(f − f(z₀))^{1/μ}`
    (`extBranch_mem_rootMV`).
  * 1.10.16 and 1.10.17: `dlmf_1_10_16` applies Lagrange inversion to `ψ`. Every value `s` of
    `(w − w₀)^{1/μ}` (`rootMV`) gives a solution `z = z₀ + Σ Fₙ sⁿ` of `f(z) = w`, together with
    `g(z) = g(z₀) + Σ Gₙ sⁿ`.
  * Integer `μ`: `dlmf_1_10_15_integer` (`f − f(z₀)` has a zero of order `μ`).
-/

open Filter Topology Set Metric Complex MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Three circle-integral lemmas -/

/-- Cauchy's formula for the inverse: if `f` is injective with `f′ ≠ 0` on `|z − z₀| < R` and
`|z₁ − z₀| < r < R`, then `(2πi)⁻¹ ∮_{|z−z₀|=r} g(z) f′(z)/(f(z) − f(z₁)) dz = g(z₁)`. -/
theorem circleIntegral_inverse_cauchy {f g : ℂ → ℂ} {z₀ z₁ : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hinj : InjOn f (ball z₀ R)) (hd0 : ∀ z ∈ ball z₀ R, deriv f z ≠ 0) (hrR : r < R)
    (hz₁ : z₁ ∈ ball z₀ r) :
    (2 * π * I)⁻¹ * ∮ z in C(z₀, r), g z * deriv f z / (f z - f z₁) = g z₁ := by
  have hr : 0 < r := dist_nonneg.trans_lt hz₁
  have hz₁R : z₁ ∈ ball z₀ R := ball_subset_ball hrR.le hz₁
  have hq : DifferentiableOn ℂ (dslope f z₁) (ball z₀ R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds hz₁R)).mpr hf
  have hsq : ∀ z, (z - z₁) * dslope f z₁ z = f z - f z₁ := fun z => by
    rw [← smul_eq_mul, sub_smul_dslope]
  have hq0 : ∀ z ∈ ball z₀ R, dslope f z₁ z ≠ 0 := by
    intro z hz h0
    by_cases hzz : z = z₁
    · subst hzz
      rw [dslope_same] at h0
      exact hd0 z hz h0
    · have := hsq z
      rw [h0, mul_zero] at this
      exact hzz (hinj hz hz₁R (sub_eq_zero.mp this.symm))
  have hf' : DifferentiableOn ℂ (deriv f) (ball z₀ R) := hf.deriv isOpen_ball
  set h : ℂ → ℂ := fun z => g z * deriv f z / dslope f z₁ z with hh
  have hhd : ∀ z ∈ ball z₀ R, DifferentiableAt ℂ h z := fun z hz =>
    ((hg.differentiableAt (isOpen_ball.mem_nhds hz)).mul
      (hf'.differentiableAt (isOpen_ball.mem_nhds hz))).div
      (hq.differentiableAt (isOpen_ball.mem_nhds hz)) (hq0 z hz)
  have hcb : closedBall z₀ r ⊆ ball z₀ R := closedBall_subset_ball hrR
  have hcif := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hz₁ (fun z hz => (hhd z (hcb hz)).continuousAt.continuousWithinAt)
    (fun z hz => hhd z (hcb (ball_subset_closedBall hz.1)))
  have hEq : EqOn (fun z => g z * deriv f z / (f z - f z₁)) (fun z => (z - z₁)⁻¹ • h z)
      (sphere z₀ r) := by
    intro z hz
    have hne : z - z₁ ≠ 0 := by
      refine sub_ne_zero.mpr fun e => ?_
      rw [e, mem_sphere] at hz
      exact (ne_of_lt (mem_ball.mp hz₁)) hz
    have hqz := hq0 z (hcb (sphere_subset_closedBall hz))
    simp only [hh, smul_eq_mul, ← hsq z]
    field_simp
  rw [circleIntegral.integral_congr hr.le hEq, ← smul_eq_mul, hcif, hh]
  simp only [dslope_same]
  field_simp [hd0 z₁ hz₁R]

/-- Geometric expansion under a circle integral: if `|u(z) − w₀| ≥ δ > |w − w₀|` on the circle,
`∮ φ/(u − w) = Σₙ ∮ (w − w₀)ⁿ φ/(u − w₀)ⁿ⁺¹`. -/
theorem hasSum_circleIntegral_div_sub {φ u : ℂ → ℂ} {c w w₀ : ℂ} {r δ : ℝ} (hr : 0 < r)
    (hφ : ContinuousOn φ (sphere c r)) (hu : ContinuousOn u (sphere c r))
    (hδ : ∀ z ∈ sphere c r, δ ≤ ‖u z - w₀‖) (hw : ‖w - w₀‖ < δ) :
    HasSum (fun n : ℕ => ∮ z in C(c, r), (w - w₀) ^ n * (φ z / (u z - w₀) ^ (n + 1)))
      (∮ z in C(c, r), φ z / (u z - w)) := by
  have hδ0 : 0 < δ := (norm_nonneg _).trans_lt hw
  set q := ‖w - w₀‖ / δ with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hδ0).2 hw
  have hcm : ∀ θ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  have hφc : Continuous fun θ => φ (circleMap c r θ) :=
    hφ.comp_continuous (continuous_circleMap c r) hcm
  have huc : Continuous fun θ => u (circleMap c r θ) :=
    hu.comp_continuous (continuous_circleMap c r) hcm
  have hδle : ∀ θ, δ ≤ ‖u (circleMap c r θ) - w₀‖ := fun θ => hδ _ (hcm θ)
  have hne : ∀ θ, u (circleMap c r θ) - w₀ ≠ 0 := fun θ h => by
    have := hδle θ
    rw [h, norm_zero] at this
    linarith
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => r * (‖φ (circleMap c r θ)‖ / δ) * q ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have : Continuous fun θ => deriv (circleMap c r) θ • ((w - w₀) ^ n *
        (φ (circleMap c r θ) / (u (circleMap c r θ) - w₀) ^ (n + 1))) := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).mul continuous_const).smul (continuous_const.mul
        (hφc.div ((huc.sub continuous_const).pow _) fun θ => pow_ne_zero _ (hne θ)))
    exact this.aestronglyMeasurable
  · refine Eventually.of_forall fun θ _ => ?_
    set a := ‖u (circleMap c r θ) - w₀‖ with ha
    have ha0 : 0 < δ ^ (n + 1) := pow_pos hδ0 _
    have hle : δ ^ (n + 1) ≤ a ^ (n + 1) := pow_le_pow_left₀ hδ0.le (hδle θ) _
    rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, norm_I, abs_of_pos hr,
      norm_mul, norm_pow, norm_div, norm_pow, ← ha, mul_one]
    calc r * (‖w - w₀‖ ^ n * (‖φ (circleMap c r θ)‖ / a ^ (n + 1)))
        ≤ r * (‖w - w₀‖ ^ n * (‖φ (circleMap c r θ)‖ / δ ^ (n + 1))) := by
          gcongr
      _ = r * (‖φ (circleMap c r θ)‖ / δ) * q ^ n := by
          rw [hqdef, div_pow, pow_succ]
          field_simp
  · exact Eventually.of_forall fun θ _ => (summable_geometric_of_lt_one hq0 hq1).mul_left _
  · have : Continuous fun θ => r * (‖φ (circleMap c r θ)‖ / δ) * (1 - q)⁻¹ :=
      (continuous_const.mul (hφc.norm.div_const δ)).mul continuous_const
    simpa only [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] using this.intervalIntegrable _ _
  · refine Eventually.of_forall fun θ _ => ?_
    set z := circleMap c r θ
    have hz0 : u z - w₀ ≠ 0 := hne θ
    have hlt : ‖w - w₀‖ < ‖u z - w₀‖ := hw.trans_le (hδle θ)
    have hx : ‖(w - w₀) / (u z - w₀)‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one ((norm_nonneg _).trans_lt hlt)).2 hlt
    have huw : u z - w ≠ 0 := fun h => by
      rw [show w - w₀ = u z - w₀ by linear_combination -h] at hlt
      exact lt_irrefl _ hlt
    have h := ((hasSum_geometric_of_norm_lt_one hx).mul_right (φ z / (u z - w₀))).mul_left
      (deriv (circleMap c r) θ)
    convert h using 1
    · funext n
      beta_reduce
      rw [smul_eq_mul, div_pow, pow_succ]
      field_simp
    · beta_reduce
      rw [smul_eq_mul]
      congr 1
      have h1x : 1 - (w - w₀) / (u z - w₀) = (u z - w) / (u z - w₀) := by
        field_simp
        ring
      rw [h1x, inv_div]
      field_simp

/-- Integration by parts on a circle: if `f ≠ w₀` on an open `U ⊇ {|z − c| = r}`,
`∮ g f′/(f − w₀)^{m+2} = (m + 1)⁻¹ ∮ g′/(f − w₀)^{m+1}`. -/
theorem circleIntegral_by_parts {f g : ℂ → ℂ} {c w₀ : ℂ} {r : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hsU : sphere c r ⊆ U) (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) (hne : ∀ z ∈ U, f z ≠ w₀) (m : ℕ) :
    (∮ z in C(c, r), g z * deriv f z / (f z - w₀) ^ (m + 1 + 1)) =
      ((m : ℂ) + 1)⁻¹ * ∮ z in C(c, r), deriv g z / (f z - w₀) ^ (m + 1) := by
  have h0 : ∀ z ∈ U, f z - w₀ ≠ 0 := fun z hz => sub_ne_zero.mpr (hne z hz)
  have hderiv : ∀ z ∈ U, HasDerivAt (fun z => g z / (f z - w₀) ^ (m + 1))
      (deriv g z / (f z - w₀) ^ (m + 1) -
        ((m : ℂ) + 1) * (g z * deriv f z / (f z - w₀) ^ (m + 1 + 1))) z := by
    intro z hz
    have hgz := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hfz := ((hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt.sub_const w₀).fun_pow
      (m + 1)
    have hz0 := h0 z hz
    convert hgz.div hfz (pow_ne_zero _ hz0) using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr
    (fun z hz => (hderiv z (hsU hz)).hasDerivWithinAt)
  have hfc : ContinuousOn f (sphere c r) := hf.continuousOn.mono hsU
  have hA : CircleIntegrable (fun z => deriv g z / (f z - w₀) ^ (m + 1)) c r :=
    (((hg.deriv hU).continuousOn.mono hsU).div ((hfc.sub continuousOn_const).pow _)
      fun z hz => pow_ne_zero _ (h0 z (hsU hz))).circleIntegrable hr
  have hB : CircleIntegrable
      (fun z => ((m : ℂ) + 1) * (g z * deriv f z / (f z - w₀) ^ (m + 1 + 1))) c r :=
    (continuousOn_const.mul (((hg.continuousOn.mono hsU).mul
      ((hf.deriv hU).continuousOn.mono hsU)).div ((hfc.sub continuousOn_const).pow _)
      fun z hz => pow_ne_zero _ (h0 z (hsU hz)))).circleIntegrable hr
  rw [circleIntegral.integral_sub hA hB, circleIntegral.integral_const_mul] at hzero
  have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp
  linear_combination -hzero

/-! ### Lagrange inversion -/

/-- The Lagrange coefficients of `g ∘ F`: `G₀ = g(z₀)` and `n Gₙ = res_{z₀} g′(z)/(f(z) − f(z₀))ⁿ`
(residue on the punctured disk of radius `R`). -/
noncomputable def lagrangeCoeff (f g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then g z₀ else residue (fun z => deriv g z / (f z - f z₀) ^ n) z₀ R / n

/-- Lagrange inversion on a disk where `f` is injective with `f′ ≠ 0`: for `z₁` near `z₀` with
`f(z₁)` near `f(z₀)`, `g(z₁) = Σₙ Gₙ (f(z₁) − f(z₀))ⁿ`. -/
theorem hasSum_lagrange {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hinj : InjOn f (ball z₀ R)) (hd0 : ∀ z ∈ ball z₀ R, deriv f z ≠ 0) :
    ∃ ρ > 0, ∀ z₁ ∈ ball z₀ (R / 2), ‖f z₁ - f z₀‖ < ρ →
      HasSum (fun n => lagrangeCoeff f g z₀ R n * (f z₁ - f z₀) ^ n) (g z₁) := by
  have hr : 0 < R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self hR
  set U := ball z₀ R \ {z₀} with hUdef
  have hUo : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hsph : sphere z₀ (R / 2) ⊆ U := fun z hz => by
    refine ⟨mem_ball.mpr ((mem_sphere.mp hz).trans_lt hrR), fun h => ?_⟩
    rw [mem_singleton_iff.mp h, mem_sphere, dist_self] at hz
    linarith
  have hneU : ∀ z ∈ U, f z ≠ f z₀ := fun z hz h => hz.2 (hinj hz.1 hz₀ h)
  have hfc : ContinuousOn f (sphere z₀ (R / 2)) := hf.continuousOn.mono fun z hz => (hsph hz).1
  obtain ⟨z', hz', hmin⟩ := (isCompact_sphere z₀ (R / 2)).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (hfc.sub continuousOn_const).norm
  set δ := ‖f z' - f z₀‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (hneU z' (hsph hz')))
  have hδle : ∀ z ∈ sphere z₀ (R / 2), δ ≤ ‖f z - f z₀‖ := fun z hz => hmin hz
  refine ⟨δ, hδ, fun z₁ hz₁ hw => ?_⟩
  have hA := circleIntegral_inverse_cauchy hf hg hinj hd0 hrR hz₁
  have hA0 := circleIntegral_inverse_cauchy hf hg hinj hd0 hrR (mem_ball_self hr)
  have hφ : ContinuousOn (fun z => g z * deriv f z) (sphere z₀ (R / 2)) :=
    (hg.continuousOn.mul (hf.deriv isOpen_ball).continuousOn).mono fun z hz => (hsph hz).1
  have hB := (hasSum_circleIntegral_div_sub (φ := fun z => g z * deriv f z) hr hφ hfc hδle
    hw).mul_left (2 * π * I)⁻¹
  rw [← hA]
  convert hB using 1
  funext n
  rw [circleIntegral.integral_const_mul]
  rcases n with _ | m
  · simp only [lagrangeCoeff, ↓reduceIte, pow_zero, mul_one, one_mul, zero_add, pow_one]
    exact hA0.symm
  · have hres : residue (fun z => deriv g z / (f z - f z₀) ^ (m + 1)) z₀ R =
        (2 * π * I)⁻¹ * ∮ z in C(z₀, R / 2), deriv g z / (f z - f z₀) ^ (m + 1) := by
      refine residue_eq (fun z hz => ?_) ⟨hr, hrR⟩
      have hz' : 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < R := hz
      have hzU : z ∈ U := ⟨mem_ball.mpr (by rw [dist_eq_norm]; exact hz'.2), fun h => by
        rw [mem_singleton_iff.mp h, sub_self, norm_zero] at hz'
        exact lt_irrefl _ hz'.1⟩
      exact (((hg.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hzU.1)).div
        (((hf.differentiableAt (isOpen_ball.mem_nhds hzU.1)).sub_const _).pow _)
        (pow_ne_zero _ (sub_ne_zero.mpr (hneU z hzU)))).differentiableWithinAt
    rw [circleIntegral_by_parts hUo hsph hr.le (hf.mono sdiff_subset) (hg.mono sdiff_subset) hneU m]
    simp only [lagrangeCoeff, Nat.succ_ne_zero, ↓reduceIte, hres]
    push_cast
    ring

/-- An analytic `f` with `f′(z₀) ≠ 0` is injective on an open neighbourhood of `z₀`. -/
theorem exists_isOpen_injOn {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ InjOn f U :=
  let hs := hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hf'
  ⟨_, (hs.toOpenPartialHomeomorph f).open_source, hs.mem_toOpenPartialHomeomorph_source,
    (hs.toOpenPartialHomeomorph f).injOn⟩

/-- **DLMF 1.10.12**: if `f` is analytic at `z₀` with `f′(z₀) ≠ 0`, the equation `f(z) = w` has a
solution `z = F(w)` analytic at `w₀ = f(z₀)` with `F(w₀) = z₀`. -/
theorem dlmf_1_10_12 {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (f z₀) ∧ F (f z₀) = z₀ ∧ ∀ᶠ w in 𝓝 (f z₀), f (F w) = w := by
  have hs := hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hf'
  set e := hs.toOpenPartialHomeomorph f with he
  have hsrc : z₀ ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z ∧ deriv f z ≠ 0 :=
    hf.eventually_analyticAt.and (hf.deriv.continuousAt.eventually_ne hf')
  obtain ⟨V, hVsub, hVo, hz₀V⟩ := _root_.mem_nhds_iff.mp hev
  have hWo : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hVo
  have hleft : e.symm (f z₀) = z₀ := e.left_inv hsrc
  have hw₀ : f z₀ ∈ e.target ∩ e.symm ⁻¹' V := ⟨e.map_source hsrc, by
    show e.symm (f z₀) ∈ V
    rw [hleft]
    exact hz₀V⟩
  refine ⟨e.symm, ?_, hleft, e.eventually_right_inverse' hsrc⟩
  have hd : DifferentiableOn ℂ e.symm (e.target ∩ e.symm ⁻¹' V) := fun w hw =>
    (e.hasDerivAt_symm hw.1 (hVsub hw.2).2
      (hVsub hw.2).1.differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hWo.mem_nhds hw₀)

/-- **DLMF 1.10.12** (uniqueness): two solutions `F₁`, `F₂` of `f(F(w)) = w` near `w₀` that are
continuous at `w₀` with `F(w₀) = z₀` agree near `w₀`. -/
theorem dlmf_1_10_12_unique {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hf' : deriv f z₀ ≠ 0) {F₁ F₂ : ℂ → ℂ} (h₁c : ContinuousAt F₁ (f z₀)) (h₁ : F₁ (f z₀) = z₀)
    (h₁e : ∀ᶠ w in 𝓝 (f z₀), f (F₁ w) = w) (h₂c : ContinuousAt F₂ (f z₀))
    (h₂ : F₂ (f z₀) = z₀) (h₂e : ∀ᶠ w in 𝓝 (f z₀), f (F₂ w) = w) :
    F₁ =ᶠ[𝓝 (f z₀)] F₂ := by
  obtain ⟨U, hUo, hz₀U, hinj⟩ := exists_isOpen_injOn hf hf'
  have hU₁ : ∀ᶠ w in 𝓝 (f z₀), F₁ w ∈ U :=
    h₁c.preimage_mem_nhds (by rw [h₁]; exact hUo.mem_nhds hz₀U)
  have hU₂ : ∀ᶠ w in 𝓝 (f z₀), F₂ w ∈ U :=
    h₂c.preimage_mem_nhds (by rw [h₂]; exact hUo.mem_nhds hz₀U)
  filter_upwards [hU₁, hU₂, h₁e, h₂e] with w a b c d
  exact hinj a b (c.trans d.symm)

/-- **DLMF 1.10.14**: if moreover `g` is analytic at `z₀`, then near `w₀ = f(z₀)`,
`g(F(w)) = g(z₀) + Σ_{n ≥ 1} Gₙ (w − w₀)ⁿ` with `n Gₙ = res_{z₀} g′(z)/(f(z) − f(z₀))ⁿ`
(`lagrangeCoeff`; the residue is taken on any punctured disk of radius `R′ ≤ R`). -/
theorem dlmf_1_10_14 {f g F : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0)
    (hg : AnalyticAt ℂ g z₀) (hFc : ContinuousAt F (f z₀)) (hF₀ : F (f z₀) = z₀)
    (hFe : ∀ᶠ w in 𝓝 (f z₀), f (F w) = w) :
    ∃ R > 0, ∀ R' ∈ Ioc 0 R, ∀ᶠ w in 𝓝 (f z₀),
      HasSum (fun n => lagrangeCoeff f g z₀ R' n * (w - f z₀) ^ n) (g (F w)) := by
  obtain ⟨U, hUo, hz₀U, hinj⟩ := exists_isOpen_injOn hf hf'
  have hev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧ deriv f z ≠ 0 ∧ z ∈ U :=
    hf.eventually_analyticAt.and (hg.eventually_analyticAt.and
      ((hf.deriv.continuousAt.eventually_ne hf').and (hUo.mem_nhds hz₀U)))
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨R, hR, fun R' hR' => ?_⟩
  have hsub : ball z₀ R' ⊆ ball z₀ R := ball_subset_ball hR'.2
  obtain ⟨ρ, hρ, hsum⟩ := hasSum_lagrange hR'.1
    (fun z hz => (hball z (hsub hz)).1.differentiableAt.differentiableWithinAt)
    (fun z hz => (hball z (hsub hz)).2.1.differentiableAt.differentiableWithinAt)
    (hinj.mono fun z hz => (hball z (hsub hz)).2.2.2) (fun z hz => (hball z (hsub hz)).2.2.1)
  have h1 : ∀ᶠ w in 𝓝 (f z₀), F w ∈ ball z₀ (R' / 2) :=
    hFc.preimage_mem_nhds (by rw [hF₀]; exact ball_mem_nhds _ (by linarith [hR'.1]))
  filter_upwards [h1, ball_mem_nhds (f z₀) hρ, hFe] with w hw1 hw2 hw3
  have := hsum (F w) hw1 (by rw [hw3, ← dist_eq_norm]; exact hw2)
  rwa [hw3] at this

/-- The inversion coefficients: `F₀ = z₀` and `n Fₙ = res_{z₀} 1/(f(z) − f(z₀))ⁿ`. -/
noncomputable def inversionCoeff (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then z₀ else residue (fun z => 1 / (f z - f z₀) ^ n) z₀ R / n

theorem lagrangeCoeff_id (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) :
    lagrangeCoeff f id z₀ R = inversionCoeff f z₀ R := by
  funext n
  simp [lagrangeCoeff, inversionCoeff]

/-- **DLMF 1.10.13**: near `w₀ = f(z₀)`, `F(w) = z₀ + Σ_{n ≥ 1} Fₙ (w − w₀)ⁿ` with
`n Fₙ = res_{z₀} 1/(f(z) − f(z₀))ⁿ`. -/
theorem dlmf_1_10_13 {f F : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0)
    (hFc : ContinuousAt F (f z₀)) (hF₀ : F (f z₀) = z₀) (hFe : ∀ᶠ w in 𝓝 (f z₀), f (F w) = w) :
    ∃ R > 0, ∀ R' ∈ Ioc 0 R, ∀ᶠ w in 𝓝 (f z₀),
      HasSum (fun n => inversionCoeff f z₀ R' (n + 1) * (w - f z₀) ^ (n + 1)) (F w - z₀) := by
  obtain ⟨R, hR, h⟩ := dlmf_1_10_14 hf hf' analyticAt_id hFc hF₀ hFe
  refine ⟨R, hR, fun R' hR' => (h R' hR').mono fun w hw => ?_⟩
  rw [lagrangeCoeff_id] at hw
  have := (hasSum_nat_add_iff' 1).mpr hw
  simpa [inversionCoeff] using this

/-! ### The extended inversion theorem -/

/-- The values of `a^{1/μ}`: all `e^L` with `e^{μL} = a`. -/
def rootMV (μ a : ℂ) : Set ℂ := {s | ∃ L : ℂ, exp L = s ∧ exp (μ * L) = a}

/-- **DLMF 1.10.15** as a many-valued function: the values of
`f(z) = w₀ + (z − z₀)^μ φ(z)`, `φ(z) = Σ fₙ (z − z₀)ⁿ`, over all branches of `(z − z₀)^μ`. -/
def extPowMV (μ : ℂ) (φ : ℂ → ℂ) (z₀ w₀ z : ℂ) : Set ℂ :=
  {w | ∃ Λ : ℂ, exp Λ = z - z₀ ∧ w = w₀ + exp (μ * Λ) * φ z}

/-- A branch `ψ(z) = (z − z₀) e^{ℓ(z)/μ}` of `(f(z) − f(z₀))^{1/μ}`, where `ℓ` is the logarithm of
`φ` with `ℓ(z₀) = L₀`. -/
noncomputable def extBranch (μ : ℂ) (φ : ℂ → ℂ) (z₀ L₀ z : ℂ) : ℂ :=
  (z - z₀) * exp ((L₀ + log (φ z / φ z₀)) / μ)

theorem exp_extLog {φ : ℂ → ℂ} {z₀ L₀ z : ℂ} (hL₀ : exp L₀ = φ z₀) (hφ0 : φ z₀ ≠ 0)
    (hφz : φ z ≠ 0) : exp (L₀ + log (φ z / φ z₀)) = φ z := by
  rw [exp_add, hL₀, exp_log (div_ne_zero hφz hφ0)]
  field_simp

/-- `ψ(z)` is one of the values of `(f(z) − f(z₀))^{1/μ}`. -/
theorem extBranch_mem_rootMV {μ : ℂ} (hμ : μ ≠ 0) {φ : ℂ → ℂ} {z₀ L₀ z : ℂ}
    (hL₀ : exp L₀ = φ z₀) (hφ0 : φ z₀ ≠ 0) (hz : z ≠ z₀) (hφz : φ z ≠ 0) :
    ∃ Λ : ℂ, exp Λ = z - z₀ ∧
      extBranch μ φ z₀ L₀ z ∈ rootMV μ (exp (μ * Λ) * φ z) := by
  have hz' : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  refine ⟨log (z - z₀), exp_log hz', log (z - z₀) + (L₀ + log (φ z / φ z₀)) / μ, ?_, ?_⟩
  · rw [exp_add, exp_log hz', extBranch]
  · rw [show μ * (log (z - z₀) + (L₀ + log (φ z / φ z₀)) / μ) =
        μ * log (z - z₀) + (L₀ + log (φ z / φ z₀)) by field_simp, exp_add,
      exp_extLog hL₀ hφ0 hφz]

theorem extBranch_self (μ : ℂ) (φ : ℂ → ℂ) (z₀ L₀ : ℂ) : extBranch μ φ z₀ L₀ z₀ = 0 := by
  simp [extBranch]

theorem analyticAt_extBranch {μ : ℂ} (hμ : μ ≠ 0) {φ : ℂ → ℂ} {z₀ : ℂ} (hφ : AnalyticAt ℂ φ z₀)
    (hφ0 : φ z₀ ≠ 0) (L₀ : ℂ) : AnalyticAt ℂ (extBranch μ φ z₀ L₀) z₀ := by
  have h1 : φ z₀ / φ z₀ ∈ slitPlane := by rw [div_self hφ0]; simp [mem_slitPlane_iff]
  exact (analyticAt_id.sub analyticAt_const).mul
    (((analyticAt_const.add ((hφ.div analyticAt_const hφ0).clog h1)).div analyticAt_const
      hμ).cexp')

theorem deriv_extBranch {μ : ℂ} (hμ : μ ≠ 0) {φ : ℂ → ℂ} {z₀ : ℂ} (hφ : AnalyticAt ℂ φ z₀)
    (hφ0 : φ z₀ ≠ 0) (L₀ : ℂ) :
    deriv (extBranch μ φ z₀ L₀) z₀ = exp ((L₀ + log (φ z₀ / φ z₀)) / μ) := by
  have h1 : φ z₀ / φ z₀ ∈ slitPlane := by rw [div_self hφ0]; simp [mem_slitPlane_iff]
  have hE : DifferentiableAt ℂ (fun z => exp ((L₀ + log (φ z / φ z₀)) / μ)) z₀ :=
    (((analyticAt_const.add ((hφ.div analyticAt_const hφ0).clog h1)).div analyticAt_const
      hμ).cexp').differentiableAt
  have h := ((hasDerivAt_id z₀).sub_const z₀).mul hE.hasDerivAt
  simp only [id, sub_self, zero_mul, add_zero, one_mul] at h
  exact h.deriv

/-- **DLMF 1.10.15–1.10.17** (extended inversion theorem): let `μ > 0` and
`f(z) = f(z₀) + (z − z₀)^μ φ(z)` with `φ` analytic at `z₀` (`φ(z) = Σ fₙ (z − z₀)ⁿ`), `φ(z₀) ≠ 0`.
Fix a logarithm `L₀` of `f₀ = φ(z₀)`, giving the branch `ψ` of `(f(z) − f(z₀))^{1/μ}`. For every
small `s` there is `z = z₀ + Σ_{n ≥ 1} Fₙ sⁿ` with `ψ(z) = s` (1.10.16), and
`g(z) = g(z₀) + Σ_{n ≥ 1} Gₙ sⁿ` (1.10.17), where `n Fₙ = res 1/ψⁿ`, `n Gₙ = res g′/ψⁿ`. Whenever
`s` is any value of `(w − w₀)^{1/μ}`, `z` solves `f(z) = w` (1.10.12): each branch of
`(w − w₀)^{1/μ}` gives a solution. -/
theorem dlmf_1_10_16 {μ : ℝ} (hμ : 0 < μ) {φ g : ℂ → ℂ} {z₀ w₀ L₀ : ℂ}
    (hφ : AnalyticAt ℂ φ z₀) (hφ0 : φ z₀ ≠ 0) (hL₀ : exp L₀ = φ z₀) (hg : AnalyticAt ℂ g z₀) :
    ∃ R > 0, ∃ ρ > 0, ∀ s ∈ ball (0 : ℂ) ρ, ∃ z, extBranch μ φ z₀ L₀ z = s ∧
      HasSum (fun n => inversionCoeff (extBranch μ φ z₀ L₀) z₀ R (n + 1) * s ^ (n + 1))
        (z - z₀) ∧
      HasSum (fun n => lagrangeCoeff (extBranch μ φ z₀ L₀) g z₀ R (n + 1) * s ^ (n + 1))
        (g z - g z₀) ∧
      ∀ w, s ∈ rootMV μ (w - w₀) → w ∈ extPowMV μ φ z₀ w₀ z := by
  have hμ0 : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  set ψ := extBranch μ φ z₀ L₀ with hψ
  have hψa : AnalyticAt ℂ ψ z₀ := analyticAt_extBranch hμ0 hφ hφ0 L₀
  have hψ' : deriv ψ z₀ ≠ 0 := by rw [hψ, deriv_extBranch hμ0 hφ hφ0 L₀]; exact exp_ne_zero _
  have hψ0 : ψ z₀ = 0 := extBranch_self _ _ _ _
  obtain ⟨F, hFa, hF₀, hFe⟩ := dlmf_1_10_12 hψa hψ'
  obtain ⟨R₁, hR₁, h₁⟩ := dlmf_1_10_14 hψa hψ' hg hFa.continuousAt hF₀ hFe
  obtain ⟨R₂, hR₂, h₂⟩ := dlmf_1_10_14 hψa hψ' analyticAt_id hFa.continuousAt hF₀ hFe
  set R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  have hφev : ∀ᶠ s in 𝓝 (ψ z₀), φ (F s) ≠ 0 := by
    have := hφ.continuousAt.eventually_ne hφ0
    rw [← hF₀] at this
    exact hFa.continuousAt.tendsto.eventually this
  have hall := (h₁ R ⟨hR, min_le_left _ _⟩).and ((h₂ R ⟨hR, min_le_right _ _⟩).and
    (hFe.and hφev))
  rw [hψ0] at hall
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨R, hR, ρ, hρ, fun s hs => ?_⟩
  obtain ⟨hsg, hsid, hsF, hsφ⟩ := hball s hs
  rw [sub_zero] at hsg hsid
  refine ⟨F s, hsF, ?_, ?_, fun w hw => ?_⟩
  · rw [lagrangeCoeff_id] at hsid
    simpa [inversionCoeff] using (hasSum_nat_add_iff' 1).mpr hsid
  · simpa [lagrangeCoeff] using (hasSum_nat_add_iff' 1).mpr hsg
  · obtain ⟨Ls, hLs, hμL⟩ := hw
    set z := F s
    have hzz : z ≠ z₀ := fun h => by
      rw [← hsF, h, hψ0] at hLs
      exact exp_ne_zero _ hLs
    have hz' : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
    set ℓ := L₀ + log (φ z / φ z₀)
    have hψz : exp (log (z - z₀) + ℓ / μ) = s := by
      rw [exp_add, exp_log hz', ← hsF, hψ, extBranch]
    obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp (hLs.trans hψz.symm)
    refine ⟨log (z - z₀) + k * (2 * π * I), ?_, ?_⟩
    · rw [exp_add, exp_log hz', exp_int_mul_two_pi_mul_I, mul_one]
    · have hmul : (μ : ℂ) * Ls = μ * (log (z - z₀) + k * (2 * π * I)) + ℓ := by
        rw [hk]
        field_simp
        ring
      rw [← exp_extLog hL₀ hφ0 hsφ, ← exp_add, ← hmul, hμL]
      ring

/-- DLMF §1.10(vii): when `μ = m` is a positive integer, `f(z) − f(z₀) = (z − z₀)^m φ(z)` has a
zero of order `m` at `z₀`. -/
theorem dlmf_1_10_15_integer {φ : ℂ → ℂ} {z₀ : ℂ} (hφ : AnalyticAt ℂ φ z₀) (hφ0 : φ z₀ ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) : IsZeroOfOrder (fun z => (z - z₀) ^ m * φ z) z₀ m := by
  have ha : AnalyticAt ℂ (fun z => (z - z₀) ^ m * φ z) z₀ :=
    ((analyticAt_id.sub analyticAt_const).pow m).mul hφ
  rw [isZeroOfOrder_iff_analyticOrderAt ha hm]
  exact ha.analyticOrderAt_eq_natCast.mpr ⟨φ, hφ, hφ0, Eventually.of_forall fun z => rfl⟩

end Azurite.DLMF
