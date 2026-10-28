/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Cauchy–Pompeiu formula for compactly supported `C¹` functions

For `g : ℂ → ℂ` continuously differentiable (in the real sense) with compact support, and
`∂̄g = (∂ₓg + i ∂ᵧg)/2` (`dbar`),
`∫ ∂̄g(p)/(p − z) dA(p) = −π g(z)` (`cauchyPompeiu`).  The proof passes to polar coordinates
around `z`: with `G(r, θ) = g(z + r e^{iθ})`, the integrand becomes
`(∂ᵣG + (i/r) ∂_θ G)/2`; the `∂ᵣG` term integrates to `−g(z)` in `r` and the `∂_θ G` term to `0`
in `θ`.  This is the identity behind Green's theorem for the winding number
(`Azurite/JordanCurve/Green.lean`).
-/

namespace Azurite.JordanCurve

open Set Filter Topology MeasureTheory Complex
open scoped Real

/-- The Wirtinger derivative `∂̄g = (∂ₓg + i ∂ᵧg)/2` of `g : ℂ → ℂ` (real derivative `fderiv ℝ`). -/
noncomputable def dbar (g : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ g z 1 + I * fderiv ℝ g z I) / 2

/-- `e^{iθ} = cos θ + i sin θ`. -/
noncomputable def unitE (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

theorem unitE_eq_smul (θ : ℝ) : unitE θ = (Real.cos θ) • (1 : ℂ) + (Real.sin θ) • I := by
  simp [unitE, Complex.real_smul]

theorem I_mul_unitE_eq_smul (θ : ℝ) : I * unitE θ = (-Real.sin θ) • (1 : ℂ) + (Real.cos θ) • I := by
  simp only [unitE, Complex.real_smul]
  apply Complex.ext <;> simp

theorem norm_unitE (θ : ℝ) : ‖unitE θ‖ = 1 := by
  have : unitE θ = exp (θ * I) := by rw [exp_mul_I, unitE, ofReal_cos, ofReal_sin]
  rw [this, norm_exp_ofReal_mul_I]

theorem unitE_ne_zero (θ : ℝ) : unitE θ ≠ 0 := by
  intro h
  have := norm_unitE θ
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem unitE_pi_eq : unitE π = unitE (-π) := by
  simp [unitE]

theorem hasDerivAt_unitE (θ : ℝ) : HasDerivAt unitE (I * unitE θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const I)
  refine h.congr_deriv ?_
  simp only [unitE]
  apply Complex.ext <;> simp

theorem continuous_unitE : Continuous unitE :=
  (continuous_ofReal.comp Real.continuous_cos).add
    ((continuous_ofReal.comp Real.continuous_sin).mul continuous_const)

/-- `fderiv g p` applied to `e^{iθ}` and `i e^{iθ}`, in terms of `∂ₓg = fderiv g p 1` and
`∂ᵧg = fderiv g p I`. -/
theorem fderiv_apply_unitE (g : ℂ → ℂ) (p : ℂ) (θ : ℝ) :
    fderiv ℝ g p (unitE θ) = (Real.cos θ : ℂ) * fderiv ℝ g p 1 + (Real.sin θ : ℂ) * fderiv ℝ g p I ∧
      fderiv ℝ g p (I * unitE θ) =
        -(Real.sin θ : ℂ) * fderiv ℝ g p 1 + (Real.cos θ : ℂ) * fderiv ℝ g p I := by
  constructor
  · rw [unitE_eq_smul, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  · rw [I_mul_unitE_eq_smul, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul,
      ofReal_neg]

/-- The polar-coordinate integrand: for `r ≠ 0`,
`r • (∂̄g(z + r e^{iθ}) / (r e^{iθ})) = (Dg(e^{iθ}) + i Dg(i e^{iθ}))/2`. -/
theorem polar_integrand (g : ℂ → ℂ) (z : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • (dbar g (z + r * unitE θ) / (z + r * unitE θ - z)) =
      (fderiv ℝ g (z + r * unitE θ) (unitE θ) +
        I * fderiv ℝ g (z + r * unitE θ) (I * unitE θ)) / 2 := by
  obtain ⟨h1, h2⟩ := fderiv_apply_unitE g (z + r * unitE θ) θ
  set A1 := fderiv ℝ g (z + r * unitE θ) 1
  set AI := fderiv ℝ g (z + r * unitE θ) I
  rw [h1, h2, dbar, Complex.real_smul, add_sub_cancel_left]
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hE := unitE_ne_zero θ
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_add, Real.cos_sq_add_sin_sq, ofReal_one]
  have key : (A1 + I * AI) / 2 / unitE θ =
      ((Real.cos θ : ℂ) * A1 + (Real.sin θ : ℂ) * AI +
        I * (-(Real.sin θ : ℂ) * A1 + (Real.cos θ : ℂ) * AI)) / 2 := by
    rw [div_div, div_eq_div_iff (mul_ne_zero two_ne_zero hE) two_ne_zero]
    simp only [unitE]
    linear_combination (-2 * (A1 + I * AI)) * hcs +
      (-2 * ((Real.sin θ : ℂ) * (Real.cos θ : ℂ) * AI - A1 * (Real.sin θ : ℂ) ^ 2)) * I_sq
  rw [← key, div_div, div_div, mul_div_assoc', mul_left_comm (2 : ℂ) (r : ℂ),
    mul_div_mul_left _ _ hr']

/-- Outside a closed ball containing the support of `g`, `fderiv g` vanishes. -/
theorem fderiv_eq_zero_of_norm_gt {g : ℂ → ℂ} {R : ℝ} (hR : tsupport g ⊆ Metric.closedBall 0 R)
    {p : ℂ} (hp : R < ‖p‖) : fderiv ℝ g p = 0 := by
  have hp' : p ∉ tsupport g := fun h => by
    have := hR h
    rw [mem_closedBall_zero_iff] at this
    linarith
  have h0 : g =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp'
  rw [h0.fderiv_eq]
  exact fderiv_const_apply 0

/-- `‖z + w‖ ≥ ‖w‖ − ‖z‖`. -/
theorem norm_sub_le_norm_add' (z w : ℂ) : ‖w‖ - ‖z‖ ≤ ‖z + w‖ := by
  have := norm_sub_le (z + w) z
  rw [add_sub_cancel_left] at this
  linarith

/-- **The Cauchy–Pompeiu formula** for a compactly supported `C¹` function `g : ℂ → ℂ`:
`∫ ∂̄g(p)/(p − z) dA(p) = −π g(z)`. -/
theorem cauchyPompeiu {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) (z : ℂ) :
    ∫ p, dbar g p / (p - z) = -π * g z := by
  set A : ℂ → ℂ →L[ℝ] ℂ := fderiv ℝ g with hA
  have hAc : Continuous A := hg.continuous_fderiv one_ne_zero
  obtain ⟨R₀', hR₀'⟩ := hsupp.isCompact.isBounded.subset_closedBall 0
  set R₀ := max R₀' 0 with hR₀def
  have hR₀ : tsupport g ⊆ Metric.closedBall 0 R₀ :=
    hR₀'.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR₀0 : 0 ≤ R₀ := le_max_right _ _
  have hA0 : ∀ p, R₀ < ‖p‖ → A p = 0 := fun p hp => fderiv_eq_zero_of_norm_gt hR₀ hp
  have hg0 : ∀ p, R₀ < ‖p‖ → g p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR₀ h
      rw [mem_closedBall_zero_iff] at this
      linarith
  set R₁ := R₀ + ‖z‖ + 1 with hR₁
  have hfar : ∀ (r : ℝ) (θ : ℝ), R₁ ≤ r → R₀ < ‖z + r * unitE θ‖ := fun r θ hr => by
    have hr0 : 0 ≤ r := by linarith [norm_nonneg z]
    calc R₀ < r - ‖z‖ := by linarith
      _ = ‖(r : ℂ) * unitE θ‖ - ‖z‖ := by
          rw [norm_mul, norm_unitE, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hr0]
      _ ≤ ‖z + r * unitE θ‖ := norm_sub_le_norm_add' _ _
  -- the derivative of `g` along rays and circles
  have hray : ∀ (θ : ℝ) (r : ℝ), HasDerivAt (fun r : ℝ => g (z + r * unitE θ))
      (A (z + r * unitE θ) (unitE θ)) r := fun θ r => by
    have hin : HasDerivAt (fun r : ℝ => z + (r : ℂ) * unitE θ) (unitE θ) r := by
      have := (((hasDerivAt_id r).ofReal_comp).mul_const (unitE θ)).const_add z
      simpa using this
    exact (hg.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r hin
  have hcirc : ∀ (r : ℝ) (θ : ℝ), HasDerivAt (fun θ : ℝ => g (z + r * unitE θ))
      (A (z + r * unitE θ) ((r : ℂ) * (I * unitE θ))) θ := fun r θ =>
    (hg.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ
      (((hasDerivAt_unitE θ).const_mul (r : ℂ)).const_add z)
  -- the two halves of the polar integrand
  set h₁ : ℝ × ℝ → ℂ := fun q => A (z + q.1 * unitE q.2) (unitE q.2) / 2 with hh₁
  set h₂ : ℝ × ℝ → ℂ := fun q => I * A (z + q.1 * unitE q.2) (I * unitE q.2) / 2 with hh₂
  have hpt : Continuous fun q : ℝ × ℝ => z + (q.1 : ℂ) * unitE q.2 :=
    continuous_const.add ((continuous_ofReal.comp continuous_fst).mul
      (continuous_unitE.comp continuous_snd))
  have hc₁ : Continuous h₁ :=
    ((hAc.comp hpt).clm_apply (continuous_unitE.comp continuous_snd)).div_const 2
  have hc₂ : Continuous h₂ :=
    (continuous_const.mul ((hAc.comp hpt).clm_apply
      (continuous_const.mul (continuous_unitE.comp continuous_snd)))).div_const 2
  have hz₁ : ∀ q : ℝ × ℝ, R₁ ≤ q.1 → h₁ q = 0 := fun q hq => by
    simp only [hh₁, hA0 _ (hfar q.1 q.2 hq), zero_apply, zero_div]
  have hz₂ : ∀ q : ℝ × ℝ, R₁ ≤ q.1 → h₂ q = 0 := fun q hq => by
    simp only [hh₂, hA0 _ (hfar q.1 q.2 hq), zero_apply, mul_zero, zero_div]
  have hint : ∀ {k : ℝ × ℝ → ℂ}, Continuous k → (∀ q : ℝ × ℝ, R₁ ≤ q.1 → k q = 0) →
      IntegrableOn k polarCoord.target := fun {k} hk hk0 => by
    have hbox : IntegrableOn k (Icc 0 R₁ ×ˢ Icc (-π) π) :=
      hk.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hbox.of_forall_sdiff_eq_zero polarCoord.open_target.measurableSet fun q hq => ?_
    rw [polarCoord_target] at hq
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    refine hk0 q ?_
    by_contra hlt
    push Not at hlt
    exact h3 ⟨⟨le_of_lt h1, hlt.le⟩, ⟨h2.1.le, h2.2.le⟩⟩
  have hint₁ := hint hc₁ hz₁
  have hint₂ := hint hc₂ hz₂
  -- change to polar coordinates about `z`
  have hpolar : ∫ p, dbar g p / (p - z) = ∫ q in polarCoord.target, (h₁ q + h₂ q) := by
    rw [← integral_add_right_eq_self (fun p => dbar g p / (p - z)) z,
      ← Complex.integral_comp_polarCoord_symm]
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun q hq => ?_
    rw [polarCoord_target] at hq
    have hq1 : (0 : ℝ) < q.1 := hq.1
    have e : (Complex.polarCoord.symm q : ℂ) + z = z + q.1 * unitE q.2 := by
      rw [Complex.polarCoord_symm_apply, unitE]
      ring
    show q.1 • (dbar g (Complex.polarCoord.symm q + z) / (Complex.polarCoord.symm q + z - z)) =
      h₁ q + h₂ q
    rw [e, polar_integrand g z hq1.ne' q.2, hh₁, hh₂]
    simp only [hA]
    ring
  have hint₁' : Integrable h₁ ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) := by
    have := hint₁
    rwa [IntegrableOn, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict] at this
  have hint₂' : Integrable h₂ ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) := by
    have := hint₂
    rwa [IntegrableOn, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict] at this
  -- the circle term vanishes: for each `r > 0`, `∫_{-π}^{π} ∂_θ G dθ = 0`
  have hterm₂ : ∫ q in polarCoord.target, h₂ q = 0 := by
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint₂']
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hr)
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]
    set Φ : ℝ → ℂ := fun θ => I / (2 * r) * g (z + r * unitE θ) with hΦ
    have hΦd : ∀ θ, HasDerivAt Φ (I / (2 * r) * A (z + r * unitE θ) ((r : ℂ) * (I * unitE θ))) θ :=
      fun θ => (hcirc r θ).const_mul _
    have hcont : Continuous fun θ => I / (2 * r) * A (z + r * unitE θ) ((r : ℂ) * (I * unitE θ)) :=
      continuous_const.mul ((hAc.comp (continuous_const.add
        (continuous_const.mul continuous_unitE))).clm_apply
        (continuous_const.mul (continuous_const.mul continuous_unitE)))
    calc ∫ θ in (-π)..π, h₂ (r, θ)
        = ∫ θ in (-π)..π, I / (2 * r) * A (z + r * unitE θ) ((r : ℂ) * (I * unitE θ)) := by
          refine intervalIntegral.integral_congr fun θ _ => ?_
          have hlin : A (z + r * unitE θ) ((r : ℂ) * (I * unitE θ)) =
              (r : ℂ) * A (z + r * unitE θ) (I * unitE θ) := by
            rw [show (r : ℂ) * (I * unitE θ) = r • (I * unitE θ) from Complex.real_smul.symm,
              map_smul, Complex.real_smul]
          simp only [hh₂]
          rw [hlin]
          field_simp
      _ = Φ π - Φ (-π) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hΦd θ)
            (hcont.intervalIntegrable _ _)
      _ = 0 := by simp [hΦ, unitE_pi_eq]
  -- the radial term: for each `θ`, `∫_0^∞ ∂ᵣG dr = −g(z)`
  have hterm₁ : ∫ q in polarCoord.target, h₁ q = -π * g z := by
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
      integral_prod_symm _ hint₁']
    have hinner : ∀ θ, ∫ r in Ioi 0, h₁ (r, θ) = -g z / 2 := fun θ => by
      have hG : ∀ r, HasDerivAt (fun r : ℝ => g (z + r * unitE θ) / 2) (h₁ (r, θ)) r :=
        fun r => (hray θ r).div_const 2
      have hIoi : IntegrableOn (fun r => h₁ (r, θ)) (Ioi 0) := by
        have hbox : IntegrableOn (fun r => h₁ (r, θ)) (Icc 0 R₁) :=
          (hc₁.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact
            isCompact_Icc
        refine hbox.of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr => hz₁ (r, θ) ?_
        simp only [Set.mem_sdiff, mem_Ioi, mem_Icc, not_and, not_le] at hr
        exact (hr.2 hr.1.le).le
      have hlim : Tendsto (fun r : ℝ => g (z + r * unitE θ) / 2) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop R₁] with r hr
        rw [hg0 _ (hfar r θ hr), zero_div]
      rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ => hG r) hIoi hlim]
      simp only [ofReal_zero, zero_mul, add_zero]
      ring
    simp_rw [hinner]
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), Complex.real_smul]
    push_cast
    ring
  rw [hpolar, integral_add hint₁ hint₂, hterm₁, hterm₂, add_zero]

end Azurite.JordanCurve
