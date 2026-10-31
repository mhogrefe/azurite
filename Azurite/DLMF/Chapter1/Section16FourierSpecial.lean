/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16Heaviside
import Azurite.DLMF.Chapter1.Section16Tempered
import Azurite.DLMF.Chapter1.Section14HilbertDense
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# DLMF §1.16(viii): Fourier transforms of special distributions

https://dlmf.nist.gov/1.16.viii

Here `n = 1` and `𝒯 = tempSpace` (§1.16(v)), so §1.14's `dlmfFourier`
`𝓕φ(x) = (1/√(2π)) ∫ φ(t) e^{ixt} dt` is used. It is Mathlib's Schwartz Fourier transform on `ℝ`
composed with `x ↦ −x/(2π)` and scaled (`fourier1CLM`), hence `𝓕 : 𝒯 → 𝒯` (`fourierTest1`) with
`𝓕𝓕φ = φ₋` (`fourierTest1_fourierTest1`). The transform of a tempered `u` is
`⟨𝓕(u), φ⟩ = ⟨u, 𝓕φ⟩` (`fourierDist1`, again tempered: `isTempDist_fourierDist1`).

* `1`, `sign`, `H` are the regular tempered distributions `tempOne`, `tempSign`, `tempH` of bounded
  functions (`boundedTemp`).
* 1.16.38–1.16.39: `𝓕(δ) = (1/√(2π)) 1`.
* 1.16.40 and 1.16.43, the formal integrals `∫ δ(t) e^{ixt} dt = 1` and
  `(1/(2π)) ∫ e^{ixt} dt = δ`, are read as `√(2π) 𝓕(δ) = 1` and `(1/√(2π)) 𝓕(1) = δ`.
* 1.16.41–1.16.42: `𝓕(1) = √(2π) δ` through `𝓕𝓕φ = φ₋`.
* 1.16.44–1.16.46: `sign = 2H − 1` off `0`, `sign' = 2H' = 2δ` (`tempDeriv`, from
  `∫_0^∞ φ' = −φ(0)`), and `𝓕(sign') = √(2/π)`.
* 1.16.47: `𝓕(u') = (x/i) 𝓕(u)` for every tempered `u` (`fourierDist1_tempDeriv`), from
  `(𝓕φ)' = 𝓕(ixφ)` (`derivTempTest_fourierTest1`).
* 1.16.48–1.16.49: `𝓕(sign) = i √(2/π) (1/x)`, with `1/x` the principal-value distribution
  `pvDist`, `⟨1/x, φ⟩ = ∫_0^∞ (φ(t) − φ(−t))/t dt` (`pvInvX`), equal to
  `lim_{ε→0+} ∫_{|x|>ε} φ(x)/x dx` (`tendsto_pvInvX`). Equation 1.16.47 alone fixes `𝓕(sign)` only
  up to a multiple of `δ`, so the proof instead inserts the damping `e^{−ε|x|}`: then
  `∫ sign(x) e^{−ε|x|} 𝓕φ(x) dx = i√(2π)` times the conjugate Poisson integral of `φ` at `0`
  (§1.14(v), `conjPoissonInt_eq_dlmfFourier`), which tends to `(1/π) ⨍ φ(x)/x dx`
  (`tendsto_conjPoissonInt_zero`).
* 1.16.50–1.16.51: `H = (1 + sign)/2` (`tempH_eq`), so
  `𝓕(H) = √(π/2) (δ + i/(πx))` and `⟨𝓕(H), φ⟩ = √(π/2) φ(0) + (i/√(2π)) ⨍ φ(x)/x dx`.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory Complex
open scoped ContDiff SchwartzMap Real FourierTransform

namespace Azurite.DLMF

/-! ### The Fourier transform on `𝒯(ℝ)` (the case `n = 1` of §1.16(vii)) -/

/-- The scaling `x ↦ −x/(2π)`. -/
noncomputable def fourierScale : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (-(2 * π)⁻¹) (by
    have := Real.pi_pos; simp))

theorem fourierScale_apply (x : ℝ) : fourierScale x = -x / (2 * π) := by
  simp [fourierScale, ContinuousLinearEquiv.unitsEquivAut_apply, div_eq_mul_inv]

/-- DLMF's Fourier transform `(1/√(2π)) ∫ φ(t) e^{ixt} dt` as a continuous linear map of
`𝓢(ℝ, ℂ)`. -/
noncomputable def fourier1CLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (((√(2 * π) : ℝ) : ℂ)⁻¹) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierScale ∘L
    SchwartzMap.fourierTransformCLM ℂ)

theorem coe_fourier1CLM (f : 𝓢(ℝ, ℂ)) : ⇑(fourier1CLM f) = dlmfFourier ⇑f := by
  funext x
  simp only [fourier1CLM, smul_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, smul_eq_mul,
    SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, dlmfFourier]
  congr 1
  rw [Real.fourier_real_eq, fourierScale_apply]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm]
  congr 2
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- `𝓕φ ∈ 𝒯` for `φ ∈ 𝒯`. -/
noncomputable def fourierTest1 : tempSpace →ₗ[ℂ] tempSpace :=
  tempEquiv.symm.toLinearMap ∘ₗ fourier1CLM.toLinearMap ∘ₗ tempEquiv.toLinearMap

theorem coe_fourierTest1 (φ : tempSpace) :
    (fourierTest1 φ : ℝ → ℂ) = dlmfFourier (φ : ℝ → ℂ) := by
  change ⇑(fourier1CLM (tempEquiv φ)) = _
  rw [coe_fourier1CLM, coe_tempEquiv]

theorem integrable_tempSpace (φ : tempSpace) : Integrable (φ : ℝ → ℂ) := by
  rw [← coe_tempEquiv]; exact (tempEquiv φ).integrable

/-- The Fourier integral formula (1.17.8): `𝓕(𝓕φ) = φ₋`. -/
theorem fourierTest1_fourierTest1 (φ : tempSpace) (x : ℝ) :
    (fourierTest1 (fourierTest1 φ) : ℝ → ℂ) x = (φ : ℝ → ℂ) (-x) := by
  rw [coe_fourierTest1, coe_fourierTest1]
  have h := congrFun (eq_dlmfFourier_neg (integrable_tempSpace φ)
    (by rw [← coe_fourierTest1]; exact integrable_tempSpace _) φ.2.1.continuous) (-x)
  rw [h, neg_neg]

/-- The Fourier transform of a tempered distribution (1.16.35 with `n = 1`). -/
noncomputable def fourierDist1 (u : tempSpace →ₗ[ℂ] ℂ) : tempSpace →ₗ[ℂ] ℂ :=
  u ∘ₗ fourierTest1

theorem isTempDist_fourierDist1 {u : tempSpace →ₗ[ℂ] ℂ} (hu : IsTempDist u) :
    IsTempDist (fourierDist1 u) := by
  rw [isTempDist_iff_continuous] at hu ⊢
  have e : ⇑(fourierDist1 u ∘ₗ tempEquiv.symm.toLinearMap) =
      ⇑(u ∘ₗ tempEquiv.symm.toLinearMap) ∘ ⇑fourier1CLM := by
    funext ψ
    simp [fourierDist1, fourierTest1]
  rw [e]
  exact hu.comp fourier1CLM.continuous

/-! ### Bounded regular tempered distributions: `1`, `sign`, `H` -/

/-- The regular tempered distribution of a bounded measurable function. -/
noncomputable def boundedTemp {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) : tempSpace →ₗ[ℂ] ℂ :=
  tempRegular hf hC (M := 0) fun x => by simpa using hb x

theorem boundedTemp_apply {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) (φ : tempSpace) :
    boundedTemp hf hC hb φ = ∫ x, f x * (φ : ℝ → ℂ) x := rfl

theorem isTempDist_boundedTemp {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) : IsTempDist (boundedTemp hf hC hb) :=
  isTempDist_tempRegular _ _ _

/-- The constant `1` as a tempered distribution, `⟨1, φ⟩ = ∫ φ`. -/
noncomputable def tempOne : tempSpace →ₗ[ℂ] ℂ :=
  boundedTemp (f := fun _ => 1) aestronglyMeasurable_const zero_le_one fun _ => by simp

theorem tempOne_apply (φ : tempSpace) : tempOne φ = ∫ x, (φ : ℝ → ℂ) x := by
  simp [tempOne, boundedTemp_apply]

theorem norm_sign_le (x : ℝ) : ‖((Real.sign x : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [Real.sign_of_neg h]
  · simp
  · simp [Real.sign_of_pos h]

/-- `sign` as a tempered distribution. -/
noncomputable def tempSign : tempSpace →ₗ[ℂ] ℂ :=
  boundedTemp (f := fun x => ((Real.sign x : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp measurable_realSign).aestronglyMeasurable zero_le_one
    norm_sign_le

theorem norm_heavisideH_le (x : ℝ) : ‖((heavisideH x : ℝ) : ℂ)‖ ≤ 1 := by
  unfold heavisideH; split_ifs <;> simp

theorem measurable_heavisideH : Measurable heavisideH := by
  unfold heavisideH
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-- `H` as a tempered distribution. -/
noncomputable def tempH : tempSpace →ₗ[ℂ] ℂ :=
  boundedTemp (f := fun x => ((heavisideH x : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp measurable_heavisideH).aestronglyMeasurable zero_le_one
    norm_heavisideH_le

/-! ### `𝓕(δ) = 1/√(2π)` and `𝓕(1) = √(2π) δ` (1.16.38–1.16.43) -/

/-- DLMF 1.16.38: `⟨𝓕(δ), φ⟩ = ⟨δ, 𝓕(φ)⟩ = (1/√(2π)) ∫ φ(t) dt = (1/√(2π)) ⟨1, φ⟩`. -/
theorem dlmf_1_16_38 (φ : tempSpace) :
    fourierDist1 (tempDirac 0) φ = tempDirac 0 (fourierTest1 φ) ∧
      tempDirac 0 (fourierTest1 φ) = ((√(2 * π) : ℝ) : ℂ)⁻¹ * ∫ t, (φ : ℝ → ℂ) t ∧
      ((√(2 * π) : ℝ) : ℂ)⁻¹ * ∫ t, (φ : ℝ → ℂ) t = ((√(2 * π) : ℝ) : ℂ)⁻¹ * tempOne φ := by
  refine ⟨rfl, ?_, by rw [tempOne_apply]⟩
  change (fourierTest1 φ : ℝ → ℂ) 0 = _
  rw [coe_fourierTest1, dlmfFourier]
  simp

/-- DLMF 1.16.39: `𝓕(δ) = 1/√(2π)`. -/
theorem dlmf_1_16_39 : fourierDist1 (tempDirac 0) = ((√(2 * π) : ℝ) : ℂ)⁻¹ • tempOne := by
  ext φ
  obtain ⟨h1, h2, h3⟩ := dlmf_1_16_38 φ
  rw [h1, h2, h3]; rfl

/-- DLMF 1.16.40, the conventional `∫ δ(t) e^{ixt} dt = 1`, read as `√(2π) 𝓕(δ) = 1`. -/
theorem dlmf_1_16_40 : ((√(2 * π) : ℝ) : ℂ) • fourierDist1 (tempDirac 0) = tempOne := by
  have h : ((√(2 * π) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [dlmf_1_16_39, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem fourierDist1_smul (c : ℂ) (u : tempSpace →ₗ[ℂ] ℂ) :
    fourierDist1 (c • u) = c • fourierDist1 u := rfl

/-- DLMF 1.16.41:
`⟨𝓕(1), φ⟩ = √(2π)⟨𝓕(𝓕(δ)), φ⟩ = √(2π)⟨𝓕(δ), 𝓕(φ)⟩ = √(2π)⟨δ, 𝓕(𝓕(φ))⟩ = √(2π)⟨δ, φ₋⟩
= √(2π) φ(0)`. -/
theorem dlmf_1_16_41 (φ : tempSpace) :
    fourierDist1 tempOne φ =
        ((√(2 * π) : ℝ) : ℂ) * fourierDist1 (fourierDist1 (tempDirac 0)) φ ∧
      fourierDist1 (fourierDist1 (tempDirac 0)) φ = fourierDist1 (tempDirac 0) (fourierTest1 φ) ∧
      fourierDist1 (tempDirac 0) (fourierTest1 φ) = tempDirac 0 (fourierTest1 (fourierTest1 φ)) ∧
      tempDirac 0 (fourierTest1 (fourierTest1 φ)) = (φ : ℝ → ℂ) (-0) ∧
      (φ : ℝ → ℂ) (-0) = (φ : ℝ → ℂ) 0 := by
  refine ⟨?_, rfl, rfl, fourierTest1_fourierTest1 φ 0, by rw [neg_zero]⟩
  rw [← dlmf_1_16_40, fourierDist1_smul]
  rfl

/-- DLMF 1.16.42: `𝓕(1) = √(2π) δ`. -/
theorem dlmf_1_16_42 : fourierDist1 tempOne = ((√(2 * π) : ℝ) : ℂ) • tempDirac 0 := by
  ext φ
  obtain ⟨h1, h2, h3, h4, h5⟩ := dlmf_1_16_41 φ
  rw [h1, h2, h3, h4, h5]
  rfl

/-- DLMF 1.16.43, the conventional `(1/(2π)) ∫ e^{ixt} dt = δ`, read as `(1/√(2π)) 𝓕(1) = δ`. -/
theorem dlmf_1_16_43 : ((√(2 * π) : ℝ) : ℂ)⁻¹ • fourierDist1 tempOne = tempDirac 0 := by
  have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [dlmf_1_16_42, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-! ### `sign` and `H` (1.16.44–1.16.46) -/

/-- DLMF 1.16.44: `sign(x) = 2H(x) − 1` for `x ≠ 0`. -/
theorem dlmf_1_16_44 {x : ℝ} (hx : x ≠ 0) : Real.sign x = 2 * heavisideH x - 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [Real.sign_of_neg h, heavisideH, not_lt.mpr h.le]
  · simp [Real.sign_of_pos h, heavisideH, h]; norm_num

theorem abs_mul_norm_le (φ : tempSpace) : ∃ c, ∀ x : ℝ, |x| * ‖(φ : ℝ → ℂ) x‖ ≤ c := by
  obtain ⟨c, hc⟩ := (isTempTest_iff_bound.mp φ.2).2 0 1
  exact ⟨c, fun x => by
    have := hc x
    rwa [norm_pow_mul, pow_one, iteratedDeriv_zero] at this⟩

theorem tendsto_tempSpace_atTop (φ : tempSpace) : Tendsto (φ : ℝ → ℂ) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := abs_mul_norm_le φ
  refine squeeze_zero_norm' (a := fun x => c / x) ?_
    ((tendsto_const_nhds (x := c)).div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [le_div_iff₀ hx, mul_comm]
  have := hc x
  rwa [abs_of_pos hx] at this

theorem tendsto_tempSpace_atBot (φ : tempSpace) : Tendsto (φ : ℝ → ℂ) atBot (𝓝 0) := by
  obtain ⟨c, hc⟩ := abs_mul_norm_le φ
  refine squeeze_zero_norm' (a := fun x => c / -x) ?_
    ((tendsto_const_nhds (x := c)).div_atTop tendsto_neg_atBot_atTop)
  filter_upwards [eventually_lt_atBot 0] with x hx
  rw [le_div_iff₀ (by linarith), mul_comm]
  have := hc x
  rwa [abs_of_neg hx] at this

theorem integral_Ioi_deriv_temp (φ : tempSpace) :
    ∫ x in Ioi 0, deriv (φ : ℝ → ℂ) x = -(φ : ℝ → ℂ) 0 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) φ.2.1.continuous.continuousWithinAt
    (fun x _ => ((φ.2.1.differentiable (by simp)) x).hasDerivAt)
    (integrable_tempSpace (derivTempTest φ)).integrableOn (tendsto_tempSpace_atTop φ), zero_sub]

theorem integral_Iic_deriv_temp (φ : tempSpace) :
    ∫ x in Iic 0, deriv (φ : ℝ → ℂ) x = (φ : ℝ → ℂ) 0 := by
  rw [integral_Iic_of_hasDerivAt_of_tendsto (m := 0) φ.2.1.continuous.continuousWithinAt
    (fun x _ => ((φ.2.1.differentiable (by simp)) x).hasDerivAt)
    (integrable_tempSpace (derivTempTest φ)).integrableOn (tendsto_tempSpace_atBot φ), sub_zero]

/-- DLMF 1.16.45: `sign' = 2δ` in the sense of distributions. -/
theorem dlmf_1_16_45_sign : tempDeriv tempSign = (2 : ℂ) • tempDirac 0 := by
  ext φ
  have hi : Integrable fun x => ((Real.sign x : ℝ) : ℂ) * deriv (φ : ℝ → ℂ) x :=
    integrable_mul_of_polyBound (M := 0) (C := 1)
      (Complex.measurable_ofReal.comp measurable_realSign).aestronglyMeasurable zero_le_one
      (fun x => by simpa using norm_sign_le x) (derivTempTest φ).2
  change -(∫ x, ((Real.sign x : ℝ) : ℂ) * deriv (φ : ℝ → ℂ) x) = 2 * (φ : ℝ → ℂ) 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic]
  have h1 : ∫ x in Iic 0, ((Real.sign x : ℝ) : ℂ) * deriv (φ : ℝ → ℂ) x =
      -∫ x in Iic 0, deriv (φ : ℝ → ℂ) x := by
    rw [← integral_neg]
    refine setIntegral_congr_ae measurableSet_Iic ?_
    filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with x hx hxI
    have : x < 0 := lt_of_le_of_ne hxI fun e => hx (by rw [e]; rfl)
    simp [Real.sign_of_neg this]
  have h2 : ∫ x in Ioi 0, ((Real.sign x : ℝ) : ℂ) * deriv (φ : ℝ → ℂ) x =
      ∫ x in Ioi 0, deriv (φ : ℝ → ℂ) x :=
    setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => by simp [Real.sign_of_pos hx]
  rw [h1, h2, integral_Iic_deriv_temp, integral_Ioi_deriv_temp]
  ring

/-- DLMF 1.16.45: `H' = δ`, so `sign' = 2H' = 2δ`. -/
theorem dlmf_1_16_45_heaviside : tempDeriv tempH = tempDirac 0 := by
  ext φ
  change -(∫ x, ((heavisideH x : ℝ) : ℂ) * deriv (φ : ℝ → ℂ) x) = (φ : ℝ → ℂ) 0
  have e : (fun x => ((heavisideH x : ℝ) : ℂ) * deriv (φ : ℝ → ℂ) x) =
      (Ioi 0).indicator (deriv (φ : ℝ → ℂ)) := funext fun x => by
    by_cases h : 0 < x <;> simp [heavisideH, h, indicator]
  rw [e, integral_indicator measurableSet_Ioi, integral_Ioi_deriv_temp, neg_neg]

/-- DLMF 1.16.46: `𝓕(sign') = 𝓕(2H') = 2𝓕(δ) = √(2/π)`. -/
theorem dlmf_1_16_46 :
    fourierDist1 (tempDeriv tempSign) = fourierDist1 ((2 : ℂ) • tempDeriv tempH) ∧
      fourierDist1 ((2 : ℂ) • tempDeriv tempH) = (2 : ℂ) • fourierDist1 (tempDirac 0) ∧
      (2 : ℂ) • fourierDist1 (tempDirac 0) = ((√(2 / π) : ℝ) : ℂ) • tempOne := by
  refine ⟨by rw [dlmf_1_16_45_sign, dlmf_1_16_45_heaviside], by
    rw [dlmf_1_16_45_heaviside]; rfl, ?_⟩
  rw [dlmf_1_16_39, smul_smul]
  congr 1
  have hπ := Real.pi_pos
  have h2 : √(2 / π) = 2 * (√(2 * π))⁻¹ := by
    rw [Real.sqrt_div' 2 hπ.le, Real.sqrt_mul (by norm_num) π]
    have hs : 0 < √π := Real.sqrt_pos.mpr hπ
    have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hππ : √π * √π = π := Real.mul_self_sqrt hπ.le
    field_simp
    nlinarith
  rw [h2]
  push_cast
  ring

/-! ### `𝓕(u') = (x/i) 𝓕(u)` (1.16.47) -/

theorem isTempTest_mul_x {φ : ℝ → ℂ} (hφ : IsTempTest φ) : IsTempTest fun t => (t : ℂ) * φ t := by
  obtain ⟨f, rfl⟩ := isTempTest_iff_schwartz.mp hφ
  refine isTempTest_iff_schwartz.mpr ⟨SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => ((t : ℝ) : ℂ)) f, ?_⟩
  funext t
  exact (SchwartzMap.smulLeftCLM_apply_apply (g := fun t : ℝ => ((t : ℝ) : ℂ))
    Complex.ofRealCLM.hasTemperateGrowth f t).trans (smul_eq_mul _ _)

/-- Multiplication by `x` on `𝒯`. -/
noncomputable def tempX : tempSpace →ₗ[ℂ] tempSpace where
  toFun φ := ⟨fun t => (t : ℂ) * (φ : ℝ → ℂ) t, isTempTest_mul_x φ.2⟩
  map_add' φ ψ := by ext x; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c φ := by
    ext x; simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

theorem hasDerivAt_dlmfFourier_temp (φ : tempSpace) (x : ℝ) :
    HasDerivAt (dlmfFourier (φ : ℝ → ℂ))
      (dlmfFourier (fun t => I * t * (φ : ℝ → ℂ) t) x) x := by
  have hφ := integrable_tempSpace φ
  have hxφ : Integrable fun t : ℝ => ‖(t : ℂ)‖ * ‖(φ : ℝ → ℂ) t‖ := by
    have := (integrable_tempSpace (tempX φ)).norm
    exact this.congr (ae_of_all _ fun t => by simp [tempX])
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := x)
    (F := fun (x t : ℝ) => (φ : ℝ → ℂ) t * cexp (I * x * t))
    (F' := fun (x t : ℝ) => (φ : ℝ → ℂ) t * (I * t * cexp (I * x * t)))
    (bound := fun t : ℝ => ‖(t : ℂ)‖ * ‖(φ : ℝ → ℂ) t‖) (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (hφ.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun t => by
      rw [show I * (y : ℂ) * t = ((y * t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])).aestronglyMeasurable)
    (hφ.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun t => by
      rw [show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]))
    (hφ.aestronglyMeasurable.mul (by fun_prop))
    (ae_of_all _ fun t y _ => by
      rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul,
        show I * (y : ℂ) * t = ((y * t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, mul_comm])
    hxφ
    (ae_of_all _ fun t y _ => by
      have h := ((hasDerivAt_id (y : ℝ)).ofReal_comp.const_mul (I * t)).cexp
      have h2 := h.const_mul ((φ : ℝ → ℂ) t)
      convert h2 using 1
      · funext z; simp only [id]; ring_nf
      · simp only [id]; push_cast; ring_nf)
  have := key.2.const_mul (((√(2 * π) : ℝ) : ℂ)⁻¹)
  convert this using 1
  · funext y; rfl
  · simp only [dlmfFourier]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    ring

/-- `(𝓕φ)' = 𝓕(i x φ)` in `𝒯`. -/
theorem derivTempTest_fourierTest1 (φ : tempSpace) :
    derivTempTest (fourierTest1 φ) = fourierTest1 (I • tempX φ) := by
  apply Subtype.ext
  funext x
  rw [coe_derivTempTest, coe_fourierTest1, coe_fourierTest1,
    (hasDerivAt_dlmfFourier_temp φ x).deriv]
  congr 1
  funext t
  simp [tempX]
  ring

/-- `⟨𝓕(u'), φ⟩ = ⟨𝓕(u), (x/i)φ⟩`, i.e. `𝓕(u') = (x/i) 𝓕(u)` (1.16.36 with `P(x) = ix`). -/
theorem fourierDist1_tempDeriv (u : tempSpace →ₗ[ℂ] ℂ) (φ : tempSpace) :
    fourierDist1 (tempDeriv u) φ = fourierDist1 u (I⁻¹ • tempX φ) := by
  simp only [fourierDist1, LinearMap.comp_apply, tempDeriv_apply, derivTempTest_fourierTest1,
    map_smul, smul_eq_mul]
  rw [inv_I]
  ring

/-- DLMF 1.16.47: `𝓕(sign') = (x/i) 𝓕(sign)`. -/
theorem dlmf_1_16_47 (φ : tempSpace) :
    fourierDist1 (tempDeriv tempSign) φ = fourierDist1 tempSign (I⁻¹ • tempX φ) :=
  fourierDist1_tempDeriv tempSign φ

/-! ### The principal value `⨍ φ(x)/x dx` -/

/-- `⨍ φ(x)/x dx = ∫_0^∞ (φ(t) − φ(−t))/t dt`. -/
noncomputable def pvInvX (φ : ℝ → ℂ) : ℂ := ∫ t in Ioi 0, (φ t - φ (-t)) / t

theorem integrableOn_pvInvX (φ : tempSpace) :
    IntegrableOn (fun t => ((φ : ℝ → ℂ) t - (φ : ℝ → ℂ) (-t)) / t) (Ioi 0) := by
  set g := fun t : ℝ => ((φ : ℝ → ℂ) t - (φ : ℝ → ℂ) (-t)) / t
  have hcont : ContinuousOn g (Ioi 0) := fun t (ht : 0 < t) =>
    (((φ.2.1.continuous.sub (φ.2.1.continuous.comp continuous_neg)).continuousAt).div
      (Complex.continuous_ofReal.continuousAt) (by exact_mod_cast ht.ne')).continuousWithinAt
  obtain ⟨M, hM⟩ := (isTempTest_iff_bound.mp (derivTempTest φ).2).2 0 0
  simp only [pow_zero, one_mul, iteratedDeriv_zero, coe_derivTempTest] at hM
  have h1 : IntegrableOn g (Ioc 0 1) := by
    refine (integrableOn_const (C := 2 * M) (by simp)).mono'
      ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := (φ : ℝ → ℂ))
      (f' := deriv (φ : ℝ → ℂ)) (a := -t) (b := t) (C := M)
      (fun x _ => ((φ.2.1.differentiable (by simp)) x).hasDerivAt.hasDerivWithinAt)
      (fun x _ => hM x) t ⟨by linarith [ht.1], le_rfl⟩
    simp only [g, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [div_le_iff₀ ht.1]
    linarith
  have h2 : IntegrableOn g (Ioi 1) := by
    refine ((integrable_tempSpace φ).norm.add
      ((integrable_tempSpace φ).comp_neg).norm).integrableOn.mono'
      ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
    simp only [g, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < t),
      Pi.add_apply]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_sub_le ((φ : ℝ → ℂ) t) ((φ : ℝ → ℂ) (-t)), norm_nonneg ((φ : ℝ → ℂ) t),
      norm_nonneg ((φ : ℝ → ℂ) (-t))]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

/-- `⨍ φ(x)/x dx` is the principal value `lim_{ε→0+} ∫_{|x|>ε} φ(x)/x dx`. -/
theorem tendsto_pvInvX (φ : tempSpace) :
    Tendsto (fun ε => ∫ x in {x : ℝ | ε < |x|}, (φ : ℝ → ℂ) x / x) (𝓝[>] 0)
      (𝓝 (pvInvX (φ : ℝ → ℂ))) := by
  set g := fun t : ℝ => ((φ : ℝ → ℂ) t - (φ : ℝ → ℂ) (-t)) / t
  have hg := integrableOn_pvInvX φ
  have hφ := integrable_tempSpace φ
  have hb : ∀ (ψ : ℝ → ℂ), Integrable ψ → ∀ ε, 0 < ε → ∀ s : Set ℝ, MeasurableSet s →
      (∀ x ∈ s, ε ≤ |x|) → IntegrableOn (fun x => ψ x / x) s := fun ψ hψ ε hε s hs hsε =>
    (hψ.integrableOn.norm.div_const ε).mono'
      (hψ.aestronglyMeasurable.restrict.div₀
        (Complex.continuous_ofReal.aestronglyMeasurable)) (by
        filter_upwards [ae_restrict_mem hs] with x hx
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hε (hsε x hx))
  have e : ∀ ε, 0 < ε → ∫ x in {x : ℝ | ε < |x|}, (φ : ℝ → ℂ) x / x =
      ∫ t in Ioi 0, (Ioi ε).indicator g t := by
    intro ε hε
    have hset : {x : ℝ | ε < |x|} = Iio (-ε) ∪ Ioi ε := by
      ext x
      simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
      constructor
      · rintro (h | h)
        · right; exact h
        · left; linarith
      · rintro (h | h)
        · right; linarith
        · left; exact h
    have hpos : ∀ x ∈ Ioi ε, ε ≤ |x| := fun x (hx : ε < x) => by
      rw [abs_of_pos (by linarith)]; exact hx.le
    have hneg : IntegrableOn (fun x => (φ : ℝ → ℂ) (-x) / ((-x : ℝ) : ℂ)) (Ioi ε) := by
      have := hb (fun x => (φ : ℝ → ℂ) (-x)) hφ.comp_neg ε hε (Ioi ε) measurableSet_Ioi hpos
      refine (this.neg).congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.neg_apply, ofReal_neg, div_neg]
    rw [hset, setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by
        simp only [mem_Iio, mem_Ioi] at h1 h2; linarith) measurableSet_Ioi
      (hb _ hφ ε hε _ measurableSet_Iio fun x (hx : x < -ε) => by
        rw [abs_of_neg (by linarith)]; linarith)
      (hb _ hφ ε hε _ measurableSet_Ioi hpos),
      ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi,
      setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi hε.le),
      ← integral_add hneg (hb _ hφ ε hε _ measurableSet_Ioi hpos)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : ε < x) => ?_
    have : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
    simp only [g]
    push_cast
    field_simp
    ring
  have key := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε t => (Ioi ε).indicator g t) (f := g) (fun t => ‖g t‖)
    (Eventually.of_forall fun ε => (hg.1.indicator measurableSet_Ioi))
    (Eventually.of_forall fun ε => ae_of_all _ fun t => norm_indicator_le_norm_self _ _)
    hg.norm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT ht] with ε hε
      rw [indicator_of_mem (show t ∈ Ioi ε from hε.2)])
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (e ε hε).symm

/-- The principal-value distribution `φ ↦ ⨍ φ(x)/x dx`. -/
noncomputable def pvDist : tempSpace →ₗ[ℂ] ℂ where
  toFun φ := pvInvX φ
  map_add' φ ψ := by
    simp only [pvInvX, Submodule.coe_add, Pi.add_apply]
    rw [← integral_add (integrableOn_pvInvX φ) (integrableOn_pvInvX ψ)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  map_smul' c φ := by
    simp only [pvInvX, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring

/-! ### `𝓕(sign)` and `𝓕(H)` (1.16.48–1.16.51) -/

theorem sqrt_two_pi_div_pi : √(2 * π) / π = √(2 / π) := by
  have hπ := Real.pi_pos
  rw [Real.sqrt_div' 2 hπ.le, Real.sqrt_mul (by norm_num) π]
  have hs : 0 < √π := Real.sqrt_pos.mpr hπ
  have hππ : √π * √π = π := Real.mul_self_sqrt hπ.le
  rw [div_eq_div_iff hπ.ne' hs.ne', mul_assoc, hππ]

theorem tendsto_conjPoissonInt_zero (φ : tempSpace) :
    Tendsto (fun ε => conjPoissonInt ε (φ : ℝ → ℂ) 0) (𝓝[>] 0)
      (𝓝 ((π : ℂ)⁻¹ * pvInvX (φ : ℝ → ℂ))) := by
  have hφ := integrable_tempSpace φ
  have hg := integrableOn_pvInvX φ
  set g := fun t : ℝ => ((φ : ℝ → ℂ) t - (φ : ℝ → ℂ) (-t)) / t
  have e : ∀ ε, 0 < ε → conjPoissonInt ε (φ : ℝ → ℂ) 0 = (π : ℂ)⁻¹ *
      ∫ s in Ioi 0, ((s / (s ^ 2 + ε ^ 2) : ℝ) : ℂ) * ((φ : ℝ → ℂ) s - (φ : ℝ → ℂ) (-s)) :=
    fun ε hε => by
      rw [conjPoissonInt, conjPoisson_eq hφ 0 hε]
      simp only [zero_add, zero_sub]
  have key := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε s => ((s / (s ^ 2 + ε ^ 2) : ℝ) : ℂ) *
      ((φ : ℝ → ℂ) s - (φ : ℝ → ℂ) (-s))) (f := g) (fun t => ‖g t‖)
    (Eventually.of_forall fun ε => ((Complex.measurable_ofReal.comp
      (by fun_prop : Measurable fun s : ℝ => s / (s ^ 2 + ε ^ 2))).aestronglyMeasurable.mul
      (hφ.aestronglyMeasurable.sub hφ.comp_neg.aestronglyMeasurable)).restrict)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      simp only [g, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, abs_of_pos (by positivity : 0 < s ^ 2 + ε ^ 2)]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hs]
      nlinarith [mul_nonneg (norm_nonneg ((φ : ℝ → ℂ) s - (φ : ℝ → ℂ) (-s))) (sq_nonneg ε)])
    hg.norm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      have hc : ContinuousAt (fun ε : ℝ => ((s / (s ^ 2 + ε ^ 2) : ℝ) : ℂ)) 0 :=
        (Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop)
          fun ε => by positivity)).continuousAt
      have h := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).mul_const
        ((φ : ℝ → ℂ) s - (φ : ℝ → ℂ) (-s))
      have hs0 := hs.ne'
      have : g s = ((s / (s ^ 2 + 0 ^ 2) : ℝ) : ℂ) * ((φ : ℝ → ℂ) s - (φ : ℝ → ℂ) (-s)) := by
        simp only [g]
        rw [show s / (s ^ 2 + 0 ^ 2) = 1 / s by field_simp; ring]
        push_cast
        ring
      rw [this]
      exact h)
  refine (key.const_mul ((π : ℂ)⁻¹)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (e ε hε).symm

/-- DLMF 1.16.49: `⟨𝓕(sign), φ⟩ = i √(2/π) ⨍ φ(x)/x dx`. -/
theorem dlmf_1_16_49 (φ : tempSpace) :
    fourierDist1 tempSign φ = I * ((√(2 / π) : ℝ) : ℂ) * pvInvX (φ : ℝ → ℂ) := by
  have hφ := integrable_tempSpace φ
  set Fφ := dlmfFourier (φ : ℝ → ℂ)
  have hF : Integrable Fφ := by
    have := integrable_tempSpace (fourierTest1 φ)
    rwa [coe_fourierTest1] at this
  have hval : fourierDist1 tempSign φ = ∫ x, ((Real.sign x : ℝ) : ℂ) * Fφ x := by
    change ∫ x, ((Real.sign x : ℝ) : ℂ) * (fourierTest1 φ : ℝ → ℂ) x = _
    rw [coe_fourierTest1]
  have hconj : ∀ ε : ℝ, 0 < ε → ∫ x, ((Real.sign x : ℝ) : ℂ) * cexp (-((ε : ℂ) * |x|)) * Fφ x =
      ((√(2 * π) : ℝ) : ℂ) * I * conjPoissonInt ε (φ : ℝ → ℂ) 0 := fun ε hε => by
    rw [conjPoissonInt_eq_dlmfFourier hφ hε 0, dlmfFourier]
    have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
    have e : ∫ ξ, -I * ((Real.sign ξ : ℝ) : ℂ) * cexp (-((ε : ℂ) * |ξ|)) * Fφ ξ *
        cexp (I * ((-0 : ℝ) : ℂ) * ξ) =
        -I * ∫ x, ((Real.sign x : ℝ) : ℂ) * cexp (-((ε : ℂ) * |x|)) * Fφ x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      simp only [neg_zero, ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      ring
    rw [e]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hlim1 : Tendsto (fun ε : ℝ => ∫ x, ((Real.sign x : ℝ) : ℂ) * cexp (-((ε : ℂ) * |x|)) *
      Fφ x) (𝓝[>] 0) (𝓝 (∫ x, ((Real.sign x : ℝ) : ℂ) * Fφ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖Fφ x‖)
      (Eventually.of_forall fun ε => (((Complex.measurable_ofReal.comp
        measurable_realSign).aestronglyMeasurable.mul (by fun_prop : Continuous fun x : ℝ =>
          cexp (-((ε : ℂ) * |x|))).aestronglyMeasurable).mul hF.aestronglyMeasurable)) ?_
      hF.norm (ae_of_all _ fun x => ?_)
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine ae_of_all _ fun x => ?_
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have h1 := norm_sign_le x
      have h2 : Real.exp (-((ε : ℂ) * |x|)).re ≤ 1 := by
        rw [Real.exp_le_one_iff]
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        nlinarith [abs_nonneg x]
      calc ‖((Real.sign x : ℝ) : ℂ)‖ * Real.exp (-((ε : ℂ) * |x|)).re * ‖Fφ x‖
          ≤ 1 * 1 * ‖Fφ x‖ := by gcongr
        _ = ‖Fφ x‖ := by ring
    · have hc : Tendsto (fun ε : ℝ => cexp (-((ε : ℂ) * |x|))) (𝓝[>] 0) (𝓝 1) := by
        have := ((by fun_prop : Continuous fun ε : ℝ => cexp (-((ε : ℂ) * |x|))).tendsto
          0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      have := (hc.const_mul ((Real.sign x : ℝ) : ℂ)).mul_const (Fφ x)
      simpa using this
  have h2 := (tendsto_conjPoissonInt_zero φ).const_mul (((√(2 * π) : ℝ) : ℂ) * I)
  have heq := tendsto_nhds_unique hlim1 (h2.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (hconj ε hε).symm))
  rw [hval, heq, ← sqrt_two_pi_div_pi]
  push_cast
  ring

/-- DLMF 1.16.48: `𝓕(sign) = √(2/π) i/x`, with `1/x` the principal-value distribution. -/
theorem dlmf_1_16_48 : fourierDist1 tempSign = (I * ((√(2 / π) : ℝ) : ℂ)) • pvDist := by
  ext φ
  rw [dlmf_1_16_49]
  rfl

theorem tempH_eq : tempH = (1 / 2 : ℂ) • (tempOne + tempSign) := by
  ext φ
  have hφ := integrable_tempSpace φ
  have hs : Integrable fun x => ((Real.sign x : ℝ) : ℂ) * (φ : ℝ → ℂ) x :=
    integrable_mul_of_polyBound (M := 0) (C := 1)
      (Complex.measurable_ofReal.comp measurable_realSign).aestronglyMeasurable zero_le_one
      (fun x => by simpa using norm_sign_le x) φ.2
  change ∫ x, ((heavisideH x : ℝ) : ℂ) * (φ : ℝ → ℂ) x =
    1 / 2 * ((∫ x, (1 : ℂ) * (φ : ℝ → ℂ) x) + ∫ x, ((Real.sign x : ℝ) : ℂ) * (φ : ℝ → ℂ) x)
  rw [← integral_add (by simpa using hφ) hs, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with x hx
  have hx0 : x ≠ 0 := fun e => hx (by rw [e]; rfl)
  have := dlmf_1_16_44 hx0
  rw [show (heavisideH x : ℝ) = (Real.sign x + 1) / 2 by linarith]
  push_cast
  ring

/-- DLMF 1.16.50: `𝓕(H) = ½ 𝓕(1 + sign) = ½ [𝓕(1) + 𝓕(sign)] = √(π/2) (δ + i/(πx))`. -/
theorem dlmf_1_16_50 :
    fourierDist1 tempH = (1 / 2 : ℂ) • (fourierDist1 tempOne + fourierDist1 tempSign) ∧
      (1 / 2 : ℂ) • (fourierDist1 tempOne + fourierDist1 tempSign) =
        ((√(π / 2) : ℝ) : ℂ) • (tempDirac 0 + (I / π) • pvDist) := by
  refine ⟨by rw [tempH_eq]; rfl, ?_⟩
  rw [dlmf_1_16_42, dlmf_1_16_48]
  have hπ := Real.pi_pos
  have hs : 0 < √π := Real.sqrt_pos.mpr hπ
  have h2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hππ : √π * √π = π := Real.mul_self_sqrt hπ.le
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e1 : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
  have e2 : √(2 / π) = √2 / √π := Real.sqrt_div' 2 hπ.le
  have e3 : √(π / 2) = √π / √2 := Real.sqrt_div' π (by norm_num)
  rw [e1, e2, e3]
  ext φ
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  have hs' : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have h2' : ((√2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.ne'
  have hπ' : (π : ℂ) = ((√π : ℝ) : ℂ) * ((√π : ℝ) : ℂ) := by
    rw [← ofReal_mul, hππ]
  have h2'' : (2 : ℂ) = ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) := by
    rw [← ofReal_mul, h22]; norm_num
  push_cast
  rw [hπ']
  field_simp
  rw [h2'']
  ring

/-- DLMF 1.16.51: `⟨𝓕(H), φ⟩ = √(π/2) φ(0) + (i/√(2π)) ⨍ φ(x)/x dx`. -/
theorem dlmf_1_16_51 (φ : tempSpace) :
    fourierDist1 tempH φ = ((√(π / 2) : ℝ) : ℂ) * (φ : ℝ → ℂ) 0 +
      I / ((√(2 * π) : ℝ) : ℂ) * pvInvX (φ : ℝ → ℂ) := by
  obtain ⟨h1, h2⟩ := dlmf_1_16_50
  rw [h1, h2]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  change ((√(π / 2) : ℝ) : ℂ) * ((φ : ℝ → ℂ) 0 + I / π * pvInvX (φ : ℝ → ℂ)) = _
  have hπ := Real.pi_pos
  have hs : 0 < √π := Real.sqrt_pos.mpr hπ
  have h2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hππ : √π * √π = π := Real.mul_self_sqrt hπ.le
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Real.sqrt_mul (by norm_num) π, Real.sqrt_div' π (by norm_num)]
  have hs' : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have h2' : ((√2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.ne'
  have hπ' : (π : ℂ) = ((√π : ℝ) : ℂ) * ((√π : ℝ) : ℂ) := by
    rw [← ofReal_mul, hππ]
  push_cast
  rw [hπ']
  field_simp

end Azurite.DLMF
