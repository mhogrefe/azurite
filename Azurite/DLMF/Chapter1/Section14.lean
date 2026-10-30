/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution

/-!
# DLMF §1.14(i): Fourier Transform

Formalizations of <https://dlmf.nist.gov/1.14#i> (basic properties). DLMF's transform
`𝓕(f)(x) = (2π)^{−1/2} ∫ f(t) e^{ixt} dt` is `dlmfFourier` (1.14.1); it is related to Mathlib's
`𝓕 f w = ∫ e^{−2πivw} f(v) dv` by `dlmfFourier_eq_fourier` and `fourier_eq_dlmfFourier`.

**Results.**
* 1.14.2: `|𝓕(f)(x)| ≤ (2π)^{−1/2} ∫ |f|` (`dlmf_1_14_2`); for integrable `f`, `𝓕(f)` is continuous
  (`dlmf_1_14_i_continuous`) and tends to `0` at `±∞` (`dlmf_1_14_i_tendsto_zero`, `_atTop`,
  `_atBot`, Riemann–Lebesgue).
* 1.14.5: the convolution `dlmfConv`, its integrability (`dlmf_1_14_5_integrable`), and
  `𝓕(f ∗ g) = 𝓕(f) 𝓕(g)` (`dlmf_1_14_5`).
* Uniqueness: continuous integrable functions with equal transforms are equal
  (`dlmf_1_14_i_unique`).

Parseval's formulas are in `Section14Parseval.lean` and the inversion theorems in
`Section14Inversion.lean`. Poisson's summation formula is `dlmf_1_8_14` (§1.8(iv)).
-/

open MeasureTheory Filter Topology Complex
open scoped FourierTransform Convolution

namespace Azurite.DLMF

/-- **DLMF (1.14.1)**: `𝓕(f)(x) = (2π)^{−1/2} ∫ f(t) e^{ixt} dt`. -/
noncomputable def dlmfFourier (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ * ∫ t, f t * cexp (I * x * t)

theorem sqrt_two_pi_ne_zero : ((√(2 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))

/-- DLMF's transform in terms of Mathlib's `𝓕 f w = ∫ e^{−2πivw} f(v) dv`. -/
theorem dlmfFourier_eq_fourier (f : ℝ → ℂ) (x : ℝ) :
    dlmfFourier f x = ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ * 𝓕 f (-(x / (2 * Real.pi))) := by
  rw [dlmfFourier, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

theorem fourier_eq_dlmfFourier (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier f (-(2 * Real.pi * w)) := by
  rw [dlmfFourier_eq_fourier, ← mul_assoc, mul_inv_cancel₀ sqrt_two_pi_ne_zero, one_mul]
  field_simp

/-- **DLMF (1.14.2)**: `|𝓕(f)(x)| ≤ (2π)^{−1/2} ∫ |f(t)| dt`. -/
theorem dlmf_1_14_2 (f : ℝ → ℂ) (x : ℝ) :
    ‖dlmfFourier f x‖ ≤ (√(2 * Real.pi))⁻¹ * ∫ t, ‖f t‖ := by
  rw [dlmfFourier, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  congr 1
  funext t
  rw [norm_mul, norm_exp, show (I * x * t).re = 0 by simp, Real.exp_zero, mul_one]

/-- **DLMF §1.14(i)**: for absolutely integrable `f`, `𝓕(f)` is continuous. -/
theorem dlmf_1_14_i_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (dlmfFourier f) := by
  refine continuous_const.mul (continuous_of_dominated (bound := fun t => ‖f t‖)
    (fun x => hf.1.mul
      (by fun_prop : Continuous fun t : ℝ => cexp (I * x * t)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun t => ?_) hf.norm (ae_of_all _ fun t => by fun_prop))
  rw [norm_mul, norm_exp, show (I * x * t).re = 0 by simp, Real.exp_zero, mul_one]

/-- **DLMF §1.14(i)** (Riemann–Lebesgue): `𝓕(f)(x) → 0` as `x → ±∞`. -/
theorem dlmf_1_14_i_tendsto_zero (f : ℝ → ℂ) :
    Tendsto (dlmfFourier f) (cocompact ℝ) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => -(x / (2 * Real.pi))) (cocompact ℝ) (cocompact ℝ) := by
    have hc : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 := by
      have := Real.pi_pos
      exact neg_ne_zero.mpr (by positivity)
    have := (Homeomorph.mulLeft₀ _ hc).toCocompactMap.cocompact_tendsto'
    refine this.congr fun x => ?_
    simp only [Homeomorph.toCocompactMap, Homeomorph.coe_mulLeft₀]
    ring
  have := ((Real.zero_at_infty_fourier f).comp h).const_mul ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹
  rw [mul_zero] at this
  exact this.congr fun x => (dlmfFourier_eq_fourier f x).symm

theorem dlmf_1_14_i_tendsto_atTop (f : ℝ → ℂ) : Tendsto (dlmfFourier f) atTop (𝓝 0) :=
  (dlmf_1_14_i_tendsto_zero f).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)

theorem dlmf_1_14_i_tendsto_atBot (f : ℝ → ℂ) : Tendsto (dlmfFourier f) atBot (𝓝 0) :=
  (dlmf_1_14_i_tendsto_zero f).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left)

/-! ### Convolution -/

/-- **DLMF (1.14.5)**: `(f ∗ g)(t) = (2π)^{−1/2} ∫ f(t − s) g(s) ds`. -/
noncomputable def dlmfConv (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ * ∫ s, f (t - s) * g s

theorem dlmfConv_eq (f g : ℝ → ℂ) :
    dlmfConv f g = fun t => ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ *
      (g ⋆[ContinuousLinearMap.mul ℂ ℂ] f) t := by
  funext t
  simp only [dlmfConv, convolution, ContinuousLinearMap.mul_apply']
  congr 1
  exact integral_congr_ae (ae_of_all _ fun s => mul_comm _ _)

/-- **DLMF §1.14(i)**: the convolution of absolutely integrable functions is absolutely
integrable. -/
theorem dlmf_1_14_5_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (dlmfConv f g) := by
  rw [dlmfConv_eq]
  exact (hg.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf).const_mul _

/-- **DLMF §1.14(i)**: `𝓕(f ∗ g) = 𝓕(f) 𝓕(g)`. -/
theorem dlmf_1_14_5 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    dlmfFourier (dlmfConv f g) x = dlmfFourier f x * dlmfFourier g x := by
  have hlin : ∀ (c : ℂ) (h : ℝ → ℂ) (w : ℝ), 𝓕 (fun t => c * h t) w = c * 𝓕 h w :=
    fun c h w => by
      simp only [Real.fourier_real_eq, smul_eq_mul, Circle.smul_def]
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun t => by ring)
  rw [dlmfFourier_eq_fourier, dlmfConv_eq, hlin,
    Real.fourier_mul_convolution_eq hg hf, dlmfFourier_eq_fourier, dlmfFourier_eq_fourier]
  ring

/-! ### Uniqueness -/

theorem integrable_mul_exp {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t => f t * cexp (I * x * t)) :=
  hf.mul_bdd (c := 1) (by fun_prop : Continuous fun t : ℝ => cexp (I * x * t)).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [norm_exp, show (I * x * t).re = 0 by simp, Real.exp_zero])

theorem dlmfFourier_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    dlmfFourier (f - g) x = dlmfFourier f x - dlmfFourier g x := by
  simp only [dlmfFourier, Pi.sub_apply, sub_mul]
  rw [integral_sub (integrable_mul_exp hf x) (integrable_mul_exp hg x), mul_sub]

/-- **DLMF §1.14(i)** (uniqueness): continuous absolutely integrable functions with the same
Fourier transform are equal. -/
theorem dlmf_1_14_i_unique {f g : ℝ → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) (h : ∀ x, dlmfFourier f x = dlmfFourier g x) :
    f = g := by
  have h0 : 𝓕 (f - g) = 0 := by
    funext w
    rw [fourier_eq_dlmfFourier, dlmfFourier_sub hf hg, h, sub_self, mul_zero, Pi.zero_apply]
  have hinv := (hfc.sub hgc).fourierInv_fourier_eq (hf.sub hg)
    (by rw [h0]; exact integrable_zero _ _ _)
  rw [h0] at hinv
  have : (f - g) = 0 := by
    rw [← hinv]
    funext v
    simp [Real.fourierInv_eq]
  exact sub_eq_zero.mp this

end Azurite.DLMF
