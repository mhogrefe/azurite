/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section14CosSin

/-!
# DLMF §1.18(vi), Example 2: sine and cosine transforms

https://dlmf.nist.gov/1.18.vi

The inner integrals `∫_0^∞ cos(xt) cos(yt) dt` of 1.18.59 diverge, so 1.18.59 is read with the
`t`-integral outside, truncated at `t ≤ R` (`cosMoment`, `sinMoment`):

* `dlmf_1_18_59_partial`: the truncation is the symmetric partial Fourier inversion integral of
  §1.14.
* 1.18.59 then holds for every `x ∈ ℝ`, giving `f(x)` for integrable `C¹` `f`
  (`dlmf_1_18_59_smooth`, from 1.14.4) and `½(f(x+) + f(x−))` at points of local bounded
  variation (`dlmf_1_18_59`, from 1.14.3).
* For even `f` the sine part vanishes and the cosine part becomes the cosine pair 1.14.9 & 1.14.11
  (`dlmf_1_18_59_even`). For odd `f` it becomes the sine pair 1.14.10 & 1.14.12
  (`dlmf_1_18_59_odd`). These are proven in `Section14CosSin.lean` (`dlmf_1_14_11`,
  `dlmf_1_14_12`), and in the δ-form of 1.17.12_1–1.17.12_2 as `dlmf_1_17_12_1`, `dlmf_1_17_12_2`.
* Obtaining the pairs from 1.18.57 with `ν = ±½` needs the Bessel–Hankel transform of Example 1,
  which is deferred.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-- `∫ f(y) cos(yt) dy`. -/
noncomputable def cosMoment (f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ y, f y * (Real.cos (y * t) : ℂ)

/-- `∫ f(y) sin(yt) dy`. -/
noncomputable def sinMoment (f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ y, f y * (Real.sin (y * t) : ℂ)

theorem integrable_mul_trig {f : ℝ → ℂ} (hf : Integrable f) {g : ℝ → ℝ} (hg : Continuous g)
    (hb : ∀ y, |g y| ≤ 1) : Integrable fun y => f y * (g y : ℂ) :=
  (hf.bdd_mul (c := 1) (Complex.continuous_ofReal.comp hg).aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Function.comp_apply, Complex.norm_real]; exact hb y)).congr
    (ae_of_all _ fun y => mul_comm _ _)

theorem dlmfFourier_eq_moments {f : ℝ → ℂ} (hf : Integrable f) (t : ℝ) :
    dlmfFourier f t = ((√(2 * π) : ℝ) : ℂ)⁻¹ * (cosMoment f t + I * sinMoment f t) := by
  rw [dlmfFourier, cosMoment, sinMoment]
  congr 1
  rw [← integral_const_mul,
    ← integral_add (integrable_mul_trig hf (by fun_prop) fun y => Real.abs_cos_le_one _)
      ((integrable_mul_trig hf (by fun_prop) fun y => Real.abs_sin_le_one _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [show I * (t : ℂ) * y = ((y * t : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem cosMoment_neg (f : ℝ → ℂ) (t : ℝ) : cosMoment f (-t) = cosMoment f t := by
  simp [cosMoment, mul_neg, Real.cos_neg]

theorem sinMoment_neg (f : ℝ → ℂ) (t : ℝ) : sinMoment f (-t) = -sinMoment f t := by
  simp [sinMoment, mul_neg, Real.sin_neg, integral_neg]

/-- DLMF 1.18.59, with the order of integration made rigorous: the truncation of the right-hand
side at `t ≤ R`, `(1/π) ∫_0^R (cos(xt) ∫ f(y) cos(yt) dy + sin(xt) ∫ f(y) sin(yt) dy) dt`, is the
symmetric partial Fourier inversion integral `(2π)^{−1/2} ∫_{−R}^{R} 𝓕(f)(t) e^{−ixt} dt`. -/
theorem dlmf_1_18_59_partial {f : ℝ → ℂ} (hf : Integrable f) (x R : ℝ) :
    ((1 / π : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R, ((Real.cos (x * t) : ℂ) * cosMoment f t +
      (Real.sin (x * t) : ℂ) * sinMoment f t) =
    ((√(2 * π) : ℝ) : ℂ)⁻¹ * ∫ t in (-R)..R, dlmfFourier f t * cexp (-(I * t * x)) := by
  rw [intervalIntegral_eq_halves (g := fun t => dlmfFourier f t * cexp (-(I * t * x)))
      ((dlmf_1_14_i_continuous hf).mul (by fun_prop)) R,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [dlmfFourier_eq_moments hf, dlmfFourier_eq_moments hf, cosMoment_neg, sinMoment_neg]
  have e1 : cexp (-(I * t * x)) = (Real.cos (x * t) : ℂ) - I * (Real.sin (x * t) : ℂ) := by
    rw [show -(I * (t : ℂ) * x) = ((-(x * t) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have e2 : cexp (-(I * ((-t : ℝ) : ℂ) * x)) =
      (Real.cos (x * t) : ℂ) + I * (Real.sin (x * t) : ℂ) := by
    rw [show -(I * ((-t : ℝ) : ℂ) * x) = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [e1, e2]
  have hs0 : ((√(2 * π) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hinv : ((√(2 * π) : ℝ) : ℂ)⁻¹ * ((√(2 * π) : ℝ) : ℂ)⁻¹ = 1 / (2 * π) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  set C := cosMoment f t
  set S := sinMoment f t
  set c := ((Real.cos (x * t) : ℝ) : ℂ)
  set d := ((Real.sin (x * t) : ℝ) : ℂ)
  push_cast
  linear_combination (-((C + I * S) * (c - I * d) + (C + I * -S) * (c + I * d))) * hinv +
    (S * d / π) * I_sq

/-- DLMF 1.18.59 at a point where `f` is of bounded variation with one-sided limits:
the right-hand side (as `lim_{R→∞}` of the truncations) equals `½(f(x+) + f(x−))`. -/
theorem dlmf_1_18_59 {f : ℝ → ℂ} (hf : Integrable f) {x δ : ℝ} (hδ : 0 < δ)
    (hbv : BoundedVariationOn f (Icc (x - δ) (x + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] x) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] x) (𝓝 Lm)) :
    Tendsto (fun R : ℝ => ((1 / π : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R,
      ((Real.cos (x * t) : ℂ) * cosMoment f t + (Real.sin (x * t) : ℂ) * sinMoment f t))
      atTop (𝓝 ((Lp + Lm) / 2)) := by
  have h := dlmf_1_14_3 hf hδ hbv hp hm
  refine h.congr fun R => ?_
  rw [dlmf_1_18_59_partial hf]

/-- DLMF 1.18.59 for `f` integrable and continuously differentiable: the right-hand side equals
`f(x)` for every `x ∈ ℝ`. -/
theorem dlmf_1_18_59_smooth {f : ℝ → ℂ} (hf : Integrable f) (hc : ContDiff ℝ 1 f) (x : ℝ) :
    Tendsto (fun R : ℝ => ((1 / π : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R,
      ((Real.cos (x * t) : ℂ) * cosMoment f t + (Real.sin (x * t) : ℂ) * sinMoment f t))
      atTop (𝓝 (f x)) := by
  have h := dlmf_1_14_4 hf hc x
  refine h.congr fun R => ?_
  rw [dlmf_1_18_59_partial hf]

/-! ### Even and odd `f` -/

theorem integral_odd_eq_zero {F : ℝ → ℂ} (hF : ∀ y, F (-y) = -F y) : ∫ y, F y = 0 := by
  have h := integral_neg_eq_self F volume
  simp only [hF, integral_neg] at h
  have : (2 : ℂ) * ∫ y, F y = 0 := by linear_combination -h
  simpa using this

theorem integral_even_eq_two_mul {F : ℝ → ℂ} (hFi : Integrable F) (hF : ∀ y, F (-y) = F y) :
    ∫ y, F y = 2 * ∫ y in Ioi 0, F y := by
  have h := integral_comp_neg_Ioi 0 F
  rw [neg_zero] at h
  rw [← integral_add_compl measurableSet_Ioi hFi, compl_Ioi, ← h]
  simp only [hF]
  ring

/-- DLMF §1.18(vi), Example 2: for even `f`, 1.18.59 is the Fourier cosine transform pair
1.14.9 & 1.14.11: the sine part vanishes and `∫ f(y) cos(yt) dy = 2 ∫_0^∞ f(y) cos(yt) dy`. -/
theorem dlmf_1_18_59_even {f : ℝ → ℂ} (hf : Integrable f) (heven : ∀ y, f (-y) = f y) (t : ℝ) :
    sinMoment f t = 0 ∧ cosMoment f t = 2 * ∫ y in Ioi 0, f y * (Real.cos (y * t) : ℂ) := by
  refine ⟨integral_odd_eq_zero fun y => ?_, integral_even_eq_two_mul
    (integrable_mul_trig hf (by fun_prop) fun y => Real.abs_cos_le_one _) fun y => ?_⟩
  · simp [heven, neg_mul, Real.sin_neg]
  · simp [heven, neg_mul, Real.cos_neg]

/-- DLMF §1.18(vi), Example 2: for odd `f`, 1.18.59 is the Fourier sine transform pair
1.14.10 & 1.14.12. -/
theorem dlmf_1_18_59_odd {f : ℝ → ℂ} (hf : Integrable f) (hodd : ∀ y, f (-y) = -f y) (t : ℝ) :
    cosMoment f t = 0 ∧ sinMoment f t = 2 * ∫ y in Ioi 0, f y * (Real.sin (y * t) : ℂ) := by
  refine ⟨integral_odd_eq_zero fun y => ?_, integral_even_eq_two_mul
    (integrable_mul_trig hf (by fun_prop) fun y => Real.abs_sin_le_one _) fun y => ?_⟩
  · simp [hodd, neg_mul, Real.cos_neg]
  · simp [hodd, neg_mul, Real.sin_neg]

end Azurite.DLMF
