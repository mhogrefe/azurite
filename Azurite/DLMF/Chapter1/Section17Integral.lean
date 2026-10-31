/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section17
import Azurite.DLMF.Chapter1.Section14CosSin
import Azurite.DLMF.Chapter1.Section16FourierSpecial

/-!
# DLMF §1.17(ii): Integral representations of the Dirac delta

https://dlmf.nist.gov/1.17.ii

The representations are formal (their inner integrals diverge). Each is proven in a rigorous
reading.

* 1.17.8: the Fourier integral formula, from §1.14's inversion theorem (`dlmf_inversion`), for
  integrable `φ` with integrable transform, continuous at `a`.
* 1.17.9: the inner integral `∫ e^{i(x−a)t} dt` does not converge (`dlmf_1_17_9_not_integrable`).
  1.17.9 holds as the generalized integral 1.17.3 with the delta sequence 1.17.11
  (`fourierGaussDelta`), under the hypotheses of 1.17.6 (`dlmf_1_17_9`).
* 1.17.10: `(1/(2π)) ∫ e^{−t²/(4n)} e^{i(x−a)t} dt = √(n/π) e^{−n(x−a)²}`, from Mathlib's
  `fourierIntegral_gaussian`. Hence 1.17.11 is the Gaussian delta sequence 1.17.5 (`dlmf_1_17_11`).
* 1.17.12: in the sense of distributions, the damped integrals converge to `δ_a`
  (`dlmf_1_17_12`). For tempered distributions it is `(1/√(2π)) 𝓕(1) = δ`
  (`dlmf_1_17_12_tempered`, = 1.16.43).
* 1.17.12_1–1.17.12_2: the cosine and sine representations are the Fourier cosine and sine
  inversion theorems 1.14.11 and 1.14.12. For `φ` integrable on `(0, ∞)`, of bounded variation
  near `a > 0` and continuous at `a`, `(2/π) ∫_0^∞ cos(at) (∫_0^∞ φ(x) cos(xt) dx) dt = φ(a)`, and
  the same with `sin`.
* 1.17.14 with `ℓ = 0`: `𝗃₀ = sinc` (`Real.sinc`), and the integrand reduces to that of 1.17.12_2
  (`dlmf_1_17_14_zero_integrand`, `dlmf_1_17_14_zero`).

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The Fourier integral (1.17.8–1.17.12) -/

/-- DLMF 1.17.8, the Fourier integral formula of §1.14:
`(1/(2π)) ∫ e^{−iat} (∫ φ(x) e^{itx} dx) dt = φ(a)` when `φ` and its Fourier transform are
integrable and `φ` is continuous at `a`. -/
theorem dlmf_1_17_8 {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hF : Integrable fun t : ℝ => ∫ x, φ x * cexp (I * t * x)) {a : ℝ} (hc : ContinuousAt φ a) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, cexp (-(I * a * t)) * ∫ x, φ x * cexp (I * t * x) = φ a := by
  have hF' : Integrable (dlmfFourier φ) := hF.const_mul _
  rw [dlmf_inversion hφ hF' hc]
  simp only [dlmfFourier]
  have hs : ((√(2 * π) : ℝ) : ℂ)⁻¹ * ((√(2 * π) : ℝ) : ℂ)⁻¹ = ((2 * π : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  rw [← hs, mul_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  ring_nf

/-- DLMF §1.17(ii): the inner integral `∫ e^{i(x−a)t} dt` of 1.17.9 does not converge. -/
theorem dlmf_1_17_9_not_integrable (x a : ℝ) :
    ¬ Integrable fun t : ℝ => cexp (I * (x - a) * t) := by
  intro h
  have h1 : Integrable fun _ : ℝ => (1 : ℝ) := by
    refine h.norm.congr (ae_of_all _ fun t => ?_)
    simp only
    rw [show I * ((x : ℂ) - a) * t = (((x - a) * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [integrable_const_iff] at h1
  rcases h1 with h1 | h1
  · exact one_ne_zero h1
  · exact measure_ne_top (volume : Measure ℝ) univ (by simp)

/-- DLMF 1.17.10: `(1/(2π)) ∫ e^{−t²/(4n)} e^{i(x−a)t} dt = √(n/π) e^{−n(x−a)²}`. -/
theorem dlmf_1_17_10 {n : ℕ} (hn : 0 < n) (x a : ℝ) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, cexp (-(t : ℂ) ^ 2 / (4 * n)) * cexp (I * (x - a) * t) =
      ((√(n / π) * Real.exp (-(n * (x - a) ^ 2)) : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < (1 / (4 * n : ℂ)).re := by
    rw [show (1 / (4 * n : ℂ)) = ((1 / (4 * n) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    positivity
  have h := fourierIntegral_gaussian hb ((x - a : ℝ) : ℂ)
  have e : ∫ t : ℝ, cexp (-(t : ℂ) ^ 2 / (4 * n)) * cexp (I * (x - a) * t) =
      ∫ t : ℝ, cexp (I * ((x - a : ℝ) : ℂ) * t) * cexp (-(1 / (4 * n : ℂ)) * t ^ 2) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    have : (4 * n : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * n : ℝ) ≠ 0)
    push_cast
    rw [mul_comm]
    congr 2
    field_simp
  rw [e, h]
  have hpow : ((π : ℂ) / (1 / (4 * n))) ^ (1 / 2 : ℂ) = ((√(4 * π * n) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    field_simp
  have hexp : cexp (-((x - a : ℝ) : ℂ) ^ 2 / (4 * (1 / (4 * n)))) =
      ((Real.exp (-(n * (x - a) ^ 2)) : ℝ) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    have : (4 * n : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * n : ℝ) ≠ 0)
    push_cast
    field_simp
  rw [hpow, hexp]
  have hsq : √(4 * π * n) = 2 * π * √(n / π) := by
    have hπ := Real.pi_pos
    rw [show 4 * π * n = (2 * π) ^ 2 * (n / π) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq]
  push_cast
  field_simp

/-- DLMF 1.17.11: the delta sequence `δₙ(x − a) = (1/(2π)) ∫ e^{−t²/(4n)} e^{i(x−a)t} dt`. -/
noncomputable def fourierGaussDelta (n : ℕ) (y : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, cexp (-(t : ℂ) ^ 2 / (4 * n)) * cexp (I * y * t)

/-- DLMF 1.17.11 with 1.17.5: the integral is the Gaussian `√(n/π) e^{−n(x−a)²}`. (For `n = 0`
both sides vanish: the integral diverges.) -/
theorem dlmf_1_17_11 (n : ℕ) (y : ℝ) : fourierGaussDelta n y = (gaussDelta n y : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := dlmf_1_17_9_not_integrable y 0
    simp only [ofReal_zero, sub_zero] at h
    simp [fourierGaussDelta, gaussDelta, integral_undef h]
  · have h := dlmf_1_17_10 hn y 0
    simp only [ofReal_zero, sub_zero] at h
    rw [fourierGaussDelta, h, gaussDelta]

/-- DLMF §1.17(ii): 1.17.9 as the generalized integral 1.17.3 with the delta sequence 1.17.11,
under the hypotheses of 1.17.6. -/
theorem dlmf_1_17_9 {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ∀ a : ℝ, ∀ᶠ n : ℕ in atTop,
      Integrable fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * φ x) (a : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, fourierGaussDelta n (x - a) * φ x) atTop (𝓝 (φ a)) := by
  have h := tendsto_integral_gaussDelta (hint a) ((hφ.tendsto a).mono_left nhdsWithin_le_nhds)
    ((hφ.tendsto a).mono_left nhdsWithin_le_nhds)
  rw [add_halves] at h
  simpa only [dlmf_1_17_11] using h

theorem locallyIntegrableOn_fourierGaussDelta (n : ℕ) (a : ℝ) :
    LocallyIntegrableOn (fun x => fourierGaussDelta n (x - a)) univ := by
  simp_rw [dlmf_1_17_11]
  exact locallyIntegrableOn_gaussDelta n a

/-- DLMF 1.17.12, `δ(x − a) = (1/(2π)) ∫ e^{i(x−a)t} dt`, in the sense of distributions: the
damped integrals 1.17.11 converge to `δ_a`. -/
theorem dlmf_1_17_12 (a : ℝ) :
    DistConverges univ
      (fun n => regularDist isOpen_univ (locallyIntegrableOn_fourierGaussDelta n a))
      (diracDist univ a) := by
  intro φ
  have h := dlmf_1_17_4_gaussDelta a φ
  simpa only [dlmf_1_16_3, dlmf_1_17_11] using h

/-- DLMF 1.17.12 for tempered distributions (`a = 0`): `(1/√(2π)) 𝓕(1) = δ` (1.16.43), i.e.
`⟨(1/(2π)) ∫ e^{ixt} dt, φ⟩ = φ(0)`. -/
theorem dlmf_1_17_12_tempered :
    ((√(2 * π) : ℝ) : ℂ)⁻¹ • fourierDist1 tempOne = tempDirac 0 :=
  dlmf_1_16_43

/-! ### Sine and cosine (1.17.12_1, 1.17.12_2) -/

theorem sqrt_two_div_pi_mul_self : ((√(2 / π) : ℝ) : ℂ) * ((√(2 / π) : ℝ) : ℂ) =
    ((2 / π : ℝ) : ℂ) := by
  rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]

/-- DLMF 1.17.12_1, `δ(x − a) = (2/π) ∫_0^∞ cos(xt) cos(at) dt` (`x, a > 0`), as the Fourier
cosine inversion of §1.14(ii) (1.14.9 & 1.14.11): for `φ` integrable on `(0, ∞)`, of bounded
variation near `a` and continuous at `a`,
`(2/π) ∫_0^∞ cos(at) (∫_0^∞ φ(x) cos(xt) dx) dt = φ(a)`, the outer integral as `lim ∫_0^R`. -/
theorem dlmf_1_17_12_1 {φ : ℝ → ℂ} (hφ : IntegrableOn φ (Ioi 0)) {a δ : ℝ} (hδ : 0 < δ)
    (hδa : δ < a) (hbv : BoundedVariationOn φ (Icc (a - δ) (a + δ))) (hc : ContinuousAt φ a) :
    Tendsto (fun R : ℝ => ((2 / π : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R,
      ((Real.cos (a * t) : ℝ) : ℂ) * ∫ x in Ioi 0, φ x * ((Real.cos (t * x) : ℝ) : ℂ)) atTop
      (𝓝 (φ a)) := by
  have h := dlmf_1_14_11 hφ hδ hδa hbv (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [add_self_div_two] at h
  refine h.congr fun R => ?_
  rw [← sqrt_two_div_pi_mul_self, mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [dlmfFourierCos]
  ring

/-- DLMF 1.17.12_2, `δ(x − a) = (2/π) ∫_0^∞ sin(xt) sin(at) dt` (`x, a > 0`), as the Fourier
sine inversion of §1.14(ii) (1.14.10 & 1.14.12). -/
theorem dlmf_1_17_12_2 {φ : ℝ → ℂ} (hφ : IntegrableOn φ (Ioi 0)) {a δ : ℝ} (hδ : 0 < δ)
    (hδa : δ < a) (hbv : BoundedVariationOn φ (Icc (a - δ) (a + δ))) (hc : ContinuousAt φ a) :
    Tendsto (fun R : ℝ => ((2 / π : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R,
      ((Real.sin (a * t) : ℝ) : ℂ) * ∫ x in Ioi 0, φ x * ((Real.sin (t * x) : ℝ) : ℂ)) atTop
      (𝓝 (φ a)) := by
  have h := dlmf_1_14_12 hφ hδ hδa hbv (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [add_self_div_two] at h
  refine h.congr fun R => ?_
  rw [← sqrt_two_div_pi_mul_self, mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [dlmfFourierSin]
  ring

/-! ### Spherical Bessel functions of order `0` (1.17.14 with `ℓ = 0`) -/

theorem mul_sinc (z : ℝ) : z * Real.sinc z = Real.sin z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Real.sinc_of_ne_zero hz]; field_simp

/-- DLMF 1.17.14 with `ℓ = 0`, where `𝗃₀ = sinc`:
`(2xa/π) t² 𝗃₀(xt) 𝗃₀(at) = (2/π) sin(xt) sin(at)`, so 1.17.14 reduces to 1.17.12_2. -/
theorem dlmf_1_17_14_zero_integrand (x a t : ℝ) :
    2 * x * a / π * (t ^ 2 * Real.sinc (x * t) * Real.sinc (a * t)) =
      2 / π * (Real.sin (x * t) * Real.sin (a * t)) := by
  rw [← mul_sinc (x * t), ← mul_sinc (a * t)]
  ring

/-- DLMF 1.17.14 with `ℓ = 0`, made rigorous as in 1.17.12_2:
`(2a/π) ∫_0^∞ t² 𝗃₀(at) (∫_0^∞ x 𝗃₀(xt) φ(x) dx) dt = φ(a)`. -/
theorem dlmf_1_17_14_zero {φ : ℝ → ℂ} (hφ : IntegrableOn φ (Ioi 0)) {a δ : ℝ} (hδ : 0 < δ)
    (hδa : δ < a) (hbv : BoundedVariationOn φ (Icc (a - δ) (a + δ))) (hc : ContinuousAt φ a) :
    Tendsto (fun R : ℝ => ((2 * a / π : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R,
      ((t ^ 2 * Real.sinc (a * t) : ℝ) : ℂ) *
        ∫ x in Ioi 0, ((x * Real.sinc (x * t) : ℝ) : ℂ) * φ x) atTop (𝓝 (φ a)) := by
  refine (dlmf_1_17_12_2 hφ hδ hδa hbv hc).congr fun R => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  have hin : ∫ x in Ioi 0, ((x * Real.sinc (x * t) : ℝ) : ℂ) * φ x =
      (t : ℂ)⁻¹ * ∫ x in Ioi 0, φ x * ((Real.sin (t * x) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have h1 : x * Real.sinc (x * t) * t = Real.sin (t * x) := by
      rw [mul_assoc, mul_comm (Real.sinc _), ← mul_assoc, mul_sinc, mul_comm]
    have : ((x * Real.sinc (x * t) : ℝ) : ℂ) = (t : ℂ)⁻¹ * ((Real.sin (t * x) : ℝ) : ℂ) := by
      have ht : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
      rw [← h1]; push_cast; field_simp
    rw [this]; ring
  rw [hin]
  have h2 := mul_sinc (a * t)
  have ht : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
  have h3 : ((Real.sin (a * t) : ℝ) : ℂ) = (a : ℂ) * t * (Real.sinc (a * t) : ℂ) := by
    rw [← h2]; push_cast; ring
  rw [h3]
  push_cast
  field_simp

end Azurite.DLMF
