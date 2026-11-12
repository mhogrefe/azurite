/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section13Bounds

/-!
# DLMF 5.13.4: Ramanujan's beta integral

`∫_{−∞}^{∞} dt/(Γ(a + t)Γ(b + t)Γ(c − t)Γ(d − t)) =
Γ(a + b + c + d − 3)/(Γ(a + c − 1)Γ(a + d − 1)Γ(b + c − 1)Γ(b + d − 1))` for
`ℜ(a + b + c + d) > 3` (`dlmf_5_13_4`).

Proof.
1. By 5.12.5 in the form `integral_cos_cpow_mul_cexp`, `1/(Γ(a + t)Γ(c − t))` is
   `2^{α}/(2πΓ(α))` times the Fourier integral `∫_{−π/2}^{π/2} cos^{α−1}φ e^{i(c−a)φ}e^{−2itφ} dφ`,
   `α = a + c − 1` (`invGammaPair_eq_integral`).
2. For `ℜ(a + c) > 2`, `ℜ(b + d) > 1` (`ramanujan_of_re`): write the second factor as its Fourier
   integral, exchange the integrals (Fubini; the first factor is integrable by
   `exists_bound_invGammaPair`), and recover `cos^{α−1}ψ e^{−i(c−a)ψ}` by Fourier inversion. What
   remains is one more instance of 5.12.5.
3. Both sides are holomorphic in `a` on `ℜ(a + b + c + d) > 3` (`differentiableOn_ramanujan`, from
   the uniform bound), which removes `ℜ(a + c) > 2` when `ℜ(b + d) > 1`; otherwise exchange the
   pairs `(a, c)` and `(b, d)`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real FourierTransform

namespace Azurite.DLMF

/-! ### Step 1: the Fourier representation -/

/-- `1/(Γ(a + t)Γ(c − t)) = 2^{α}/(2πΓ(α)) ∫_{−π/2}^{π/2} cos^{α−1}φ e^{i(c−a−2t)φ} dφ`,
`α = a + c − 1`, `ℜα > 0`. -/
theorem invGammaPair_eq_integral {a c : ℂ} (hac : 0 < (a + c - 1).re) (t : ℝ) :
    invGammaPair a c t = 2 ^ (a + c - 1) / (2 * π * Gamma (a + c - 1)) *
      ∫ φ in Ioo (-(π / 2)) (π / 2), (Real.cos φ : ℂ) ^ (a + c - 1 - 1) *
        cexp ((c - a - 2 * t) * φ * I) := by
  have h := (integral_cos_cpow_mul_cexp hac (c - a - 2 * t)).2
  rw [h, fourierBetaG, show (a + c - 1 - (c - a - 2 * t) + 1) / 2 = a + t by ring,
    show (a + c - 1 + (c - a - 2 * t) + 1) / 2 = c - t by ring,
    show a + t + (c - t) - 1 = a + c - 1 by ring, show (1 : ℂ) - (a + t) - (c - t) = -(a + c - 1)
      by ring, show (1 : ℂ) + 1 = 2 by norm_num, cpow_neg, invGammaPair]
  have hG := Complex.Gamma_ne_zero_of_re_pos hac
  have h2 : (2 : ℂ) ^ (a + c - 1) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem continuous_invGammaPair (a c : ℂ) : Continuous (invGammaPair a c) := by
  unfold invGammaPair
  exact (continuous_inv_Gamma.comp (by fun_prop)).mul (continuous_inv_Gamma.comp (by fun_prop))

theorem integrable_invGammaPair {a c : ℂ} (hac : 2 < (a + c).re) :
    Integrable (invGammaPair a c) := by
  obtain ⟨M, -, hM⟩ := exists_bound_invGammaPair a c le_rfl
  refine ((integrable_one_add_abs_rpow (r := (a + c).re - 1) (by linarith)).const_mul M).mono'
    (continuous_invGammaPair a c).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  refine (hM a (Metric.mem_closedBall_self le_rfl) t).trans (le_of_eq ?_)
  congr 2; ring

/-- The weight `cos^{α−1}φ e^{iβφ}` on `(−π/2, π/2)`, extended by `0`. -/
noncomputable def cosWeight (α β : ℂ) : ℝ → ℂ :=
  (Ioo (-(π / 2)) (π / 2)).indicator fun φ => (Real.cos φ : ℂ) ^ (α - 1) * cexp (β * φ * I)

theorem integrable_cosWeight {α : ℂ} (hα : 0 < α.re) (β : ℂ) : Integrable (cosWeight α β) :=
  (integrable_indicator_iff measurableSet_Ioo).mpr (integral_cos_cpow_mul_cexp hα β).1

/-- `1/(Γ(a + t)Γ(c − t)) = K 𝓕[cosWeight](t/π)`. -/
theorem invGammaPair_eq_fourier {a c : ℂ} (hac : 0 < (a + c - 1).re) (t : ℝ) :
    invGammaPair a c t = 2 ^ (a + c - 1) / (2 * π * Gamma (a + c - 1)) *
      𝓕 (cosWeight (a + c - 1) (c - a)) (t / π) := by
  rw [invGammaPair_eq_integral hac, Real.fourier_real_eq_integral_exp_smul, cosWeight]
  congr 1
  have e : ∀ v : ℝ, cexp (((-2 * π * v * (t / π)) : ℝ) * I) • (Ioo (-(π / 2)) (π / 2)).indicator
      (fun φ => (Real.cos φ : ℂ) ^ (a + c - 1 - 1) * cexp ((c - a) * φ * I)) v =
      (Ioo (-(π / 2)) (π / 2)).indicator (fun φ => (Real.cos φ : ℂ) ^ (a + c - 1 - 1) *
        cexp ((c - a - 2 * t) * φ * I)) v := fun v => by
    simp only [indicator, smul_eq_mul]
    split_ifs
    · rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
      ring
    · simp
  simp_rw [e]
  rw [integral_indicator measurableSet_Ioo]

/-- Fourier inversion for `cosWeight` at interior points. -/
theorem fourier_inversion_cosWeight {α β : ℂ} (hα : 0 < α.re) (hF : Integrable (𝓕 (cosWeight α β)))
    {ψ : ℝ} (hψ : ψ ∈ Ioo (-(π / 2)) (π / 2)) :
    ∫ ξ : ℝ, cexp (((-2 * π * ξ * ψ) : ℝ) * I) * 𝓕 (cosWeight α β) ξ =
      (Real.cos ψ : ℂ) ^ (α - 1) * cexp (-(β * ψ * I)) := by
  have hψ' : -ψ ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hψ.2], by linarith [hψ.1]⟩
  have hc : ContinuousAt (cosWeight α β) (-ψ) := by
    have hcos : 0 < Real.cos (-ψ) := Real.cos_pos_of_mem_Ioo hψ'
    have h1 : ContinuousAt (fun φ : ℝ => (Real.cos φ : ℂ) ^ (α - 1) * cexp (β * φ * I)) (-ψ) := by
      refine ContinuousAt.mul ?_ (by fun_prop)
      exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (mem_slitPlane_iff.mpr (Or.inl (by simp only [ofReal_re]; exact hcos)))
    refine h1.congr ?_
    filter_upwards [isOpen_Ioo.mem_nhds hψ'] with v hv
    simp [cosWeight, indicator_of_mem hv]
  have h := (integrable_cosWeight hα β).fourierInv_fourier_eq hF hc
  rw [Real.fourierInv_eq', cosWeight, indicator_of_mem hψ', Real.cos_neg] at h
  rw [show -(β * ψ * I) = β * ((-ψ : ℝ) : ℂ) * I by push_cast; ring, ← h]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [smul_eq_mul]
  congr 3
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-! ### Step 2: the case `ℜ(a + c) > 2`, `ℜ(b + d) > 1` -/

theorem ramanujan_of_re {a b c d : ℂ} (hac : 2 < (a + c).re) (hbd : 1 < (b + d).re) :
    ∫ t : ℝ, invGammaPair a c t * invGammaPair b d t =
      Gamma (a + b + c + d - 3) / (Gamma (a + c - 1) * Gamma (a + d - 1) * Gamma (b + c - 1) *
        Gamma (b + d - 1)) := by
  have hπ := Real.pi_pos
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set α₁ := a + c - 1
  set α₂ := b + d - 1
  have hα₁ : 0 < α₁.re := by simp only [α₁, sub_re, one_re]; linarith
  have hα₂ : 0 < α₂.re := by simp only [α₂, sub_re, one_re]; linarith
  set K₁ := 2 ^ α₁ / (2 * π * Gamma α₁)
  set K₂ := 2 ^ α₂ / (2 * π * Gamma α₂)
  set W := cosWeight α₁ (c - a)
  set u₂ : ℝ → ℂ := fun ψ => (Real.cos ψ : ℂ) ^ (α₂ - 1) * cexp ((d - b) * ψ * I)
  have hK₁ : K₁ ≠ 0 := by
    have h2 : (2 : ℂ) ^ α₁ ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
    exact div_ne_zero h2 (mul_ne_zero (mul_ne_zero two_ne_zero hπ0)
      (Complex.Gamma_ne_zero_of_re_pos hα₁))
  have hP := integrable_invGammaPair hac
  -- `𝓕W` is integrable
  have hF : Integrable (𝓕 W) := by
    have h := (hP.comp_mul_left' (R := π) (by positivity)).const_mul K₁⁻¹
    refine h.congr (ae_of_all _ fun ξ => ?_)
    simp only
    rw [invGammaPair_eq_fourier hα₁, show π * ξ / π = ξ by field_simp, ← mul_assoc,
      inv_mul_cancel₀ hK₁, one_mul]
  have hu₂ : IntegrableOn u₂ (Ioo (-(π / 2)) (π / 2)) := (integral_cos_cpow_mul_cexp hα₂ _).1
  -- the second factor as a Fourier integral
  have hbd' : ∀ t : ℝ, invGammaPair b d t =
      K₂ * ∫ ψ in Ioo (-(π / 2)) (π / 2), u₂ ψ * cexp (((-2 * ψ * t) : ℝ) * I) := fun t => by
    rw [invGammaPair_eq_integral hα₂]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun ψ _ => ?_
    have e : cexp ((d - b) * ψ * I) * cexp (((-2 * ψ * t) : ℝ) * I) =
        cexp ((d - b - 2 * t) * ψ * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [u₂]
    rw [mul_assoc ((Real.cos ψ : ℂ) ^ (α₂ - 1)), e]
  -- Fubini
  set f : ℝ → ℝ → ℂ := fun t ψ => invGammaPair a c t * (u₂ ψ * cexp (((-2 * ψ * t) : ℝ) * I))
  have hfi : Integrable (Function.uncurry f)
      (volume.prod (volume.restrict (Ioo (-(π / 2)) (π / 2)))) := by
    refine Integrable.mono' (hP.norm.mul_prod hu₂.norm) ?_ (ae_of_all _ fun p => ?_)
    · have hm : Measurable fun p : ℝ × ℝ => invGammaPair a c p.1 *
          ((Real.cos p.2 : ℂ) ^ (α₂ - 1) * cexp ((d - b) * p.2 * I) *
            cexp (((-2 * p.2 * p.1) : ℝ) * I)) :=
        ((continuous_invGammaPair a c).measurable.comp measurable_fst).mul (by fun_prop)
      exact hm.aestronglyMeasurable
    · simp only [Function.uncurry, f, norm_mul, norm_exp_ofReal_mul_I, mul_one]
      exact le_rfl
  have hswap := integral_integral_swap hfi
  have hLHS : ∫ t : ℝ, invGammaPair a c t * invGammaPair b d t =
      K₂ * ∫ t : ℝ, ∫ ψ in Ioo (-(π / 2)) (π / 2), f t ψ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [hbd' t]
    simp only [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun ψ _ => ?_
    simp only [f]
    ring
  -- the inner `t`-integral by Fourier inversion
  have hinner : ∀ ψ ∈ Ioo (-(π / 2)) (π / 2), ∫ t : ℝ, f t ψ =
      u₂ ψ * (K₁ * π * ((Real.cos ψ : ℂ) ^ (α₁ - 1) * cexp (-((c - a) * ψ * I)))) := by
    intro ψ hψ
    simp only [f]
    rw [show (fun t : ℝ => invGammaPair a c t * (u₂ ψ * cexp (((-2 * ψ * t) : ℝ) * I))) =
      fun t => u₂ ψ * (invGammaPair a c t * cexp (((-2 * ψ * t) : ℝ) * I)) by funext t; ring,
      integral_const_mul]
    congr 1
    have hsub := Measure.integral_comp_mul_left
      (fun t : ℝ => invGammaPair a c t * cexp (((-2 * ψ * t) : ℝ) * I)) π
    rw [abs_inv, abs_of_pos hπ, Complex.real_smul] at hsub
    rw [show ∫ t : ℝ, invGammaPair a c t * cexp (((-2 * ψ * t) : ℝ) * I) =
      π * ∫ ξ : ℝ, invGammaPair a c (π * ξ) * cexp (((-2 * ψ * (π * ξ)) : ℝ) * I) by
        rw [hsub, ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]]
    have hI : ∫ ξ : ℝ, invGammaPair a c (π * ξ) * cexp (((-2 * ψ * (π * ξ)) : ℝ) * I) =
        K₁ * ∫ ξ : ℝ, cexp (((-2 * π * ξ * ψ) : ℝ) * I) * 𝓕 W ξ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      simp only
      rw [invGammaPair_eq_fourier hα₁, show π * ξ / π = ξ by field_simp,
        show (-2 * ψ * (π * ξ) : ℝ) = -2 * π * ξ * ψ by ring]
      ring
    rw [hI, fourier_inversion_cosWeight hα₁ hF hψ]
    ring
  rw [hLHS, hswap, setIntegral_congr_fun measurableSet_Ioo hinner]
  -- the final instance of 5.12.5
  have hS : 0 < (a + b + c + d - 3).re := by
    simp only [sub_re, add_re] at hac hbd ⊢; norm_num; linarith
  have hfin := (integral_cos_cpow_mul_cexp hS (a + d - b - c)).2
  have hpt : ∀ ψ ∈ Ioo (-(π / 2)) (π / 2),
      u₂ ψ * (K₁ * π * ((Real.cos ψ : ℂ) ^ (α₁ - 1) * cexp (-((c - a) * ψ * I)))) =
      K₁ * π * ((Real.cos ψ : ℂ) ^ (a + b + c + d - 3 - 1) * cexp ((a + d - b - c) * ψ * I)) := by
    intro ψ hψ
    have hcos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo hψ
    have hc0 : (Real.cos ψ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcos.ne'
    simp only [u₂]
    rw [show a + b + c + d - 3 - 1 = (α₂ - 1) + (α₁ - 1) by simp only [α₁, α₂]; ring,
      cpow_add _ _ hc0]
    have e : cexp ((d - b) * ψ * I) * cexp (-((c - a) * ψ * I)) =
        cexp ((a + d - b - c) * ψ * I) := by rw [← Complex.exp_add]; congr 1; ring
    linear_combination (K₁ * π * (Real.cos ψ : ℂ) ^ (α₂ - 1) * (Real.cos ψ : ℂ) ^ (α₁ - 1)) * e
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, hfin, fourierBetaG]
  rw [show (a + b + c + d - 3 - (a + d - b - c) + 1) / 2 = b + c - 1 by ring,
    show (a + b + c + d - 3 + (a + d - b - c) + 1) / 2 = a + d - 1 by ring,
    show b + c - 1 + (a + d - 1) - 1 = a + b + c + d - 3 by ring,
    show (1 : ℂ) - (b + c - 1) - (a + d - 1) = -(α₁ + α₂) + 1 by simp only [α₁, α₂]; ring,
    show (1 : ℂ) + 1 = 2 by norm_num]
  have hG₁ := Complex.Gamma_ne_zero_of_re_pos hα₁
  have hG₂ := Complex.Gamma_ne_zero_of_re_pos hα₂
  have h2 : (2 : ℂ) ^ (-(α₁ + α₂) + 1) * 2 ^ α₁ * 2 ^ α₂ = 2 := by
    rw [mul_assoc, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show -(α₁ + α₂) + 1 + (α₁ + α₂) = 1 by ring, cpow_one]
  have h2' : (2 : ℂ) ^ (-(α₁ + α₂) + 1) = 2 * ((2 : ℂ) ^ α₁)⁻¹ * ((2 : ℂ) ^ α₂)⁻¹ := by
    rw [cpow_add _ _ two_ne_zero, cpow_neg, cpow_add _ _ two_ne_zero, cpow_one, mul_inv]
    ring
  have h2a : (2 : ℂ) ^ α₁ ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
  have h2b : (2 : ℂ) ^ α₂ ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
  simp only [K₁, K₂]
  rw [h2', div_eq_mul_inv (Gamma (a + b + c + d - 3)), mul_inv, mul_inv, mul_inv]
  field_simp

/-! ### Step 3: analytic continuation -/

theorem differentiable_inv_Gamma : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
  simpa [one_div] using Complex.differentiable_one_div_Gamma

theorem continuous_deriv_inv_Gamma : Continuous (deriv fun z : ℂ => (Gamma z)⁻¹) :=
  (differentiable_inv_Gamma.contDiff (n := 1)).continuous_deriv le_rfl

/-- The left side of 5.13.4 is holomorphic in `a` on `ℜ(a + b + c + d) > 3`. -/
theorem differentiableOn_ramanujan (b c d : ℂ) :
    DifferentiableOn ℂ (fun a => ∫ t : ℝ, invGammaPair a c t * invGammaPair b d t)
      {a | 3 < (a + b + c + d).re} := by
  set g : ℂ → ℂ := fun z => (Gamma z)⁻¹
  refine differentiableOn_integral_of_holo
    (F := fun a (t : ℝ) => invGammaPair a c t * invGammaPair b d t)
    (F' := fun a (t : ℝ) => deriv g (a + t) * g (c - t) * invGammaPair b d t)
    (fun a _ => ((continuous_invGammaPair a c).mul
      (continuous_invGammaPair b d)).aestronglyMeasurable)
    (fun a _ => (((continuous_deriv_inv_Gamma.comp (by fun_prop : Continuous fun t : ℝ =>
      a + t)).mul (continuous_inv_Gamma.comp (by fun_prop : Continuous fun t : ℝ => c - t))).mul
      (continuous_invGammaPair b d)).aestronglyMeasurable)
    fun a₀ ha₀ => ?_
  have hS : 3 < (a₀ + b + c + d).re := ha₀
  set ρ := ((a₀ + b + c + d).re - 3) / 2
  have hρ : 0 < ρ := by simp only [ρ]; linarith
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_invGammaPair a₀ c hρ.le
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_invGammaPair b d le_rfl
  refine ⟨ρ / 2, by positivity, fun a ha => ?_, fun t => M₁ * M₂ *
    (1 + |t|) ^ (-((a₀ + b + c + d).re - 2 - ρ)),
    (integrable_one_add_abs_rpow (by simp only [ρ]; linarith)).const_mul _,
    ae_of_all _ fun t a _ => ?_, ae_of_all _ fun t a ha => ?_⟩
  · have hd := Metric.mem_ball.mp ha
    rw [dist_eq_norm] at hd
    have := (abs_re_le_norm (a - a₀)).trans hd.le
    rw [sub_re] at this
    show 3 < (a + b + c + d).re
    simp only [add_re] at hS ⊢
    simp only [ρ, add_re] at this
    linarith [(abs_le.mp this).1]
  · have h1 := (differentiable_inv_Gamma (a + t)).hasDerivAt.comp a
      ((hasDerivAt_id a).add_const (t : ℂ))
    simp only [id, mul_one] at h1
    have := (h1.mul_const (g (c - t))).mul_const (invGammaPair b d t)
    simpa [invGammaPair, g, mul_assoc] using this
  · rw [show 2 * (ρ / 2) = ρ by ring] at ha
    have h1 := hM₁ a ha t
    have h2 := hM₂ b (Metric.mem_closedBall_self le_rfl) t
    rw [norm_mul]
    have hpos : (0 : ℝ) < 1 + |t| := by positivity
    calc ‖invGammaPair a c t‖ * ‖invGammaPair b d t‖
        ≤ (M₁ * (1 + |t|) ^ (1 - (a₀ + c).re + ρ)) * (M₂ * (1 + |t|) ^ (1 - (b + d).re + 0)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = M₁ * M₂ * (1 + |t|) ^ (-((a₀ + b + c + d).re - 2 - ρ)) := by
          rw [mul_mul_mul_comm, ← Real.rpow_add hpos]
          congr 2
          simp only [add_re]; ring

theorem ramanujanRHS_eq (a b c d : ℂ) :
    Gamma (a + b + c + d - 3) / (Gamma (a + c - 1) * Gamma (a + d - 1) * Gamma (b + c - 1) *
      Gamma (b + d - 1)) = Gamma (a + b + c + d - 3) * (Gamma (a + c - 1))⁻¹ *
        (Gamma (a + d - 1))⁻¹ * (Gamma (b + c - 1))⁻¹ * (Gamma (b + d - 1))⁻¹ := by
  rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
  ring

theorem ramanujan_of_bd {a b c d : ℂ} (hbd : 1 < (b + d).re) (hS : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, invGammaPair a c t * invGammaPair b d t =
      Gamma (a + b + c + d - 3) / (Gamma (a + c - 1) * Gamma (a + d - 1) * Gamma (b + c - 1) *
        Gamma (b + d - 1)) := by
  set H := {a : ℂ | 3 < (a + b + c + d).re}
  have hH : IsOpen H := isOpen_lt continuous_const (continuous_re.comp (by fun_prop))
  have hHc : IsPreconnected H := by
    have : H = {a : ℂ | 3 - (b + c + d).re < a.re} := by
      ext a; simp only [H, mem_ofPred_eq, add_re]; constructor <;> intro h <;> linarith
    rw [this]; exact (convex_halfSpace_re_gt _).isPreconnected
  have hg : DifferentiableOn ℂ (fun a => Gamma (a + b + c + d - 3) * (Gamma (a + c - 1))⁻¹ *
      (Gamma (a + d - 1))⁻¹ * (Gamma (b + c - 1))⁻¹ * (Gamma (b + d - 1))⁻¹) H := fun a ha => by
    have ha'' : 0 < a.re + b.re + c.re + d.re - 3 := by
      have : 3 < (a + b + c + d).re := ha; simp only [add_re] at this; linarith
    have hG : DifferentiableAt ℂ (fun a => Gamma (a + b + c + d - 3)) a :=
      (Complex.differentiableAt_Gamma _ fun m h => by
        have := congrArg re h; simp at this
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp a (by fun_prop)
    exact ((((hG.mul ((differentiable_inv_Gamma.comp (by fun_prop : Differentiable ℂ fun a : ℂ =>
      a + c - 1)) a)).mul ((differentiable_inv_Gamma.comp (by fun_prop : Differentiable ℂ
        fun a : ℂ => a + d - 1)) a)).mul_const _).mul_const _).differentiableWithinAt
  set a₁ : ℂ := 3 - c
  have ha₁ : a₁ ∈ H := by
    show 3 < (a₁ + b + c + d).re
    simp only [a₁, add_re, sub_re] at hbd ⊢; norm_num; linarith
  have heq := ((differentiableOn_ramanujan b c d).analyticOnNhd
    hH).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hH) hHc ha₁ (by
      filter_upwards [(isOpen_lt continuous_const (continuous_re.comp
        (by fun_prop : Continuous fun a : ℂ => a + c))).mem_nhds
        (show a₁ ∈ {a : ℂ | 2 < (a + c).re} by simp [a₁]; norm_num)] with a ha
      rw [ramanujan_of_re ha hbd, ramanujanRHS_eq])
  have h := heq hS
  simp only at h
  rw [h, ramanujanRHS_eq]

/-- **DLMF 5.13.4** (Ramanujan's beta integral):
`∫_{−∞}^{∞} dt/(Γ(a + t)Γ(b + t)Γ(c − t)Γ(d − t)) =
Γ(a + b + c + d − 3)/(Γ(a + c − 1)Γ(a + d − 1)Γ(b + c − 1)Γ(b + d − 1))`,
`ℜ(a + b + c + d) > 3`. -/
theorem dlmf_5_13_4 {a b c d : ℂ} (hS : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, 1 / (Gamma (a + t) * Gamma (b + t) * Gamma (c - t) * Gamma (d - t)) =
      Gamma (a + b + c + d - 3) / (Gamma (a + c - 1) * Gamma (a + d - 1) * Gamma (b + c - 1) *
        Gamma (b + d - 1)) := by
  have e : ∀ t : ℝ, 1 / (Gamma (a + t) * Gamma (b + t) * Gamma (c - t) * Gamma (d - t)) =
      invGammaPair a c t * invGammaPair b d t := fun t => by
    rw [invGammaPair, invGammaPair, one_div, mul_inv, mul_inv, mul_inv]; ring
  simp_rw [e]
  rcases lt_or_ge 1 (b + d).re with hbd | hbd
  · exact ramanujan_of_bd hbd hS
  · have hac : 1 < (a + c).re := by simp only [add_re] at hS hbd ⊢; linarith
    have h := ramanujan_of_bd (a := b) (b := a) (c := d) (d := c) hac
      (by simp only [add_re] at hS ⊢; linarith)
    rw [show b + a + d + c - 3 = a + b + c + d - 3 by ring] at h
    rw [show (fun t : ℝ => invGammaPair a c t * invGammaPair b d t) =
      fun t => invGammaPair b d t * invGammaPair a c t by funext t; ring, h]
    congr 1
    ring

end Azurite.DLMF
