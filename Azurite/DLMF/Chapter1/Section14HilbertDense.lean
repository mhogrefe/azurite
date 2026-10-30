/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertCore

/-!
# DLMF 1.14.45: Poisson integrals as the dense class

For integrable `g` and `b > 0`, `P_b ∗ g` (`poissonInt`) has Hilbert transform `Q_b ∗ g`
(`conjPoissonInt`, DLMF's conjugate Poisson kernel) everywhere (`hasHilbert_poissonInt`). The
proof writes both through the Fourier multipliers `e^{−b|ξ|}` and `−i sign(ξ) e^{−b|ξ|}`, using the
explicit integrals `integral_expKernel` and `integral_sign_expKernel`.

`cauchyExt` is the holomorphic extension `F(z) = (i/π) ∫ g(t)/(z + ib − t) dt`, with
`F = P_b ∗ g − i Q_b ∗ g` on `ℝ` (`cauchyExt_ofReal`). For `g` vanishing outside a bounded
interval it has the decay `cauchyExt_bounds`, which gives the sharp bound on the class
(`integral_conjPoissonInt_rpow_le`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Two Fourier integrals -/

theorem integrableOn_exp_Ioi_aux {b : ℝ} (hb : 0 < b) (s : ℝ) :
    IntegrableOn (fun ξ : ℝ => cexp ((-(b : ℂ) + I * s) * ξ)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hb) 0

theorem integral_exp_Ioi_aux {b : ℝ} (hb : 0 < b) (s : ℝ) :
    ∫ ξ in Ioi (0 : ℝ), cexp ((-(b : ℂ) + I * s) * ξ) = 1 / ((b : ℂ) - I * s) := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hb) 0]
  have : (b : ℂ) - I * s ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show -(b : ℂ) + I * s = -((b : ℂ) - I * s) by ring, div_neg, neg_div, neg_neg]

/-- The kernel `e^{−b|ξ| + iξs}`. -/
noncomputable def expKernel (b s ξ : ℝ) : ℂ := cexp (-((b : ℂ) * |ξ|) + I * ξ * s)

theorem expKernel_of_pos {b s ξ : ℝ} (hξ : 0 < ξ) :
    expKernel b s ξ = cexp ((-(b : ℂ) + I * s) * ξ) := by
  rw [expKernel, abs_of_pos hξ]; congr 1; ring

theorem expKernel_neg_of_pos {b s ξ : ℝ} (hξ : 0 < ξ) :
    expKernel b s (-ξ) = cexp ((-(b : ℂ) + I * (-s : ℝ)) * ξ) := by
  rw [expKernel, abs_neg, abs_of_pos hξ]; congr 1; push_cast; ring

theorem norm_expKernel (b s ξ : ℝ) : ‖expKernel b s ξ‖ = Real.exp (-(b * |ξ|)) := by
  rw [expKernel, Complex.norm_exp]; congr 1; simp

theorem integrable_expKernel {b : ℝ} (hb : 0 < b) (s : ℝ) : Integrable (expKernel b s) := by
  refine integrable_of_halves ((integrableOn_exp_Ioi_aux hb s).congr_fun
    (fun ξ hξ => (expKernel_of_pos hξ).symm) measurableSet_Ioi)
    ((integrableOn_exp_Ioi_aux hb (-s)).congr_fun
    (fun ξ hξ => (expKernel_neg_of_pos hξ).symm) measurableSet_Ioi)

/-- `∫ e^{−b|ξ|} e^{iξs} dξ = 2b/(b² + s²)`. -/
theorem integral_expKernel {b : ℝ} (hb : 0 < b) (s : ℝ) :
    ∫ ξ, expKernel b s ξ = 2 * b / (b ^ 2 + s ^ 2) := by
  rw [integral_eq_halves (integrable_expKernel hb s)]
  rw [integral_add ((integrableOn_exp_Ioi_aux hb s).congr_fun
    (fun ξ hξ => (expKernel_of_pos hξ).symm) measurableSet_Ioi)
    ((integrableOn_exp_Ioi_aux hb (-s)).congr_fun
    (fun ξ hξ => (expKernel_neg_of_pos hξ).symm) measurableSet_Ioi)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => expKernel_of_pos hξ),
    setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => expKernel_neg_of_pos hξ),
    integral_exp_Ioi_aux hb, integral_exp_Ioi_aux hb]
  have h1 : (b : ℂ) - I * s ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have h2 : (b : ℂ) - I * ((-s : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have h3 : ((b ^ 2 + s ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < b ^ 2 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast at h2 h3 ⊢
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring_nf
  rw [I_sq]
  ring

/-- `∫ (−i sign ξ) e^{−b|ξ|} e^{iξs} dξ = 2s/(b² + s²)`. -/
theorem integral_sign_expKernel {b : ℝ} (hb : 0 < b) (s : ℝ) :
    ∫ ξ, -I * (Real.sign ξ : ℂ) * expKernel b s ξ = 2 * s / (b ^ 2 + s ^ 2) := by
  have hi : Integrable fun ξ => -I * (Real.sign ξ : ℂ) * expKernel b s ξ :=
    (integrable_expKernel hb s).bdd_mul (c := 1) ((Continuous.aestronglyMeasurable
      (by fun_prop)).mul (Complex.measurable_ofReal.comp measurable_realSign).aestronglyMeasurable)
      (ae_of_all _ norm_neg_I_mul_sign_le)
  rw [integral_eq_halves hi]
  have e : ∀ ξ ∈ Ioi (0 : ℝ), -I * (Real.sign ξ : ℂ) * expKernel b s ξ +
      -I * (Real.sign (-ξ) : ℂ) * expKernel b s (-ξ) =
      -I * cexp ((-(b : ℂ) + I * s) * ξ) + I * cexp ((-(b : ℂ) + I * (-s : ℝ)) * ξ) :=
    fun ξ hξ => by
      rw [Real.sign_neg, Real.sign_of_pos hξ, expKernel_of_pos hξ, expKernel_neg_of_pos hξ]
      push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add
    ((integrableOn_exp_Ioi_aux hb s).const_mul _) ((integrableOn_exp_Ioi_aux hb (-s)).const_mul _),
    integral_const_mul, integral_const_mul, integral_exp_Ioi_aux hb, integral_exp_Ioi_aux hb]
  have h1 : (b : ℂ) - I * s ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have h2 : (b : ℂ) - I * ((-s : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have h3 : ((b ^ 2 + s ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < b ^ 2 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast at h2 h3 ⊢
  rw [mul_one_div, mul_one_div, div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring_nf
  rw [I_sq]
  ring

/-! ### Poisson and conjugate Poisson integrals through the Fourier transform -/

theorem integrable_exp_neg_abs {b : ℝ} (hb : 0 < b) :
    Integrable fun ξ : ℝ => Real.exp (-(b * |ξ|)) := by
  have := (integrable_expKernel hb 0).norm
  simpa only [norm_expKernel] using this

theorem continuous_expKernel (b : ℝ) :
    Continuous fun q : ℝ × ℝ => expKernel b q.1 q.2 := by
  unfold expKernel; fun_prop

/-- `𝓕⁻¹(φ e^{−b|ξ|} 𝓕g)(x) = (1/2π) ∫ g(t) (∫ φ(ξ) e^{−b|ξ| + iξ(t−x)} dξ) dt`, by Fubini. -/
theorem dlmfFourier_expKernel {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφb : ∀ ξ, ‖φ ξ‖ ≤ 1) (x : ℝ) :
    dlmfFourier (fun ξ => φ ξ * cexp (-((b : ℂ) * |ξ|)) * dlmfFourier g ξ) (-x) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t, g t * ∫ ξ, φ ξ * expKernel b (t - x) ξ := by
  set c : ℂ := ((√(2 * π) : ℝ) : ℂ) with hc
  have hcc : c⁻¹ * c⁻¹ = ((2 * π : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, hc, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  set H : ℝ → ℝ → ℂ := fun ξ t => g t * (φ ξ * expKernel b (t - x) ξ) with hH
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    refine ((integrable_exp_neg_abs hb).mul_prod hg.norm).mono' ?_ (ae_of_all _ fun q => ?_)
    · exact (hg.aestronglyMeasurable.comp_snd).mul ((hφm.aestronglyMeasurable.comp_fst).mul
        (((continuous_expKernel b).comp (by fun_prop : Continuous fun q : ℝ × ℝ =>
          (q.2 - x, q.1))).aestronglyMeasurable))
    · change ‖g q.2 * (φ q.1 * expKernel b (q.2 - x) q.1)‖ ≤ Real.exp (-(b * |q.1|)) * ‖g q.2‖
      rw [norm_mul, norm_mul, norm_expKernel]
      calc ‖g q.2‖ * (‖φ q.1‖ * Real.exp (-(b * |q.1|))) ≤
          ‖g q.2‖ * (1 * Real.exp (-(b * |q.1|))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hφb _) (Real.exp_pos _).le)
              (norm_nonneg _)
        _ = Real.exp (-(b * |q.1|)) * ‖g q.2‖ := by ring
  have hswap := integral_integral_swap hHi
  rw [dlmfFourier]
  calc c⁻¹ * ∫ ξ, φ ξ * cexp (-((b : ℂ) * |ξ|)) * dlmfFourier g ξ * cexp (I * ((-x : ℝ) : ℂ) * ξ)
      = c⁻¹ * ∫ ξ, c⁻¹ * ∫ t, H ξ t := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
        simp only
        rw [dlmfFourier, show φ ξ * cexp (-((b : ℂ) * |ξ|)) * (c⁻¹ * ∫ t, g t * cexp (I * ξ * t)) *
          cexp (I * ((-x : ℝ) : ℂ) * ξ) = c⁻¹ * ((φ ξ * cexp (-((b : ℂ) * |ξ|)) *
          cexp (I * ((-x : ℝ) : ℂ) * ξ)) * ∫ t, g t * cexp (I * ξ * t)) by ring,
          ← integral_const_mul]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [hH, expKernel]
        rw [show φ ξ * cexp (-((b : ℂ) * |ξ|)) * cexp (I * ((-x : ℝ) : ℂ) * ξ) *
          (g t * cexp (I * ξ * t)) = g t * (φ ξ * (cexp (-((b : ℂ) * |ξ|)) * cexp (I * ξ * t) *
          cexp (I * ((-x : ℝ) : ℂ) * ξ))) by ring, ← Complex.exp_add, ← Complex.exp_add]
        congr 3
        push_cast; ring
    _ = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t, g t * ∫ ξ, φ ξ * expKernel b (t - x) ξ := by
        rw [integral_const_mul, ← mul_assoc, hcc, hswap]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [hH]
        rw [integral_const_mul]

/-- The Poisson integral `(P_b ∗ g)(x) = (1/π) ∫ b/((t − x)² + b²) g(t) dt`. -/
noncomputable def poissonInt (b : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ t, ((b / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * g t

/-- The conjugate Poisson integral `(1/π) ∫ (t − x)/((t − x)² + b²) g(t) dt` of 1.14.42. -/
noncomputable def conjPoissonInt (b : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ t, (((t - x) / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * g t

theorem poissonInt_eq_dlmfFourier {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    poissonInt b g x =
      dlmfFourier (fun ξ => cexp (-((b : ℂ) * |ξ|)) * dlmfFourier g ξ) (-x) := by
  have h := dlmfFourier_expKernel hg hb (φ := fun _ => 1) measurable_const (fun _ => by simp) x
  simp only [one_mul] at h
  rw [h, poissonInt]
  simp_rw [integral_expKernel hb]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : ((b ^ 2 + (t - x) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < b ^ 2 + (t - x) ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hd' : ((t : ℂ) - x) ^ 2 + (b : ℂ) ^ 2 ≠ 0 := by
    push_cast at hd; rwa [add_comm]
  push_cast at hd ⊢
  field_simp
  ring

theorem conjPoissonInt_eq_dlmfFourier {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b)
    (x : ℝ) : conjPoissonInt b g x = dlmfFourier
      (fun ξ => -I * (Real.sign ξ : ℂ) * cexp (-((b : ℂ) * |ξ|)) * dlmfFourier g ξ) (-x) := by
  have h := dlmfFourier_expKernel hg hb (φ := fun ξ => -I * (Real.sign ξ : ℂ))
    (measurable_const.mul (Complex.measurable_ofReal.comp measurable_realSign))
    norm_neg_I_mul_sign_le x
  rw [h, conjPoissonInt]
  simp_rw [integral_sign_expKernel hb]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : ((b ^ 2 + (t - x) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < b ^ 2 + (t - x) ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hd' : ((t : ℂ) - x) ^ 2 + (b : ℂ) ^ 2 ≠ 0 := by
    push_cast at hd; rwa [add_comm]
  push_cast at hd ⊢
  field_simp
  ring

theorem integrable_poissonMultiplier {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b) :
    Integrable fun ξ : ℝ => cexp (-((b : ℂ) * |ξ|)) * dlmfFourier g ξ := by
  refine ((integrable_exp_neg_abs hb).mul_const ((√(2 * π))⁻¹ * ∫ t, ‖g t‖)).mono'
    (((by fun_prop : Continuous fun ξ : ℝ => cexp (-((b : ℂ) * |ξ|))).mul
      (dlmf_1_14_i_continuous hg)).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_mul, Complex.norm_exp]
  have : (-((b : ℂ) * |ξ|)).re = -(b * |ξ|) := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (dlmf_1_14_2 g ξ) (Real.exp_pos _).le

/-- The Hilbert transform of the Poisson integral is the conjugate Poisson integral:
`ℋ(P_b ∗ g) = Q_b ∗ g` (in DLMF's sign convention), for integrable `g` and `b > 0`. -/
theorem hasHilbert_poissonInt {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasHilbert (poissonInt b g) x (conjPoissonInt b g x) := by
  have key := hasHilbert_dlmfFourier (integrable_poissonMultiplier hg hb) x
  have hf : (fun u => dlmfFourier (fun ξ => cexp (-((b : ℂ) * |ξ|)) * dlmfFourier g ξ) (-u)) =
      poissonInt b g := funext fun u => (poissonInt_eq_dlmfFourier hg hb u).symm
  rw [hf] at key
  rw [conjPoissonInt_eq_dlmfFourier hg hb]
  convert key using 2
  funext ξ
  ring

/-! ### The holomorphic extension `F(z) = (i/π) ∫ g(t)/(z + ib − t) dt` -/

/-- The Cauchy integral `F(z) = (i/π) ∫ g(t)/(z + ib − t) dt`, holomorphic on `Im z > −b`, with
boundary values `F(x) = (P_b ∗ g)(x) − i (Q_b ∗ g)(x)`. -/
noncomputable def cauchyExt (b : ℝ) (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  (I / π) * ∫ t, g t / (z + I * b - t)

/-- `|z + ib − t| ≥ κ (1 + |z|)` for `Im z ≥ 0`, `|t| ≤ M`, with `κ = b/(1 + 2(M + b))`. -/
theorem norm_cauchy_denom_ge {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) {z : ℂ} (hz : 0 ≤ z.im)
    {t : ℝ} (ht : |t| ≤ M) :
    b / (1 + 2 * (M + b)) * (1 + ‖z‖) ≤ ‖z + I * b - t‖ := by
  set κ := b / (1 + 2 * (M + b)) with hκ
  have hD : 0 < 1 + 2 * (M + b) := by positivity
  have him : (z + I * b - t).im = z.im + b := by simp
  have h1 : b ≤ ‖z + I * b - t‖ := by
    have := Complex.abs_im_le_norm (z + I * b - t)
    rw [him, abs_of_nonneg (by linarith)] at this
    linarith
  have h2 : ‖z‖ - (b + M) ≤ ‖z + I * b - t‖ := by
    have := norm_sub_norm_le z (-(I * b - t))
    have e : ‖-(I * (b : ℂ) - t)‖ ≤ b + M := by
      rw [norm_neg]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hb.le, Real.norm_eq_abs]
      linarith
    rw [show z - -(I * (b : ℂ) - t) = z + I * b - t by ring] at this
    linarith
  rcases le_or_gt ‖z‖ (2 * (M + b)) with h | h
  · calc κ * (1 + ‖z‖) ≤ κ * (1 + 2 * (M + b)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = b := by rw [hκ]; field_simp
      _ ≤ _ := h1
  · have hz0 : 0 < ‖z‖ := by linarith [show 0 < 2 * (M + b) by positivity]
    calc κ * (1 + ‖z‖) ≤ ‖z‖ / 2 := by
          rw [hκ, div_mul_eq_mul_div, div_le_div_iff₀ hD (by norm_num)]
          nlinarith
      _ ≤ ‖z‖ - (b + M) := by linarith
      _ ≤ _ := h2

theorem hasDerivAt_cauchyExt {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} {z₀ : ℂ}
    (hz₀ : -b < z₀.im) :
    HasDerivAt (cauchyExt b g) (I / π * ∫ t, -(g t / (z₀ + I * b - t) ^ 2)) z₀ := by
  set ε := (z₀.im + b) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hden : ∀ z ∈ Metric.ball z₀ ε, ∀ t : ℝ, ε ≤ ‖z + I * b - t‖ := fun z hz t => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (Complex.abs_im_le_norm (z - z₀)).trans_lt hz
    rw [sub_im, abs_lt] at h1
    have := Complex.abs_im_le_norm (z + I * b - t)
    have him : (z + I * b - t).im = z.im + b := by simp
    rw [him] at this
    rw [abs_le] at this
    linarith [h1.1]
  have hne : ∀ z ∈ Metric.ball z₀ ε, ∀ t : ℝ, z + I * b - t ≠ 0 := fun z hz t h => by
    have := hden z hz t; rw [h, norm_zero] at this; linarith
  have hcont : ∀ z ∈ Metric.ball z₀ ε, Continuous fun t : ℝ => (z + I * b - t)⁻¹ :=
    fun z hz => (by fun_prop : Continuous fun t : ℝ => z + I * b - t).inv₀ (hne z hz)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z (t : ℝ) => g t / (z + I * b - t))
    (F' := fun z (t : ℝ) => -(g t / (z + I * b - t) ^ 2))
    (bound := fun t => ‖g t‖ / ε ^ 2) (x₀ := z₀) (Metric.ball_mem_nhds z₀ hεpos)
    (by
      filter_upwards [Metric.ball_mem_nhds z₀ hεpos] with z hz
      exact (hg.aestronglyMeasurable.mul (hcont z hz).aestronglyMeasurable).congr
        (ae_of_all _ fun t => (div_eq_mul_inv _ _).symm))
    (hg.mul_bdd (c := ε⁻¹) (hcont z₀ (Metric.mem_ball_self hεpos)).aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [norm_inv]; exact inv_anti₀ hεpos (hden z₀ (Metric.mem_ball_self hεpos) t))
      |>.congr (ae_of_all _ fun t => (div_eq_mul_inv _ _).symm))
    ((hg.aestronglyMeasurable.mul (((hcont z₀ (Metric.mem_ball_self hεpos)).pow 2)
      ).aestronglyMeasurable).neg.congr (ae_of_all _ fun t => by
        simp only [Pi.neg_apply, Pi.mul_apply, Pi.pow_apply, inv_pow, div_eq_mul_inv]))
    (ae_of_all _ fun t z hz => by
      rw [norm_neg, norm_div, norm_pow]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ hεpos.le (hden z hz t) 2))
    (hg.norm.div_const _)
    (ae_of_all _ fun t z hz => by
      have h1 : HasDerivAt (fun z : ℂ => z + I * b - t) 1 z := by
        simpa using ((hasDerivAt_id z).add_const (I * b)).sub_const (t : ℂ)
      exact ((hasDerivAt_const z (g t)).div h1 (hne z hz t)).congr_deriv (by ring))
  exact key.2.const_mul (I / π)

theorem differentiableOn_cauchyExt {g : ℝ → ℂ} (hg : Integrable g) (b : ℝ) :
    DifferentiableOn ℂ (cauchyExt b g) {z | -b < z.im} := fun _ hz =>
  (hasDerivAt_cauchyExt hg hz).differentiableAt.differentiableWithinAt

/-- Decay of `F` and `F′` on the closed upper half-plane when `g` vanishes outside `[−M, M]`. -/
theorem cauchyExt_bounds {g : ℝ → ℂ} (hg : Integrable g) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (hgs : ∀ t : ℝ, M < |t| → g t = 0) :
    (∀ z : ℂ, 0 ≤ z.im → ‖cauchyExt b g z‖ ≤
      (π⁻¹ * (∫ t, ‖g t‖) / (b / (1 + 2 * (M + b))) ^ 2) / (1 + ‖z‖)) ∧
    (∀ z : ℂ, 0 ≤ z.im → ‖deriv (cauchyExt b g) z‖ ≤
      (π⁻¹ * (∫ t, ‖g t‖) / (b / (1 + 2 * (M + b))) ^ 2) / (1 + ‖z‖) ^ 2) := by
  set κ := b / (1 + 2 * (M + b)) with hκ
  have hκpos : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one (by positivity)]; linarith
  set G := ∫ t, ‖g t‖ with hG
  have hG0 : 0 ≤ G := integral_nonneg fun _ => norm_nonneg _
  have hπ : 0 < π := Real.pi_pos
  have hpt : ∀ z : ℂ, 0 ≤ z.im → ∀ (k : ℕ) (t : ℝ),
      ‖g t‖ / ‖z + I * b - t‖ ^ k ≤ ‖g t‖ / (κ * (1 + ‖z‖)) ^ k := fun z hz k t => by
    by_cases ht : |t| ≤ M
    · exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by positivity) (norm_cauchy_denom_ge hb hM hz ht) k)
    · rw [hgs t (not_le.mp ht), norm_zero, zero_div, zero_div]
  have hIπ : ‖I / (π : ℂ)‖ = π⁻¹ := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hπ.le, one_div]
  constructor
  · intro z hz
    have h1 : ‖∫ t, g t / (z + I * b - t)‖ ≤ ∫ t, ‖g t‖ / (κ * (1 + ‖z‖)) :=
      norm_integral_le_of_norm_le (hg.norm.div_const _) (ae_of_all _ fun t => by
        have := hpt z hz 1 t; rw [pow_one, pow_one] at this; rwa [norm_div])
    rw [integral_div] at h1
    rw [cauchyExt, norm_mul, hIπ]
    calc π⁻¹ * ‖∫ t, g t / (z + I * b - t)‖ ≤ π⁻¹ * (G / (κ * (1 + ‖z‖))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ π⁻¹ * G / κ ^ 2 / (1 + ‖z‖) := by
          have h1z : 0 < 1 + ‖z‖ := by positivity
          rw [div_div, mul_div_assoc]
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hG0 (by positivity) ?_)
            (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right hκ1 (mul_nonneg hκpos.le h1z.le)]
  · intro z hz
    rw [(hasDerivAt_cauchyExt hg (by linarith : -b < z.im)).deriv, norm_mul, hIπ]
    have h1 : ‖∫ t, -(g t / (z + I * b - t) ^ 2)‖ ≤ ∫ t, ‖g t‖ / (κ * (1 + ‖z‖)) ^ 2 :=
      norm_integral_le_of_norm_le (hg.norm.div_const _) (ae_of_all _ fun t => by
        rw [norm_neg, norm_div, norm_pow]; exact hpt z hz 2 t)
    rw [integral_div] at h1
    calc π⁻¹ * ‖∫ t, -(g t / (z + I * b - t) ^ 2)‖ ≤ π⁻¹ * (G / (κ * (1 + ‖z‖)) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = π⁻¹ * G / κ ^ 2 / (1 + ‖z‖) ^ 2 := by rw [mul_pow]; field_simp

/-- The boundary values: `F(x) = (P_b ∗ g)(x) − i (Q_b ∗ g)(x)`. -/
theorem cauchyExt_ofReal {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    cauchyExt b g x = poissonInt b g x - I * conjPoissonInt b g x := by
  have hk1 : Integrable fun t : ℝ => ((b / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * g t :=
    hg.bdd_mul (c := 1 / b) ((Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
          div_le_div_iff₀ (by positivity) hb]
        nlinarith [sq_nonneg (t - x)])
  have hk2 : Integrable fun t : ℝ => (((t - x) / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * g t :=
    hg.bdd_mul (c := 1 / b) ((Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_div_sq_add_sq_le hb)
  have hR : poissonInt b g x - I * conjPoissonInt b g x = (π : ℂ)⁻¹ * ∫ t,
      (((b / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * g t -
        I * ((((t - x) / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * g t)) := by
    rw [integral_sub hk1 (hk2.const_mul I), integral_const_mul, poissonInt, conjPoissonInt]
    ring
  have hL : cauchyExt b g x = (π : ℂ)⁻¹ * ∫ t, I * (g t / (x + I * b - t)) := by
    rw [cauchyExt, integral_const_mul]; ring
  rw [hL, hR]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hD : (((t - x) ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < (t - x) ^ 2 + b ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hz : (x : ℂ) + I * b - t ≠ 0 := fun h => by
    have := congrArg im h; simp at this; linarith
  have hz' : (x : ℂ) - I * b - t ≠ 0 := fun h => by
    have := congrArg im h; simp at this; linarith
  have hprod : ((x : ℂ) + I * b - t) * ((x : ℂ) - I * b - t) =
      (((t - x) ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hinv : g t / ((x : ℂ) + I * b - t) =
      g t * ((x : ℂ) - I * b - t) / (((t - x) ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    rw [← hprod, mul_comm ((x : ℂ) + I * b - t), ← div_div, mul_div_assoc, div_self hz', mul_one]
  simp only
  rw [hinv]
  simp only [ofReal_div]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc' I (((t - x : ℝ) : ℂ) * g t),
    ← sub_div, mul_div_assoc', div_left_inj' hD]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-! ### The sharp bound on the dense class -/

theorem poissonInt_ofReal (b : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    poissonInt b (fun t => (g t : ℂ)) x =
      ((π⁻¹ * ∫ t, b / ((t - x) ^ 2 + b ^ 2) * g t : ℝ) : ℂ) := by
  rw [poissonInt]
  have : (fun t : ℝ => ((b / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * (g t : ℂ)) =
      fun t => ((b / ((t - x) ^ 2 + b ^ 2) * g t : ℝ) : ℂ) := funext fun t => by push_cast; ring
  rw [this, integral_complex_ofReal]
  push_cast; ring

theorem conjPoissonInt_ofReal (b : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    conjPoissonInt b (fun t => (g t : ℂ)) x =
      ((π⁻¹ * ∫ t, (t - x) / ((t - x) ^ 2 + b ^ 2) * g t : ℝ) : ℂ) := by
  rw [conjPoissonInt]
  have : (fun t : ℝ => (((t - x) / ((t - x) ^ 2 + b ^ 2) : ℝ) : ℂ) * (g t : ℂ)) =
      fun t => (((t - x) / ((t - x) ^ 2 + b ^ 2) * g t : ℝ) : ℂ) :=
    funext fun t => by push_cast; ring
  rw [this, integral_complex_ofReal]
  push_cast; ring

/-- **DLMF 1.14.45 on the dense class** (`1 < p ≤ 2`): for real integrable `g` vanishing outside a
bounded interval and `b > 0`, `f = P_b ∗ g` has `ℋf = Q_b ∗ g` (`hasHilbert_poissonInt`), and
`∫ |ℋf|^p ≤ tan^p(π/2p) ∫ |f|^p`. -/
theorem integral_conjPoissonInt_rpow_le {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {g : ℝ → ℝ}
    (hg : Integrable g) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) (hgs : ∀ t : ℝ, M < |t| → g t = 0) :
    Integrable (fun x => ‖poissonInt b (fun t => (g t : ℂ)) x‖ ^ p) ∧
    Integrable (fun x => ‖conjPoissonInt b (fun t => (g t : ℂ)) x‖ ^ p) ∧
    ∫ x, ‖conjPoissonInt b (fun t => (g t : ℂ)) x‖ ^ p ≤
      pichoridesA p ^ p * ∫ x, ‖poissonInt b (fun t => (g t : ℂ)) x‖ ^ p := by
  set gC : ℝ → ℂ := fun t => (g t : ℂ) with hgC
  have hgCi : Integrable gC := hg.ofReal
  have hgCs : ∀ t : ℝ, M < |t| → gC t = 0 := fun t ht => by simp [hgC, hgs t ht]
  obtain ⟨hFb, hF'b⟩ := cauchyExt_bounds hgCi hb hM hgCs
  have hK : 0 ≤ π⁻¹ * (∫ t, ‖gC t‖) / (b / (1 + 2 * (M + b))) ^ 2 := by
    have : 0 ≤ ∫ t, ‖gC t‖ := integral_nonneg fun t => norm_nonneg (gC t)
    positivity
  obtain ⟨h1, h2, h3⟩ := integral_im_rpow_le hp1 hp2 hb (differentiableOn_cauchyExt hgCi b) hK
    hFb hF'b
  have hre : ∀ x : ℝ, |(cauchyExt b gC x).re| ^ p = ‖poissonInt b gC x‖ ^ p := fun x => by
    rw [cauchyExt_ofReal hgCi hb, poissonInt_ofReal, conjPoissonInt_ofReal]
    simp [Complex.norm_real, Real.norm_eq_abs]
  have him : ∀ x : ℝ, |(cauchyExt b gC x).im| ^ p = ‖conjPoissonInt b gC x‖ ^ p := fun x => by
    rw [cauchyExt_ofReal hgCi hb, poissonInt_ofReal, conjPoissonInt_ofReal]
    simp [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hre, him] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

end Azurite.DLMF
