/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# DLMF §1.14(i): Parseval's formulas

Formalizations of (1.14.6)–(1.14.8) for `f`, `g` absolutely and square integrable. Mathlib has
the Fourier transform on `L²` as an isometry, but not the identification with the integral on
`L¹ ∩ L²`, so Plancherel's identity is proved here directly.

**Method.**
* `h = f ⋆ f̃` with `f̃(t) = conj f(−t)` has `𝓕h = |𝓕f|²` (`fourier_conj_neg`).
* `h` is continuous, by continuity of translation in `L²` (`continuous_integral_mul_add`, through
  Mathlib's continuity of the `DomAddAct` action on `Lᵖ`).
* Damping with Gaussians gives `∫ e^{−w²/c} 𝓕h(w) dw → h(0)` (`gauss_mult`, `fourier_gauss`,
  `tendsto_gauss_fourier`), and monotone convergence gives `∫ 𝓕h = h(0)`
  (`integrable_and_integral_fourier_of_nonneg`).

**Results.**
* `plancherel` (Mathlib's normalization) and 1.14.8 (`dlmf_1_14_8`), including integrability of
  `|𝓕(f)|²`.
* 1.14.7_5 by polarization (`polar`, `integral_polar`, `dlmf_1_14_7_5`); 1.14.7
  (`dlmf_1_14_7`).
* Inversion when `f` and `𝓕(f)` are integrable, in DLMF's normalization (`dlmf_inversion`), and
  1.14.6 (`dlmf_1_14_6`, with `𝓕(f)𝓕(g)` integrable and `f ∗ g` continuous).
-/

open MeasureTheory Filter Topology Complex
open scoped FourierTransform Convolution ComplexConjugate

namespace Azurite.DLMF

/-- For square-integrable `f`, `g`, the correlation `v ↦ ∫ f(t) g(v + t) dt` is continuous
(continuity of translation in `L²`). -/
theorem continuous_integral_mul_add {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    Continuous fun v : ℝ => ∫ t, f t * g (v + t) := by
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hf' : MemLp (star f) 2 := hf.star
  set A : Lp ℂ 2 (volume : Measure ℝ) := hf'.toLp _
  set G : Lp ℂ 2 (volume : Measure ℝ) := hg.toLp g
  have hc : Continuous fun v : ℝ => (inner ℂ A ((DomAddAct.mk v) +ᵥ G) : ℂ) :=
    continuous_const.inner (DomAddAct.continuous_mk.vadd continuous_const)
  refine hc.congr fun v => ?_
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  have h1 := hf'.coeFn_toLp
  have h2 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk v) G
  have h3 : (fun t => G (v + t)) =ᵐ[volume] fun t => g (v + t) :=
    (measurePreserving_add_left volume v).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2]
  simp only [Equiv.symm_apply_apply, vadd_eq_add] at ht3 ⊢
  rw [ht3]
  simp [Pi.star_apply, RCLike.inner_apply]
  ring

/-! ### The Gaussian and the multiplication formula -/

theorem fourier_gauss {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun w : ℝ => cexp (-(c : ℂ)⁻¹ * w ^ 2)) ξ =
      (Real.pi * c : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi ^ 2 * c * ξ ^ 2) := by
  have hb : 0 < ((c : ℂ)⁻¹).re := by
    rw [← ofReal_inv, ofReal_re]; positivity
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := fourierIntegral_gaussian hb (-2 * Real.pi * ξ)
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  calc ∫ v : ℝ, cexp (↑(-2 * Real.pi * v * ξ) * I) • cexp (-(c : ℂ)⁻¹ * v ^ 2)
      = ∫ x : ℝ, cexp (I * (-2 * Real.pi * ξ) * x) * cexp (-(c : ℂ)⁻¹ * x ^ 2) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [smul_eq_mul]
        congr 2
        push_cast
        ring
    _ = _ := by
        rw [h]
        congr 1
        · rw [div_inv_eq_mul]
        · congr 1
          field_simp
          ring

theorem integrable_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun w : ℝ => cexp (-(c : ℂ)⁻¹ * w ^ 2)) := by
  have hb : 0 < ((c : ℂ)⁻¹).re := by
    rw [← ofReal_inv, ofReal_re]; positivity
  simpa using integrable_cexp_quadratic hb 0 0

/-- `∫ e^{−w²/c} 𝓕h(w) dw = ∫ (πc)^{1/2} e^{−π² c t²} h(t) dt`. -/
theorem gauss_mult {h : ℝ → ℂ} (hh : Integrable h) {c : ℝ} (hc : 0 < c) :
    ∫ w : ℝ, cexp (-(c : ℂ)⁻¹ * w ^ 2) * 𝓕 h w =
      ∫ t : ℝ, ((Real.pi * c : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi ^ 2 * c * t ^ 2)) * h t := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume)
    (ν := volume) Real.continuous_fourierChar continuous_inner hh (integrable_gauss hc)
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hflip] at this
  simp only [smul_eq_mul] at this
  change ∫ ξ : ℝ, 𝓕 h ξ * cexp (-(c : ℂ)⁻¹ * ξ ^ 2) =
    ∫ x : ℝ, h x * 𝓕 (fun w : ℝ => cexp (-(c : ℂ)⁻¹ * w ^ 2)) x at this
  simp_rw [fourier_gauss hc] at this
  rw [show (fun w : ℝ => cexp (-(c : ℂ)⁻¹ * w ^ 2) * 𝓕 h w) =
    fun w => 𝓕 h w * cexp (-(c : ℂ)⁻¹ * w ^ 2) from funext fun _ => mul_comm _ _, this]
  exact integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)

/-- The Gaussian approximate identity: `∫ e^{−w²/c} 𝓕h(w) dw → h(0)` as `c → ∞`, for integrable
`h` continuous at `0`. -/
theorem tendsto_gauss_fourier {h : ℝ → ℂ} (hh : Integrable h) (hc : ContinuousAt h 0) :
    Tendsto (fun c : ℝ => ∫ w : ℝ, cexp (-(c : ℂ)⁻¹ * w ^ 2) * 𝓕 h w) atTop (𝓝 (h 0)) := by
  have := Real.tendsto_integral_gaussian_smul' hh hc
  refine this.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  rw [gauss_mult hh hc]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Module.finrank_self, Nat.cast_one, smul_eq_mul, zero_sub, norm_neg,
    Real.norm_eq_abs]
  have ht : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by rw [← ofReal_pow, sq_abs, ofReal_pow]
  rw [ht]

/-- **Plancherel's identity, core form**: if `h` is integrable, continuous at `0`, and `𝓕h` is
real and nonnegative, then `𝓕h` is integrable and `∫ 𝓕h = h(0)`. -/
theorem integrable_and_integral_fourier_of_nonneg {h : ℝ → ℂ} (hh : Integrable h)
    (hc : ContinuousAt h 0) {φ : ℝ → ℝ} (hφ : ∀ w, 𝓕 h w = φ w) (hφ0 : ∀ w, 0 ≤ φ w) :
    Integrable φ ∧ ((∫ w, φ w : ℝ) : ℂ) = h 0 := by
  have hFc : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hh
  have hφc : Continuous φ := by
    have : φ = fun w => (𝓕 h w).re := funext fun w => by rw [hφ, ofReal_re]
    rw [this]; exact continuous_re.comp hFc
  have hφb : ∀ w, ‖φ w‖ ≤ ∫ t, ‖h t‖ := fun w => by
    have := VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) h w
    rw [← norm_real, ← hφ]
    exact this
  -- the damped integrals
  set f : ℕ → ℝ → ℝ := fun n w => Real.exp (-((n : ℝ) + 1)⁻¹ * w ^ 2) * φ w with hfdef
  have hfi : ∀ n, Integrable (f n) := fun n =>
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)).mul_bdd
      hφc.aestronglyMeasurable (ae_of_all _ (hφb ·))
  have hcast : ∀ n : ℕ, ((∫ w, f n w : ℝ) : ℂ) =
      ∫ w : ℝ, cexp (-(((n : ℝ) + 1 : ℝ) : ℂ)⁻¹ * w ^ 2) * 𝓕 h w := fun n => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hfdef, hφ]
    push_cast
    rfl
  have hlim : Tendsto (fun n : ℕ => ((∫ w, f n w : ℝ) : ℂ)) atTop (𝓝 (h 0)) := by
    have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact ((tendsto_gauss_fourier hh hc).comp hn).congr fun n => (hcast n).symm
  have hlimre : Tendsto (fun n : ℕ => ∫ w, f n w) atTop (𝓝 (h 0).re) := by
    have := (continuous_re.tendsto _).comp hlim
    simpa [Function.comp_def] using this
  have hh0 : ((h 0).re : ℂ) = h 0 := by
    have hlim' := (continuous_ofReal.tendsto _).comp hlimre
    exact tendsto_nhds_unique hlim' hlim
  -- monotone convergence
  have hmono : ∀ w, Monotone fun n => f n w := fun w n m hnm => by
    simp only [hfdef]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hφ0 w)
    have : ((m : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
    nlinarith [sq_nonneg w]
  have hpt : ∀ w, Tendsto (fun n => f n w) atTop (𝓝 (φ w)) := fun w => by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have h2 := ((h1.neg.mul_const (w ^ 2)).rexp.mul_const (φ w))
    simpa [hfdef] using h2
  have hlin : Tendsto (fun n => ∫⁻ w, ENNReal.ofReal (f n w)) atTop
      (𝓝 (∫⁻ w, ENNReal.ofReal (φ w))) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hfi n).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun w n m hnm => ENNReal.ofReal_le_ofReal (hmono w hnm))
      (ae_of_all _ fun w => (ENNReal.continuous_ofReal.tendsto _).comp (hpt w))
  have hf0 : ∀ n w, 0 ≤ f n w := fun n w => mul_nonneg (Real.exp_pos _).le (hφ0 w)
  have hlin' : Tendsto (fun n => ∫⁻ w, ENNReal.ofReal (f n w)) atTop
      (𝓝 (ENNReal.ofReal (h 0).re)) := by
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hlimre).congr fun n => ?_
    exact ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hf0 n))
  have heq := tendsto_nhds_unique hlin hlin'
  have hint : Integrable φ := by
    refine ⟨hφc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hφ0), heq]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hφ0) hint.1, heq,
    ENNReal.toReal_ofReal]
  · exact hh0
  · exact ge_of_tendsto' hlimre fun n => integral_nonneg (hf0 n)

/-! ### Plancherel -/

theorem fourier_conj_neg (f : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun t => conj (f (-t))) w = conj (𝓕 f w) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_conj, ← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [neg_neg, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [conj_ofReal, conj_I]
  push_cast
  ring

theorem integrable_conj_neg {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t => conj (f (-t))) := by
  have h1 : Integrable (fun t => f (-t)) := hf.comp_neg
  rw [← memLp_one_iff_integrable] at h1 ⊢
  exact h1.star

theorem memLp_conj_neg {f : ℝ → ℂ} (hf : MemLp f 2) : MemLp (fun t => conj (f (-t))) 2 := by
  have := (hf.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))).star
  exact this

/-- **Plancherel** for `f ∈ L¹ ∩ L²`, with Mathlib's normalization of `𝓕`. -/
theorem plancherel {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun w => ‖𝓕 f w‖ ^ 2) ∧ ∫ w, ‖𝓕 f w‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  set g : ℝ → ℂ := fun t => conj (f (-t)) with hg
  set h : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℂ ℂ] g with hh
  have hhi : Integrable h := hf.integrable_convolution _ (integrable_conj_neg hf)
  have hhv : ∀ v, h v = ∫ t, f t * star f (-v + t) := fun v => by
    simp only [hh, convolution, ContinuousLinearMap.mul_apply', hg]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [Pi.star_apply, RCLike.star_def]
    congr 3
    ring
  have hcont : ContinuousAt h 0 := by
    have := (continuous_integral_mul_add hf2 hf2.star).comp continuous_neg
    refine (this.congr fun v => ?_).continuousAt
    simp only [Function.comp_apply]
    exact (hhv v).symm
  have hF : ∀ w, 𝓕 h w = ((‖𝓕 f w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [hh, Real.fourier_mul_convolution_eq hf (integrable_conj_neg hf), fourier_conj_neg,
      mul_conj, normSq_eq_norm_sq]
  obtain ⟨hi, he⟩ := integrable_and_integral_fourier_of_nonneg hhi hcont hF
    (fun w => by positivity)
  refine ⟨hi, ?_⟩
  have h0 : h 0 = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
    rw [hhv, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [neg_zero, zero_add, Pi.star_apply, RCLike.star_def, mul_conj, normSq_eq_norm_sq]
  exact ofReal_injective (he.trans h0)

/-! ### DLMF's normalization -/

theorem integral_comp_dlmf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℝ → E) :
    ∫ x : ℝ, φ (-(x / (2 * Real.pi))) = (2 * Real.pi) • ∫ w, φ w := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have := Measure.integral_comp_mul_left φ (-(1 / (2 * Real.pi)))
  simp only [neg_mul, one_div, inv_neg, inv_inv, abs_neg] at this
  rw [abs_of_pos (by positivity)] at this
  convert this using 2
  ext x; congr 1; field_simp

theorem integrable_comp_dlmf {E : Type*} [NormedAddCommGroup E] {φ : ℝ → E}
    (hφ : Integrable φ) :
    Integrable fun x : ℝ => φ (-(x / (2 * Real.pi))) := by
  have := hφ.comp_mul_left' (show (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 by
    have := Real.pi_pos; exact neg_ne_zero.mpr (by positivity))
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only
  congr 1
  ring

theorem norm_dlmfFourier_sq (f : ℝ → ℂ) (x : ℝ) :
    ‖dlmfFourier f x‖ ^ 2 = (2 * Real.pi)⁻¹ * ‖𝓕 f (-(x / (2 * Real.pi)))‖ ^ 2 := by
  rw [dlmfFourier_eq_fourier, norm_mul, mul_pow, norm_inv, norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by positivity)]

/-- **DLMF (1.14.8)** (Parseval): for `f` absolutely and square integrable,
`∫ |𝓕(f)(x)|² dx = ∫ |f(t)|² dt`. -/
theorem dlmf_1_14_8 {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun x => ‖dlmfFourier f x‖ ^ 2) ∧
      ∫ x, ‖dlmfFourier f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  obtain ⟨hi, he⟩ := plancherel hf hf2
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simp_rw [norm_dlmfFourier_sq]
  refine ⟨(integrable_comp_dlmf hi).const_mul _, ?_⟩
  rw [integral_const_mul, integral_comp_dlmf (fun w => ‖𝓕 f w‖ ^ 2), smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hπ, one_mul, he]

theorem dlmfFourier_add_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c : ℂ)
    (x : ℝ) : dlmfFourier (fun t => f t + c * g t) x = dlmfFourier f x + c * dlmfFourier g x := by
  simp only [dlmfFourier]
  rw [show (fun t => (f t + c * g t) * cexp (I * x * t)) =
      fun t => f t * cexp (I * x * t) + c * (g t * cexp (I * x * t)) from
      funext fun t => by ring,
    integral_add (integrable_mul_exp hf x) ((integrable_mul_exp hg x).const_mul c),
    integral_const_mul]
  ring

theorem polar (a b : ℂ) : a * conj b =
    (((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 : ℝ) : ℂ) + I * ((‖a + I * b‖ ^ 2 - ‖a - I * b‖ ^ 2 : ℝ) : ℂ)) /
      4 := by
  simp only [Complex.sq_norm, normSq_apply]
  apply Complex.ext <;> simp <;> ring

/-- The polarization identity, integrated. -/
theorem integral_polar {a b : ℝ → ℂ} (h1 : Integrable fun x => ‖a x + b x‖ ^ 2)
    (h2 : Integrable fun x => ‖a x - b x‖ ^ 2) (h3 : Integrable fun x => ‖a x + I * b x‖ ^ 2)
    (h4 : Integrable fun x => ‖a x - I * b x‖ ^ 2) :
    ∫ x, a x * conj (b x) =
      (((∫ x, ‖a x + b x‖ ^ 2) - ∫ x, ‖a x - b x‖ ^ 2 : ℝ) +
        I * ((∫ x, ‖a x + I * b x‖ ^ 2) - ∫ x, ‖a x - I * b x‖ ^ 2 : ℝ)) / 4 := by
  simp_rw [polar]
  have hA : Integrable fun x => ((‖a x + b x‖ ^ 2 - ‖a x - b x‖ ^ 2 : ℝ) : ℂ) :=
    (h1.sub h2).ofReal
  have hB : Integrable fun x => I * ((‖a x + I * b x‖ ^ 2 - ‖a x - I * b x‖ ^ 2 : ℝ) : ℂ) :=
    ((h3.sub h4).ofReal).const_mul I
  rw [integral_div, integral_add hA hB, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_sub h1 h2, integral_sub h3 h4]

/-- **DLMF (1.14.7_5)** (Parseval): `∫ 𝓕(f) conj 𝓕(g) = ∫ f conj g` for absolutely and square
integrable `f`, `g`. -/
theorem dlmf_1_14_7_5 {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) (hg : Integrable g)
    (hg2 : MemLp g 2) :
    ∫ x, dlmfFourier f x * conj (dlmfFourier g x) = ∫ t, f t * conj (g t) := by
  have key : ∀ c : ℂ, Integrable (fun x => ‖dlmfFourier f x + c * dlmfFourier g x‖ ^ 2) ∧
      ∫ x, ‖dlmfFourier f x + c * dlmfFourier g x‖ ^ 2 = ∫ t, ‖f t + c * g t‖ ^ 2 := fun c => by
    have h := dlmf_1_14_8 (f := fun t => f t + c * g t) (hf.add (hg.const_mul c))
      (hf2.add (hg2.const_mul c))
    simp only [dlmfFourier_add_mul hf hg c] at h
    exact h
  have keyf : ∀ c : ℂ, Integrable (fun t => ‖f t + c * g t‖ ^ 2) := fun c =>
    ((hf2.add (hg2.const_mul c)).integrable_norm_pow (by norm_num))
  have e1 := key 1
  have e2 := key (-1)
  have e3 := key I
  have e4 := key (-I)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at e1 e2 e3 e4
  have k1 := keyf 1
  have k2 := keyf (-1)
  have k3 := keyf I
  have k4 := keyf (-I)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at k1 k2 k3 k4
  rw [integral_polar e1.1 e2.1 e3.1 e4.1, integral_polar k1 k2 k3 k4, e1.2, e2.2, e3.2, e4.2]

theorem dlmfFourier_conj_neg (g : ℝ → ℂ) (x : ℝ) :
    dlmfFourier (fun t => conj (g (-t))) x = conj (dlmfFourier g x) := by
  rw [dlmfFourier_eq_fourier, dlmfFourier_eq_fourier, fourier_conj_neg, map_mul, map_inv₀,
    conj_ofReal]

/-- **DLMF (1.14.7)**: `∫ 𝓕(f)(x) 𝓕(g)(x) dx = ∫ f(t) g(−t) dt`. -/
theorem dlmf_1_14_7 {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) (hg : Integrable g)
    (hg2 : MemLp g 2) :
    ∫ x, dlmfFourier f x * dlmfFourier g x = ∫ t, f t * g (-t) := by
  have := dlmf_1_14_7_5 hf hf2 (integrable_conj_neg hg) (memLp_conj_neg hg2)
  simp only [dlmfFourier_conj_neg, conj_conj] at this
  exact this

/-! ### Inversion and (1.14.6) -/

/-- Fourier inversion in DLMF's normalization: if `f` and `𝓕(f)` are integrable and `f` is
continuous at `t`, then `f(t) = (2π)^{−1/2} ∫ 𝓕(f)(x) e^{−ixt} dx`. -/
theorem dlmf_inversion {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    {t : ℝ} (hc : ContinuousAt f t) :
    f t = ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ * ∫ x, dlmfFourier f x * cexp (-(I * x * t)) := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hFeq : 𝓕 f = fun w => ((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier f (-(2 * Real.pi * w)) :=
    funext (fourier_eq_dlmfFourier f)
  have hFi : Integrable (𝓕 f) := by
    rw [hFeq]
    refine ((hF.comp_mul_left' (show (-(2 * Real.pi) : ℝ) ≠ 0 by
      exact neg_ne_zero.mpr hπ)).const_mul ((√(2 * Real.pi) : ℝ) : ℂ)).congr
      (ae_of_all _ fun w => ?_)
    simp only [neg_mul]
  have hinv := hf.fourierInv_fourier_eq hFi hc
  rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hFeq]
  have := Measure.integral_comp_mul_left
    (fun x : ℝ => cexp (-(I * x * t)) * (((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier f x))
    (-(2 * Real.pi))
  rw [abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
  have hs : ((√(2 * Real.pi) : ℝ) : ℂ) ^ 2 = 2 * Real.pi := by
    rw [← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  calc ∫ v : ℝ, cexp (↑(-2 * Real.pi * v * -t) * I) •
        (((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier f (-(2 * Real.pi * v)))
      = ∫ v : ℝ, cexp (-(I * ↑(-(2 * Real.pi) * v) * t)) *
          (((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier f (-(2 * Real.pi) * v)) := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only [smul_eq_mul, neg_mul]
        congr 2
        push_cast
        ring
    _ = _ := by
        rw [this, Complex.real_smul, ← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        have h0 : ((√(2 * Real.pi) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
        have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
        push_cast
        field_simp
        linear_combination (dlmfFourier f x) * hs

theorem integrable_dlmfFourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) :
    Integrable fun x => dlmfFourier f x * dlmfFourier g x := by
  refine Integrable.mono' (((dlmf_1_14_8 hf hf2).1.add (dlmf_1_14_8 hg hg2).1).div_const 2)
    ((dlmf_1_14_i_continuous hf).mul (dlmf_1_14_i_continuous hg)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [norm_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖dlmfFourier f x‖ - ‖dlmfFourier g x‖)]

theorem continuous_dlmfConv {f g : ℝ → ℂ} (hf2 : MemLp f 2) (hg2 : MemLp g 2) :
    Continuous (dlmfConv f g) := by
  have hg' : MemLp (fun r => g (-r)) 2 :=
    hg2.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  refine ((continuous_const (y := ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹)).mul
    (continuous_integral_mul_add hg' hf2)).congr fun t => ?_
  simp only [dlmfConv, Pi.mul_apply]
  congr 1
  have := integral_neg_eq_self (fun s => f (t - s) * g s) (volume : Measure ℝ)
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  simp only [sub_neg_eq_add]
  ring

/-- **DLMF (1.14.6)**: `(f ∗ g)(t) = (2π)^{−1/2} ∫ 𝓕(f)(x) 𝓕(g)(x) e^{−itx} dx` for absolutely
and square integrable `f`, `g`. -/
theorem dlmf_1_14_6 {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) (hg : Integrable g)
    (hg2 : MemLp g 2) (t : ℝ) :
    dlmfConv f g t = ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ *
      ∫ x, dlmfFourier f x * dlmfFourier g x * cexp (-(I * t * x)) := by
  have hφ := dlmf_1_14_5_integrable hf hg
  have hF : dlmfFourier (dlmfConv f g) = fun x => dlmfFourier f x * dlmfFourier g x :=
    funext (dlmf_1_14_5 hf hg)
  have hFi : Integrable (dlmfFourier (dlmfConv f g)) := by
    rw [hF]; exact integrable_dlmfFourier_mul hf hf2 hg hg2
  rw [dlmf_inversion hφ hFi (continuous_dlmfConv hf2 hg2).continuousAt, hF]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring_nf

end Azurite.DLMF
