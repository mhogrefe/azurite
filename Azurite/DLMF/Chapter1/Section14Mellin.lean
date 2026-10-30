/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14LaplaceInversion
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# DLMF §1.14(iv): Mellin transform

The Mellin transform 1.14.32 is Mathlib's `mellin`, and `MellinConvergent f s` says
`x^{s−1} f(x)` is integrable on `(0, ∞)`. Everything is reduced to §1.14(i) by `x = e^{−u}`
(`setIntegral_Ioi_zero_eq_exp`, `integrableOn_Ioi_zero_iff_exp`). This turns `𝓜f` into the
two-sided Laplace transform `∫ e^{−su} f(e^{−u}) du` (`mellin_eq_integral_exp`), and on
`ℜs = σ` into a Fourier transform of `mellinLine f σ = e^{−σu} f(e^{−u})`
(`mellin_eq_dlmfFourier`).

**Results.**
* Analyticity in the strip `a < ℜs < b` when `x^{σ−1} f(x)` is integrable for every
  `σ ∈ (a, b)` (`dlmf_1_14_iv_analytic`, `hasDerivAt_mellin`). This is proved by dominated
  differentiation, using `|u| e^{−ℜs·u} ≤ ε⁻¹ (e^{−(σ−2ε)u} + e^{−(σ+2ε)u})` (`abs_mul_exp_le`).
  Mathlib proves it only under `O`-bounds.
* 1.14.33 (`dlmf_1_14_33_atTop`, `dlmf_1_14_33_atBot`), Riemann–Lebesgue.
* The Note on `O(x^α)`, `O(x^β)` bounds (`dlmf_1_14_iv_note`, from Mathlib).
* 1.14.34 (`dlmf_1_14_34`, `dlmf_1_14_34'`): inversion at a point of bounded variation. This is
  1.14.3 for `mellinLine f σ` at `−ln u`; bounded variation transfers through the monotone map
  `e^{−v}` (`eVariationOn.comp_le_of_antitoneOn`) and products (`boundedVariationOn_mul`).
* 1.14.35 (`dlmf_1_14_35`, from Mathlib's `mellinInv_mellin_eq`).
* Fourier inversion almost everywhere for integrable `G` with integrable `𝓕G`
  (`fourierInv_fourier_ae`), and hence Mellin inversion almost everywhere
  (`mellinInv_mellin_ae`). Neither is in Mathlib. The proof tests against smooth compactly
  supported functions, using the multiplication formula twice (`integral_fourier_mul`), and
  carries null sets through `e^{−u}`.
* 1.14.36–1.14.38 (`dlmf_1_14_36`, `dlmf_1_14_37`, `dlmf_1_14_38`): Parseval-type formulas,
  under either of DLMF's integrability hypotheses, by Fubini and a.e. inversion.
  `mellin_conj_of_real` gives `𝓜f(s̄) = conj 𝓜f(s)` for real `f`.
* 1.14.39–1.14.40 (`mellinConv`, `dlmf_1_14_40`, `mellinConvergent_mellinConv`): the Mellin
  convolution becomes an additive convolution under `x = e^{−w}` (`mellinConv_exp`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped FourierTransform Real SchwartzMap ComplexConjugate Convolution

namespace Azurite.DLMF

/-! ### The substitution `x = e^{−u}` -/

theorem hasDerivWithinAt_exp_neg :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

theorem image_exp_neg : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

theorem injOn_exp_neg : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- `∫_0^∞ h(x) dx = ∫_ℝ h(e^{−u}) e^{−u} du`. -/
theorem setIntegral_Ioi_zero_eq_exp (h : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), h x = ∫ u : ℝ, (rexp (-u) : ℂ) * h (rexp (-u)) := by
  rw [← image_exp_neg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    hasDerivWithinAt_exp_neg injOn_exp_neg, Measure.restrict_univ]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp [abs_of_pos (Real.exp_pos _), Complex.real_smul]

theorem integrableOn_Ioi_zero_iff_exp (h : ℝ → ℂ) :
    IntegrableOn h (Ioi 0) ↔ Integrable fun u : ℝ => (rexp (-u) : ℂ) * h (rexp (-u)) := by
  rw [← image_exp_neg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    hasDerivWithinAt_exp_neg injOn_exp_neg, IntegrableOn, Measure.restrict_univ]
  refine integrable_congr (ae_of_all _ fun u => ?_)
  simp [abs_of_pos (Real.exp_pos _), Complex.real_smul]

theorem ofReal_exp_cpow (a : ℝ) (w : ℂ) : ((rexp a : ℝ) : ℂ) ^ w = cexp (a * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos a).ne'),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp]

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = cexp (Real.log x * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

theorem exp_neg_mul_cpow (u : ℝ) (s : ℂ) :
    (rexp (-u) : ℂ) * ((rexp (-u) : ℝ) : ℂ) ^ (s - 1) = cexp (-(s * u)) := by
  rw [ofReal_exp_cpow, ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Mellin transform as a two-sided Laplace transform: `𝓜f(s) = ∫ e^{−su} f(e^{−u}) du`. -/
theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, cexp (-(s * u)) * f (rexp (-u)) := by
  rw [mellin, setIntegral_Ioi_zero_eq_exp]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, exp_neg_mul_cpow]

theorem mellinConvergent_iff_exp (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable fun u : ℝ => cexp (-(s * u)) * f (rexp (-u)) := by
  rw [MellinConvergent, integrableOn_Ioi_zero_iff_exp]
  refine integrable_congr (ae_of_all _ fun u => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, exp_neg_mul_cpow]

/-- The function `g(u) = e^{−σu} f(e^{−u})` whose Fourier transform is `𝓜f` on `ℜs = σ`. -/
noncomputable def mellinLine (f : ℝ → ℂ) (σ : ℝ) (u : ℝ) : ℂ :=
  cexp (-((σ : ℂ) * u)) * f (rexp (-u))

theorem integrable_mellinLine {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ) :
    Integrable (mellinLine f σ) :=
  (mellinConvergent_iff_exp f σ).mp hf

/-- On the line `ℜs = σ`, `𝓜f(σ + iτ) = √(2π) 𝓕g(−τ)` with `g = mellinLine f σ`. -/
theorem mellin_eq_dlmfFourier (f : ℝ → ℂ) (σ τ : ℝ) :
    mellin f (σ + τ * I) = ((√(2 * π) : ℝ) : ℂ) * dlmfFourier (mellinLine f σ) (-τ) := by
  rw [dlmfFourier, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast sqrt_two_pi_ne_zero), one_mul,
    mellin_eq_integral_exp]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [mellinLine]
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### Convergence and decay (1.14.33) -/

/-- Convergence of `𝓜f(s)` depends only on `ℜs`. -/
theorem mellinConvergent_of_re {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s.re) :
    MellinConvergent f s := by
  rw [mellinConvergent_iff_exp] at hf ⊢
  have hm : AEStronglyMeasurable (fun u : ℝ => cexp (-(s * u)) * f (rexp (-u))) := by
    have := ((by fun_prop : Continuous fun u : ℝ => cexp (-((s.im * I) * u))).aestronglyMeasurable
      ).mul hf.aestronglyMeasurable
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    conv_rhs => rw [← re_add_im s]
    ring
  refine hf.mono hm (ae_of_all _ fun u => ?_)
  simp [Complex.norm_exp]

/-- **DLMF 1.14.33**: `𝓜f(σ + it) → 0` as `t → +∞` (Riemann–Lebesgue). With Bochner integrals
this needs no hypothesis: if `x^{σ−1} f(x)` is not integrable, `𝓜f(σ + it) = 0`. -/
theorem dlmf_1_14_33_atTop (f : ℝ → ℂ) (σ : ℝ) :
    Tendsto (fun t : ℝ => mellin f (σ + t * I)) atTop (𝓝 0) := by
  have := (dlmf_1_14_i_tendsto_atBot (mellinLine f σ)).comp tendsto_neg_atTop_atBot
  simpa [mellin_eq_dlmfFourier, Function.comp_def] using this.const_mul ((√(2 * π) : ℝ) : ℂ)

/-- **DLMF 1.14.33**: `𝓜f(σ + it) → 0` as `t → −∞`. -/
theorem dlmf_1_14_33_atBot (f : ℝ → ℂ) (σ : ℝ) :
    Tendsto (fun t : ℝ => mellin f (σ + t * I)) atBot (𝓝 0) := by
  have := (dlmf_1_14_i_tendsto_atTop (mellinLine f σ)).comp tendsto_neg_atBot_atTop
  simpa [mellin_eq_dlmfFourier, Function.comp_def] using this.const_mul ((√(2 * π) : ℝ) : ℂ)

/-- **DLMF §1.14(iv), Note**: if `f` is continuous on `(0, ∞)`, `f(x) = O(x^α)` as `x → 0+` and
`f(x) = O(x^β)` as `x → ∞`, then `x^{σ−1} f(x)` is integrable on `(0, ∞)` for
`σ ∈ (−α, −β)`. -/
theorem dlmf_1_14_iv_note {f : ℝ → ℂ} (hc : ContinuousOn f (Ioi 0)) {α β : ℝ}
    (h0 : f =O[𝓝[>] 0] (· ^ α)) (hinf : f =O[atTop] (· ^ β)) {σ : ℝ}
    (hσ : σ ∈ Ioo (-α) (-β)) : MellinConvergent f σ :=
  mellinConvergent_of_isBigO_rpow (a := -β) (b := -α)
    (hc.locallyIntegrableOn measurableSet_Ioi) (by simpa using hinf) (by simpa using hσ.2)
    (by simpa using h0) (by simpa using hσ.1)

/-! ### Analyticity in a strip -/

theorem abs_mul_exp_le {σ₀ ε r : ℝ} (hε : 0 < ε) (hr : |r - σ₀| < ε) (u : ℝ) :
    |u| * rexp (-(r * u)) ≤
      ε⁻¹ * (rexp (-((σ₀ - 2 * ε) * u)) + rexp (-((σ₀ + 2 * ε) * u))) := by
  have h1 : -(r * u) ≤ -(σ₀ * u) + ε * |u| := by
    have h := neg_abs_le ((r - σ₀) * u)
    rw [abs_mul] at h
    nlinarith [abs_nonneg u, mul_le_mul_of_nonneg_right hr.le (abs_nonneg u)]
  have h2 : |u| ≤ ε⁻¹ * rexp (ε * |u|) := by
    rw [le_inv_mul_iff₀ hε]; linarith [Real.add_one_le_exp (ε * |u|)]
  have h3 : |u| * rexp (-(r * u)) ≤ ε⁻¹ * rexp (-(σ₀ * u) + 2 * ε * |u|) := by
    calc |u| * rexp (-(r * u)) ≤ (ε⁻¹ * rexp (ε * |u|)) * rexp (-(σ₀ * u) + ε * |u|) :=
          mul_le_mul h2 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
      _ = ε⁻¹ * rexp (-(σ₀ * u) + 2 * ε * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  refine h3.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hε.le))
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have : -(σ₀ * u) + 2 * ε * u = -((σ₀ - 2 * ε) * u) := by ring
    rw [this]; linarith [Real.exp_pos (-((σ₀ + 2 * ε) * u))]
  · rw [abs_of_neg hu]
    have : -(σ₀ * u) + 2 * ε * -u = -((σ₀ + 2 * ε) * u) := by ring
    rw [this]; linarith [Real.exp_pos (-((σ₀ - 2 * ε) * u))]

/-- `𝓜f′(s) = −∫ u e^{−su} f(e^{−u}) du`, i.e. `𝓜f′(s) = 𝓜(f log)(s)`, inside the strip. -/
theorem hasDerivAt_mellin {f : ℝ → ℂ} {a b : ℝ} (hf : ∀ σ ∈ Ioo a b, MellinConvergent f σ)
    {s₀ : ℂ} (hs : s₀.re ∈ Ioo a b) :
    HasDerivAt (mellin f) (-∫ u : ℝ, (u : ℂ) * (cexp (-(s₀ * u)) * f (rexp (-u)))) s₀ := by
  obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε > 0, a < s₀.re - 2 * ε ∧ s₀.re + 2 * ε < b := by
    refine ⟨min (s₀.re - a) (b - s₀.re) / 4,
      div_pos (lt_min (by linarith [hs.1]) (by linarith [hs.2])) (by norm_num), ?_, ?_⟩
    · have := min_le_left (s₀.re - a) (b - s₀.re); linarith [hs.1]
    · have := min_le_right (s₀.re - a) (b - s₀.re); linarith [hs.2]
  have hF : ∀ s : ℂ, s.re ∈ Ioo a b →
      Integrable fun u : ℝ => cexp (-(s * u)) * f (rexp (-u)) := fun s hs' =>
    (mellinConvergent_iff_exp f s).mp (mellinConvergent_of_re (hf _ hs'))
  have hlo := hF ((s₀.re - 2 * ε : ℝ) : ℂ) (by simp only [ofReal_re]; constructor <;> linarith)
  have hhi := hF ((s₀.re + 2 * ε : ℝ) : ℂ) (by simp only [ofReal_re]; constructor <;> linarith)
  have hre : ∀ s ∈ Metric.ball s₀ ε, |s.re - s₀.re| < ε := fun s hs' => by
    rw [Metric.mem_ball, dist_eq_norm] at hs'
    have := (Complex.abs_re_le_norm (s - s₀)).trans_lt hs'
    rwa [sub_re] at this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s (u : ℝ) => cexp (-(s * u)) * f (rexp (-u)))
    (F' := fun s (u : ℝ) => -((u : ℂ) * (cexp (-(s * u)) * f (rexp (-u)))))
    (bound := fun u : ℝ => ε⁻¹ * (‖cexp (-(((s₀.re - 2 * ε : ℝ) : ℂ) * u)) * f (rexp (-u))‖ +
      ‖cexp (-(((s₀.re + 2 * ε : ℝ) : ℂ) * u)) * f (rexp (-u))‖)) (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hε)
    (by
      filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs'
      have := abs_lt.mp (hre s hs')
      exact (hF s ⟨by linarith, by linarith⟩).aestronglyMeasurable)
    (hF s₀ hs)
    (((by fun_prop : Continuous fun u : ℝ => (u : ℂ)).aestronglyMeasurable).mul
      (hF s₀ hs).aestronglyMeasurable).neg
    (ae_of_all _ fun (u : ℝ) s hs' => by
      simp only [norm_neg, norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        ofReal_re]
      have := abs_mul_exp_le hε (hre s hs') u
      calc |u| * (rexp (-(s.re * u)) * ‖f (rexp (-u))‖)
          = (|u| * rexp (-(s.re * u))) * ‖f (rexp (-u))‖ := by ring
        _ ≤ (ε⁻¹ * (rexp (-((s₀.re - 2 * ε) * u)) + rexp (-((s₀.re + 2 * ε) * u)))) *
            ‖f (rexp (-u))‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := by ring)
    ((hlo.norm.add hhi.norm).const_mul ε⁻¹)
    (ae_of_all _ fun (u : ℝ) s _ => by
      have h1 : HasDerivAt (fun s : ℂ => -(s * u)) (-(u : ℂ)) s := by
        have := ((hasDerivAt_id s).mul_const (u : ℂ)).neg
        exact this.congr_deriv (by simp)
      exact (h1.cexp.mul_const (f (rexp (-u)))).congr_deriv (by ring))
  have h2 := key.2
  rw [integral_neg] at h2
  have hfun : (fun s : ℂ => ∫ u : ℝ, cexp (-(s * u)) * f (rexp (-u))) = mellin f :=
    funext fun s => (mellin_eq_integral_exp f s).symm
  rwa [hfun] at h2

/-- **DLMF §1.14(iv)**: if `x^{σ−1} f(x)` is integrable on `(0, ∞)` for all `σ ∈ (a, b)`, then
1.14.32 converges in the strip `a < ℜs < b`, where `𝓜f` is analytic. -/
theorem dlmf_1_14_iv_analytic {f : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ σ ∈ Ioo a b, MellinConvergent f σ) :
    (∀ s : ℂ, s.re ∈ Ioo a b → MellinConvergent f s) ∧
      AnalyticOnNhd ℂ (mellin f) {s | s.re ∈ Ioo a b} :=
  ⟨fun _ hs => mellinConvergent_of_re (hf _ hs),
    DifferentiableOn.analyticOnNhd
      (fun _ hs => (hasDerivAt_mellin hf hs).differentiableAt.differentiableWithinAt)
      (isOpen_Ioo.preimage continuous_re)⟩

/-! ### Fourier inversion almost everywhere -/

/-- The multiplication formula `∫ 𝓕F · G = ∫ F · 𝓕G` for integrable `F`, `G`. -/
theorem integral_fourier_mul {F G : ℝ → ℂ} (hF : Integrable F) (hG : Integrable G) :
    ∫ ξ, 𝓕 F ξ * G ξ = ∫ x, F x * 𝓕 G x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume)
    (ν := volume) Real.continuous_fourierChar continuous_inner hF hG
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hflip] at this
  exact this

theorem continuous_fourierInv {F : ℝ → ℂ} (hF : Integrable F) : Continuous (𝓕⁻ F) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hF.comp_neg

/-- Fourier inversion almost everywhere: if `G` and `𝓕G` are integrable, `𝓕⁻(𝓕G) = G` a.e.
(Mathlib has it at continuity points.) Tested against smooth compactly supported functions,
by the multiplication formula twice. -/
theorem fourierInv_fourier_ae {G : ℝ → ℂ} (hG : Integrable G) (hF : Integrable (𝓕 G)) :
    ∀ᵐ x, 𝓕⁻ (𝓕 G) x = G x := by
  have hc : Continuous (𝓕⁻ (𝓕 G)) := continuous_fourierInv hF
  have hloc : LocallyIntegrable (fun x => 𝓕⁻ (𝓕 G) x - G x) volume :=
    hc.locallyIntegrable.sub hG.locallyIntegrable
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψc => ?_
  · filter_upwards [this] with x hx using sub_eq_zero.mp hx
  set S : 𝓢(ℝ, ℂ) := (hψc.comp_left (g := ofRealCLM) rfl).toSchwartzMap
    (ofRealCLM.contDiff.comp hψ) with hS
  set s : ℝ → ℂ := fun x => (ψ x : ℂ) with hs
  have hSs : (S : ℝ → ℂ) = s := by ext; simp [S, s]
  have hsi : Integrable s := hSs ▸ S.integrable
  have hsc : Continuous s := hSs ▸ S.continuous
  have hsF : Integrable (𝓕 s) := by
    rw [← hSs, ← SchwartzMap.fourier_coe]; exact (𝓕 S).integrable
  have hsI : Integrable (𝓕⁻ s) := by
    rw [← hSs, ← SchwartzMap.fourierInv_coe]; exact (𝓕⁻ S).integrable
  have hFFs : 𝓕 (𝓕⁻ s) = s := hsc.fourier_fourierInv_eq hsi hsF
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hcs : HasCompactSupport s := hψc.comp_left (g := ofRealCLM) rfl
  have h1 : Integrable fun x => s x * 𝓕⁻ (𝓕 G) x :=
    (hsc.mul hc).integrable_of_hasCompactSupport hcs.mul_right
  have h2 : Integrable fun x => s x * G x :=
    hG.bdd_mul hsc.aestronglyMeasurable (ae_of_all _ fun x => by simpa [s] using hC x)
  have key : ∫ x, s x * 𝓕⁻ (𝓕 G) x = ∫ x, s x * G x := by
    calc ∫ x, s x * 𝓕⁻ (𝓕 G) x = ∫ x, s (-x) * 𝓕 (𝓕 G) x := by
          rw [← integral_neg_eq_self (fun x => s x * 𝓕⁻ (𝓕 G) x) volume]
          simp_rw [Real.fourierInv_eq_fourier_neg, neg_neg]
      _ = ∫ x, 𝓕 (𝓕 G) x * (fun y => s (-y)) x := by simp_rw [mul_comm (s _)]
      _ = ∫ ξ, 𝓕 G ξ * 𝓕 (fun y => s (-y)) ξ := integral_fourier_mul hF hsi.comp_neg
      _ = ∫ ξ, 𝓕 G ξ * 𝓕⁻ s ξ := by rw [Real.fourierInv_eq_fourier_comp_neg]
      _ = ∫ x, G x * 𝓕 (𝓕⁻ s) x := integral_fourier_mul hG hsI
      _ = ∫ x, s x * G x := by rw [hFFs]; simp_rw [mul_comm (G _)]
  simp only [real_smul]
  rw [show (fun x => (ψ x : ℂ) * (𝓕⁻ (𝓕 G) x - G x)) =
    fun x => s x * 𝓕⁻ (𝓕 G) x - s x * G x from funext fun x => by simp [s]; ring,
    integral_sub h1 h2, key, sub_self]

/-! ### Inversion (1.14.35) -/

/-- **DLMF 1.14.35**: if `𝓜f` is integrable on the line `ℜs = σ` and `f` is continuous at
`x > 0`, then `f(x) = (1/2πi) ∫_{σ−i∞}^{σ+i∞} x^{−s} 𝓜f(s) ds`, written with `s = σ + it`. -/
theorem dlmf_1_14_35 {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ)
    (hF : VerticalIntegrable (mellin f) σ) {x : ℝ} (hx : 0 < x) (hc : ContinuousAt f x) :
    f x = (2 * π : ℂ)⁻¹ * ∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (σ + t * I) := by
  rw [← mellinInv_mellin_eq σ f hx hf hF hc, mellinInv]
  simp [smul_eq_mul]

/-- Mellin inversion almost everywhere: if `x^{σ−1} f(x)` is integrable on `(0, ∞)` and `𝓜f` is
integrable on `ℜs = σ`, the inverse transform recovers `f` at almost every `x > 0`. -/
theorem mellinInv_mellin_ae {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) :
    ∀ᵐ x ∂(volume.restrict (Ioi 0)), mellinInv σ (mellin f) x = f x := by
  let g := fun (u : ℝ) => Real.exp (-σ * u) • f (Real.exp (-u))
  replace hf : Integrable g := by
    refine (integrable_mellinLine hf).congr (ae_of_all _ fun u => ?_)
    simp only [mellinLine, g, Complex.real_smul, ofReal_exp]
    push_cast
    ring_nf
  replace hFf : Integrable (𝓕 g) := by
    have h2π : 2 * π ≠ 0 := by simp [Real.pi_ne_zero]
    have : Integrable (𝓕 (fun u ↦ rexp (-(σ * u)) • f (rexp (-u)))) := by
      simpa [mellin_eq_fourier, mul_div_cancel_right₀ _ h2π] using hFf.comp_mul_right' h2π
    simp_rw [neg_mul_eq_neg_mul] at this
    exact this
  have hpt : ∀ x : ℝ, 0 < x → 𝓕⁻ (𝓕 g) (-Real.log x) = g (-Real.log x) →
      mellinInv σ (mellin f) x = f x := fun x hx heq => by
    calc
      mellinInv σ (mellin f) x
        = mellinInv σ (fun s ↦ 𝓕 g (s.im / (2 * π))) x := by
        simp [g, mellinInv, mellin_eq_fourier]
      _ = (x : ℂ) ^ (-σ : ℂ) • g (-Real.log x) := by
        rw [mellinInv_eq_fourierInv _ _ hx, ← heq]
        simp [mul_div_cancel_left₀ _ (show 2 * π ≠ 0 by simp [Real.pi_ne_zero])]
      _ = (x : ℂ) ^ (-σ : ℂ) • rexp (σ * Real.log x) • f (rexp (Real.log x)) := by simp [g]
      _ = f x := by
        norm_cast
        rw [mul_comm σ, ← Real.rpow_def_of_pos hx, Real.exp_log hx, ← Complex.ofReal_cpow hx.le]
        norm_cast
        rw [← smul_assoc, smul_eq_mul, Real.rpow_neg hx.le,
          inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hx σ)), one_smul]
  have hN := fourierInv_fourier_ae hf hFf
  rw [ae_iff] at hN
  rw [ae_restrict_iff' measurableSet_Ioi, ae_iff]
  have hd : DifferentiableOn ℝ (rexp ∘ Neg.neg) {a | ¬𝓕⁻ (𝓕 g) a = g a} :=
    (Real.differentiable_exp.comp differentiable_neg).differentiableOn
  refine measure_mono_null (fun x hx => ?_)
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd hN)
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hx
  refine ⟨-Real.log x, fun h => hx.2 (hpt x hx.1 h), ?_⟩
  simp [Real.exp_log hx.1]

/-! ### Inversion for functions of bounded variation (1.14.34) -/

/-- **DLMF 1.14.34**: if 1.14.32 converges absolutely on `ℜs = σ` and `f` has bounded variation
near `u > 0`, then `½(f(u+) + f(u−)) = (1/2πi) lim_{T→∞} ∫_{σ−iT}^{σ+iT} u^{−s} 𝓜f(s) ds`. The
contour integral is written with `s = σ + it`, `ds = i dt`. The proof applies 1.14.3 to
`g(v) = e^{−σv} f(e^{−v})` at `v = −ln u`; `g` has bounded variation there because `e^{−v}` is
monotone and products of functions of bounded variation are. -/
theorem dlmf_1_14_34 {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ) {u δ : ℝ} (hu : 0 < u)
    (hδ : 0 < δ) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] u) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] u) (𝓝 Lm)) :
    Tendsto (fun T : ℝ => (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (u : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (σ + t * I))
      atTop (𝓝 ((Lp + Lm) / 2)) := by
  set g := mellinLine f σ with hg
  set w := Real.log u with hw
  set v₀ := -w with hv₀
  set δ' := Real.log (1 + δ / u) with hδ'
  have hδu : 0 < δ / u := div_pos hδ hu
  have hδ'pos : 0 < δ' := Real.log_pos (by linarith)
  have hexp : rexp δ' = 1 + δ / u := Real.exp_log (by linarith)
  have hu' : rexp w = u := Real.exp_log hu
  have hmaps : MapsTo (fun v : ℝ => rexp (-v)) (Icc (v₀ - δ') (v₀ + δ'))
      (Icc (u - δ) (u + δ)) := by
    intro v hv
    constructor
    · have h1 : rexp (-(v₀ + δ')) ≤ rexp (-v) := Real.exp_le_exp.mpr (by linarith [hv.2])
      have h2 : rexp (-(v₀ + δ')) = u / (1 + δ / u) := by
        rw [show -(v₀ + δ') = w - δ' by ring, Real.exp_sub, hu', hexp]
      have h3 : u - δ ≤ u / (1 + δ / u) := by
        rw [le_div_iff₀ (by linarith)]
        have : (u - δ) * (1 + δ / u) = u - δ ^ 2 / u := by field_simp; ring
        have : 0 ≤ δ ^ 2 / u := by positivity
        linarith
      linarith
    · have h1 : rexp (-v) ≤ rexp (-(v₀ - δ')) := Real.exp_le_exp.mpr (by linarith [hv.1])
      have h2 : rexp (-(v₀ - δ')) = u + δ := by
        rw [show -(v₀ - δ') = w + δ' by ring, Real.exp_add, hu', hexp]; field_simp
      linarith
  have hanti : AntitoneOn (fun v : ℝ => rexp (-v)) (Icc (v₀ - δ') (v₀ + δ')) :=
    fun a _ b _ hab => Real.exp_le_exp.mpr (neg_le_neg hab)
  have hcomp : BoundedVariationOn (fun v => f (rexp (-v))) (Icc (v₀ - δ') (v₀ + δ')) :=
    ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_antitoneOn f _ hanti hmaps)
  have hcx := boundedVariationOn_cexp σ (v₀ - δ') (v₀ + δ')
  have hmem : v₀ ∈ Icc (v₀ - δ') (v₀ + δ') := ⟨by linarith, by linarith⟩
  have hbvg : BoundedVariationOn g (Icc (v₀ - δ') (v₀ + δ')) :=
    boundedVariationOn_mul hcx hcomp (bv_norm_le_of_mem hcx hmem) (bv_norm_le_of_mem hcomp hmem)
  have hv₀u : rexp (-v₀) = u := by rw [hv₀, neg_neg, hu']
  have hcont : Continuous fun v : ℝ => cexp (-((σ : ℂ) * v)) := by fun_prop
  have hgt : Tendsto (fun v : ℝ => rexp (-v)) (𝓝[>] v₀) (𝓝[<] u) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Real.continuous_exp.comp continuous_neg).tendsto v₀
      simp only [Function.comp_def, hv₀u] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      rw [← hv₀u]; exact Real.exp_lt_exp.mpr (neg_lt_neg hv)
  have hlt : Tendsto (fun v : ℝ => rexp (-v)) (𝓝[<] v₀) (𝓝[>] u) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Real.continuous_exp.comp continuous_neg).tendsto v₀
      simp only [Function.comp_def, hv₀u] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      rw [← hv₀u]; exact Real.exp_lt_exp.mpr (neg_lt_neg hv)
  set K := cexp (-((σ : ℂ) * v₀)) with hK
  have hp' : Tendsto g (𝓝[>] v₀) (𝓝 (K * Lm)) :=
    ((hcont.tendsto v₀).mono_left nhdsWithin_le_nhds).mul (hm.comp hgt)
  have hm' : Tendsto g (𝓝[<] v₀) (𝓝 (K * Lp)) :=
    ((hcont.tendsto v₀).mono_left nhdsWithin_le_nhds).mul (hp.comp hlt)
  have h3 := dlmf_1_14_3 (integrable_mellinLine hf) hδ'pos hbvg hp' hm'
  set c : ℂ := ((√(2 * π) : ℝ) : ℂ) with hcdef
  set k := cexp (-((σ : ℂ) * w)) with hk
  have hc : c * c = 2 * π := by
    rw [hcdef, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hc0 : c ≠ 0 := by
    rw [hcdef]; exact_mod_cast sqrt_two_pi_ne_zero
  have h2π : (2 * π : ℂ)⁻¹ * c = c⁻¹ := by
    rw [← hc]; field_simp
  have hfun : ∀ T : ℝ, (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (u : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (σ + t * I) =
      k * (c⁻¹ * ∫ x in (-T)..T, dlmfFourier g x * cexp (-(I * x * v₀))) := fun T => by
    have h1 : ∫ t in (-T)..T, (u : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (σ + t * I) =
        ∫ x in (-T)..T, (u : ℂ) ^ (-((σ : ℂ) + ((-x : ℝ) : ℂ) * I)) *
          mellin f (σ + ((-x : ℝ) : ℂ) * I) := by
      rw [intervalIntegral.integral_comp_neg
        (fun t : ℝ => (u : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (σ + t * I)), neg_neg]
    have h2 : ∫ x in (-T)..T, (u : ℂ) ^ (-((σ : ℂ) + ((-x : ℝ) : ℂ) * I)) *
          mellin f (σ + ((-x : ℝ) : ℂ) * I) =
        (k * c) * ∫ x in (-T)..T, dlmfFourier g x * cexp (-(I * x * v₀)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [ofReal_cpow_eq_exp hu, mellin_eq_dlmfFourier, neg_neg]
      have : cexp (Real.log u * -((σ : ℂ) + ((-x : ℝ) : ℂ) * I)) =
          k * cexp (-(I * x * v₀)) := by
        rw [hk, ← Complex.exp_add]; congr 1; simp only [hv₀, hw, ofReal_neg]; ring
      rw [this]; ring
    rw [h1, h2, ← mul_assoc, ← mul_assoc, mul_comm _ k, mul_assoc k, h2π, mul_assoc]
  have hkK : k * K = 1 := by
    rw [hk, hK, ← Complex.exp_add, hv₀]; push_cast; ring_nf; exact Complex.exp_zero
  have h4 := h3.const_mul k
  rw [show k * ((K * Lm + K * Lp) / 2) = (Lp + Lm) / 2 by
    linear_combination (Lm + Lp) / 2 * hkK] at h4
  exact h4.congr fun T => (hfun T).symm

/-- **DLMF 1.14.34** with the one-sided limits `f(u±)` supplied by bounded variation. -/
theorem dlmf_1_14_34' {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ) {u δ : ℝ} (hu : 0 < u)
    (hδ : 0 < δ) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) :
    ∃ Lp Lm, Tendsto f (𝓝[>] u) (𝓝 Lp) ∧ Tendsto f (𝓝[<] u) (𝓝 Lm) ∧
      Tendsto (fun T : ℝ => (2 * π : ℂ)⁻¹ *
        ∫ t in (-T)..T, (u : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (σ + t * I))
        atTop (𝓝 ((Lp + Lm) / 2)) := by
  obtain ⟨⟨Lp, hp⟩, ⟨Lm, hm⟩⟩ := exists_tendsto_of_bv (a := u - δ) (u := u) (b := u + δ)
    (by linarith) (by linarith) hbv
  exact ⟨Lp, Lm, hp, hm, dlmf_1_14_34 hf hu hδ hbv hp hm⟩

/-! ### Parseval-type formulas (1.14.36–1.14.38) -/

/-- Mellin inversion almost everywhere, transported by `x ↦ xy`. -/
theorem mellinInv_mellin_ae_mul {g : ℝ → ℂ} {σ : ℝ} (hg : MellinConvergent g σ)
    (hG : VerticalIntegrable (mellin g) σ) {y : ℝ} (hy : 0 < y) :
    ∀ᵐ x ∂(volume.restrict (Ioi 0)), mellinInv σ (mellin g) (x * y) = g (x * y) := by
  have h := mellinInv_mellin_ae hg hG
  rw [ae_restrict_iff' measurableSet_Ioi, ae_iff] at h ⊢
  have h2 := Real.volume_preimage_mul_right hy.ne'
    {a | ¬(a ∈ Ioi 0 → mellinInv σ (mellin g) a = g a)}
  rw [h, mul_zero] at h2
  refine measure_mono_null (fun x hx => ?_) h2
  simp only [Set.mem_ofPred_eq, Classical.not_imp, mem_Ioi, mem_preimage] at hx ⊢
  exact ⟨mul_pos hx.1 hy, hx.2⟩

/-- 1.14.36 when `𝓜g` is integrable on `ℜs = σ`. -/
theorem dlmf_1_14_36_of_right {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (1 - σ))
    (hg : MellinConvergent g σ) (hG : VerticalIntegrable (mellin g) σ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ioi (0 : ℝ), f x * g (y * x) = (2 * π : ℂ)⁻¹ * ∫ t : ℝ,
      (y : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (1 - (σ + t * I)) * mellin g (σ + t * I) := by
  set P : ℝ → ℂ := fun t => (y : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin g (σ + t * I) with hP
  set R : ℝ → ℂ := fun x => (x : ℂ) ^ (-(σ : ℂ)) * f x with hR
  set Q : ℝ → ℝ → ℂ := fun t x => (x : ℂ) ^ (-((t : ℂ) * I)) with hQ
  set F : ℝ → ℝ → ℂ := fun t x => P t * (Q t x * R x) with hF
  have hPi : Integrable P := by
    refine hG.bdd_mul (c := y ^ (-σ)) ((Continuous.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable) (ae_of_all _ fun t => ?_)
    rw [norm_cpow_eq_rpow_re_of_pos hy]; simp
  have hRi : IntegrableOn R (Ioi 0) := by
    refine hf.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hR, smul_eq_mul]; congr 2; ring
  have hQn : ∀ t x : ℝ, 0 < x → ‖Q t x‖ = 1 := fun t x hx => by
    simp only [hQ]; rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hQm : Measurable (Function.uncurry Q) := by
    change Measurable fun p : ℝ × ℝ => ((p.2 : ℂ)) ^ (-((p.1 : ℂ) * I))
    exact (Complex.measurable_ofReal.comp measurable_snd).pow
      ((Complex.measurable_ofReal.comp measurable_fst).mul_const I).neg
  have hFi : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (hPi.norm.mul_prod hRi.norm).mono'
      (hPi.aestronglyMeasurable.comp_fst.mul
        (hQm.aestronglyMeasurable.mul hRi.aestronglyMeasurable.comp_snd)) ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
      with z hz
    change ‖P z.1 * (Q z.1 z.2 * R z.2)‖ ≤ ‖P z.1‖ * ‖R z.2‖
    rw [norm_mul (P z.1), norm_mul (Q z.1 z.2), hQn _ _ hz, one_mul]
  have hswap := integral_integral_swap hFi
  have hL : ∀ t : ℝ, ∫ x in Ioi (0 : ℝ), F t x = P t * mellin f (1 - (σ + t * I)) := fun t => by
    simp only [hF]
    rw [integral_const_mul, mellin]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    simp only [hQ, hR, smul_eq_mul]
    rw [← mul_assoc, ← cpow_add _ _ hx0]
    congr 2; ring
  have hRt : ∀ x : ℝ, 0 < x → mellinInv σ (mellin g) (x * y) = g (x * y) →
      (2 * π : ℂ)⁻¹ * ∫ t, F t x = f x * g (y * x) := fun x hx hinv => by
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    have : ∀ t : ℝ, F t x =
        ((x * y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin g (σ + t * I) * f x := fun t => by
      simp only [hF, hP, hQ, hR]
      rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le hy.le, neg_add, cpow_add _ _ hx0]
      ring
    simp_rw [this]
    rw [integral_mul_const, mul_comm y x, ← hinv, mellinInv]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  calc ∫ x in Ioi (0 : ℝ), f x * g (y * x)
      = ∫ x in Ioi (0 : ℝ), (2 * π : ℂ)⁻¹ * ∫ t, F t x := by
        refine integral_congr_ae ?_
        filter_upwards [mellinInv_mellin_ae_mul hg hG hy, ae_restrict_mem measurableSet_Ioi]
          with x hinv hx
        exact (hRt x hx hinv).symm
    _ = (2 * π : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), ∫ t, F t x := integral_const_mul _ _
    _ = (2 * π : ℂ)⁻¹ * ∫ t, ∫ x in Ioi (0 : ℝ), F t x := by rw [hswap]
    _ = _ := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [hL, hP]
        ring

/-- **DLMF 1.14.36**: if `x^{−σ} f(x)` and `x^{σ−1} g(x)` are integrable on `(0, ∞)` and either
`𝓜g(σ + it)` or `𝓜f(1 − σ − it)` is integrable, then for `y > 0`
`∫_0^∞ f(x) g(yx) dx = (1/2πi) ∫_{σ−i∞}^{σ+i∞} y^{−s} 𝓜f(1 − s) 𝓜g(s) ds` (with `s = σ + it`).
The proof uses Fubini and Mellin inversion almost everywhere (`mellinInv_mellin_ae`). The
second case follows from the first with `f` and `g` exchanged, by `x ↦ x / y`. -/
theorem dlmf_1_14_36 {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (1 - σ))
    (hg : MellinConvergent g σ)
    (hint : VerticalIntegrable (mellin g) σ ∨ Integrable fun t : ℝ => mellin f (1 - σ - t * I))
    {y : ℝ} (hy : 0 < y) :
    ∫ x in Ioi (0 : ℝ), f x * g (y * x) = (2 * π : ℂ)⁻¹ * ∫ t : ℝ,
      (y : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin f (1 - (σ + t * I)) * mellin g (σ + t * I) := by
  rcases hint with hG | hB
  · exact dlmf_1_14_36_of_right hf hg hG hy
  have hg' : MellinConvergent g (1 - ((1 - σ : ℝ) : ℂ)) := by
    convert hg using 2; push_cast; ring
  have hf' : MellinConvergent f ((1 - σ : ℝ) : ℂ) := by
    convert hf using 2; push_cast; ring
  have hB' : VerticalIntegrable (mellin f) (1 - σ) := by
    refine hB.comp_neg.congr (ae_of_all _ fun t => ?_)
    simp only
    congr 1; push_cast; ring
  have key := dlmf_1_14_36_of_right hg' hf' hB' (inv_pos.mpr hy)
  have hL : ∫ x in Ioi (0 : ℝ), f x * g (y * x) =
      (y⁻¹ : ℂ) * ∫ z in Ioi (0 : ℝ), g z * f (y⁻¹ * z) := by
    have := integral_comp_mul_left_Ioi (fun z => g z * f (y⁻¹ * z)) 0 hy
    simp only [mul_zero, inv_mul_cancel_left₀ hy.ne', Complex.real_smul] at this
    rw [show (fun x => f x * g (y * x)) = fun x => g (y * x) * f x from
      funext fun _ => mul_comm _ _, this]
    push_cast; rfl
  rw [hL, key, ← mul_assoc, mul_comm (y⁻¹ : ℂ), mul_assoc, ← integral_const_mul,
    ← integral_neg_eq_self _ (volume : Measure ℝ)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hyi : ((y⁻¹ : ℝ) : ℂ) = cexp (-(Real.log y : ℂ)) := by
    rw [← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log hy]
  simp only
  rw [ofReal_cpow_eq_exp (inv_pos.mpr hy), ofReal_cpow_eq_exp hy, Real.log_inv,
    show ((y : ℂ))⁻¹ = ((y⁻¹ : ℝ) : ℂ) by push_cast; rfl, hyi]
  have e1 : mellin g (1 - (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) = mellin g (σ + t * I) := by
    congr 1; push_cast; ring
  have e2 : mellin f (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = mellin f (1 - (σ + t * I)) := by
    congr 1; push_cast; ring
  rw [e1, e2]
  have e3 : cexp (-(Real.log y : ℂ)) *
      cexp (((-Real.log y : ℝ) : ℂ) * -(((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) =
      cexp ((Real.log y : ℂ) * -((σ : ℂ) + t * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e3]; ring

/-- **DLMF 1.14.37**: the case `y = 1` of 1.14.36. -/
theorem dlmf_1_14_37 {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (1 - σ))
    (hg : MellinConvergent g σ)
    (hint : VerticalIntegrable (mellin g) σ ∨ Integrable fun t : ℝ => mellin f (1 - σ - t * I)) :
    ∫ x in Ioi (0 : ℝ), f x * g x = (2 * π : ℂ)⁻¹ * ∫ t : ℝ,
      mellin f (1 - (σ + t * I)) * mellin g (σ + t * I) := by
  simpa using dlmf_1_14_36 hf hg hint one_pos

/-- For real `f`, `𝓜f(s̄) = conj 𝓜f(s)`. -/
theorem mellin_conj_of_real (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun x => (f x : ℂ)) (conj s) = conj (mellin (fun x => (f x : ℂ)) s) := by
  rw [mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [smul_eq_mul, map_mul, conj_ofReal]
  rw [ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hx, ← Complex.exp_conj]
  congr 2
  simp [map_sub, map_mul, conj_ofReal]

/-- **DLMF 1.14.38**: for real `f` and `σ = ½`, `∫_0^∞ f(x)² dx = (1/2π) ∫ |𝓜f(½ + it)|² dt`,
under the hypotheses of 1.14.36 with `g = f`. -/
theorem dlmf_1_14_38 {f : ℝ → ℝ} (hf : MellinConvergent (fun x => (f x : ℂ)) (1 / 2))
    (hF : VerticalIntegrable (mellin fun x => (f x : ℂ)) (1 / 2)) :
    ∫ x in Ioi (0 : ℝ), f x ^ 2 =
      (2 * π)⁻¹ * ∫ t : ℝ, ‖mellin (fun x => (f x : ℂ)) (1 / 2 + t * I)‖ ^ 2 := by
  have hf1 : MellinConvergent (fun x => (f x : ℂ)) (1 - ((1 / 2 : ℝ) : ℂ)) := by
    convert hf using 2; push_cast; ring
  have hf2 : MellinConvergent (fun x => (f x : ℂ)) ((1 / 2 : ℝ) : ℂ) := by
    convert hf using 2; push_cast; ring
  have hF' : VerticalIntegrable (mellin fun x => (f x : ℂ)) (1 / 2 : ℝ) := hF
  have key := dlmf_1_14_37 hf1 hf2 (Or.inl hF')
  have hpt : ∀ t : ℝ, mellin (fun x => (f x : ℂ)) (1 - (((1 / 2 : ℝ) : ℂ) + t * I)) *
      mellin (fun x => (f x : ℂ)) (((1 / 2 : ℝ) : ℂ) + t * I) =
      ((‖mellin (fun x => (f x : ℂ)) (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) := fun t => by
    have : (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + t * I) = conj ((1 / 2 : ℂ) + t * I) := by
      apply Complex.ext <;> norm_num
    rw [this, mellin_conj_of_real, show (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) by push_cast; rfl,
      Complex.conj_mul']
    push_cast; rfl
  simp_rw [hpt] at key
  rw [integral_complex_ofReal] at key
  have hl : ∫ x in Ioi (0 : ℝ), (f x : ℂ) * (f x : ℂ) =
      ((∫ x in Ioi (0 : ℝ), f x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; simp_rw [sq]
  rw [hl] at key
  exact_mod_cast key

/-! ### Convolution (1.14.39–1.14.40) -/

/-- **DLMF 1.14.39**: the Mellin convolution `(f ∗ g)(x) = ∫_0^∞ f(y) g(x/y) dy/y`. -/
noncomputable def mellinConv (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), f y * g (x / y) / y

/-- Under `x = e^{−w}`, the Mellin convolution becomes an additive convolution:
`e^{−sw} (f ∗ g)(e^{−w}) = (φ ⋆ ψ)(w)` with `φ(u) = e^{−su} f(e^{−u})` and
`ψ(u) = e^{−su} g(e^{−u})`. -/
theorem mellinConv_exp (f g : ℝ → ℂ) (s : ℂ) (w : ℝ) :
    cexp (-(s * w)) * mellinConv f g (rexp (-w)) =
      ((fun u : ℝ => cexp (-(s * u)) * f (rexp (-u))) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun u : ℝ => cexp (-(s * u)) * g (rexp (-u)))) w := by
  rw [convolution_def, mellinConv, setIntegral_Ioi_zero_eq_exp, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hu : (rexp (-u) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have hq : rexp (-w) / rexp (-u) = rexp (-(w - u)) := by
    rw [← Real.exp_sub]; congr 1; ring
  simp only [ContinuousLinearMap.mul_apply']
  rw [hq]
  have he : cexp (-(s * w)) = cexp (-(s * u)) * cexp (-(s * ((w - u : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [he]
  field_simp

/-- The Mellin convolution of `f`, `g` with `x^{σ−1} f`, `x^{σ−1} g` integrable has
`x^{s−1} (f ∗ g)` integrable for `ℜs = σ`. -/
theorem mellinConvergent_mellinConv {f g : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : MellinConvergent (mellinConv f g) s := by
  rw [mellinConvergent_iff_exp] at hf hg ⊢
  have := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  refine this.congr (ae_of_all _ fun w => ?_)
  exact (mellinConv_exp f g s w).symm

/-- **DLMF 1.14.40**: if `x^{σ−1} f(x)` and `x^{σ−1} g(x)` are integrable on `(0, ∞)`, then for
`s = σ + it`, `∫_0^∞ x^{s−1} (f ∗ g)(x) dx = 𝓜f(s) 𝓜g(s)`. -/
theorem dlmf_1_14_40 {f g : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ)
    (hg : MellinConvergent g σ) {s : ℂ} (hs : s.re = σ) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * mellinConv f g x = mellin f s * mellin g s := by
  have hf' := (mellinConvergent_iff_exp f s).mp (mellinConvergent_of_re (hs ▸ hf))
  have hg' := (mellinConvergent_iff_exp g s).mp (mellinConvergent_of_re (hs ▸ hg))
  rw [mellin_eq_integral_exp, mellin_eq_integral_exp, setIntegral_Ioi_zero_eq_exp,
    ← ContinuousLinearMap.mul_apply' ℂ ℂ,
    ← integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) hf'
      hg']
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [← mellinConv_exp, ← mul_assoc, exp_neg_mul_cpow]

end Azurite.DLMF
