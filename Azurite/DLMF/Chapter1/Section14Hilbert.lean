/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Mellin
import Azurite.DLMF.Chapter1.Section14CosSin
import Mathlib.Basic.Real.Sign

/-!
# DLMF §1.14(v): Hilbert transform

Functions are complex-valued (DLMF takes `f` real; everything here is linear, so the real case is
included). `HasHilbert f x L` says the principal value of 1.14.41, at `x` and at `∞` in the sense
of DLMF §1.4(v), exists and equals `L`; `hilbert f x` is its value. Both are written with the
truncations `hilbertTrunc f x ε R = (1/π) ∫_ε^R (f(x + t) − f(x − t))/t dt` of 1.14.43.

**Results.**
* 1.14.41 (`hilbertTrunc_eq_pv`): the truncations of 1.14.41 and 1.14.43 agree for locally
  integrable `f`.
* 1.14.43 (`dlmf_1_14_43`): for integrable `f`, `ℋf(x) = lim_{ε→0+} (1/π) ∫_ε^∞ …`.
* 1.14.42 (`dlmf_1_14_42`): for integrable `f` continuous at `x`, the conjugate Poisson integral
  has the same limit. The two kernels differ by `o(1)` (`tendsto_conjPoisson_sub`, an explicit
  `ε`–`δ` estimate).
* The multiplier formula (`hasHilbert_dlmfFourier`, `hasHilbert_of_fourier`): if `m` is
  integrable, the Hilbert transform of `𝓕⁻¹m` exists everywhere and equals `𝓕⁻¹(−i sign(ξ) m)`.
  The truncations are `∫ m(ξ) e^{−iξx} (−2i)(Si(ξR) − Si(ξε)) dξ` by Fubini, and dominated
  convergence with the bounded sine integral gives both limits.
* 1.14.44 (`dlmf_1_14_44`; general form `hasHilbert_hilbert`): `ℋ(ℋf) = −f`, since
  `(−i sign ξ)² = −1` off `ξ = 0`. For `f` continuously differentiable with compact support,
  `𝓕f` is integrable (`integrable_dlmfFourier_of_contDiff`, via Plancherel for `f′`).
* 1.14.46 (`dlmf_1_14_46`; general form `dlmf_1_14_46_of_bv`): `𝓕(ℋf) = −i sign(x) 𝓕f`. Here
  `ℋf` is not integrable in general (it decays like `1/u`), so the integral is `lim ∫_{−R}^R`.
  The result is 1.14.3 applied to the multiplier, which has bounded variation because `𝓕f` is
  Lipschitz (`lipschitzWith_dlmfFourier`) and `sign` is monotone.
* 1.14.45 for `p = 2` (`dlmf_1_14_45_two`): `∫ |ℋf|² = ∫ |f|²`, where `A₂ = 1` and equality holds.

1.14.45 for general `p > 1` (M. Riesz's theorem with Pichorides' sharp constant) is
`dlmf_1_14_45` in `Section14HilbertLp.lean`, built over `Section14HilbertPichorides` through
`Section14HilbertExtension`. The sharp inequality for integrals has constant `A_p^p`, not `A_p`
as printed, because Pichorides' `A_p` is the operator norm on `L^p`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The sine integral with a signed frequency -/

theorem sinInt_neg (a : ℝ) : sinInt (-a) = -sinInt a := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun z : ℝ => Real.sin z / z)
  have he : (fun x : ℝ => Real.sin (-x) / -x) = fun x => Real.sin x / x := by
    funext x; rw [Real.sin_neg, neg_div_neg_eq]
  rw [he, neg_zero] at h
  simp only [sinInt]
  rw [h, intervalIntegral.integral_symm 0 (-a), neg_neg]

theorem sinInt_zero : sinInt 0 = 0 := by simp [sinInt]

/-- `∫_ε^R sin(ξt)/t dt = Si(ξR) − Si(ξε)` for every real `ξ`. -/
theorem integral_sin_mul_div_eq (ξ ε R : ℝ) :
    ∫ t in ε..R, Real.sin (ξ * t) / t = sinInt (ξ * R) - sinInt (ξ * ε) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [sinInt_zero]
  have h1 : (fun s : ℝ => Real.sin (ξ * s) / s) = fun s => ξ * (Real.sin (ξ * s) / (ξ * s)) := by
    funext s
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · field_simp
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun z => Real.sin z / z) hξ, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hξ, one_mul, sinInt, sinInt,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_sin_div _ _)
      (intervalIntegrable_sin_div _ _)]

theorem monotone_realSign : Monotone Real.sign := fun a b hab => by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;> rcases lt_trichotomy b 0 with hb | rfl | hb <;>
    simp [Real.sign_of_neg, Real.sign_of_pos, Real.sign_zero, *] <;> linarith

theorem measurable_realSign : Measurable Real.sign := monotone_realSign.measurable

theorem exists_bound_sinInt' : ∃ B, 0 ≤ B ∧ ∀ a, |sinInt a| ≤ B := by
  obtain ⟨B, hB, h⟩ := exists_bound_sinInt
  refine ⟨B, hB, fun a => ?_⟩
  rcases le_total 0 a with ha | ha
  · exact h a ha
  · have := h (-a) (by linarith)
    rwa [sinInt_neg, abs_neg] at this

/-- `Si(ξR) → sign(ξ) π/2` as `R → ∞`. -/
theorem tendsto_sinInt_mul (ξ : ℝ) :
    Tendsto (fun R => sinInt (ξ * R)) atTop (𝓝 (Real.sign ξ * (π / 2))) := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · have h := (tendsto_sinInt.comp (tendsto_id.const_mul_atTop (neg_pos.mpr hξ))).neg
    rw [Real.sign_of_neg hξ, show (-1 : ℝ) * (π / 2) = -(π / 2) by ring]
    refine h.congr fun R => ?_
    simp only [Function.comp, id]
    rw [show -ξ * R = -(ξ * R) by ring, sinInt_neg, neg_neg]
  · simp [Real.sign_zero, sinInt_zero]
  · rw [Real.sign_of_pos hξ, one_mul]
    exact tendsto_sinInt.comp (tendsto_id.const_mul_atTop hξ)

/-! ### Definitions (1.14.41, 1.14.43) -/

/-- The truncation `(1/π) ∫_ε^R (f(x + t) − f(x − t))/t dt` of 1.14.43; it equals the truncation
`(1/π) ∫_{ε<|t−x|<R} f(t)/(t − x) dt` of 1.14.41 (`hilbertTrunc_eq_pv`). -/
noncomputable def hilbertTrunc (f : ℝ → ℂ) (x ε R : ℝ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ t in ε..R, (f (x + t) - f (x - t)) / t

/-- The Hilbert transform of `f` at `x` exists and equals `L`: the principal value of 1.14.41 at
`x` and at `∞`, `lim_{ε→0+} lim_{R→∞} (1/π) ∫_{ε<|t−x|<R} f(t)/(t − x) dt = L` (DLMF §1.4(v)). -/
def HasHilbert (f : ℝ → ℂ) (x : ℝ) (L : ℂ) : Prop :=
  ∃ T : ℝ → ℂ, (∀ ε, 0 < ε → Tendsto (fun R => hilbertTrunc f x ε R) atTop (𝓝 (T ε))) ∧
    Tendsto T (𝓝[>] 0) (𝓝 L)

/-- **DLMF 1.14.41**: the Hilbert transform `ℋf(x)`, the value of the limits in `HasHilbert`. -/
noncomputable def hilbert (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => limUnder atTop fun R => hilbertTrunc f x ε R

theorem HasHilbert.hilbert_eq {f : ℝ → ℂ} {x : ℝ} {L : ℂ} (h : HasHilbert f x L) :
    hilbert f x = L := by
  obtain ⟨T, hT, hL⟩ := h
  have : (fun ε => limUnder atTop fun R => hilbertTrunc f x ε R) =ᶠ[𝓝[>] 0] T := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using (hT ε hε).limUnder_eq
  exact (hL.congr' this.symm).limUnder_eq

theorem HasHilbert.unique {f : ℝ → ℂ} {x : ℝ} {L L' : ℂ} (h : HasHilbert f x L)
    (h' : HasHilbert f x L') : L = L' := h.hilbert_eq.symm.trans h'.hilbert_eq

/-! ### The Fourier multiplier `−i sign ξ` -/

theorem integrable_mul_cexp_neg {m : ℝ → ℂ} (hm : Integrable m) (a : ℝ) :
    Integrable fun ξ : ℝ => m ξ * cexp (-(I * a * ξ)) := by
  have := integrable_mul_exp hm (-a)
  refine this.congr (ae_of_all _ fun ξ => ?_)
  simp only
  congr 2; push_cast; ring

theorem cexp_sub_sin (x t ξ : ℝ) :
    cexp (I * ((-(x + t) : ℝ) : ℂ) * ξ) - cexp (I * ((-(x - t) : ℝ) : ℂ) * ξ) =
      cexp (-(I * x * ξ)) * (-2 * I) * ((Real.sin (ξ * t) : ℝ) : ℂ) := by
  have h1 : cexp (I * ((-(x + t) : ℝ) : ℂ) * ξ) =
      cexp (-(I * x * ξ)) * cexp (-((ξ * t : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : cexp (I * ((-(x - t) : ℝ) : ℂ) * ξ) =
      cexp (-(I * x * ξ)) * cexp (((ξ * t : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, h2, ofReal_sin, Complex.sin]
  linear_combination (cexp (-(I * x * ξ)) * (cexp (-((ξ * t : ℝ) : ℂ) * I) -
    cexp (((ξ * t : ℝ) : ℂ) * I))) * I_sq

/-- The key computation: if `m` is integrable and `g(u) = 𝓕m(−u)` (so `g = 𝓕⁻¹m`), then the
Hilbert transform of `g` exists everywhere and `ℋg = 𝓕⁻¹(−i sign(ξ) m(ξ))`. The truncations are
`∫ m(ξ) e^{−iξx} (−2i)(Si(ξR) − Si(ξε)) dξ`, by Fubini; then dominated convergence twice. -/
theorem hasHilbert_dlmfFourier {m : ℝ → ℂ} (hm : Integrable m) (x : ℝ) :
    HasHilbert (fun u => dlmfFourier m (-u)) x
      (dlmfFourier (fun ξ => -I * Real.sign ξ * m ξ) (-x)) := by
  obtain ⟨B, hB, hBd⟩ := exists_bound_sinInt'
  set c : ℂ := ((√(2 * π) : ℝ) : ℂ) with hc
  set Ψ : ℝ → ℂ := fun ξ => m ξ * cexp (-(I * x * ξ)) * (-2 * I) with hΨ
  have hΨi : Integrable Ψ := (integrable_mul_cexp_neg hm x).mul_const _
  have hdiff : ∀ t : ℝ, dlmfFourier m (-(x + t)) - dlmfFourier m (-(x - t)) =
      c⁻¹ * ∫ ξ, Ψ ξ * ((Real.sin (ξ * t) : ℝ) : ℂ) := fun t => by
    rw [dlmfFourier, dlmfFourier, ← mul_sub, ← integral_sub (integrable_mul_exp hm _)
      (integrable_mul_exp hm _)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [hΨ]
    rw [← mul_sub, cexp_sub_sin]
    ring
  have hmeas : Measurable fun p : ℝ × ℝ => ((Real.sin (p.2 * p.1) / p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have htrunc : ∀ ε R : ℝ, 0 < ε → ε ≤ R →
      hilbertTrunc (fun u => dlmfFourier m (-u)) x ε R =
        (π : ℂ)⁻¹ * (c⁻¹ * ∫ ξ, Ψ ξ * ((sinInt (ξ * R) - sinInt (ξ * ε) : ℝ) : ℂ)) := by
    intro ε R hε hR
    rw [hilbertTrunc]
    congr 1
    have hF : Integrable (Function.uncurry fun (t ξ : ℝ) => Ψ ξ *
        ((Real.sin (ξ * t) / t : ℝ) : ℂ)) ((volume.restrict (Ioc ε R)).prod volume) := by
      refine ((integrable_const ε⁻¹).mul_prod hΨi.norm).mono'
        (hΨi.aestronglyMeasurable.comp_snd.mul hmeas.aestronglyMeasurable) ?_
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)]
        with p hp
      change ‖Ψ p.2 * ((Real.sin (p.2 * p.1) / p.1 : ℝ) : ℂ)‖ ≤ ε⁻¹ * ‖Ψ p.2‖
      have hp1 : 0 < p.1 := hε.trans hp.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm, abs_div,
        abs_of_pos hp1]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [div_le_iff₀ hp1]
      calc |Real.sin (p.2 * p.1)| ≤ 1 := Real.abs_sin_le_one _
        _ = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
        _ ≤ ε⁻¹ * p.1 := mul_le_mul_of_nonneg_left hp.1.le (inv_nonneg.mpr hε.le)
    have hswap := integral_integral_swap hF
    rw [intervalIntegral.integral_of_le hR]
    calc ∫ t in Ioc ε R, (dlmfFourier m (-(x + t)) - dlmfFourier m (-(x - t))) / (t : ℂ)
        = ∫ t in Ioc ε R, c⁻¹ * ∫ ξ, Ψ ξ * ((Real.sin (ξ * t) / t : ℝ) : ℂ) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
          rw [hdiff, mul_div_assoc, ← integral_div]
          congr 2; funext ξ; push_cast; ring
      _ = c⁻¹ * ∫ t in Ioc ε R, ∫ ξ, Ψ ξ * ((Real.sin (ξ * t) / t : ℝ) : ℂ) :=
          integral_const_mul _ _
      _ = c⁻¹ * ∫ ξ, Ψ ξ * ((sinInt (ξ * R) - sinInt (ξ * ε) : ℝ) : ℂ) := by
          rw [hswap]
          congr 1
          refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
          dsimp only
          rw [integral_const_mul, ← integral_sin_mul_div_eq, intervalIntegral.integral_of_le hR,
            integral_complex_ofReal]
  set T : ℝ → ℂ := fun ε => (π : ℂ)⁻¹ *
    (c⁻¹ * ∫ ξ, Ψ ξ * ((Real.sign ξ * (π / 2) - sinInt (ξ * ε) : ℝ) : ℂ)) with hT
  have hsc : Continuous fun p : ℝ => sinInt p := continuous_sinInt
  refine ⟨T, fun ε hε => ?_, ?_⟩
  · have hlim : Tendsto (fun R => ∫ ξ, Ψ ξ * ((sinInt (ξ * R) - sinInt (ξ * ε) : ℝ) : ℂ))
        atTop (𝓝 (∫ ξ, Ψ ξ * ((Real.sign ξ * (π / 2) - sinInt (ξ * ε) : ℝ) : ℂ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖Ψ ξ‖ * (2 * B))
        (Eventually.of_forall fun R => hΨi.aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp ((hsc.comp (by fun_prop)).sub
            (hsc.comp (by fun_prop)))).aestronglyMeasurable)
        (Eventually.of_forall fun R => ae_of_all _ fun ξ => ?_) (hΨi.norm.mul_const _)
        (ae_of_all _ fun ξ => ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 := hBd (ξ * R)
        have h2 := hBd (ξ * ε)
        calc |sinInt (ξ * R) - sinInt (ξ * ε)| ≤ |sinInt (ξ * R)| + |sinInt (ξ * ε)| :=
              abs_sub _ _
          _ ≤ 2 * B := by linarith
      · exact (Complex.continuous_ofReal.tendsto _ |>.comp
          ((tendsto_sinInt_mul ξ).sub_const _)).const_mul (Ψ ξ)
    refine ((hlim.const_mul c⁻¹).const_mul (π : ℂ)⁻¹).congr' ?_
    filter_upwards [eventually_ge_atTop ε] with R hR using (htrunc ε R hε hR).symm
  · have hlim : Tendsto (fun ε => ∫ ξ, Ψ ξ *
        ((Real.sign ξ * (π / 2) - sinInt (ξ * ε) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (∫ ξ, Ψ ξ * ((Real.sign ξ * (π / 2) : ℝ) : ℂ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖Ψ ξ‖ * (π / 2 + B))
        (Eventually.of_forall fun ε => hΨi.aestronglyMeasurable.mul
          (Complex.measurable_ofReal.comp ((measurable_realSign.mul_const _).sub
            (hsc.comp (by fun_prop)).measurable)).aestronglyMeasurable)
        (Eventually.of_forall fun ε => ae_of_all _ fun ξ => ?_) (hΨi.norm.mul_const _)
        (ae_of_all _ fun ξ => ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 := hBd (ξ * ε)
        have h2 : |Real.sign ξ * (π / 2)| ≤ π / 2 := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
          rcases Real.sign_apply_eq ξ with h | h | h <;> rw [h] <;> norm_num
          positivity
        calc |Real.sign ξ * (π / 2) - sinInt (ξ * ε)|
            ≤ |Real.sign ξ * (π / 2)| + |sinInt (ξ * ε)| := abs_sub _ _
          _ ≤ π / 2 + B := by linarith
      · have h0 : Tendsto (fun ε : ℝ => sinInt (ξ * ε)) (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun ε : ℝ => ξ * ε) (𝓝 0) (𝓝 0) := by
            simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul ξ
          have := (sinInt_zero ▸ hsc.tendsto 0).comp h1
          exact this.mono_left nhdsWithin_le_nhds
        have := (Complex.continuous_ofReal.tendsto _).comp (h0.const_sub (Real.sign ξ * (π / 2)))
        rw [sub_zero] at this
        exact this.const_mul (Ψ ξ)
    have hval : dlmfFourier (fun ξ => -I * Real.sign ξ * m ξ) (-x) =
        (π : ℂ)⁻¹ * (c⁻¹ * ∫ ξ, Ψ ξ * ((Real.sign ξ * (π / 2) : ℝ) : ℂ)) := by
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      rw [dlmfFourier, mul_left_comm (π : ℂ)⁻¹, ← integral_const_mul (π : ℂ)⁻¹]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      have he : cexp (I * ((-x : ℝ) : ℂ) * ξ) = cexp (-(I * x * ξ)) := by
        congr 1; push_cast; ring
      simp only [hΨ]
      rw [he]
      push_cast
      field_simp
    rw [hval]
    exact (hlim.const_mul c⁻¹).const_mul (π : ℂ)⁻¹

/-! ### The principal-value form (1.14.41) and the symmetric form (1.14.43) -/

/-- The truncations of 1.14.43 and 1.14.41 agree:
`∫_ε^R (f(x + t) − f(x − t))/t dt` equals
`∫_{x−R}^{x−ε} f(t)/(t − x) dt + ∫_{x+ε}^{x+R} f(t)/(t − x) dt`. -/
theorem hilbertTrunc_eq_pv {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (x : ℝ) {ε R : ℝ}
    (hε : 0 < ε) (hR : ε ≤ R) :
    hilbertTrunc f x ε R = (π : ℂ)⁻¹ * ((∫ t in (x - R)..(x - ε), f t / (t - x)) +
      ∫ t in (x + ε)..(x + R), f t / (t - x)) := by
  have hii : ∀ a b, IntervalIntegrable f volume a b := fun a b =>
    (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hc1 : ContinuousOn (fun s : ℝ => ((s - x : ℝ) : ℂ)⁻¹) (uIcc (x + ε) (x + R)) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun s hs => ?_
    rw [uIcc_of_le (by linarith)] at hs
    exact_mod_cast (show s - x ≠ 0 by linarith [hs.1])
  have hc2 : ContinuousOn (fun s : ℝ => ((x - s : ℝ) : ℂ)⁻¹) (uIcc (x - ε) (x - R)) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun s hs => ?_
    rw [uIcc_of_ge (by linarith)] at hs
    exact_mod_cast (show x - s ≠ 0 by linarith [hs.2])
  have i1 := ((hii (x + ε) (x + R)).mul_continuousOn hc1).comp_add_left x
  have i2 := ((hii (x - ε) (x - R)).mul_continuousOn hc2).comp_sub_left x
  simp only [add_sub_cancel_left, sub_sub_cancel] at i1 i2
  have e1 := intervalIntegral.integral_comp_add_left (a := ε) (b := R)
    (fun s => f s / ((s : ℂ) - x)) x
  have e2 := intervalIntegral.integral_comp_sub_left (a := ε) (b := R)
    (fun s => f s / ((x : ℂ) - s)) x
  rw [hilbertTrunc]
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub
    (i1.congr fun t _ => by ring) (i2.congr fun t _ => by ring)]
  rw [show (fun t : ℝ => f (x + t) / (t : ℂ)) = fun t => f (x + t) / (((x + t : ℝ) : ℂ) - x)
    from funext fun t => by push_cast; ring_nf,
    show (fun t : ℝ => f (x - t) / (t : ℂ)) = fun t => f (x - t) / ((x : ℂ) - ((x - t : ℝ) : ℂ))
    from funext fun t => by push_cast; ring_nf, e1, e2]
  rw [show (fun s : ℝ => f s / ((x : ℂ) - s)) = fun s => -(f s / ((s : ℂ) - x)) from
    funext fun s => by rw [← neg_sub, div_neg], intervalIntegral.integral_neg]
  ring

theorem integrableOn_hilbert {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => (f (x + t) - f (x - t)) / t) (Ioi ε) := by
  have hg : Integrable fun t => f (x + t) - f (x - t) :=
    (hf.comp_add_left x).sub (hf.comp_sub_left x)
  refine (hg.integrableOn.norm.div_const ε).mono'
    (hg.aestronglyMeasurable.restrict.mul
      (by fun_prop : Measurable fun t : ℝ => (t : ℂ)⁻¹).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  have ht' : (0 : ℝ) < t := hε.trans ht
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht'.le]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hε (le_of_lt ht)

theorem tendsto_hilbertTrunc {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R => hilbertTrunc f x ε R) atTop
      (𝓝 ((π : ℂ)⁻¹ * ∫ t in Ioi ε, (f (x + t) - f (x - t)) / t)) :=
  (intervalIntegral_tendsto_integral_Ioi ε (integrableOn_hilbert hf x hε) tendsto_id).const_mul _

/-- **DLMF 1.14.43**: for integrable `f`,
`ℋf(x) = lim_{ε→0+} (1/π) ∫_ε^∞ (f(x + t) − f(x − t))/t dt`, the integrals over `(ε, ∞)`
being absolutely convergent. -/
theorem dlmf_1_14_43 {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) (L : ℂ) :
    HasHilbert f x L ↔ Tendsto (fun ε => (π : ℂ)⁻¹ * ∫ t in Ioi ε, (f (x + t) - f (x - t)) / t)
      (𝓝[>] 0) (𝓝 L) := by
  constructor
  · rintro ⟨T, hT, hL⟩
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact tendsto_nhds_unique (hT ε hε) (tendsto_hilbertTrunc hf x hε)
  · exact fun h => ⟨_, fun ε hε => tendsto_hilbertTrunc hf x hε, h⟩

/-! ### The conjugate Poisson form (1.14.42) -/

theorem abs_div_sq_add_sq_le {s y : ℝ} (hy : 0 < y) : |s / (s ^ 2 + y ^ 2)| ≤ 1 / y := by
  rw [abs_div, abs_of_pos (by positivity : 0 < s ^ 2 + y ^ 2), div_le_div_iff₀ (by positivity) hy,
    one_mul]
  nlinarith [sq_abs s, abs_nonneg s, sq_nonneg (|s| - y)]

theorem abs_kernel_sub_le {s y : ℝ} (hy : 0 < y) (hs : y ≤ s) :
    |s / (s ^ 2 + y ^ 2) - 1 / s| ≤ y / s ^ 2 := by
  have hs0 : 0 < s := hy.trans_le hs
  have key : s / (s ^ 2 + y ^ 2) - 1 / s = -(y ^ 2 / (s * (s ^ 2 + y ^ 2))) := by
    field_simp; ring
  rw [key, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have : y * s ≤ s ^ 2 + y ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ y * s ^ 2)]

/-- The conjugate Poisson kernel and the truncated kernel `1_{s>y}/s` differ by `o(1)` against
`g` integrable on `(0, ∞)` with `g(0+) = 0`. -/
theorem tendsto_conjPoisson_sub {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0))
    (h0 : Tendsto g (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun y : ℝ => (∫ s in Ioi 0, ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s) -
      ∫ s in Ioi y, g s / s) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  set η := e / 4 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hδg⟩ := Metric.tendsto_nhdsWithin_nhds.mp h0 η hηpos
  set G := ∫ s in Ioi 0, ‖g s‖ with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _
  refine ⟨min δ (η * δ ^ 2 / (G + 1)), lt_min hδ (by positivity), fun y hy hyd => ?_⟩
  have hy0 : (0 : ℝ) < y := hy
  rw [dist_zero_right, Real.norm_of_nonneg hy0.le] at hyd
  have hyδ : y < δ := hyd.trans_le (min_le_left _ _)
  have hyG : y * G / δ ^ 2 ≤ η := by
    have h1 : y < η * δ ^ 2 / (G + 1) := hyd.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hgs : ∀ s, 0 < s → s < δ → ‖g s‖ < η := fun s hs hsδ => by
    have := hδg (x := s) hs (by rw [dist_zero_right, Real.norm_of_nonneg hs.le]; exact hsδ)
    rwa [dist_zero_right] at this
  have hkm : Measurable fun s : ℝ => ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have hk : IntegrableOn (fun s : ℝ => ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s) (Ioi 0) :=
    hg.bdd_mul (c := 1 / y) hkm.aestronglyMeasurable (ae_of_all _ fun s => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_div_sq_add_sq_le hy0)
  have hgy : IntegrableOn g (Ioi y) := hg.mono_set (Ioi_subset_Ioi hy0.le)
  have hd : IntegrableOn (fun s : ℝ => g s / s) (Ioi y) := by
    refine (hgy.norm.div_const y).mono' (hgy.aestronglyMeasurable.mul
      (by fun_prop : Measurable fun t : ℝ => (t : ℂ)⁻¹).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht' : (0 : ℝ) < t := hy0.trans ht
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht'.le]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hy0 (le_of_lt ht)
  rw [← Ioc_union_Ioi_eq_Ioi hy0.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hk.mono_set (by rw [← Ioc_union_Ioi_eq_Ioi hy0.le]; exact subset_union_left))
    (hk.mono_set (Ioi_subset_Ioi hy0.le)), add_sub_assoc, ← integral_sub
    (hk.mono_set (Ioi_subset_Ioi hy0.le)) hd]
  have hA : ‖∫ s in Ioc 0 y, ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s‖ ≤ η := by
    have := norm_setIntegral_le_of_norm_le_const (C := η / y) (μ := volume)
      (f := fun s : ℝ => ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s) measure_Ioc_lt_top
      fun s hs => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv η, mul_comm η]
        refine mul_le_mul ?_ (hgs s hs.1 (hs.2.trans_lt hyδ)).le (norm_nonneg _)
          (by positivity)
        simpa [one_div] using abs_div_sq_add_sq_le (s := s) hy0
    rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hy0.le,
      div_mul_cancel₀ _ hy0.ne'] at this
    exact this
  have hbi : IntegrableOn (fun s : ℝ => y * η * s ^ (-2 : ℝ) + y / δ ^ 2 * ‖g s‖) (Ioi y) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hy0).const_mul _).add
      (hgy.norm.const_mul _)
  have hB : ‖∫ s in Ioi y, (((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s - g s / s)‖ ≤
      η + y * G / δ ^ 2 := by
    refine (norm_integral_le_of_norm_le hbi ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun s hs => ?_))).trans ?_
    · have hs0 : (0 : ℝ) < s := hy0.trans hs
      have hk2 := abs_kernel_sub_le hy0 (le_of_lt hs)
      have heq : ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s - g s / s =
          ((s / (s ^ 2 + y ^ 2) - 1 / s : ℝ) : ℂ) * g s := by
        push_cast; field_simp
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hs0.le,
        Real.rpow_two]
      calc |s / (s ^ 2 + y ^ 2) - 1 / s| * ‖g s‖ ≤ y / s ^ 2 * ‖g s‖ :=
            mul_le_mul_of_nonneg_right hk2 (norm_nonneg _)
        _ ≤ y * η * (s ^ 2)⁻¹ + y / δ ^ 2 * ‖g s‖ := by
            rcases lt_or_ge s δ with hsδ | hsδ
            · have := hgs s hs0 hsδ
              have h3 : y / s ^ 2 * ‖g s‖ ≤ y / s ^ 2 * η :=
                mul_le_mul_of_nonneg_left this.le (by positivity)
              have h4 : 0 ≤ y / δ ^ 2 * ‖g s‖ := by positivity
              have h5 : y / s ^ 2 * η = y * η * (s ^ 2)⁻¹ := by ring
              linarith
            · have : y / s ^ 2 ≤ y / δ ^ 2 :=
                div_le_div_of_nonneg_left hy0.le (by positivity) (by nlinarith)
              have : y / s ^ 2 * ‖g s‖ ≤ y / δ ^ 2 * ‖g s‖ :=
                mul_le_mul_of_nonneg_right this (norm_nonneg _)
              have : 0 ≤ y * η * (s ^ 2)⁻¹ := by positivity
              linarith
    · rw [integral_add ((integrableOn_Ioi_rpow_of_lt (by norm_num) hy0).const_mul _)
        (hgy.norm.const_mul _), integral_const_mul, integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num) hy0]
      have h1 : y * η * (-y ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1)) = η := by
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp
      have h2 : ∫ s in Ioi y, ‖g s‖ ≤ G :=
        setIntegral_mono_set hg.norm (ae_of_all _ fun _ => norm_nonneg _)
          (Ioi_subset_Ioi hy0.le).eventuallyLE
      rw [h1]
      have : y / δ ^ 2 * ∫ s in Ioi y, ‖g s‖ ≤ y / δ ^ 2 * G :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have : y / δ ^ 2 * G = y * G / δ ^ 2 := by ring
      linarith
  rw [dist_zero_right]
  calc ‖(∫ s in Ioc 0 y, ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s) +
        ∫ s in Ioi y, (((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s - g s / s)‖
      ≤ η + (η + y * G / δ ^ 2) := (norm_add_le _ _).trans (add_le_add hA hB)
    _ ≤ η + (η + η) := by linarith
    _ < e := by rw [hη]; linarith

/-- The conjugate Poisson integral `(1/π) ∫ (t − x)/((t − x)² + y²) f(t) dt` as an integral over
`(0, ∞)` of `s/(s² + y²) (f(x + s) − f(x − s))`. -/
theorem conjPoisson_eq {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * f t =
      ∫ s in Ioi 0, ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * (f (x + s) - f (x - s)) := by
  set h : ℝ → ℂ := fun s => ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * f (x + s) with hh
  have hhi : Integrable h :=
    (hf.comp_add_left x).bdd_mul (c := 1 / y)
      (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_div_sq_add_sq_le hy)
  have h1 : ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * f t = ∫ t, h (t - x) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hh, add_sub_cancel]
  rw [h1, integral_sub_right_eq_self h x, integral_eq_halves hhi]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [hh, ← sub_eq_add_neg]
  rw [neg_sq, neg_div]
  push_cast
  ring

/-- **DLMF 1.14.42**: for integrable `f` continuous at `x`,
`ℋf(x) = lim_{y→0+} (1/π) ∫ (t − x)/((t − x)² + y²) f(t) dt`: either limit exists if the other
does, with the same value. -/
theorem dlmf_1_14_42 {f : ℝ → ℂ} (hf : Integrable f) {x : ℝ} (hc : ContinuousAt f x) (L : ℂ) :
    HasHilbert f x L ↔ Tendsto (fun y : ℝ => (π : ℂ)⁻¹ *
      ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * f t) (𝓝[>] 0) (𝓝 L) := by
  set g : ℝ → ℂ := fun s => f (x + s) - f (x - s) with hg
  have hgi : IntegrableOn g (Ioi 0) :=
    ((hf.comp_add_left x).sub (hf.comp_sub_left x)).integrableOn
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => x + s) (𝓝 0) (𝓝 x) := by
      simpa using (tendsto_const_nhds (x := x)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    have h2 : Tendsto (fun s : ℝ => x - s) (𝓝 0) (𝓝 x) := by
      simpa using (tendsto_const_nhds (x := x)).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
    have := (hc.tendsto.comp h1).sub (hc.tendsto.comp h2)
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hD := (tendsto_conjPoisson_sub hgi hg0).const_mul (π : ℂ)⁻¹
  rw [mul_zero] at hD
  have heq : ∀ᶠ y in 𝓝[>] (0 : ℝ), (π : ℂ)⁻¹ *
      ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * f t =
      (π : ℂ)⁻¹ * (∫ s in Ioi y, g s / s) + (π : ℂ)⁻¹ * ((∫ s in Ioi 0,
        ((s / (s ^ 2 + y ^ 2) : ℝ) : ℂ) * g s) - ∫ s in Ioi y, g s / s) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [conjPoisson_eq hf x hy]
    ring
  rw [dlmf_1_14_43 hf x L]
  constructor
  · intro h
    have := h.add hD
    rw [add_zero] at this
    exact this.congr' (heq.mono fun y hy => hy.symm)
  · intro h
    have := (h.congr' heq).sub hD
    rw [sub_zero] at this
    exact this.congr fun y => by ring

/-! ### `ℋf` through the Fourier transform -/

/-- The multiplier `−i sign(ξ) 𝓕f(ξ)`. -/
noncomputable def hilbertMultiplier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  -I * Real.sign ξ * dlmfFourier f ξ

theorem norm_neg_I_mul_sign_le (ξ : ℝ) : ‖-I * (Real.sign ξ : ℂ)‖ ≤ 1 := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases Real.sign_apply_eq ξ with h | h | h <;> rw [h] <;> norm_num

theorem integrable_hilbertMultiplier {f : ℝ → ℂ} (hF : Integrable (dlmfFourier f)) :
    Integrable (hilbertMultiplier f) :=
  hF.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop) |>.mul
    (Complex.measurable_ofReal.comp measurable_realSign).aestronglyMeasurable)
    (ae_of_all _ norm_neg_I_mul_sign_le)

/-- Under Fourier inversion (`f`, `𝓕f` integrable, `f` continuous), `f(u) = 𝓕(𝓕f)(−u)`. -/
theorem eq_dlmfFourier_neg {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    (hc : Continuous f) : f = fun u => dlmfFourier (dlmfFourier f) (-u) := by
  funext u
  rw [dlmf_inversion hf hF hc.continuousAt, dlmfFourier]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  congr 2; push_cast; ring

/-- For integrable continuous `f` with integrable `𝓕f`, the Hilbert transform exists everywhere and
`ℋf = 𝓕⁻¹(−i sign(ξ) 𝓕f(ξ))`. -/
theorem hasHilbert_of_fourier {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    (hc : Continuous f) (x : ℝ) :
    HasHilbert f x (dlmfFourier (hilbertMultiplier f) (-x)) := by
  have key := hasHilbert_dlmfFourier hF x
  rwa [← eq_dlmfFourier_neg hf hF hc] at key

theorem hilbert_eq_of_fourier {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    (hc : Continuous f) : hilbert f = fun x => dlmfFourier (hilbertMultiplier f) (-x) :=
  funext fun x => (hasHilbert_of_fourier hf hF hc x).hilbert_eq

theorem ae_ne_zero : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by
  rw [ae_iff]
  simp

theorem dlmfFourier_congr_ae {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) (x : ℝ) :
    dlmfFourier g x = dlmfFourier h x := by
  rw [dlmfFourier, dlmfFourier]
  congr 1
  exact integral_congr_ae (hgh.mono fun ξ hξ => by simp only [hξ])

theorem dlmfFourier_neg (g : ℝ → ℂ) (x : ℝ) :
    dlmfFourier (fun ξ => -g ξ) x = -dlmfFourier g x := by
  rw [dlmfFourier, dlmfFourier, ← mul_neg, ← integral_neg]
  simp only [neg_mul]

/-! ### Inversion (1.14.44) -/

/-- **DLMF 1.14.44**, general form: for integrable continuous `f` with integrable `𝓕f`,
`f(x) = −(1/π) ⨍ ℋf(u)/(u − x) du`, i.e. `ℋ(ℋf) = −f`. -/
theorem hasHilbert_hilbert {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    (hc : Continuous f) (x : ℝ) : HasHilbert (hilbert f) x (-f x) := by
  have key := hasHilbert_dlmfFourier (integrable_hilbertMultiplier hF) x
  rw [← hilbert_eq_of_fourier hf hF hc] at key
  convert key using 1
  rw [dlmfFourier_congr_ae (g := fun ξ => -I * Real.sign ξ * hilbertMultiplier f ξ)
    (h := fun ξ => -dlmfFourier f ξ) (ae_ne_zero.mono fun ξ hξ => ?_), dlmfFourier_neg,
    congrFun (eq_dlmfFourier_neg hf hF hc) x]
  simp only [hilbertMultiplier]
  have hs : (Real.sign ξ : ℂ) ^ 2 = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero ξ hξ with h | h <;> rw [h] <;> norm_num
  linear_combination (I ^ 2 * dlmfFourier f ξ) * hs + dlmfFourier f ξ * I_sq

/-- The derivative rule `𝓕(f′)(x) = −ix 𝓕f(x)` in DLMF's normalization. -/
theorem dlmfFourier_deriv {f : ℝ → ℂ} (hf : Integrable f) (hd : Differentiable ℝ f)
    (hf' : Integrable (deriv f)) (x : ℝ) :
    dlmfFourier (deriv f) x = -I * x * dlmfFourier f x := by
  rw [dlmfFourier_eq_fourier, dlmfFourier_eq_fourier, Real.fourier_deriv hf hd hf']
  simp only [smul_eq_mul]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- For `f` continuously differentiable with compact support, `𝓕f` is integrable: by Plancherel
`x 𝓕f(x) = i 𝓕(f′)(x)` is square integrable, and `|𝓕f| ≤ |x 𝓕f|²/2 + 1/(1 + x²)` for `|x| ≥ 1`. -/
theorem integrable_dlmfFourier_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) : Integrable (dlmfFourier f) := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hs
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hds : HasCompactSupport (deriv f) := hs.deriv
  have hdi : Integrable (deriv f) := hdc.integrable_of_hasCompactSupport hds
  have hd2 : MemLp (deriv f) 2 := hdc.memLp_of_hasCompactSupport hds
  have hG := (dlmf_1_14_8 hdi hd2).1
  set C := (√(2 * π))⁻¹ * ∫ t, ‖f t‖ with hC
  have hC0 : 0 ≤ C := by positivity
  refine ((hG.div_const 2).add (integrable_inv_one_add_sq.const_mul (2 * C + 1))).mono'
    (dlmf_1_14_i_continuous hfi).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hFC : ‖dlmfFourier f x‖ ≤ C := dlmf_1_14_2 f x
  show ‖dlmfFourier f x‖ ≤ ‖dlmfFourier (deriv f) x‖ ^ 2 / 2 + (2 * C + 1) * (1 + x ^ 2)⁻¹
  have hGx : ‖dlmfFourier (deriv f) x‖ = |x| * ‖dlmfFourier f x‖ := by
    rw [dlmfFourier_deriv hfi (hf.differentiable (by norm_num)) hdi, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hGx]
  set a := ‖dlmfFourier f x‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  set w := (1 + x ^ 2)⁻¹ with hw
  have hw1 : w * (1 + x ^ 2) = 1 := inv_mul_cancel₀ (by positivity)
  have hw0 : 0 < w := by positivity
  have hxa : (|x| * a) ^ 2 = x ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]
  rw [hxa]
  rcases le_or_gt 1 (x ^ 2) with hx | hx
  · have key : 0 ≤ 2 * x ^ 2 * (x ^ 2 * a ^ 2 / 2 + w - a) := by
      nlinarith [sq_nonneg (x ^ 2 * a - 1), mul_nonneg hw0.le (sub_nonneg.mpr hx)]
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * x ^ 2)).mp key
    nlinarith [mul_pos hw0 (by positivity : (0 : ℝ) < 2 * C + 1)]
  · have : C ≤ (2 * C + 1) * w := by
      nlinarith [mul_le_mul_of_nonneg_left (show 1 + x ^ 2 ≤ 2 by linarith) hw0.le]
    nlinarith [sq_nonneg (x ^ 2 * a)]

/-- **DLMF 1.14.44**: if `f` is continuously differentiable and vanishes outside a bounded
interval, then `f(x) = −(1/π) ⨍ ℋf(u)/(u − x) du`. -/
theorem dlmf_1_14_44 {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (x : ℝ) :
    HasHilbert (hilbert f) x (-f x) :=
  hasHilbert_hilbert (hf.continuous.integrable_of_hasCompactSupport hs)
    (integrable_dlmfFourier_of_contDiff hf hs) hf.continuous x

/-! ### Fourier transform (1.14.46) -/

theorem boundedVariationOn_neg_I_mul_sign (s : Set ℝ) :
    BoundedVariationOn (fun ξ : ℝ => -I * (Real.sign ξ : ℂ)) s := by
  have hL : LipschitzWith 1 fun r : ℝ => -I * (r : ℂ) := LipschitzWith.of_dist_le_mul fun r q => by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, norm_neg, Complex.norm_I, one_mul,
      ← ofReal_sub, Complex.norm_real, NNReal.coe_one, one_mul]
  have hs : BoundedVariationOn Real.sign s :=
    (monotone_realSign.monotoneOn s).boundedVariationOn (C := 1) fun ξ _ => by
      rcases Real.sign_apply_eq ξ with h | h | h <;> rw [h] <;> norm_num
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs)
    ((hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (mapsTo_univ _ _))

/-- `𝓕f` is Lipschitz when `t f(t)` is integrable. -/
theorem lipschitzWith_dlmfFourier {f : ℝ → ℂ} (hf : Integrable f)
    (ht : Integrable fun t => |t| * ‖f t‖) :
    LipschitzWith (Real.toNNReal ((√(2 * π))⁻¹ * ∫ t, |t| * ‖f t‖)) (dlmfFourier f) := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, dlmfFourier, dlmfFourier, ← mul_sub,
    ← integral_sub (integrable_mul_exp hf x) (integrable_mul_exp hf y), norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (ht.mul_const _) (ae_of_all _ fun t => ?_)
  have he : cexp (I * x * t) - cexp (I * y * t) =
      cexp (I * y * t) * (cexp (I * (((x - y) * t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [← mul_sub, he, norm_mul, norm_mul, norm_exp, show (I * y * t).re = 0 by simp,
    Real.exp_zero, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (x - y) * t)
  rw [Real.norm_eq_abs, abs_mul] at this
  calc ‖f t‖ * ‖cexp (I * (((x - y) * t : ℝ) : ℂ)) - 1‖ ≤ ‖f t‖ * (|x - y| * |t|) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = |t| * ‖f t‖ * ‖x - y‖ := by rw [Real.norm_eq_abs]; ring

/-- **DLMF 1.14.46**, general form: if `f` is integrable and continuous, `𝓕f` is integrable and of
bounded variation near `x`, then
`(1/√(2π)) ∫ ℋf(u) e^{iux} du = −i sign(x) 𝓕f(x)`, the integral over `ℝ` being the limit of
`∫_{−R}^R` (`ℋf` need not be integrable: it decays only like `1/u`). -/
theorem dlmf_1_14_46_of_bv {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    (hc : Continuous f) {x : ℝ}
    (hbv : BoundedVariationOn (dlmfFourier f) (Icc (x - 1) (x + 1))) :
    Tendsto (fun R : ℝ => ((√(2 * π) : ℝ) : ℂ)⁻¹ *
      ∫ u in (-R)..R, hilbert f u * cexp (I * u * x)) atTop
      (𝓝 (-I * Real.sign x * dlmfFourier f x)) := by
  set M := hilbertMultiplier f with hMdef
  have hM := integrable_hilbertMultiplier hF
  have hFc := dlmf_1_14_i_continuous hf
  obtain ⟨C, hC⟩ : ∃ C, ∀ ξ ∈ Icc (x - 1) (x + 1), ‖dlmfFourier f ξ‖ ≤ C :=
    ⟨_, bv_norm_le_of_mem hbv (a := x) ⟨by linarith, by linarith⟩⟩
  have hbvM : BoundedVariationOn M (Icc (x - 1) (x + 1)) :=
    boundedVariationOn_mul (boundedVariationOn_neg_I_mul_sign _) hbv
      (fun ξ _ => norm_neg_I_mul_sign_le ξ) hC
  have hlim : ∀ {Lp Lm : ℂ}, Tendsto M (𝓝[>] x) (𝓝 Lp) → Tendsto M (𝓝[<] x) (𝓝 Lm) →
      (Lp + Lm) / 2 = -I * Real.sign x * dlmfFourier f x →
      Tendsto (fun R : ℝ => ((√(2 * π) : ℝ) : ℂ)⁻¹ *
        ∫ u in (-R)..R, hilbert f u * cexp (I * u * x)) atTop
        (𝓝 (-I * Real.sign x * dlmfFourier f x)) := by
    intro Lp Lm hp hm hL
    have h3 := dlmf_1_14_3 hM one_pos hbvM hp hm
    rw [hL] at h3
    refine h3.congr fun R => ?_
    congr 1
    rw [hilbert_eq_of_fourier hf hF hc]
    have := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun v => dlmfFourier M v * cexp (-(I * v * x)))
    rw [neg_neg] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only
    congr 2; push_cast; ring
  have hR : ∀ s : ℂ, (∀ᶠ ξ in 𝓝 x, M ξ = s * dlmfFourier f ξ) →
      Tendsto M (𝓝 x) (𝓝 (s * dlmfFourier f x)) := fun s hev =>
    ((hFc.tendsto x).const_mul s).congr' (hev.mono fun _ h => h.symm)
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : ∀ᶠ ξ in 𝓝 x, M ξ = I * dlmfFourier f ξ := by
      filter_upwards [Iio_mem_nhds hx] with ξ hξ
      simp [hMdef, hilbertMultiplier, Real.sign_of_neg (show ξ < 0 from hξ)]
    have h := hR _ hev
    refine hlim (h.mono_left nhdsWithin_le_nhds) (h.mono_left nhdsWithin_le_nhds) ?_
    rw [Real.sign_of_neg hx]; push_cast; ring
  · have hp : Tendsto M (𝓝[>] 0) (𝓝 (-I * dlmfFourier f 0)) := by
      refine ((hFc.tendsto 0).const_mul (-I)).mono_left nhdsWithin_le_nhds |>.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ξ hξ
      simp [hMdef, hilbertMultiplier, Real.sign_of_pos (show 0 < ξ from hξ)]
    have hm : Tendsto M (𝓝[<] 0) (𝓝 (I * dlmfFourier f 0)) := by
      refine ((hFc.tendsto 0).const_mul I).mono_left nhdsWithin_le_nhds |>.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ξ hξ
      simp [hMdef, hilbertMultiplier, Real.sign_of_neg (show ξ < 0 from hξ)]
    refine hlim hp hm ?_
    rw [Real.sign_zero]; push_cast; ring
  · have hev : ∀ᶠ ξ in 𝓝 x, M ξ = -I * dlmfFourier f ξ := by
      filter_upwards [Ioi_mem_nhds hx] with ξ hξ
      simp [hMdef, hilbertMultiplier, Real.sign_of_pos (show 0 < ξ from hξ)]
    have h := hR _ hev
    refine hlim (h.mono_left nhdsWithin_le_nhds) (h.mono_left nhdsWithin_le_nhds) ?_
    rw [Real.sign_of_pos hx]; push_cast; ring

/-- **DLMF 1.14.46**: for `f` continuously differentiable and vanishing outside a bounded
interval, `(1/√(2π)) ∫ ℋf(u) e^{iux} du = −i sign(x) 𝓕f(x)` (the integral as `lim ∫_{−R}^R`). -/
theorem dlmf_1_14_46 {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (x : ℝ) :
    Tendsto (fun R : ℝ => ((√(2 * π) : ℝ) : ℂ)⁻¹ *
      ∫ u in (-R)..R, hilbert f u * cexp (I * u * x)) atTop
      (𝓝 (-I * Real.sign x * dlmfFourier f x)) := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hs
  have ht : Integrable fun t => |t| * ‖f t‖ :=
    (continuous_abs.mul hf.continuous.norm).integrable_of_hasCompactSupport
      (hs.norm.mul_left)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K (dlmfFourier f) (Icc (x - 1) (x + 1)) :=
    ⟨_, (lipschitzWith_dlmfFourier hfi ht).lipschitzOnWith⟩
  have hbv : BoundedVariationOn (dlmfFourier f) (Icc (x - 1) (x + 1)) := by
    have := hK.locallyBoundedVariationOn (x - 1) (x + 1) ⟨le_rfl, by linarith⟩
      ⟨by linarith, le_rfl⟩
    rwa [inter_self] at this
  exact dlmf_1_14_46_of_bv hfi (integrable_dlmfFourier_of_contDiff hf hs) hf.continuous hbv

/-! ### Inequalities (1.14.45): the case `p = 2` -/

theorem memLp_two_of_bound {g : ℝ → ℂ} (hi : Integrable g) {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) :
    MemLp g 2 := by
  refine (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
    ((hi.norm.const_mul C).mono' (hi.aestronglyMeasurable.norm.pow 2) (ae_of_all _ fun x => ?_))
  rw [Real.norm_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- **DLMF 1.14.45** for `p = 2`, where `A₂ = tan(π/4) = 1` and the inequality is an equality:
for integrable continuous `f` with integrable `𝓕f`, `∫ |ℋf|² = ∫ |f|²` (Plancherel, since
`|−i sign(ξ) 𝓕f(ξ)| = |𝓕f(ξ)|` for `ξ ≠ 0`). -/
theorem dlmf_1_14_45_two {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (dlmfFourier f))
    (hc : Continuous f) :
    Integrable (fun x => ‖hilbert f x‖ ^ 2) ∧ ∫ x, ‖hilbert f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  have hM := integrable_hilbertMultiplier hF
  have hMb : ∀ ξ, ‖hilbertMultiplier f ξ‖ ≤ (√(2 * π))⁻¹ * ∫ t, ‖f t‖ := fun ξ => by
    rw [hilbertMultiplier, norm_mul]
    calc ‖-I * (Real.sign ξ : ℂ)‖ * ‖dlmfFourier f ξ‖ ≤ 1 * ‖dlmfFourier f ξ‖ :=
          mul_le_mul_of_nonneg_right (norm_neg_I_mul_sign_le ξ) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact dlmf_1_14_2 f ξ
  have hfb : ∀ u, ‖f u‖ ≤ (√(2 * π))⁻¹ * ∫ t, ‖dlmfFourier f t‖ := fun u => by
    rw [congrFun (eq_dlmfFourier_neg hf hF hc) u]; exact dlmf_1_14_2 _ _
  obtain ⟨h1, h2⟩ := dlmf_1_14_8 hM (memLp_two_of_bound hM hMb)
  obtain ⟨-, h4⟩ := dlmf_1_14_8 hf (memLp_two_of_bound hf hfb)
  rw [hilbert_eq_of_fourier hf hF hc]
  refine ⟨h1.comp_neg, ?_⟩
  rw [integral_neg_eq_self (fun x => ‖dlmfFourier (hilbertMultiplier f) x‖ ^ 2), h2, ← h4]
  refine integral_congr_ae (ae_ne_zero.mono fun ξ hξ => ?_)
  simp only [hilbertMultiplier, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rcases Real.sign_apply_eq_of_ne_zero ξ hξ with h | h <;> rw [h] <;> norm_num

end Azurite.DLMF
