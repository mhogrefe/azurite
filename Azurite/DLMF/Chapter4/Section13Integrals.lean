/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Moments
import Azurite.DLMF.Chapter4.Section13Taylor
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# DLMF §4.13: the integral representations 4.13.15–4.13.16

With `a(t) = (sin t/t) e^{t cot t}` (`lamA`), on `ℂ ∖ (−∞, −e⁻¹]`:

* 4.13.16 (`dlmf_4_13_16`): `W₀(z) = (1/π) ∫₀^π ln(1 + z a(t)) dt`;
* 4.13.15 (`dlmf_4_13_15`):
  `W₀(z) = (z/π) ∫₀^π ((1 − t cot t)² + t²)/(z + t e^{−t cot t} csc t) dt`.

4.13.16 holds on `|z| < e⁻¹` by integrating the series of `ln(1 + z a)` termwise against the
moments `integral_lamA_pow`, which reproduces 4.13.5; both sides are analytic on
`ℂ ∖ (−∞, −e⁻¹]` (`1 + z s ∉ (−∞, 0]` for `0 ≤ s ≤ e`), so they agree there. 4.13.15 follows by
integrating by parts (`−t a′ = ((1 − t cot t)² + t²) a`).
-/

open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped Real Nat Interval

namespace Azurite.DLMF

/-! ### 4.13.16 near `0` -/

theorem integral_ofReal_lamA_pow (n : ℕ) :
    ∫ t in (0 : ℝ)..π, ((lamA t : ℂ)) ^ n = ((π * n ^ n / n ! : ℝ) : ℂ) := by
  rw [← integral_lamA_pow n, ← intervalIntegral.integral_ofReal]
  push_cast; rfl

theorem lamA_mem_Icc_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι 0 π) : 0 ≤ lamA t ∧ lamA t ≤ Real.exp 1 := by
  rw [uIoc_of_le Real.pi_pos.le] at ht
  exact lamA_mem_Icc (abs_le.mpr ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)

/-- 4.13.16 for `|z| < e⁻¹`, via the series of `ln(1 + z a)` and the moments. -/
theorem dlmf_4_13_16_small {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    lambertW 0 z = 1 / π * ∫ t in (0 : ℝ)..π, log (1 + z * lamA t) := by
  set r := ‖z‖ * Real.exp 1
  have hr : r < 1 := by
    have := mul_lt_mul_of_pos_right hz (Real.exp_pos 1)
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have hr0 : 0 ≤ r := by positivity
  set F : ℕ → ℝ → ℂ := fun n t => (-1) ^ (n + 1) * (z * lamA t) ^ n / n
  have hnorm : ∀ t ∈ Ι 0 π, ‖z * lamA t‖ ≤ r := by
    intro t ht
    obtain ⟨h0, h1⟩ := lamA_mem_Icc_of_mem_uIoc ht
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg z)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := π) (F := F) (f := fun t => log (1 + z * lamA t)) (fun n _ => r ^ n)
    (fun n => ((measurable_const.mul ((measurable_const.mul
      (Complex.measurable_ofReal.comp measurable_lamA)).pow_const n)).div_const _ :
      Measurable (F n)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t ht => by
      have h1 := hnorm t ht
      simp only [F, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [div_le_iff₀ (by exact_mod_cast hn)]
        calc (‖z‖ * ‖(lamA t : ℂ)‖) ^ n = ‖z * lamA t‖ ^ n := by rw [norm_mul]
          _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) h1 n
          _ ≤ r ^ n * n := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hn))
    (Eventually.of_forall fun _ _ => summable_geometric_of_lt_one hr0 hr)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht => by
      have := hasSum_taylorSeries_log (z := z * lamA t) ((hnorm t ht).trans_lt hr)
      exact this)
  -- the terms: `∫ F n = (−1)^{n+1} zⁿ/n · π nⁿ/n!`
  have hterm : ∀ n, ∫ t in (0 : ℝ)..π, F n t =
      (-1) ^ (n + 1) * z ^ n / n * ((π * n ^ n / n ! : ℝ) : ℂ) := by
    intro n
    simp only [F, mul_pow]
    rw [← integral_ofReal_lamA_pow n, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    ring
  simp only [hterm] at hsum
  have hsum' := hsum.mul_left (1 / π : ℂ)
  -- compare with 4.13.5
  have h5 := dlmf_4_13_5 hz
  rw [← hasSum_nat_add_iff' 1] at hsum'
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, mul_zero,
    zero_mul, sub_zero] at hsum'
  refine h5.unique ?_
  convert hsum' using 1
  funext n
  rw [neg_pow]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hf : ((n + 1)! : ℂ) = (n + 1 : ℕ) * (n ! : ℂ) := by push_cast [Nat.factorial_succ]; ring
  push_cast
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-! ### Analyticity on `ℂ ∖ (−∞, −e⁻¹]` -/

/-- `lamA` is continuous on `[0, π]` (`lamA π = 0`). -/
theorem continuousOn_lamA_Icc : ContinuousOn lamA (Icc 0 π) := by
  intro t ht
  rcases ht.2.lt_or_eq with hlt | rfl
  · exact (continuousOn_lamA.continuousAt (isOpen_lt continuous_abs continuous_const |>.mem_nhds
      (show |t| < π by rw [abs_of_nonneg ht.1]; exact hlt))).continuousWithinAt
  · have hπ := Real.pi_pos
    have hval : lamA π = 0 := by
      rw [lamA, sinc_eq_zero_of_abs_eq_pi (abs_of_pos hπ), zero_mul]
    rw [ContinuousWithinAt, hval]
    have hs : Tendsto Real.sinc (𝓝[Icc 0 π] π) (𝓝 0) := by
      have := (Real.continuous_sinc.tendsto π).mono_left (nhdsWithin_le_nhds (s := Icc 0 π))
      rwa [sinc_eq_zero_of_abs_eq_pi (abs_of_pos hπ)] at this
    refine squeeze_zero' ?_ ?_ hs
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (lamA_mem_Icc (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)).1
    · have hev : ∀ᶠ t in 𝓝[Icc 0 π] π, π / 2 ≤ t :=
        nhdsWithin_le_nhds (Ici_mem_nhds (by linarith))
      filter_upwards [hev, self_mem_nhdsWithin] with t h1 h2
      have hc : Real.cos t ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith [h2.2])
      have hs0 : 0 ≤ Real.sinc t := by
        rcases h2.2.lt_or_eq with h | h
        · exact (sinc_pos_of_abs_lt (by rw [abs_of_nonneg h2.1]; exact h)).le
        · rw [h, sinc_eq_zero_of_abs_eq_pi (abs_of_pos hπ)]
      have he : Real.exp (Real.cos t / Real.sinc t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hc hs0)
      calc lamA t ≤ Real.sinc t * 1 := mul_le_mul_of_nonneg_left he hs0
        _ = Real.sinc t := mul_one _

theorem lamA_mem_Icc_of_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 π) : 0 ≤ lamA t ∧ lamA t ≤ Real.exp 1 :=
  lamA_mem_Icc (abs_le.mpr ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)

theorem one_add_mul_lamA_mem_slitPlane {z : ℂ} (hz : z ∈ cutW0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ Real.exp 1) : 1 + z * s ∈ slitPlane := by
  rcases hs0.lt_or_eq with hpos | rfl
  · rw [mem_slitPlane_iff]
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at h1
    simp only [add_im, one_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add] at h2
    have hzi : z.im = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hpos.ne'
    apply hz
    refine ⟨hzi, ?_⟩
    have h3 : z.re * s ≤ -1 := by linarith
    have h4 : -1 / s ≤ -Real.exp (-1) := by
      rw [div_le_iff₀ hpos, Real.exp_neg]
      have : (Real.exp 1)⁻¹ * s ≤ 1 := by
        rw [inv_mul_le_iff₀ (Real.exp_pos 1)]; linarith
      linarith
    have h5 : z.re ≤ -1 / s := by rw [le_div_iff₀ hpos]; exact h3
    linarith
  · simp

/-- A uniform lower bound for `|1 + z s|`, `z` near `z₀ ∈ ℂ ∖ (−∞, −e⁻¹]`, `0 ≤ s ≤ e`. -/
theorem exists_norm_one_add_mul_lamA_ge {z₀ : ℂ} (hz₀ : z₀ ∈ cutW0) :
    ∃ ε > 0, ∃ δ > 0, Metric.ball z₀ ε ⊆ cutW0 ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ s : ℝ, 0 ≤ s → s ≤ Real.exp 1 → δ ≤ ‖1 + z * s‖ := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp isOpen_cutW0 z₀ hz₀
  set M := ‖z₀‖ + ε₀
  have hM : 0 < M := by positivity
  refine ⟨ε₀ / 2, by positivity, min (1 / 2) (ε₀ / (4 * M)), by positivity,
    (Metric.ball_subset_ball (by linarith)).trans hball, fun z hz s hs0 hs => ?_⟩
  have hzM : ‖z‖ ≤ M := by
    have := norm_le_norm_add_norm_sub' z z₀
    rw [Metric.mem_ball, dist_eq_norm] at hz
    simp only [M]; linarith [norm_sub_rev z z₀]
  by_cases hsmall : s ≤ 1 / (2 * M)
  · have h1 : ‖z * s‖ ≤ 1 / 2 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      calc ‖z‖ * s ≤ M * (1 / (2 * M)) := mul_le_mul hzM hsmall hs0 hM.le
        _ = 1 / 2 := by field_simp
    have h2 : 1 - ‖z * s‖ ≤ ‖1 + z * s‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(z * s))
      rw [norm_one, norm_neg, sub_neg_eq_add] at this; exact this
    exact (min_le_left _ _).trans (by linarith)
  · push Not at hsmall
    have hpos : 0 < s := lt_trans (by positivity) hsmall
    -- `−1/s ∉ ℂ ∖ (−∞, −e⁻¹]`, so it is at distance `≥ ε₀` from `z₀`
    have hout : ((-1 / s : ℝ) : ℂ) ∉ cutW0 := by
      intro h
      apply h
      refine ⟨by simp, ?_⟩
      simp only [ofReal_re]
      rw [div_le_iff₀ hpos, Real.exp_neg]
      have : (Real.exp 1)⁻¹ * s ≤ 1 := by rw [inv_mul_le_iff₀ (Real.exp_pos 1)]; linarith
      linarith
    have hd : ε₀ ≤ dist ((-1 / s : ℝ) : ℂ) z₀ := by
      by_contra h; push Not at h; exact hout (hball (Metric.mem_ball.mpr h))
    have hd2 : ε₀ / 2 ≤ ‖z + 1 / s‖ := by
      rw [Metric.mem_ball] at hz
      have := dist_triangle ((-1 / s : ℝ) : ℂ) z z₀
      have he : dist ((-1 / s : ℝ) : ℂ) z = ‖z + 1 / s‖ := by
        rw [dist_comm, dist_eq_norm]; congr 1; push_cast; ring
      linarith
    have heq : ‖1 + z * s‖ = s * ‖z + 1 / s‖ := by
      rw [show (1 : ℂ) + z * s = s * (z + 1 / s) by
          rw [mul_add, mul_one_div_cancel (ofReal_ne_zero.mpr hpos.ne')]; ring, norm_mul, norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
    rw [heq]
    calc min (1 / 2) (ε₀ / (4 * M)) ≤ ε₀ / (4 * M) := min_le_right _ _
      _ = 1 / (2 * M) * (ε₀ / 2) := by field_simp; ring
      _ ≤ s * ‖z + 1 / s‖ := mul_le_mul hsmall.le hd2 (by positivity) hpos.le

theorem continuousOn_log_one_add_mul {z : ℂ} (hz : z ∈ cutW0) :
    ContinuousOn (fun t => log (1 + z * lamA t)) (Icc 0 π) :=
  (continuousOn_const.add (continuousOn_const.mul
    (continuous_ofReal.comp_continuousOn continuousOn_lamA_Icc))).clog fun _ ht =>
      one_add_mul_lamA_mem_slitPlane hz (lamA_mem_Icc_of_mem_Icc ht).1
        (lamA_mem_Icc_of_mem_Icc ht).2

theorem uIoc_zero_pi_subset : Ι 0 π ⊆ Icc 0 π := by
  rw [uIoc_of_le Real.pi_pos.le]; exact Ioc_subset_Icc_self

/-- `z ↦ ∫₀^π ln(1 + z a(t)) dt` is analytic on `ℂ ∖ (−∞, −e⁻¹]`. -/
theorem differentiableOn_integral_log :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..π, log (1 + z * lamA t)) cutW0 := by
  intro z₀ hz₀
  obtain ⟨ε, hε, δ, hδ, hsub, hbd⟩ := exists_norm_one_add_mul_lamA_ge hz₀
  have hπ := Real.pi_pos
  have hmeas : ∀ z ∈ cutW0, AEStronglyMeasurable (fun t => log (1 + z * lamA t))
      (volume.restrict (Ι 0 π)) := fun z hz =>
    ((continuousOn_log_one_add_mul hz).mono uIoc_zero_pi_subset).aestronglyMeasurable
      measurableSet_uIoc
  have hF' : ContinuousOn (fun t => (lamA t : ℂ) / (1 + z₀ * lamA t)) (Icc 0 π) :=
    (continuous_ofReal.comp_continuousOn continuousOn_lamA_Icc).div
      (continuousOn_const.add (continuousOn_const.mul
        (continuous_ofReal.comp_continuousOn continuousOn_lamA_Icc))) fun t ht => by
          have := hbd z₀ (Metric.mem_ball_self hε) (lamA t) (lamA_mem_Icc_of_mem_Icc ht).1
            (lamA_mem_Icc_of_mem_Icc ht).2
          exact norm_pos_iff.mp (lt_of_lt_of_le hδ this)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := π)
    (F := fun z t => log (1 + z * lamA t)) (F' := fun z t => (lamA t : ℂ) / (1 + z * lamA t))
    (x₀ := z₀) (bound := fun _ => Real.exp 1 / δ) (Metric.ball_mem_nhds z₀ hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hε) fun z hz => hmeas z (hsub hz))
    ((continuousOn_log_one_add_mul hz₀).intervalIntegrable_of_Icc hπ.le)
    ((hF'.mono uIoc_zero_pi_subset).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun t ht z hz => by
      obtain ⟨h0, h1⟩ := lamA_mem_Icc_of_mem_Icc (uIoc_zero_pi_subset ht)
      have hb := hbd z hz (lamA t) h0 h1
      rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      exact div_le_div₀ (Real.exp_pos 1).le h1 hδ hb)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht z hz => by
      obtain ⟨h0, h1⟩ := lamA_mem_Icc_of_mem_Icc (uIoc_zero_pi_subset ht)
      have hs := one_add_mul_lamA_mem_slitPlane (hsub hz) h0 h1
      have := (((hasDerivAt_id z).mul_const (lamA t : ℂ)).const_add 1).clog hs
      simpa using this)
  exact h.2.differentiableAt.differentiableWithinAt

/-! ### 4.13.16 -/

theorem starConvex_cutW0 : StarConvex ℝ 0 cutW0 := by
  intro y hy a b _ hb hab
  rintro ⟨him, hre⟩
  simp only [smul_zero, zero_add, smul_im, smul_re, smul_eq_mul] at him hre
  rcases hb.lt_or_eq with hb0 | rfl
  · apply hy
    have hyi : y.im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h hb0.ne'
      · exact h
    refine ⟨hyi, ?_⟩
    have hb1 : b ≤ 1 := by linarith
    have he := Real.exp_pos (-1)
    by_contra h; push Not at h
    nlinarith
  · simp at hre; linarith [Real.exp_pos (-1)]

theorem isPreconnected_cutW0 : IsPreconnected cutW0 :=
  (starConvex_cutW0.isPathConnected zero_mem_cutW0).isConnected.isPreconnected

/-- 4.13.16 with `a = lamA`, on `ℂ ∖ (−∞, −e⁻¹]`. -/
theorem lambertW_zero_eq_integral_log {z : ℂ} (hz : z ∈ cutW0) :
    lambertW 0 z = 1 / π * ∫ t in (0 : ℝ)..π, log (1 + z * lamA t) := by
  have hF : AnalyticOnNhd ℂ (fun z => 1 / (π : ℂ) * ∫ t in (0 : ℝ)..π, log (1 + z * lamA t))
      cutW0 :=
    (differentiableOn_integral_log.const_mul _).analyticOnNhd isOpen_cutW0
  have hfg : lambertW 0 =ᶠ[𝓝 0]
      fun z => 1 / (π : ℂ) * ∫ t in (0 : ℝ)..π, log (1 + z * lamA t) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-1))] with z hz
    exact dlmf_4_13_16_small (by simpa using hz)
  exact analyticOnNhd_lambertW_zero.eqOn_of_preconnected_of_eventuallyEq hF isPreconnected_cutW0
    zero_mem_cutW0 hfg hz

theorem lamA_eq {t : ℝ} (ht : t ∈ Ioo 0 π) :
    lamA t = Real.sin t / t * Real.exp (t * Real.cot t) := by
  have h0 : t ≠ 0 := ht.1.ne'
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  rw [lamA, Real.sinc_of_ne_zero h0, Real.cot_eq_cos_div_sin]
  congr 2
  field_simp

theorem ae_ne_pi : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π := by
  rw [ae_iff]; simp

theorem mem_Ioo_of_uIoc {t : ℝ} (h1 : t ≠ π) (h2 : t ∈ Ι 0 π) : t ∈ Ioo 0 π := by
  rw [uIoc_of_le Real.pi_pos.le] at h2
  exact ⟨h2.1, lt_of_le_of_ne h2.2 h1⟩

/-- **DLMF 4.13.16**: `W₀(z) = (1/π) ∫₀^π ln(1 + z (sin t/t) e^{t cot t}) dt`, on
`ℂ ∖ (−∞, −e⁻¹]`. -/
theorem dlmf_4_13_16 {z : ℂ} (hz : z ∈ cutW0) :
    lambertW 0 z = 1 / π * ∫ t in (0 : ℝ)..π,
      log (1 + z * (Real.sin t / t * Real.exp (t * Real.cot t) : ℝ)) := by
  rw [lambertW_zero_eq_integral_log hz]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_pi] with t h1 h2
  rw [lamA_eq (mem_Ioo_of_uIoc h1 h2)]

/-! ### 4.13.15 -/

/-- `(1 − t cot t)² + t²`, the numerator of 4.13.15. -/
noncomputable def nFun (t : ℝ) : ℝ := (1 - t * Real.cot t) ^ 2 + t ^ 2

/-- `a′ = −((1 − t cot t)² + t²) a / t` on `(0, π)`. -/
theorem hasDerivAt_lamA {t : ℝ} (ht : t ∈ Ioo 0 π) :
    HasDerivAt lamA (-(nFun t * lamA t) / t) t := by
  have h0 : t ≠ 0 := ht.1.ne'
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hev : (fun x => Real.sin x / x * Real.exp (x * Real.cos x / Real.sin x)) =ᶠ[𝓝 t] lamA := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    rw [lamA_eq hx, Real.cot_eq_cos_div_sin, mul_div_assoc]
  have h1 : HasDerivAt (fun x => Real.sin x / x) ((Real.cos t * t - Real.sin t * 1) / t ^ 2) t :=
    (Real.hasDerivAt_sin t).div (hasDerivAt_id t) h0
  have h2 : HasDerivAt (fun x => x * Real.cos x / Real.sin x)
      (((1 * Real.cos t + t * -Real.sin t) * Real.sin t - t * Real.cos t * Real.cos t) /
        Real.sin t ^ 2) t :=
    ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)).div (Real.hasDerivAt_sin t) hs
  refine (h1.mul h2.exp).congr_of_eventuallyEq hev.symm |>.congr_deriv ?_
  rw [nFun, lamA_eq ht, Real.cot_eq_cos_div_sin]
  field_simp
  ring

theorem cos_div_sinc_le_one {t : ℝ} (ht : |t| < π) : Real.cos t / Real.sinc t ≤ 1 := by
  have hs := sinc_pos_of_abs_lt ht
  by_cases hc : Real.cos t ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg hc hs.le).trans zero_le_one
  · push Not at hc
    have hpi : |t| < π / 2 := by
      by_contra h; push Not at h
      exact absurd (cos_nonpos_of_le_abs le_rfl h ht.le) (not_le.mpr hc)
    rw [div_le_one hs]; exact Real.cos_le_sinc hpi

theorem mul_cot_eq {t : ℝ} (ht : t ∈ Ioo 0 π) : t * Real.cot t = Real.cos t / Real.sinc t := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  rw [Real.cot_eq_cos_div_sin, Real.sinc_of_ne_zero ht.1.ne']
  field_simp

/-- `0 ≤ ((1 − t cot t)² + t²) a(t) ≤ (2 + π²) e` on `(0, π)`. -/
theorem nFun_mul_lamA_mem {t : ℝ} (ht : t ∈ Ioo 0 π) :
    0 ≤ nFun t * lamA t ∧ nFun t * lamA t ≤ (2 + π ^ 2) * Real.exp 1 := by
  have hab : |t| < π := by rw [abs_of_pos ht.1]; exact ht.2
  have hs := sinc_pos_of_abs_lt hab
  set u := Real.cos t / Real.sinc t
  have hu : u ≤ 1 := cos_div_sinc_le_one hab
  have hN : nFun t = (1 - u) ^ 2 + t ^ 2 := by rw [nFun, mul_cot_eq ht]
  have hA : lamA t = Real.sinc t * Real.exp u := rfl
  have hN0 : 0 ≤ nFun t := by rw [hN]; positivity
  refine ⟨mul_nonneg hN0 (by rw [hA]; positivity), ?_⟩
  -- `(1 − u)² eᵘ ≤ 2e` (with `v = 1 − u ≥ 0`, `v² ≤ 2eᵛ`)
  have hv : (1 - u) ^ 2 * Real.exp u ≤ 2 * Real.exp 1 := by
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 1 - u)
    have he : Real.exp u * Real.exp (1 - u) = Real.exp 1 := by rw [← Real.exp_add]; ring_nf
    have hpos := Real.exp_pos u
    nlinarith [sq_nonneg (1 - u)]
  have hexp : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.mpr hu
  have ht2 : t ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ ht.1.le ht.2.le 2
  have hsle := Real.sinc_le_one t
  rw [hN, hA]
  calc ((1 - u) ^ 2 + t ^ 2) * (Real.sinc t * Real.exp u)
      ≤ ((1 - u) ^ 2 + t ^ 2) * (1 * Real.exp u) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsle (Real.exp_pos u).le
    _ = (1 - u) ^ 2 * Real.exp u + t ^ 2 * Real.exp u := by ring
    _ ≤ 2 * Real.exp 1 + π ^ 2 * Real.exp 1 := by
        gcongr
    _ = (2 + π ^ 2) * Real.exp 1 := by ring

theorem measurable_nFun : Measurable nFun := by
  have : nFun = fun t => (1 - t * (Real.cos t / Real.sin t)) ^ 2 + t ^ 2 := by
    funext t; rw [nFun, Real.cot_eq_cos_div_sin]
  rw [this]
  exact ((measurable_const.sub (measurable_id.mul
    (Real.measurable_cos.div Real.measurable_sin))).pow_const 2).add (measurable_id.pow_const 2)

theorem lamA_pi : lamA π = 0 := by
  rw [lamA, sinc_eq_zero_of_abs_eq_pi (abs_of_pos Real.pi_pos), zero_mul]

/-- Integration by parts: `∫₀^π ln(1 + z a) = z ∫₀^π ((1 − t cot t)² + t²) a/(1 + z a)`. -/
theorem integral_log_eq_mul_integral {z : ℂ} (hz : z ∈ cutW0) :
    ∫ t in (0 : ℝ)..π, log (1 + z * lamA t) =
      z * ∫ t in (0 : ℝ)..π, ((nFun t * lamA t : ℝ) : ℂ) / (1 + z * lamA t) := by
  obtain ⟨ε, hε, δ, hδ, -, hbd⟩ := exists_norm_one_add_mul_lamA_ge hz
  have hbz : ∀ s : ℝ, 0 ≤ s → s ≤ Real.exp 1 → δ ≤ ‖1 + z * s‖ :=
    hbd z (Metric.mem_ball_self hε)
  have hπ := Real.pi_pos
  set g : ℝ → ℂ := fun t => ((nFun t * lamA t : ℝ) : ℂ) / (1 + z * lamA t)
  have hlog := (continuousOn_log_one_add_mul hz).intervalIntegrable_of_Icc (μ := volume) hπ.le
  have hgi : IntervalIntegrable g volume 0 π := by
    refine (intervalIntegrable_const (μ := volume) (c := (2 + π ^ 2) * Real.exp 1 / δ)).mono_fun
      ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (measurable_nFun.mul measurable_lamA)).div
        (measurable_const.add (measurable_const.mul
          (Complex.measurable_ofReal.comp measurable_lamA)))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
      have hC : 0 ≤ (2 + π ^ 2) * Real.exp 1 / δ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hC]
      by_cases htπ : t = π
      · simp [g, htπ, lamA_pi, hC]
      have hIoo := mem_Ioo_of_uIoc htπ ht
      obtain ⟨h0, h1⟩ := lamA_mem_Icc_of_mem_Icc (uIoc_zero_pi_subset ht)
      obtain ⟨n0, n1⟩ := nFun_mul_lamA_mem hIoo
      have hb := hbz (lamA t) h0 h1
      simp only [g, norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg n0]
      exact div_le_div₀ (by positivity) n1 hδ hb
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t : ℝ => (t : ℂ) * log (1 + z * lamA t))
    (f' := fun t => log (1 + z * lamA t) - z * g t) hπ.le
    ((continuous_ofReal.comp_continuousOn continuousOn_id).mul (continuousOn_log_one_add_mul hz))
    (fun t ht => by
      have h0 : t ≠ 0 := ht.1.ne'
      obtain ⟨a0, a1⟩ := lamA_mem_Icc_of_mem_Icc (Ioo_subset_Icc_self ht)
      have hs := one_add_mul_lamA_mem_slitPlane hz a0 a1
      have hL := (((hasDerivAt_lamA ht).ofReal_comp.const_mul z).const_add 1).clog_real hs
      have hφ := (hasDerivAt_id t).ofReal_comp.mul hL
      refine hφ.congr_deriv ?_
      have hne : (1 + z * lamA t) ≠ 0 := slitPlane_ne_zero hs
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr h0
      simp only [g, id]
      push_cast
      field_simp
      ring)
    (hlog.sub (hgi.const_mul z))
  simp only [lamA_pi, ofReal_zero, mul_zero, add_zero, log_one, ofReal_zero, zero_mul,
    sub_zero] at hFTC
  rw [integral_sub hlog (hgi.const_mul z), intervalIntegral.integral_const_mul] at hFTC
  linear_combination hFTC

/-- **DLMF 4.13.15**: `W₀(z) = (z/π) ∫₀^π ((1 − t cot t)² + t²)/(z + t e^{−t cot t} csc t) dt`,
on `ℂ ∖ (−∞, −e⁻¹]`. -/
theorem dlmf_4_13_15 {z : ℂ} (hz : z ∈ cutW0) :
    lambertW 0 z = z / π * ∫ t in (0 : ℝ)..π,
      (((1 - t * Real.cot t) ^ 2 + t ^ 2 : ℝ) : ℂ) /
        (z + (t * Real.exp (-(t * Real.cot t)) * (Real.sin t)⁻¹ : ℝ)) := by
  rw [lambertW_zero_eq_integral_log hz, integral_log_eq_mul_integral hz,
    show ∀ a : ℂ, 1 / (π : ℂ) * (z * a) = z / π * a from fun a => by ring]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_pi] with t h1 h2
  have ht := mem_Ioo_of_uIoc h1 h2
  obtain ⟨a0, a1⟩ := lamA_mem_Icc_of_mem_Icc (Ioo_subset_Icc_self ht)
  have hne : (1 + z * lamA t) ≠ 0 := slitPlane_ne_zero (one_add_mul_lamA_mem_slitPlane hz a0 a1)
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hb : t * Real.exp (-(t * Real.cot t)) * (Real.sin t)⁻¹ = (lamA t)⁻¹ := by
    rw [lamA_eq ht, Real.exp_neg]
    field_simp
  have ha : lamA t ≠ 0 := by
    rw [lamA_eq ht]; exact mul_ne_zero (div_ne_zero hs ht.1.ne') (Real.exp_pos _).ne'
  have ha' : (lamA t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  have hden : z + (((lamA t)⁻¹ : ℝ) : ℂ) = (1 + z * lamA t) / lamA t := by
    push_cast; field_simp; ring
  rw [hb, hden, div_div_eq_mul_div, nFun]
  push_cast
  ring

end Azurite.DLMF
