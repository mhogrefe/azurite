/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section15FourierIntegrals
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# DLMF §1.18(vi): the Sokhotski–Plemelj formula 1.18.54

https://dlmf.nist.gov/1.18.vi

* The Poisson integral of an integrable `f` tends to `f(x)` at every point of continuity
  (`tendsto_poissonInt_of_continuousAt`, via Mathlib's peak-function theorem).
* 1.18.54: `lim_{ε→0+} ∫ f(y)/(x ± iε − y) dy = ⨍ f(y)/(x − y) dy ∓ iπ f(x)` for `f`
  integrable, continuous at `x`, whose principal value exists at `x` (`dlmf_1_18_54`, with
  `⨍ f(y)/(x − y) dy = −π ℋf(x)` in terms of §1.14's Hilbert transform).
* **DLMF imprecision**: DLMF states 1.18.54 for `f ∈ C(X)`. Continuity does not even make the
  integrals exist: for `f = 1` on `X = [0, ∞)` the integrand is not integrable
  (`dlmf_1_18_54_counterexample`). Nor does continuity guarantee the principal value: e.g.
  `f(y) = sign(y − x)/|log|y − x||` near `x` is continuous, but its principal value diverges.
  That second example is not formalized.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The Poisson integral at points of continuity -/

theorem tendsto_tail_pK :
    Tendsto (fun ε => ∫ s in {s : ℝ | 1 ≤ |s|}, pK ε s) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_tail_dilate (integrable_pK one_pos) one_pos).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp]
  exact setIntegral_congr_fun (measurableSet_le measurable_const continuous_abs.measurable)
    fun s _ => (pK_dilate hε s).symm

theorem pK_le_of_le {ε δ s : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hs : δ ≤ |s|) :
    pK ε s ≤ ε / (π * δ ^ 2) := by
  have hπ := Real.pi_pos
  unfold pK
  have : δ ^ 2 ≤ s ^ 2 + ε ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  gcongr

/-- The Poisson integral of an integrable `f` tends to `f(x)` at every point of continuity. -/
theorem tendsto_poissonInt_of_continuousAt {f : ℝ → ℂ} (hf : Integrable f) {x : ℝ}
    (hc : ContinuousAt f x) : Tendsto (fun ε => poissonInt ε f x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hπ := Real.pi_pos
  have hball : ∀ ε, 0 < ε → ∫ t in Metric.ball x 1, pK ε (t - x) =
      1 - ∫ s in {s : ℝ | 1 ≤ |s|}, pK ε s := fun ε hε => by
    have hc : (Metric.ball (0 : ℝ) 1)ᶜ = {s : ℝ | 1 ≤ |s|} := by
      ext s; simp [Metric.mem_ball]
    have h1 := integral_add_compl (s := Metric.ball (0 : ℝ) 1) measurableSet_ball
      (integrable_pK hε)
    rw [integral_pK hε, hc] at h1
    have h2 : ∫ t in Metric.ball x 1, pK ε (t - x) = ∫ s in Metric.ball (0 : ℝ) 1, pK ε s := by
      rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
        ← integral_sub_right_eq_self (fun s => (Metric.ball (0 : ℝ) 1).indicator (pK ε) s) x]
      congr 1
      funext t
      by_cases ht : t ∈ Metric.ball x 1
      · have ht' : t - x ∈ Metric.ball (0 : ℝ) 1 := by
          simpa [Metric.mem_ball, Real.dist_eq] using ht
        simp [indicator_of_mem ht, indicator_of_mem ht']
      · have ht' : t - x ∉ Metric.ball (0 : ℝ) 1 := by
          simpa [Metric.mem_ball, Real.dist_eq] using ht
        simp [indicator_of_notMem ht, indicator_of_notMem ht']
    rw [h2]
    linarith
  have key := tendsto_integral_peak_smul_of_integrable_of_tendsto (μ := volume)
    (l := 𝓝[>] (0 : ℝ)) (φ := fun ε t => pK ε (t - x)) (x₀ := x) (t := Metric.ball x 1)
    measurableSet_ball (Metric.ball_mem_nhds x one_pos) measure_ball_lt_top.ne
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) t using pK_nonneg hε _)
    (fun u hu hxu => by
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hu x hxu
      rw [Metric.tendstoUniformlyOn_iff]
      intro e he
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show 0 < e * (π * δ ^ 2) by
        positivity)] with ε (hε : 0 < ε) hε' t ht
      have htδ : δ ≤ |t - x| := by
        by_contra h
        exact ht (hsub (by rw [Metric.mem_ball, Real.dist_eq]; linarith))
      rw [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (pK_nonneg hε _)]
      calc pK ε (t - x) ≤ ε / (π * δ ^ 2) := pK_le_of_le hε hδ htδ
        _ < e := by rw [div_lt_iff₀ (by positivity)]; exact hε'.2)
    (by
      have h := tendsto_tail_pK.const_sub 1
      rw [sub_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (hball ε hε).symm)
    (Eventually.of_forall fun ε =>
      ((by unfold pK; fun_prop) : Measurable fun t : ℝ => pK ε (t - x)).aestronglyMeasurable) hf hc
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [poissonInt_eq_pK]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  show pK ε (t - x) • f t = _
  rw [Complex.real_smul]

/-! ### 1.18.54 -/

theorem integrable_realKernel_mul {f : ℝ → ℂ} (hf : Integrable f) {k : ℝ → ℝ}
    (hk : Continuous k) {C : ℝ} (hkC : ∀ y, |k y| ≤ C) :
    Integrable fun y => (k y : ℂ) * f y :=
  hf.bdd_mul (c := C) (Complex.continuous_ofReal.comp hk).aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Complex.norm_real]; exact hkC y)

theorem one_div_sokhotski {x y ε : ℝ} (hε : 0 < ε) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    1 / ((x : ℂ) + σ * ε * I - y) = -((((y - x) / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) -
      σ * I * (((ε / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) := by
  have hD : 0 < (y - x) ^ 2 + ε ^ 2 := by positivity
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hz : ((x : ℂ) + σ * ε * I - y) * ((x - y : ℂ) - σ * ε * I) = ((y - x) ^ 2 + ε ^ 2 : ℝ) := by
    push_cast
    ring_nf
    rw [I_sq, hσ2]
    ring
  have hz0 : ((x : ℂ) + σ * ε * I - y) ≠ 0 := by
    intro h; rw [h, zero_mul] at hz
    exact hD.ne' (by exact_mod_cast hz.symm)
  have hD' : (((y - x) ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [div_eq_iff hz0]
  push_cast at hD' hz ⊢
  field_simp
  linear_combination (-1 : ℂ) * hz

/-- DLMF 1.18.54 (Sokhotski–Plemelj), with hypotheses that make it true: for integrable `f`,
continuous at `x`, whose principal value exists there (the Hilbert transform
`ℋf(x) = (1/π) ⨍ f(y)/(y − x) dy = L` of 1.14.41, so `⨍ f(y)/(x − y) dy = −πL`),
`lim_{ε→0+} ∫ f(y)/(x ± iε − y) dy = −πL ∓ iπ f(x)`. -/
theorem dlmf_1_18_54 {f : ℝ → ℂ} (hf : Integrable f) {x : ℝ} (hc : ContinuousAt f x) {L : ℂ}
    (hH : HasHilbert f x L) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun ε : ℝ => ∫ y, f y / ((x : ℂ) + σ * ε * I - y)) (𝓝[>] 0)
      (𝓝 (-(π * L) - σ * π * I * f x)) := by
  have hC := (dlmf_1_14_42 hf hc L).mp hH
  have hP := tendsto_poissonInt_of_continuousAt hf hc
  have h := (hC.const_mul (-(π : ℂ))).sub (hP.const_mul ((σ : ℂ) * π * I))
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  convert h.congr' ?_ using 2
  · ring
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hA : Integrable fun y => ((((y - x) / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y :=
    integrable_realKernel_mul hf (by
      exact continuous_id.sub continuous_const |>.div (by fun_prop) fun y => by positivity)
      fun y => abs_div_sq_add_sq_le hε
  have hB : Integrable fun y => (((ε / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y :=
    integrable_realKernel_mul hf (by
      exact continuous_const.div (by fun_prop) fun y => by positivity)
      fun y => by
        rw [abs_div, abs_of_pos hε, abs_of_pos (by positivity),
          div_le_div_iff₀ (by positivity) hε, one_mul]
        nlinarith [sq_nonneg (y - x)]
  have e : ∫ y, f y / ((x : ℂ) + σ * ε * I - y) =
      -(∫ y, ((((y - x) / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y) -
        σ * I * ∫ y, (((ε / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y := by
    have hfun : (fun y => f y / ((x : ℂ) + σ * ε * I - y)) = fun y =>
        -(((((y - x) / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y) -
          σ * I * ((((ε / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y) := funext fun y => by
      rw [div_eq_mul_one_div, one_div_sokhotski hε σ hσ]
      ring
    rw [hfun, integral_sub (f := fun y => -(((((y - x) / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y))
      (g := fun y => σ * I * ((((ε / ((y - x) ^ 2 + ε ^ 2)) : ℝ) : ℂ) * f y)) hA.neg
      (hB.const_mul _), integral_neg, integral_const_mul]
  rw [e, poissonInt]
  field_simp

/-- **DLMF imprecision in 1.18.54**: DLMF asserts the formula for `f ∈ C(X)`, but continuity is
not enough for the integrals even to exist: for `f = 1` on `X = [0, ∞)`,
`y ↦ 1/(x + iε − y)` is not integrable. Integrability of `f`, and the existence of the principal
value at `x` (e.g. a Dini condition, as in `dlmf_1_18_54`), are needed. -/
theorem dlmf_1_18_54_counterexample (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ¬ IntegrableOn (fun y : ℝ => (1 : ℂ) / (x + ε * I - y)) (Ici 0) := by
  intro h
  set c := |x| + ε + 1
  have hc : 0 < c := by positivity
  have h2 : IntegrableOn (fun y : ℝ => 2 * ‖(1 : ℂ) / (x + ε * I - y)‖) (Ioi c) :=
    (h.mono_set (Ioi_subset_Ici hc.le)).norm.const_mul 2
  refine not_integrableOn_Ioi_inv (a := c) (h2.mono' measurable_inv.aestronglyMeasurable ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : c < y)
  have hy0 : 0 < y := hc.trans hy
  have hnorm : ‖((x : ℂ) + ε * I - y)‖ ≤ 2 * y := by
    calc ‖((x : ℂ) + ε * I - y)‖ = ‖(((x - y : ℝ) : ℂ)) + ε * I‖ := by push_cast; ring_nf
      _ ≤ |x - y| + ε := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, norm_I, mul_one,
          Real.norm_of_nonneg hε.le]
      _ ≤ 2 * y := by
        rw [abs_sub_comm, abs_of_pos (by linarith [le_abs_self x])]
        linarith [neg_abs_le x, le_abs_self x]
  have hpos : 0 < ‖((x : ℂ) + ε * I - y)‖ := by
    refine norm_pos_iff.mpr fun h0 => ?_
    have := congrArg Complex.im h0
    simp at this
    linarith
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hy0.le), norm_div, norm_one]
  rw [inv_le_iff_one_le_mul₀' hy0]
  calc (1 : ℝ) = 2 * y * (1 / (2 * y)) := by field_simp
    _ ≤ 2 * y * (1 / ‖((x : ℂ) + ε * I - y)‖) := by gcongr
    _ = y * (2 * (1 / ‖((x : ℂ) + ε * I - y)‖)) := by ring

end Azurite.DLMF
