/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertDense
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# DLMF 1.14.45: the Poisson kernel at Lebesgue points

`ae_tendsto_poissonKernel`: if `f` is measurable with `∫ |f(t)|/(1 + t²) dt < ∞`, then
`∫ ε/(ε² + s²) |f(x + s) − f(x)| ds → 0` as `ε → 0+` for almost every `x`. This uses Mathlib's
Lebesgue differentiation theorem and a layer-cake estimate (`integral_poissonKernel_mul_le`), so
no maximal function is needed.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

theorem poissonKernel_eq {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    ε / (ε ^ 2 + r ^ 2) = ε⁻¹ * (1 + (r / ε) ^ 2)⁻¹ := by
  field_simp

theorem integrable_poissonKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable fun r : ℝ => ε / (ε ^ 2 + r ^ 2) := by
  have := (integrable_inv_one_add_sq.comp_div hε.ne').const_mul ε⁻¹
  refine this.congr (ae_of_all _ fun r => ?_)
  simp only
  rw [poissonKernel_eq hε]

theorem integral_poissonKernel {ε : ℝ} (hε : 0 < ε) : ∫ r, ε / (ε ^ 2 + r ^ 2) = π := by
  simp_rw [poissonKernel_eq hε]
  rw [integral_const_mul, Measure.integral_comp_div (fun y => (1 + y ^ 2)⁻¹) ε,
    integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos hε]
  field_simp

/-- The layer-cake estimate: if `∫_{−r}^r u ≤ 2ηr` for `0 < r ≤ δ`, then
`∫_{−δ}^δ ε/(ε² + s²) u(s) ds ≤ 17η` for every `ε > 0`. -/
theorem integral_poissonKernel_mul_le {u : ℝ → ℝ} (hu0 : ∀ s, 0 ≤ u s) {δ ε η : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hui : IntegrableOn u (Icc (-δ) δ))
    (hω : ∀ r ∈ Ioc 0 δ, ∫ s in Icc (-r) r, u s ≤ η * (2 * r)) :
    ∫ s in Icc (-δ) δ, ε / (ε ^ 2 + s ^ 2) * u s ≤ 17 * η := by
  set W : ℝ → ℝ := fun r => ε / (ε ^ 2 + r ^ 2) with hW
  set V : ℝ → ℝ := fun r => 2 * ε * r / (ε ^ 2 + r ^ 2) ^ 2 with hV
  have hη : 0 ≤ η := by
    have := hω δ ⟨hδ, le_rfl⟩
    have h0 : 0 ≤ ∫ s in Icc (-δ) δ, u s := setIntegral_nonneg measurableSet_Icc fun s _ => hu0 s
    nlinarith
  have hWd : ∀ r, HasDerivAt (fun r => -W r) (V r) r := fun r => by
    have h := ((hasDerivAt_pow 2 r).const_add (ε ^ 2)).inv
      (by positivity : ε ^ 2 + r ^ 2 ≠ 0)
    refine (h.const_mul ε).neg.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      |>.congr_deriv ?_
    · simp only [hW, div_eq_mul_inv, Pi.neg_apply, Pi.inv_apply]
    · simp only [hV]
      field_simp
      ring
  have hVc : Continuous V := by
    simp only [hV]
    exact Continuous.div (by fun_prop) (by fun_prop) fun r => by positivity
  have hftc : ∀ a b : ℝ, ∫ r in a..b, V r = W a - W b := fun a b => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hWd r)
      (hVc.intervalIntegrable a b)]
    ring
  have hVb : ∀ r ∈ Icc (0 : ℝ) δ, 0 ≤ V r ∧ V r ≤ 2 * δ / ε ^ 3 := fun r hr => by
    have hD : ε ^ 4 ≤ (ε ^ 2 + r ^ 2) ^ 2 := by nlinarith [sq_nonneg r, sq_nonneg ε]
    refine ⟨by simp only [hV]; have := hr.1; positivity, ?_⟩
    simp only [hV]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hr.1, hr.2, mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * δ)]
  -- `W(s) = W(δ) + ∫_{|s|}^δ V` on `[−δ, δ]`
  have hWs : ∀ s ∈ Icc (-δ) δ, W s = W δ + ∫ r in Icc 0 δ, V r * (Icc |s| δ).indicator 1 r :=
    fun s hs => by
      have habs : |s| ≤ δ := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
      have : ∫ r in Icc 0 δ, V r * (Icc |s| δ).indicator 1 r = ∫ r in Icc |s| δ, V r := by
        rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
        congr 1; funext r
        by_cases h1 : r ∈ Icc |s| δ
        · have h2 : r ∈ Icc 0 δ := ⟨(abs_nonneg s).trans h1.1, h1.2⟩
          simp [indicator_of_mem h1, indicator_of_mem h2]
        · simp [indicator_of_notMem h1]
      have h1 : ∫ r in Icc |s| δ, V r = ∫ r in |s|..δ, V r := by
        rw [intervalIntegral.integral_of_le habs, integral_Icc_eq_integral_Ioc]
      rw [this, h1, hftc]
      simp only [hW, sq_abs]
      ring
  set ind : ℝ → ℝ → ℝ := fun s r => (Icc |s| δ).indicator 1 r with hind
  have hindeq : (fun q : ℝ × ℝ => ind q.1 q.2) =
      {q : ℝ × ℝ | |q.1| ≤ q.2 ∧ q.2 ≤ δ}.indicator 1 := funext fun q => by
    simp only [hind, Set.indicator, mem_Icc, Set.mem_ofPred_eq, Pi.one_apply]
  have hindm : Measurable fun q : ℝ × ℝ => ind q.1 q.2 := by
    rw [hindeq]
    exact measurable_one.indicator ((measurableSet_le (f := fun q : ℝ × ℝ => |q.1|)
      (g := fun q => q.2) (by fun_prop) measurable_snd).inter
      (measurableSet_le (f := fun q : ℝ × ℝ => q.2) measurable_snd measurable_const))
  have hind01 : ∀ s r, 0 ≤ ind s r ∧ ind s r ≤ 1 := fun s r => by
    simp only [hind, Set.indicator]; split_ifs <;> simp
  -- Fubini
  set H : ℝ → ℝ → ℝ := fun s r => V r * ind s r * u s with hH
  have hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Icc (-δ) δ)).prod (volume.restrict (Icc 0 δ))) := by
    refine (hui.mul_prod (integrableOn_const (C := 2 * δ / ε ^ 3)
      (by simp))).mono' ?_ ?_
    · exact ((hVc.measurable.comp measurable_snd).mul hindm).aestronglyMeasurable.mul
        hui.aestronglyMeasurable.comp_fst
    · filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)]
        with q hq
      change ‖V q.2 * ind q.1 q.2 * u q.1‖ ≤ u q.1 * (2 * δ / ε ^ 3)
      obtain ⟨hV0, hV1⟩ := hVb q.2 hq
      obtain ⟨hi0, hi1⟩ := hind01 q.1 q.2
      rw [Real.norm_of_nonneg (by have := hu0 q.1; positivity)]
      have := hu0 q.1
      calc V q.2 * ind q.1 q.2 * u q.1 ≤ (2 * δ / ε ^ 3) * 1 * u q.1 := by gcongr
        _ = u q.1 * (2 * δ / ε ^ 3) := by ring
  have hswap := integral_integral_swap hHi
  -- the left side
  have hLHS : ∫ s in Icc (-δ) δ, W s * u s =
      W δ * (∫ s in Icc (-δ) δ, u s) + ∫ s in Icc (-δ) δ, ∫ r in Icc 0 δ, H s r := by
    rw [← integral_const_mul, ← integral_add (hui.const_mul _)]
    · refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      simp only [hH]
      rw [hWs s hs, integral_mul_const]
      ring
    · exact hHi.integral_prod_left
  -- the inner integral in `s`
  have hinner : ∀ r ∈ Icc (0 : ℝ) δ, ∫ s in Icc (-δ) δ, H s r ≤ V r * (η * (2 * r)) := by
    intro r hr
    have heq : ∫ s in Icc (-δ) δ, H s r = V r * ∫ s in Icc (-r) r, u s := by
      simp only [hH]
      rw [← integral_const_mul, ← integral_indicator measurableSet_Icc,
        ← integral_indicator measurableSet_Icc]
      congr 1; funext s
      by_cases hs : s ∈ Icc (-r) r
      · have hs' : s ∈ Icc (-δ) δ := ⟨by linarith [hs.1, hr.2], by linarith [hs.2, hr.2]⟩
        have hr' : r ∈ Icc |s| δ := ⟨abs_le.mpr hs, hr.2⟩
        simp [indicator_of_mem hs, indicator_of_mem hs', hind, indicator_of_mem hr']
      · have hr' : r ∉ Icc |s| δ := fun h => hs (abs_le.mp h.1)
        have h0 : ind s r = 0 := by simp only [hind]; exact indicator_of_notMem hr' _
        simp only [indicator_of_notMem hs]
        by_cases hs' : s ∈ Icc (-δ) δ
        · rw [indicator_of_mem hs']; simp only [h0]; ring
        · rw [indicator_of_notMem hs']
    rw [heq]
    rcases hr.1.lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (hω r ⟨h, hr.2⟩) (hVb r hr).1
    · subst h; simp [hV]
  have hRHS : ∫ r in Icc 0 δ, ∫ s in Icc (-δ) δ, H s r ≤ 4 * π * η := by
    have hb : ∀ r ∈ Icc (0 : ℝ) δ, V r * (η * (2 * r)) ≤ 4 * η * W r := fun r hr => by
      simp only [hV, hW]
      have hD : 0 < ε ^ 2 + r ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : r ^ 2 ≤ ε ^ 2 + r ^ 2 := by nlinarith
      have h4 : 0 ≤ 4 * η * ε := by positivity
      calc 2 * ε * r * (η * (2 * r)) = 4 * η * ε * r ^ 2 := by ring
        _ ≤ 4 * η * ε * (ε ^ 2 + r ^ 2) := mul_le_mul_of_nonneg_left this h4
        _ = 4 * η * (ε / (ε ^ 2 + r ^ 2)) * (ε ^ 2 + r ^ 2) ^ 2 := by field_simp
    have hWi : IntegrableOn W (Icc 0 δ) := (integrable_poissonKernel hε).integrableOn
    calc ∫ r in Icc 0 δ, ∫ s in Icc (-δ) δ, H s r ≤ ∫ r in Icc 0 δ, 4 * η * W r := by
          refine setIntegral_mono_on hHi.integral_prod_right (hWi.const_mul _)
            measurableSet_Icc fun r hr => (hinner r hr).trans (hb r hr)
      _ = 4 * η * ∫ r in Icc 0 δ, W r := integral_const_mul _ _
      _ ≤ 4 * η * ∫ r, W r := by
          refine mul_le_mul_of_nonneg_left (setIntegral_le_integral
            (integrable_poissonKernel hε) (ae_of_all _ fun r => ?_)) (by positivity)
          simp only [hW]; positivity
      _ = 4 * π * η := by rw [integral_poissonKernel hε]; ring
  have hfirst : W δ * (∫ s in Icc (-δ) δ, u s) ≤ η := by
    have := hω δ ⟨hδ, le_rfl⟩
    have hW0 : 0 ≤ W δ := by simp only [hW]; positivity
    calc W δ * (∫ s in Icc (-δ) δ, u s) ≤ W δ * (η * (2 * δ)) := mul_le_mul_of_nonneg_left this hW0
      _ ≤ η := by
          simp only [hW]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg (ε - δ), mul_nonneg hη (sq_nonneg (ε - δ))]
  have hπ := Real.pi_le_four
  change ∫ s in Icc (-δ) δ, W s * u s ≤ 17 * η
  rw [hLHS, hswap]
  nlinarith

/-! ### Convergence at Lebesgue points -/

theorem one_div_sq_le_of_le (x : ℝ) {a s : ℝ} (ha : 0 < a) (hs : a ≤ |s|) :
    1 / s ^ 2 ≤ ((1 + 2 * x ^ 2) / a ^ 2 + 2) / (1 + (x + s) ^ 2) := by
  have hs2 : a ^ 2 ≤ s ^ 2 := by rw [← sq_abs s]; exact pow_le_pow_left₀ ha.le hs 2
  have hs0 : 0 < s ^ 2 := lt_of_lt_of_le (by positivity) hs2
  rw [div_le_div_iff₀ hs0 (by positivity), one_mul]
  have h1 : (1 + 2 * x ^ 2) ≤ (1 + 2 * x ^ 2) / a ^ 2 * s ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hs2 (by positivity)
  nlinarith [sq_nonneg (x - s)]

theorem one_div_add_sq_le (x : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    1 / (ε ^ 2 + s ^ 2) ≤ ((1 + 2 * x ^ 2) / ε ^ 2 + 2) / (1 + (x + s) ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h1 : (1 + 2 * x ^ 2) ≤ (1 + 2 * x ^ 2) / ε ^ 2 * (ε ^ 2 + s ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg s, sq_nonneg x]
  nlinarith [sq_nonneg (x - s)]

theorem integrableOn_Icc_of_weighted {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hw : Integrable fun t => ‖f t‖ / (1 + t ^ 2)) (R : ℝ) :
    IntegrableOn f (Icc (-R) R) := by
  refine (hw.integrableOn.const_mul (1 + R ^ 2)).mono' hfm.restrict
    ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_))
  have ht2 : t ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) 2
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (f t)]

theorem locallyIntegrable_of_weighted {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hw : Integrable fun t => ‖f t‖ / (1 + t ^ 2)) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (integrableOn_Icc_of_weighted hfm hw R).mono_set ?_
  intro t ht
  have := hR ht
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact abs_le.mp this

/-- `∫_{−r}^r ‖f(x + s) − f(x)‖ ds = 2r · ⨍_{B(x, r)} ‖f − f(x)‖`. -/
theorem integral_Icc_eq_average {f : ℝ → ℂ} (x : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ s in Icc (-r) r, ‖f (x + s) - f x‖ =
      2 * r * ⨍ y in Metric.closedBall x r, ‖f y - f x‖ := by
  rw [setAverage_eq, Real.closedBall_eq_Icc, smul_eq_mul, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), ← mul_assoc, show x + r - (x - r) = 2 * r by ring,
    mul_inv_cancel₀ (by positivity), one_mul, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_left (fun y => ‖f y - f x‖)]
  congr 1

/-- **The Poisson kernel at Lebesgue points**: if `f` is measurable with
`∫ |f(t)|/(1 + t²) dt < ∞` (e.g. `f ∈ L^p`), then for almost every `x`,
`∫ ε/(ε² + s²) |f(x + s) − f(x)| ds → 0` as `ε → 0+`. -/
theorem ae_tendsto_poissonKernel {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hw : Integrable fun t => ‖f t‖ / (1 + t ^ 2)) :
    ∀ᵐ x, Tendsto (fun ε => ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖f (x + s) - f x‖) (𝓝[>] 0) (𝓝 0) := by
  have hloc := locallyIntegrable_of_weighted hfm hw
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume) hloc 1]
    with x hx
  have hav : Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, ‖f y - f x‖) (𝓝[>] 0)
      (𝓝 0) := by
    refine hx (fun _ => x) id tendsto_id ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp [hr.le]
  set u : ℝ → ℝ := fun s => ‖f (x + s) - f x‖ with hu
  set G : ℝ → ℝ := fun s => (‖f (x + s)‖ + ‖f x‖) / (1 + (x + s) ^ 2) with hG
  have hGi : Integrable G := by
    have h1 := (hw.comp_add_left x)
    have h2 := (integrable_inv_one_add_sq.comp_add_left x).const_mul ‖f x‖
    refine (h1.add h2).congr (ae_of_all _ fun s => ?_)
    simp only [hG, Pi.add_apply]
    rw [add_div, div_eq_mul_inv ‖f x‖]
  have hum : AEStronglyMeasurable u volume :=
    ((hfm.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume x)).sub
      aestronglyMeasurable_const).norm
  have huG : ∀ s, u s ≤ (1 + (x + s) ^ 2) * G s := fun s => by
    simp only [hu, hG]
    rw [mul_div_cancel₀ _ (by positivity)]
    exact norm_sub_le _ _
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  set η := e / 40 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hav η hη0
  set δ := δ₀ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hω : ∀ r ∈ Ioc 0 δ, ∫ s in Icc (-r) r, u s ≤ η * (2 * r) := fun r hr => by
    have h1 := hδ₀' (x := r) hr.1 (by
      rw [dist_zero_right, Real.norm_of_nonneg hr.1.le]; linarith [hr.2])
    rw [dist_zero_right] at h1
    rw [integral_Icc_eq_average x hr.1]
    have h2 := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ h1.le)
    nlinarith [hr.1]
  set Cδ := (1 + 2 * x ^ 2) / δ ^ 2 + 2 with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  set IG := ∫ s, G s with hIG
  have hIG0 : 0 ≤ IG := integral_nonneg fun s => by simp only [hG]; positivity
  refine ⟨min δ (e / (2 * (Cδ * IG + 1))), lt_min hδ0 (by positivity), fun ε hε hεd => ?_⟩
  have hε0 : 0 < ε := hε
  rw [dist_zero_right, Real.norm_of_nonneg hε0.le] at hεd
  have hεsmall : ε * (Cδ * IG) < e / 2 := by
    have h1 : ε < e / (2 * (Cδ * IG + 1)) := hεd.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  -- global integrability
  have hWu : Integrable fun s => ε / (ε ^ 2 + s ^ 2) * u s := by
    refine (hGi.const_mul (ε * ((1 + 2 * x ^ 2) / ε ^ 2 + 2))).mono'
      (((Continuous.div continuous_const (by fun_prop) (fun s => by positivity) :
        Continuous fun s : ℝ => ε / (ε ^ 2 + s ^ 2)).aestronglyMeasurable).mul
        hum) (ae_of_all _ fun s => ?_)
    have hb := one_div_add_sq_le x hε0 s
    have hu0 : 0 ≤ u s := norm_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    calc ε / (ε ^ 2 + s ^ 2) * u s ≤ ε / (ε ^ 2 + s ^ 2) * ((1 + (x + s) ^ 2) * G s) :=
          mul_le_mul_of_nonneg_left (huG s) (by positivity)
      _ = ε * (1 / (ε ^ 2 + s ^ 2)) * (1 + (x + s) ^ 2) * G s := by ring
      _ ≤ ε * (((1 + 2 * x ^ 2) / ε ^ 2 + 2) / (1 + (x + s) ^ 2)) * (1 + (x + s) ^ 2) * G s := by
          have : 0 ≤ G s := by simp only [hG]; positivity
          gcongr
      _ = ε * ((1 + 2 * x ^ 2) / ε ^ 2 + 2) * G s := by field_simp
  have hnonneg : 0 ≤ ∫ s, ε / (ε ^ 2 + s ^ 2) * u s :=
    integral_nonneg fun s => by simp only [hu]; positivity
  rw [dist_zero_right, Real.norm_of_nonneg hnonneg,
    ← integral_add_compl measurableSet_Icc hWu (s := Icc (-δ) δ)]
  have hnear := integral_poissonKernel_mul_le (u := u) (fun s => norm_nonneg _) hδ0 hε0
    (((integrableOn_Icc_of_weighted (hfm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_add_left volume x)) ?_ δ).sub (integrableOn_const ?_)).norm) hω
  · have hfar : ∫ s in (Icc (-δ) δ)ᶜ, ε / (ε ^ 2 + s ^ 2) * u s ≤ ε * (Cδ * IG) := by
      calc ∫ s in (Icc (-δ) δ)ᶜ, ε / (ε ^ 2 + s ^ 2) * u s
          ≤ ∫ s in (Icc (-δ) δ)ᶜ, ε * Cδ * G s := by
            refine setIntegral_mono_on hWu.integrableOn ((hGi.const_mul _).integrableOn)
              measurableSet_Icc.compl fun s hs => ?_
            have hs' : δ ≤ |s| := by
              by_contra h
              exact hs (abs_le.mp (not_le.mp h).le)
            have hb := one_div_sq_le_of_le x hδ0 hs'
            have hu0 : 0 ≤ u s := norm_nonneg _
            have hG0 : 0 ≤ G s := by simp only [hG]; positivity
            have hs2 : 0 < s ^ 2 := by
              have := pow_le_pow_left₀ hδ0.le hs' 2; rw [sq_abs] at this
              exact lt_of_lt_of_le (by positivity) this
            calc ε / (ε ^ 2 + s ^ 2) * u s ≤ ε * (1 / s ^ 2) * ((1 + (x + s) ^ 2) * G s) := by
                  have : ε / (ε ^ 2 + s ^ 2) ≤ ε * (1 / s ^ 2) := by
                    rw [mul_one_div]
                    exact div_le_div_of_nonneg_left hε0.le hs2 (by nlinarith)
                  exact mul_le_mul this (huG s) hu0 (by positivity)
              _ ≤ ε * (Cδ / (1 + (x + s) ^ 2)) * ((1 + (x + s) ^ 2) * G s) := by gcongr
              _ = ε * Cδ * G s := by field_simp
        _ ≤ ∫ s, ε * Cδ * G s := setIntegral_le_integral (hGi.const_mul _)
            (ae_of_all _ fun s => by simp only [hG]; positivity)
        _ = ε * (Cδ * IG) := by rw [integral_const_mul]; ring
    linarith
  · refine ((hw.comp_add_left x).const_mul (2 * (1 + 2 * x ^ 2))).mono'
      ((hfm.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume x)).norm.mul
        (Continuous.inv₀ (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2)
          (fun s => by positivity)).aestronglyMeasurable)
      (ae_of_all _ fun s => ?_)
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (by positivity), mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by positivity)]
    have h1 : 1 + (x + s) ^ 2 ≤ 2 * (1 + 2 * x ^ 2) * (1 + s ^ 2) := by
      nlinarith [sq_nonneg (x - s), sq_nonneg (x * s)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg (f (x + s)))]
  · simp

end Azurite.DLMF
