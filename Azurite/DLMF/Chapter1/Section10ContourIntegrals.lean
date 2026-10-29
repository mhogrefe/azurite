/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# DLMF §1.10(viii): Functions Defined by Contour Integrals

Formalizations of <https://dlmf.nist.gov/1.10.viii> (`D` open, `f : ℂ → ℝ → ℂ`).

* **Finite segment.** `dlmf_1_10_18` covers 1.10.18. If `f(z, t)` is analytic in `z ∈ D` for each
  `t ∈ [a, b]` and continuous in both variables, then `F(z) = ∫ₐᵇ f(z, t) dt` is analytic in `D`
  and `F⁽ᵏ⁾(z) = ∫ₐᵇ ∂ᵏf/∂zᵏ(z, t) dt` for every `k`. The proof has two steps:
  * `continuousOn_deriv_param`: `∂f/∂z` is again jointly continuous, by Cauchy's estimate
    `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` and uniform continuity on compacts;
  * `hasDerivAt_integral_param_complex`: dominated differentiation under the integral sign
    (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
* **Infinite or singular endpoint.** The upper limit `c → b` runs along a filter `l` on
  `T = [a, b)`:
  * `upperLimit_atTop` sets up `b = ∞`, and `upperLimit_nhdsLT` sets up a singularity at `t = b`;
  * uniform convergence on compacts (`IntegralConvergesUniformlyOn`) makes `F` analytic, with
    derivatives the improper integrals of `∂ᵏf/∂zᵏ` (`dlmf_1_10_viii_improper`, via Mathlib's
    `TendstoLocallyUniformlyOn.differentiableOn` and `TendstoLocallyUniformlyOn.deriv`);
  * the tail form of uniform convergence is 1.10.19 (`dlmf_1_10_19_atTop`,
    `dlmf_1_10_19_nhdsLT`);
  * the M-test gives absolute and uniform convergence (`dlmf_1_10_viii_Mtest`, by dominated
    convergence of the tails `∫_{T \ [a, c]} M`).
-/

open Filter Topology Set Metric Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-! ### Finite segments -/

/-- If `f(z, t)` is analytic in `z ∈ D` for each `t ∈ [a, b]` and jointly continuous, then so is
`∂f/∂z`: Cauchy's estimate on small circles plus uniform continuity on compacts. -/
theorem continuousOn_deriv_param {f : ℂ → ℝ → ℂ} {D : Set ℂ} {a b : ℝ} (hD : IsOpen D)
    (hf : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Icc a b)) :
    ContinuousOn (fun p : ℂ × ℝ => deriv (fun z => f z p.2) p.1) (D ×ˢ Icc a b) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨z₁, t₁⟩ ⟨hz₁, ht₁⟩ ε hε
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hD z₁ hz₁
  set r := ρ / 3 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall z₁ (2 * r) ⊆ D := (closedBall_subset_ball (by linarith)).trans hball
  have hKsub : closedBall z₁ (2 * r) ×ˢ Icc a b ⊆ D ×ˢ Icc a b := prod_mono hcb subset_rfl
  have hK : IsCompact (closedBall z₁ (2 * r) ×ˢ Icc a b) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hc.mono hKsub)) (ε * r / 2) (by positivity)
  have hd1 : ContinuousAt (deriv fun z => f z t₁) z₁ :=
    ((hf t₁ ht₁).deriv hD).continuousOn.continuousAt (hD.mem_nhds hz₁)
  obtain ⟨η', hη', hd1'⟩ := Metric.continuousAt_iff.mp hd1 (ε / 2) (half_pos hε)
  refine ⟨min (min η η') r, by positivity, ?_⟩
  rintro ⟨z, t⟩ ⟨hz, ht⟩ hdist
  rw [Prod.dist_eq, max_lt_iff] at hdist
  obtain ⟨hdz, hdt⟩ := hdist
  simp only at hdz hdt ⊢
  have hzr : dist z z₁ < r := hdz.trans_le (min_le_right _ _)
  have hcbz : closedBall z r ⊆ D := fun w hw => hcb (by
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w z z₁])
  have hsph : ∀ ζ ∈ sphere z r, ‖f ζ t - f ζ t₁‖ ≤ ε * r / 2 := by
    intro ζ hζ
    have hζK : ζ ∈ closedBall z₁ (2 * r) := by
      rw [mem_closedBall]
      linarith [dist_triangle ζ z z₁, (mem_sphere.mp hζ).le]
    have := huc (ζ, t) ⟨hζK, ht⟩ (ζ, t₁) ⟨hζK, ht₁⟩ (by
      rw [Prod.dist_eq, dist_self]
      simp only
      rw [max_eq_right dist_nonneg]
      exact hdt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    rw [dist_eq_norm] at this
    exact this.le
  have hdiff : DiffContOnCl ℂ (fun w => f w t - f w t₁) (ball z r) :=
    (((hf t ht).sub (hf t₁ ht₁)).mono hcbz).diffContOnCl_ball subset_rfl
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hdiff hsph
  have hzD : z ∈ D := hz
  rw [deriv_fun_sub ((hf t ht).differentiableAt (hD.mem_nhds hzD))
    ((hf t₁ ht₁).differentiableAt (hD.mem_nhds hzD))] at hest
  have h2 := hd1' (hdz.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  rw [dist_eq_norm] at h2 ⊢
  have h3 : ε * r / 2 / r = ε / 2 := by field_simp
  rw [h3] at hest
  calc ‖deriv (fun z => f z t) z - deriv (fun z => f z t₁) z₁‖
      ≤ ‖deriv (fun z => f z t) z - deriv (fun z => f z t₁) z‖ +
          ‖deriv (fun z => f z t₁) z - deriv (fun z => f z t₁) z₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hest h2
    _ = ε := add_halves ε

theorem continuousOn_param_slice {f : ℂ → ℝ → ℂ} {D : Set ℂ} {T : Set ℝ}
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ T)) {z : ℂ} (hz : z ∈ D) :
    ContinuousOn (fun t => f z t) T :=
  hc.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht => ⟨hz, ht⟩

/-- Differentiation under the integral sign for `F(z) = ∫ₐᵇ f(z, t) dt`. -/
theorem hasDerivAt_integral_param_complex {f : ℂ → ℝ → ℂ} {D : Set ℂ} {a b : ℝ} (hab : a ≤ b)
    (hD : IsOpen D) (hf : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Icc a b)) {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    HasDerivAt (fun z => ∫ t in a..b, f z t) (∫ t in a..b, deriv (fun z => f z t) z₀) z₀ := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hD z₀ hz₀
  have hcb : closedBall z₀ (ρ / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hball
  have hg := continuousOn_deriv_param hD hf hc
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall z₀ (ρ / 2)).prod isCompact_Icc).exists_bound_of_continuousOn
    (hg.mono (prod_mono hcb subset_rfl))
  have hIoc : Ι a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z t => f z t) (F' := fun z t => deriv (fun z => f z t) z) (bound := fun _ => C)
    (ball_mem_nhds z₀ (half_pos hρ)) ?_ ?_ ?_ ?_ intervalIntegrable_const
    ?_).2
  · filter_upwards [hD.mem_nhds hz₀] with z hz
    exact ((continuousOn_param_slice hc hz).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (continuousOn_param_slice hc hz₀).intervalIntegrable_of_Icc hab
  · exact ((continuousOn_param_slice (f := fun z t => deriv (fun z => f z t) z) hg hz₀).mono
      hIoc).aestronglyMeasurable measurableSet_uIoc
  · refine Eventually.of_forall fun t ht z hz => ?_
    exact hC (z, t) ⟨ball_subset_closedBall hz, hIoc ht⟩
  · refine Eventually.of_forall fun t ht z hz => ?_
    exact ((hf t (hIoc ht)).differentiableAt
      (hD.mem_nhds (hcb (ball_subset_closedBall hz)))).hasDerivAt

theorem differentiableOn_iteratedDeriv_of_isOpen {g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hg : DifferentiableOn ℂ g D) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k g) D := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv hD

/-- **DLMF 1.10.18**: if `f(z, t)` is analytic in `z ∈ D` for each `t ∈ [a, b]` and continuous in
both variables, then `F(z) = ∫ₐᵇ f(z, t) dt` is analytic in `D` and its derivatives of all orders
are found by differentiating under the integral sign. -/
theorem dlmf_1_10_18 {f : ℂ → ℝ → ℂ} {D : Set ℂ} {a b : ℝ} (hab : a ≤ b) (hD : IsOpen D)
    (hf : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Icc a b)) :
    AnalyticOnNhd ℂ (fun z => ∫ t in a..b, f z t) D ∧
      ∀ k : ℕ, ∀ z ∈ D, iteratedDeriv k (fun z => ∫ t in a..b, f z t) z =
        ∫ t in a..b, iteratedDeriv k (fun z => f z t) z := by
  have hd : DifferentiableOn ℂ (fun z => ∫ t in a..b, f z t) D := fun z hz =>
    (hasDerivAt_integral_param_complex hab hD hf hc hz).differentiableAt.differentiableWithinAt
  refine ⟨hd.analyticOnNhd hD, fun k => ?_⟩
  -- the iterated derivatives satisfy the same hypotheses
  have key : ∀ k : ℕ, (∀ t ∈ Icc a b, DifferentiableOn ℂ
      (fun z => iteratedDeriv k (fun z => f z t) z) D) ∧
      ContinuousOn (Function.uncurry fun z t => iteratedDeriv k (fun z => f z t) z)
        (D ×ˢ Icc a b) ∧
      ∀ z ∈ D, iteratedDeriv k (fun z => ∫ t in a..b, f z t) z =
        ∫ t in a..b, iteratedDeriv k (fun z => f z t) z := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hf, by simpa using hc, fun z _ => by simp⟩
    | succ k ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      have hc' := continuousOn_deriv_param hD ih1 ih2
      refine ⟨fun t ht => ?_, ?_, fun z hz => ?_⟩
      · rw [iteratedDeriv_succ]
        exact differentiableOn_iteratedDeriv_of_isOpen hD (hf t ht) (k + 1) |>.congr
          fun z _ => by rw [iteratedDeriv_succ]
      · refine hc'.congr ?_
        rintro ⟨z, t⟩ -
        simp only [Function.uncurry_apply_pair, iteratedDeriv_succ]
      · have heq : iteratedDeriv k (fun z => ∫ t in a..b, f z t) =ᶠ[𝓝 z]
            fun z => ∫ t in a..b, iteratedDeriv k (fun z => f z t) z :=
          eventually_of_mem (hD.mem_nhds hz) ih3
        rw [iteratedDeriv_succ, heq.deriv_eq,
          (hasDerivAt_integral_param_complex hab hD ih1 ih2 hz).deriv]
        simp only [iteratedDeriv_succ]
  exact (key k).2.2

/-! ### Infinite segments and singular endpoints

The integral `∫ₐᵇ f(z, t) dt` over `t ∈ T = [a, b)` is the limit of `∫ₐᶜ f(z, t) dt` as `c → b`
along a filter `l`: `l = atTop` with `T = [a, ∞)` for `b = ∞`, and `l = 𝓝[<] b` with `T = [a, b)`
for a singularity at `t = b` (`upperLimit_atTop`, `upperLimit_nhdsLT`). -/

/-- The integral converges at `b` uniformly on `S`: `∫ₐᶜ f(z, t) dt → F(z)` uniformly for `z ∈ S`
as `c → b` along `l`. -/
def IntegralConvergesUniformlyOn (f : ℂ → ℝ → ℂ) (a : ℝ) (l : Filter ℝ) (F : ℂ → ℂ)
    (S : Set ℂ) : Prop :=
  TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) F l S

/-- DLMF §1.10(viii), infinite or singular endpoint: if `f(z, t)` is analytic in `z ∈ D` for each
`t ∈ T = [a, b)`, continuous in both variables, and the integral converges at `b` uniformly on
every compact subset of `D`, then `F(z) = ∫ₐᵇ f(z, t) dt` is analytic in `D`, and its derivatives
of all orders are the (improper) integrals of the derivatives of `f`. -/
theorem dlmf_1_10_viii_improper {f : ℂ → ℝ → ℂ} {D : Set ℂ} (hD : IsOpen D) {a : ℝ}
    {T : Set ℝ} {l : Filter ℝ} [l.NeBot] (hl : ∀ᶠ c in l, a ≤ c ∧ Icc a c ⊆ T)
    (hf : ∀ t ∈ T, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ T)) {F : ℂ → ℂ}
    (hu : ∀ S ⊆ D, IsCompact S → IntegralConvergesUniformlyOn f a l F S) :
    AnalyticOnNhd ℂ F D ∧ ∀ k : ℕ, ∀ z ∈ D,
      Tendsto (fun c => ∫ t in a..c, iteratedDeriv k (fun z => f z t) z) l
        (𝓝 (iteratedDeriv k F z)) := by
  set G : ℝ → ℂ → ℂ := fun c z => ∫ t in a..c, f z t with hG
  have hloc : TendstoLocallyUniformlyOn G F l D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  have hfin : ∀ᶠ c in l, AnalyticOnNhd ℂ (G c) D ∧ ∀ k : ℕ, ∀ z ∈ D,
      iteratedDeriv k (G c) z = ∫ t in a..c, iteratedDeriv k (fun z => f z t) z := by
    filter_upwards [hl] with c hc'
    exact dlmf_1_10_18 hc'.1 hD (fun t ht => hf t (hc'.2 ht)) (hc.mono (prod_mono subset_rfl hc'.2))
  have hGd : ∀ k : ℕ, ∀ᶠ c in l, DifferentiableOn ℂ (iteratedDeriv k (G c)) D := fun k => by
    filter_upwards [hfin] with c hc'
    exact differentiableOn_iteratedDeriv_of_isOpen hD hc'.1.differentiableOn k
  have hk : ∀ k : ℕ, TendstoLocallyUniformlyOn (fun c => iteratedDeriv k (G c))
      (iteratedDeriv k F) l D := by
    intro k
    induction k with
    | zero => simpa using hloc
    | succ k ih =>
      have := ih.deriv (hGd k) hD
      simp only [iteratedDeriv_succ]
      exact this
  refine ⟨(hloc.differentiableOn (by simpa using hGd 0) hD).analyticOnNhd hD,
    fun k z hz => ?_⟩
  refine ((hk k).tendsto_at hz).congr' ?_
  filter_upwards [hfin] with c hc'
  exact hc'.2 k z hz

/-- For `b = ∞`: `T = [a, ∞)` and `c → ∞`. -/
theorem upperLimit_atTop (a : ℝ) : ∀ᶠ c in atTop, a ≤ c ∧ Icc a c ⊆ Ici a :=
  (eventually_ge_atTop a).mono fun _ h => ⟨h, Icc_subset_Ici_self⟩

/-- For a singularity at `t = b`: `T = [a, b)` and `c → b⁻`. -/
theorem upperLimit_nhdsLT {a b : ℝ} (hab : a < b) : ∀ᶠ c in 𝓝[<] b, a ≤ c ∧ Icc a c ⊆ Ico a b := by
  filter_upwards [Ioo_mem_nhdsLT hab, self_mem_nhdsWithin] with c hc hcb
  exact ⟨hc.1.le, Icc_subset_Ico_right hcb⟩

/-- **DLMF 1.10.19** (`b = ∞`): the integral converges uniformly on `S` iff for every `ε > 0` there
is `a₀ ≥ a`, independent of `z`, with `|∫_{a₁}^∞ f(z, t) dt| < ε` for all `a₁ ≥ a₀` and `z ∈ S`
(the tail is `F(z) − ∫ₐ^{a₁} f(z, t) dt`). -/
theorem dlmf_1_10_19_atTop {f : ℂ → ℝ → ℂ} {a : ℝ} {F : ℂ → ℂ} {S : Set ℂ} :
    IntegralConvergesUniformlyOn f a atTop F S ↔ ∀ ε > 0, ∃ a₀ ≥ a, ∀ a₁ ≥ a₀, ∀ z ∈ S,
      ‖F z - ∫ t in a..a₁, f z t‖ < ε := by
  simp only [IntegralConvergesUniformlyOn, Metric.tendstoUniformlyOn_iff, eventually_atTop,
    dist_eq_norm]
  refine forall₂_congr fun ε _ => ⟨fun ⟨a₀, h⟩ => ⟨max a₀ a, le_max_right _ _,
    fun a₁ ha₁ => h a₁ ((le_max_left _ _).trans ha₁)⟩, fun ⟨a₀, _, h⟩ => ⟨a₀, h⟩⟩

/-- **DLMF 1.10.19** (singularity at `t = b`): the integral converges uniformly on `S` iff for every
`ε > 0` there is `a₀ ∈ [a, b)` with `|∫_{a₁}^b f(z, t) dt| < ε` for all `a₁ ∈ [a₀, b)`, `z ∈ S`. -/
theorem dlmf_1_10_19_nhdsLT {f : ℂ → ℝ → ℂ} {a b : ℝ} (hab : a < b) {F : ℂ → ℂ} {S : Set ℂ} :
    IntegralConvergesUniformlyOn f a (𝓝[<] b) F S ↔ ∀ ε > 0, ∃ a₀ ∈ Ico a b, ∀ a₁ ∈ Ico a₀ b,
      ∀ z ∈ S, ‖F z - ∫ t in a..a₁, f z t‖ < ε := by
  simp only [IntegralConvergesUniformlyOn, Metric.tendstoUniformlyOn_iff, dist_eq_norm]
  refine forall₂_congr fun ε _ => ⟨fun h => ?_, fun ⟨a₀, ha₀, h⟩ => ?_⟩
  · obtain ⟨x, hx, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp h
    set m := max x a
    have hm : m < b := max_lt hx hab
    refine ⟨(m + b) / 2, ⟨by linarith [le_max_right x a], by linarith⟩, fun a₁ ha₁ => hsub ?_⟩
    exact ⟨by linarith [le_max_left x a, ha₁.1], ha₁.2⟩
  · exact mem_of_superset (Ico_mem_nhdsLT ha₀.2) fun a₁ ha₁ => h a₁ ha₁

/-- **M-test** (DLMF §1.10(viii)): if `|f(z, t)| ≤ M(t)` for `z ∈ S`, `t ∈ T`, and `∫_T M`
converges, then the integral converges absolutely and uniformly on `S`. Here `T ⊇ [a, c]`
exhausts `T ⊆ [a, ∞)` as `c → b` along `l`. -/
theorem dlmf_1_10_viii_Mtest {f : ℂ → ℝ → ℂ} {S : Set ℂ} {a : ℝ} {T : Set ℝ}
    (hTm : MeasurableSet T) (hTa : T ⊆ Ici a) {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : ∀ᶠ c in l, a ≤ c ∧ Icc a c ⊆ T) (hexh : ∀ t ∈ T, ∀ᶠ c in l, t ≤ c)
    (hcont : ∀ z ∈ S, ContinuousOn (f z) T) {M : ℝ → ℝ} (hM : ∀ z ∈ S, ∀ t ∈ T, ‖f z t‖ ≤ M t)
    (hMi : IntegrableOn M T) :
    (∀ z ∈ S, IntegrableOn (f z) T) ∧
      IntegralConvergesUniformlyOn f a l (fun z => ∫ t in T, f z t) S := by
  have hint : ∀ z ∈ S, IntegrableOn (f z) T := fun z hz =>
    hMi.mono' ((hcont z hz).aestronglyMeasurable hTm)
      ((ae_restrict_iff' hTm).mpr (Eventually.of_forall (hM z hz)))
  refine ⟨hint, ?_⟩
  -- the tails `∫_{T \ [a, c]} M` tend to `0`
  have htail : Tendsto (fun c => ∫ t, (T \ Icc a c).indicator M t) l (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖T.indicator M t‖)
      (Eventually.of_forall fun c => ?_) (Eventually.of_forall fun c => ?_)
      (hMi.integrable_indicator hTm).norm ?_
    · have : (T \ Icc a c).indicator M = (Icc a c)ᶜ.indicator (T.indicator M) := by
        rw [Set.indicator_indicator, inter_comm, ← Set.sdiff_eq]
      rw [this]
      exact (hMi.integrable_indicator hTm).aestronglyMeasurable.indicator
        measurableSet_Icc.compl
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ T \ Icc a c
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht.1]
      · rw [Set.indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ T
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hexh t ht] with c hc
        rw [Set.indicator_of_notMem fun h => h.2 ⟨hTa ht, hc⟩]
      · exact tendsto_const_nhds.congr fun c => (Set.indicator_of_notMem (fun h => ht h.1) _).symm
  rw [IntegralConvergesUniformlyOn, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hl, htail.eventually (gt_mem_nhds hε)] with c hc hcε z hz
  have h1 : ∫ t in a..c, f z t = ∫ t in Icc a c, f z t := by
    rw [intervalIntegral.integral_of_le hc.1, integral_Icc_eq_integral_Ioc]
  have h2 : (∫ t in T, f z t) - ∫ t in Icc a c, f z t = ∫ t in T \ Icc a c, f z t :=
    (setIntegral_sdiff measurableSet_Icc (hint z hz) hc.2).symm
  have h3 : ∫ t, (T \ Icc a c).indicator M t = ∫ t in T \ Icc a c, M t :=
    integral_indicator (hTm.diff measurableSet_Icc)
  rw [dist_eq_norm, h1, h2]
  rw [h3] at hcε
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le (hMi.mono_set sdiff_subset)
    ((ae_restrict_iff' (hTm.diff measurableSet_Icc)).mpr
      (Eventually.of_forall fun t ht => hM z hz t ht.1))) hcε

end Azurite.DLMF
