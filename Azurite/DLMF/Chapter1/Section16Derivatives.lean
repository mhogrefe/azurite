/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16

/-!
# DLMF §1.16(ii)–(iii): Derivatives of distributions; the Dirac delta

https://dlmf.nist.gov/1.16.ii
https://dlmf.nist.gov/1.16.iii

* Differentiation `derivTest` on `𝒟(I)` preserves convergence (`TestConverges.deriv`).
* 1.16.8–1.16.9: `derivDist` (`⟨Λ', φ⟩ = −⟨Λ, φ'⟩`), its iterates `⟨Λ⁽ᵏ⁾, φ⟩ = (−1)ᵏ⟨Λ, φ⁽ᵏ⁾⟩`,
  and these are distributions.
* `Df = Λ_f'` (`distDeriv`). For `f` of class `C¹` on `I` it is the regular distribution of the
  classical derivative (`distDeriv_of_contDiffOn`).
* 1.16.9_5: `μ_α = Dα` (`dlmf_1_16_9_5`). It rests on the integration by parts
  `∫ φ dα = −∫ α φ'` (`integral_stieltjes_eq_neg`), proved by Fubini with
  `φ(x) = −∫_{t ≥ x} φ'`. In the absolutely continuous case `Dα = Λ_w`
  (`distDeriv_stieltjes_of_density`).
* 1.16.10–1.16.12: the Dirac delta `δ_{x₀}` (`diracDist`) and `⟨δ_{x₀}⁽ⁿ⁾, φ⟩ = (−1)ⁿ φ⁽ⁿ⁾(x₀)`.
  `δ_{x₀}` is singular for `x₀ ∈ I` (`diracDist_not_isRegular`). Bump functions `φ` with
  `φ(x₀) = 1` supported in `[x₀ − r, x₀ + r]` would give `1 ≤ ∫_{|x−x₀|≤r} |f| → 0`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

variable {I : Set ℝ}

/-! ### Differentiation on `𝒟(I)` -/

theorem isTestFunction_deriv {φ : ℝ → ℂ} (hφ : IsTestFunction I φ) :
    IsTestFunction I (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.mp hφ.1).2, hφ.2.1.deriv, tsupport_deriv_subset.trans hφ.2.2⟩

/-- Differentiation `φ ↦ φ'` as a linear map on `𝒟(I)`. -/
noncomputable def derivTest (I : Set ℝ) : testSpace I →ₗ[ℂ] testSpace I where
  toFun φ := ⟨deriv (φ : ℝ → ℂ), isTestFunction_deriv φ.2⟩
  map_add' φ ψ := by
    ext x
    simp only [Submodule.coe_add, Pi.add_apply]
    exact deriv_add ((φ.2.1.differentiable (by simp)) x) ((ψ.2.1.differentiable (by simp)) x)
  map_smul' c φ := by
    ext x
    simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply]
    exact deriv_const_smul c ((φ.2.1.differentiable (by simp)) x)

theorem coe_derivTest (φ : testSpace I) : (derivTest I φ : ℝ → ℂ) = deriv (φ : ℝ → ℂ) := rfl

theorem coe_derivTest_iterate (k : ℕ) (φ : testSpace I) :
    ((derivTest I)^[k] φ : ℝ → ℂ) = iteratedDeriv k (φ : ℝ → ℂ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coe_derivTest, ih, iteratedDeriv_succ]

/-- Differentiation preserves convergence in `𝒟(I)`. -/
theorem TestConverges.deriv {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ} (h : TestConverges I φs φ) :
    TestConverges I (fun n => _root_.deriv (φs n)) (_root_.deriv φ) := by
  obtain ⟨K, hK, hKI, hs, hφK, hu⟩ := h
  refine ⟨K, hK, hKI, fun n => tsupport_deriv_subset.trans (hs n),
    tsupport_deriv_subset.trans hφK, fun k => ?_⟩
  simp only [← iteratedDeriv_succ']
  exact hu (k + 1)

/-! ### Derivatives of distributions (1.16.8–1.16.9) -/

/-- DLMF 1.16.8: the derivative `⟨Λ', φ⟩ = −⟨Λ, φ'⟩` of a distribution. -/
noncomputable def derivDist (Λ : testSpace I →ₗ[ℂ] ℂ) : testSpace I →ₗ[ℂ] ℂ :=
  -(Λ ∘ₗ derivTest I)

theorem dlmf_1_16_8 (Λ : testSpace I →ₗ[ℂ] ℂ) (φ : testSpace I) :
    derivDist Λ φ = -Λ (derivTest I φ) := rfl

theorem isDistribution_derivDist {Λ : testSpace I →ₗ[ℂ] ℂ} (hΛ : IsDistribution I Λ) :
    IsDistribution I (derivDist Λ) :=
  fun φs φ h => (hΛ (fun n => derivTest I (φs n)) (derivTest I φ) h.deriv).neg

/-- DLMF 1.16.9: `⟨Λ⁽ᵏ⁾, φ⟩ = (−1)ᵏ ⟨Λ, φ⁽ᵏ⁾⟩`, where `φ⁽ᵏ⁾ = (derivTest I)^[k] φ` is the
`k`-th derivative of `φ`. -/
theorem dlmf_1_16_9 (Λ : testSpace I →ₗ[ℂ] ℂ) (k : ℕ) (φ : testSpace I) :
    (derivDist^[k] Λ) φ = (-1) ^ k * Λ ((derivTest I)^[k] φ) ∧
      ((derivTest I)^[k] φ : ℝ → ℂ) = iteratedDeriv k (φ : ℝ → ℂ) := by
  refine ⟨?_, coe_derivTest_iterate k φ⟩
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', dlmf_1_16_8, ih, Function.iterate_succ_apply]
    ring

theorem isDistribution_derivDist_iterate {Λ : testSpace I →ₗ[ℂ] ℂ} (hΛ : IsDistribution I Λ)
    (k : ℕ) : IsDistribution I (derivDist^[k] Λ) := by
  induction k with
  | zero => exact hΛ
  | succ k ih => rw [Function.iterate_succ_apply']; exact isDistribution_derivDist ih

/-! ### Distributional derivatives of functions -/

theorem locallyIntegrableOn_ofReal {g : ℝ → ℝ} {s : Set ℝ} (h : LocallyIntegrableOn g s) :
    LocallyIntegrableOn (fun x => (g x : ℂ)) s := fun x hx => by
  obtain ⟨t, ht, hint⟩ := h x hx
  exact ⟨t, ht, hint.ofReal⟩

/-- `Df = Λ_f'`: the distributional derivative of a locally integrable `f`. -/
noncomputable def distDeriv (hI : IsOpen I) {f : ℝ → ℂ} (hf : LocallyIntegrableOn f I) :
    testSpace I →ₗ[ℂ] ℂ :=
  derivDist (regularDist hI hf)

theorem distDeriv_apply (hI : IsOpen I) {f : ℝ → ℂ} (hf : LocallyIntegrableOn f I)
    (φ : testSpace I) :
    distDeriv hI hf φ = -∫ x in I, f x * deriv (φ : ℝ → ℂ) x := rfl

theorem contDiff_one_mul_of_contDiffOn {f φ : ℝ → ℂ} (hI : IsOpen I) (hf : ContDiffOn ℝ 1 f I)
    (hφ : ContDiff ℝ 1 φ) (hs : tsupport φ ⊆ I) : ContDiff ℝ 1 fun x => f x * φ x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ I
  · exact (hf.contDiffAt (hI.mem_nhds hx)).mul hφ.contDiffAt
  · have hev : (fun y => f y * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hs h)] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem deriv_mul_of_contDiffOn {f φ : ℝ → ℂ} (hI : IsOpen I) (hf : ContDiffOn ℝ 1 f I)
    (hφ : ContDiff ℝ 1 φ) (hs : tsupport φ ⊆ I) (x : ℝ) :
    deriv (fun y => f y * φ y) x = deriv f x * φ x + f x * deriv φ x := by
  by_cases hx : x ∈ I
  · exact deriv_mul ((hf.contDiffAt (hI.mem_nhds hx)).differentiableAt one_ne_zero)
      (hφ.differentiable one_ne_zero x)
  · have hxs : x ∉ tsupport φ := fun h => hx (hs h)
    have hev : (fun y => f y * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
      simp [hy]
    rw [hev.deriv_eq, deriv_const, image_eq_zero_of_notMem_tsupport hxs,
      image_eq_zero_of_notMem_tsupport fun h => hxs (tsupport_deriv_subset h)]
    simp

theorem exists_Ioo_superset_tsupport {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, x ∉ Ioo (-R) R → g x = 0 := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx ?_⟩
  have := hR h
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  rw [mem_Ioo]
  constructor <;> cases abs_le.mp (this.trans (le_abs_self R)) <;> linarith

/-- `∫ g' = 0` for `g` of class `C¹` with compact support. -/
theorem integral_deriv_eq_zero_of_hasCompactSupport {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) : ∫ x, deriv g x = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_Ioo_superset_tsupport hs
  obtain ⟨R', hR'0, hR'⟩ := exists_Ioo_superset_tsupport hs.deriv
  set T := max R R'
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-T) T) fun x hx =>
    hR' x fun h => hx ⟨by linarith [h.1, le_max_right R R'], by linarith [h.2, le_max_right R R']⟩,
    ← intervalIntegral.integral_of_le (by linarith [le_max_left R R']),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hg.differentiable one_ne_zero x).hasDerivAt)
      ((hg.continuous_deriv le_rfl).intervalIntegrable _ _),
    hR T fun h => by linarith [h.2, le_max_left R R'],
    hR (-T) fun h => by linarith [h.1, le_max_left R R'], sub_zero]

/-- For `f` of class `C¹` on `I`, the distributional derivative is the regular distribution of
the classical derivative: `Df = Λ_{f'}`. -/
theorem distDeriv_of_contDiffOn (hI : IsOpen I) {f : ℝ → ℂ} (hf : ContDiffOn ℝ 1 f I)
    (φ : testSpace I) :
    distDeriv hI (hf.continuousOn.locallyIntegrableOn hI.measurableSet) φ =
      regularDist hI ((hf.continuousOn_deriv_of_isOpen hI le_rfl).locallyIntegrableOn
        hI.measurableSet) φ := by
  rw [distDeriv_apply, dlmf_1_16_3]
  have hφ1 : ContDiff ℝ 1 (φ : ℝ → ℂ) := φ.2.1.of_le (by exact_mod_cast le_top)
  have h1 := integrableOn_mul_testFunction (μ := volume) hI
    ((hf.continuousOn_deriv_of_isOpen hI le_rfl).locallyIntegrableOn hI.measurableSet) φ.2
  have h2 := integrableOn_mul_testFunction (μ := volume) hI
    (hf.continuousOn.locallyIntegrableOn hI.measurableSet) (isTestFunction_deriv φ.2)
  have hsum : ∫ x in I, (deriv f x * (φ : ℝ → ℂ) x + f x * deriv (φ : ℝ → ℂ) x) = 0 := by
    have e := integral_deriv_eq_zero_of_hasCompactSupport
      (contDiff_one_mul_of_contDiffOn hI hf hφ1 φ.2.2.2) (φ.2.2.1.mul_left (f := f))
    simp_rw [deriv_mul_of_contDiffOn hI hf hφ1 φ.2.2.2] at e
    rwa [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have hxs : x ∉ tsupport (φ : ℝ → ℂ) := fun h => hx (φ.2.2.2 h)
      rw [image_eq_zero_of_notMem_tsupport hxs,
        image_eq_zero_of_notMem_tsupport fun h => hxs (tsupport_deriv_subset h)]
      simp] at e
  rw [integral_add h1 h2] at hsum
  linear_combination -hsum

/-! ### `μ_α = Dα` (1.16.9_5) -/

/-- Integration by parts against a Lebesgue–Stieltjes measure:
`∫ φ dα = −∫ α φ' dx` for `φ` of class `C¹` with compact support. -/
theorem integral_stieltjes_eq_neg (α : StieltjesFunction ℝ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) :
    ∫ x, φ x ∂α.measure = -∫ x, (α x : ℂ) * deriv φ x := by
  obtain ⟨R, hR0, hR⟩ := exists_Ioo_superset_tsupport hs
  obtain ⟨R', hR'0, hR'⟩ := exists_Ioo_superset_tsupport hs.deriv
  set T := max R R'
  set c := -T - 1
  set d := T + 1
  set S := Ioc c d
  have hRT := le_max_left R R'
  have hR'T := le_max_right R R'
  have hzero : ∀ x, x ∉ Ioo (-T) T → φ x = 0 := fun x hx =>
    hR x fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
  have hzero' : ∀ x, x ∉ Ioo (-T) T → deriv φ x = 0 := fun x hx =>
    hR' x fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
  have hoS : ∀ x, x ∉ S → x ∉ Ioo (-T) T := fun x hx h =>
    hx ⟨by linarith [h.1], by linarith [h.2]⟩
  set μ := α.measure
  have : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hφ' := hφ.continuous_deriv le_rfl
  have hint' : IntervalIntegrable (deriv φ) volume c d := hφ'.intervalIntegrable _ _
  have hFTC : ∀ a b, ∫ t in a..b, deriv φ t = φ b - φ a := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt) (hφ'.intervalIntegrable _ _)
  have hφd : φ d = 0 := hzero d fun h => by linarith [h.2]
  have hφc : φ c = 0 := hzero c fun h => by linarith [h.1]
  -- `φ x = −∫_{t ∈ S, t ≥ x} φ'(t) dt` on `S`
  set F : ℝ → ℝ → ℂ := fun x t => if x ≤ t then deriv φ t else 0
  have hrep : ∀ x ∈ S, φ x = -∫ t in S, F x t := fun x hx => by
    have e : ∫ t in S, F x t = ∫ t in Icc x d, deriv φ t := by
      have : (fun t => F x t) = (Ici x).indicator (deriv φ) := funext fun t => by
        simp only [F, indicator, mem_Ici]
      have hset : S ∩ Ici x = Icc x d := by
        ext t
        simp only [S, mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [hx.1], h2⟩, h1⟩
      rw [this, setIntegral_indicator measurableSet_Ici, hset]
    rw [e, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.2, hFTC, hφd]
    ring
  have hL : ∫ x, φ x ∂μ = -∫ x in S, (∫ t in S, F x t) ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) fun x hx => hzero x (hoS x hx),
      ← integral_neg]
    exact setIntegral_congr_fun (μ := μ) measurableSet_Ioc hrep
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := c) (b := d)).exists_bound_of_continuousOn
    hφ'.continuousOn
  have hFi : Integrable (Function.uncurry F) ((μ.restrict S).prod (volume.restrict S)) := by
    refine (integrable_const (max M 0)).mono' ?_ (ae_of_all _ fun p => ?_)
    · exact (Measurable.ite (measurableSet_le measurable_fst measurable_snd)
        (hφ'.measurable.comp measurable_snd) measurable_const).aestronglyMeasurable
    · simp only [Function.uncurry, F]
      split_ifs
      · by_cases hp : p.2 ∈ Icc c d
        · exact (hM _ hp).trans (le_max_left _ _)
        · rw [hzero' p.2 fun h => hp ⟨by linarith [h.1], by linarith [h.2]⟩, norm_zero]
          exact le_max_right _ _
      · rw [norm_zero]; exact le_max_right _ _
  rw [hL, integral_integral_swap hFi]
  have hinner : ∀ t ∈ S, ∫ x in S, F x t ∂μ = ((α t - α c : ℝ) : ℂ) * deriv φ t := fun t ht => by
    have : (fun x => F x t) = (Iic t).indicator (fun _ => deriv φ t) := funext fun x => by
      simp only [F, indicator, mem_Iic]
    rw [this, setIntegral_indicator measurableSet_Iic, setIntegral_const]
    have hset : S ∩ Iic t = Ioc c t := by
      ext x
      simp only [S, mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans ht.2⟩, h2⟩
    rw [hset, measureReal_def, α.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (α.mono ht.1.le)), Complex.real_smul]
  rw [setIntegral_congr_fun measurableSet_Ioc hinner]
  have hαi : IntegrableOn (fun t => (α t : ℂ) * deriv φ t) S :=
    (((α.mono.locallyIntegrable (μ := volume)).integrableOn_isCompact
      isCompact_Icc).ofReal.mul_continuousOn hφ'.continuousOn isCompact_Icc).mono_set
        Ioc_subset_Icc_self
  have hci : IntegrableOn (fun t => (α c : ℂ) * deriv φ t) S :=
    (hint'.1.const_mul _)
  have e2 : ∫ t in S, ((α t - α c : ℝ) : ℂ) * deriv φ t =
      (∫ t in S, (α t : ℂ) * deriv φ t) - ∫ t in S, (α c : ℂ) * deriv φ t := by
    rw [show (fun t => ((α t - α c : ℝ) : ℂ) * deriv φ t) =
      fun t => (α t : ℂ) * deriv φ t - (α c : ℂ) * deriv φ t from funext fun t => by
        push_cast; ring]
    rw [integral_sub hαi hci]
  rw [e2, integral_const_mul, ← intervalIntegral.integral_of_le (f := deriv φ) (by linarith),
    hFTC, hφd, hφc]
  simp only [sub_zero, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hzero' x (hoS x hx), mul_zero]]

theorem locallyIntegrableOn_stieltjes (α : StieltjesFunction ℝ) (I : Set ℝ) :
    LocallyIntegrableOn (fun x => (α x : ℂ)) I :=
  locallyIntegrableOn_ofReal ((α.mono.locallyIntegrable (μ := volume)).locallyIntegrableOn I)

/-- DLMF 1.16.9_5: `μ_α = Dα`. -/
theorem dlmf_1_16_9_5 (hI : IsOpen I) (α : StieltjesFunction ℝ) :
    stieltjesDist hI α = distDeriv hI (locallyIntegrableOn_stieltjes α I) := by
  ext φ
  rw [dlmf_1_16_3_5, distDeriv_apply,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 h),
    integral_stieltjes_eq_neg α (φ.2.1.of_le (by exact_mod_cast le_top)) φ.2.2.1,
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := I) fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 (tsupport_deriv_subset h)),
        mul_zero]]

/-- DLMF §1.16(ii): if `μ_α` is absolutely continuous with density `w` (in the sense of 1.4.23_1),
then `Dα = Λ_w`. -/
theorem distDeriv_stieltjes_of_density (hI : IsOpen I) {α : StieltjesFunction ℝ} {w : ℝ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (hwi : LocallyIntegrable w volume)
    (hα : ∀ c d, c ≤ d → α d - α c = ∫ x in c..d, w x) :
    distDeriv hI (locallyIntegrableOn_stieltjes α I) =
      regularDist hI (locallyIntegrableOn_ofReal (hwi.locallyIntegrableOn I)) := by
  ext φ
  rw [← dlmf_1_16_9_5, dlmf_1_16_3_5, dlmf_1_16_3, dlmf_1_4_23_1 hw0 hwi hα,
    restrict_withDensity hI.measurableSet,
    integral_withDensity_eq_integral_toReal_smul₀
      (hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hI.measurableSet fun x _ => ?_
  rw [ENNReal.toReal_ofReal (hw0 x), Complex.real_smul]

/-! ### The Dirac delta (1.16.10–1.16.12) -/

/-- DLMF 1.16.11: the Dirac delta `⟨δ_{x₀}, φ⟩ = φ(x₀)`. -/
noncomputable def diracDist (I : Set ℝ) (x₀ : ℝ) : testSpace I →ₗ[ℂ] ℂ where
  toFun φ := (φ : ℝ → ℂ) x₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dlmf_1_16_11 (x₀ : ℝ) (φ : testSpace I) : diracDist I x₀ φ = (φ : ℝ → ℂ) x₀ := rfl

/-- DLMF 1.16.10: `⟨δ, φ⟩ = φ(0)`. -/
theorem dlmf_1_16_10 (φ : testSpace I) : diracDist I 0 φ = (φ : ℝ → ℂ) 0 := rfl

theorem isDistribution_diracDist (x₀ : ℝ) : IsDistribution I (diracDist I x₀) := by
  rintro φs φ ⟨K, -, -, hs, hφK, hu⟩
  simp only [dlmf_1_16_11]
  by_cases hx : x₀ ∈ K
  · simpa using (hu 0).tendsto_at hx
  · have h1 : ∀ n, (φs n : ℝ → ℂ) x₀ = 0 := fun n =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hs n h)
    simp only [h1, image_eq_zero_of_notMem_tsupport fun h => hx (hφK h)]
    exact tendsto_const_nhds

/-- DLMF 1.16.12: `⟨δ_{x₀}⁽ⁿ⁾, φ⟩ = (−1)ⁿ φ⁽ⁿ⁾(x₀)`. -/
theorem dlmf_1_16_12 (x₀ : ℝ) (n : ℕ) (φ : testSpace I) :
    (derivDist^[n] (diracDist I x₀)) φ = (-1) ^ n * iteratedDeriv n (φ : ℝ → ℂ) x₀ := by
  obtain ⟨h1, h2⟩ := dlmf_1_16_9 (diracDist I x₀) n φ
  rw [h1, dlmf_1_16_11, h2]

/-- DLMF §1.16(iii): the Dirac delta `δ_{x₀}`, `x₀ ∈ I`, is singular. -/
theorem diracDist_not_isRegular (hI : IsOpen I) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ¬ IsRegularDist hI (diracDist I x₀) := by
  rintro ⟨f, hf, hΛ⟩
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp hI x₀ hx₀
  set R := R₀ / 2
  have hR : 0 < R := by positivity
  have hcl : Metric.closedBall x₀ R ⊆ I :=
    (Metric.closedBall_subset_ball (show R₀ / 2 < R₀ by linarith)).trans hball
  set r : ℕ → ℝ := fun n => R / (n + 1)
  have hr : ∀ n, 0 < r n := fun n => by positivity
  have hrR : ∀ n, r n ≤ R := fun n =>
    div_le_self hR.le (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  set s : ℕ → Set ℝ := fun n => Metric.closedBall x₀ (r n)
  have hfi : IntegrableOn f (s 0) :=
    hf.integrableOn_compact_subset ((Metric.closedBall_subset_closedBall (hrR 0)).trans hcl)
      (isCompact_closedBall _ _)
  -- the bumps `φₙ`
  have hbound : ∀ n, 1 ≤ ∫ x in s n, ‖f x‖ := fun n => by
    let b : ContDiffBump x₀ := ⟨r n / 2, r n, by linarith [hr n], by linarith [hr n]⟩
    have hT : IsTestFunction I fun x => ((b x : ℝ) : ℂ) :=
      ⟨Complex.ofRealCLM.contDiff.comp b.contDiff,
        b.hasCompactSupport.comp_left Complex.ofReal_zero,
        (tsupport_comp_subset Complex.ofReal_zero _).trans
          (by rw [b.tsupport_eq]; exact (Metric.closedBall_subset_closedBall (hrR n)).trans hcl)⟩
    have h1 := LinearMap.congr_fun hΛ ⟨_, hT⟩
    rw [dlmf_1_16_11, dlmf_1_16_3] at h1
    have hb1 : (b x₀ : ℂ) = 1 := by
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
    simp only [hb1] at h1
    have hsn : s n ⊆ I := (Metric.closedBall_subset_closedBall (hrR n)).trans hcl
    have hts : tsupport (fun x => ((b x : ℝ) : ℂ)) ⊆ s n :=
      (tsupport_comp_subset Complex.ofReal_zero _).trans (by rw [b.tsupport_eq])
    rw [setIntegral_mul_testFunction_eq (K := s n) hI hsn hts] at h1
    have hfin : IntegrableOn f (s n) := hfi.mono_set (Metric.closedBall_subset_closedBall
      (div_le_div_of_nonneg_left hR.le (by positivity) (by simp)))
    calc (1 : ℝ) = ‖∫ x in s n, f x * ((b x : ℝ) : ℂ)‖ := by rw [← h1]; simp
      _ ≤ ∫ x in s n, ‖f x‖ := by
        refine norm_integral_le_of_norm_le hfin.norm (ae_of_all _ fun x => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg b.nonneg]
        exact mul_le_of_le_one_right (norm_nonneg _) b.le_one
  have hanti : Antitone s := fun m n hmn => Metric.closedBall_subset_closedBall
    (div_le_div_of_nonneg_left hR.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1))
  have hinter : (⋂ n, s n) = {x₀} := by
    ext x
    simp only [mem_iInter, mem_singleton_iff, s, Metric.mem_closedBall]
    constructor
    · intro h
      by_contra hne
      have hd : 0 < dist x x₀ := dist_pos.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hd hR)
      have := h n
      have e : r n = R * (1 / ((n : ℝ) + 1)) := by simp only [r]; ring
      rw [e] at this
      rw [lt_div_iff₀ hR] at hn
      linarith
    · rintro rfl n
      rw [dist_self]; exact (hr n).le
  have hlim := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖f x‖)
    (fun n => Metric.isClosed_closedBall.measurableSet) hanti ⟨0, hfi.norm⟩
  rw [hinter, setIntegral_measure_zero _ (Real.volume_singleton)] at hlim
  linarith [ge_of_tendsto' hlim hbound]

end Azurite.DLMF
