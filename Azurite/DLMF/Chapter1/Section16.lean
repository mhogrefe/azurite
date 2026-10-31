/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section4
import Mathlib.Analysis.Distribution.Distribution

/-!
# DLMF §1.16(i): Test functions and distributions

https://dlmf.nist.gov/1.16.i

Test functions on an open set `I ⊆ ℝ` (DLMF: an open interval `(a, b)`, possibly infinite), with
complex values, and distributions as sequentially continuous linear functionals.

* Support and compact support (`dlmf_1_16_i_support`). Test functions `IsTestFunction`, the space
  `testSpace I` (`𝒟(I)`), and the agreement with Mathlib's `𝓓(Ω, ℂ)`
  (`isTestFunction_iff_testFunction`).
* Convergence in `𝒟(I)`: DLMF's literal definition `TestConvergesDLMF` and the corrected
  `TestConverges`, which has unique limits (`TestConverges.unique`).
* 1.16.1–1.16.2: linear functionals, `IsDistribution`, and the space `distributionSpace I`
  (`𝒟*(I)`). 1.16.4–1.16.5 cover sums and scalar multiples.
* 1.16.3: the regular distributions `regularDist` of locally integrable `f`. Such a distribution
  determines `f` almost everywhere on `I` (`regularDist_ae_eq`, from Mathlib's fundamental lemma).
  1.16.3_5 is the Lebesgue–Stieltjes measure as a distribution (`stieltjesDist`). Both are cases
  of `weightedDist`, `φ ↦ ∫_I f φ dμ`.
* 1.16.6: `αΛ` for `α` infinitely differentiable on `I` (`mulDist`). Continuity comes from the
  Leibniz bound (`TestConverges.mul`).
* 1.16.7: convergence of distributions (`DistConverges`), with the example `Λ_{fₙ} → Λ_f` for
  `fₙ → f` in `L¹` on compact subsets of `I`.

DLMF discrepancy: DLMF's convergence of test functions asks the supports of the `φₙ` to lie in a
fixed compact `K`, with `φₙ⁽ᵏ⁾ → φ⁽ᵏ⁾` uniformly on `K`. It puts no condition on the support of
the limit `φ`. Then the zero sequence converges to every test function: take `K` a single point
of `I` outside `supp φ` (`testConvergesDLMF_zero`). So the only "distribution" is `0`
(`dlmf_1_16_2_literal`), and even the regular `Λ_f` would not qualify. The standard definition
also requires `supp φ ⊆ K` (`TestConverges`), and is used throughout.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

/-! ### Test functions -/

/-- DLMF §1.16(i): the support of `φ` is the closure of the set where `φ ≠ 0`. -/
theorem dlmf_1_16_i_support (φ : ℝ → ℂ) : tsupport φ = closure {x | φ x ≠ 0} := rfl

/-- DLMF §1.16(i): `φ` has compact support when its support is compact. -/
theorem dlmf_1_16_i_compact_support (φ : ℝ → ℂ) :
    HasCompactSupport φ ↔ IsCompact (closure {x | φ x ≠ 0}) := Iff.rfl

/-- DLMF §1.16(i): a test function on the open set `I`: an infinitely differentiable function of
compact support, the support lying in `I`. -/
def IsTestFunction (I : Set ℝ) (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ I

/-- The linear space `𝒟(I)` of test functions. -/
def testSpace (I : Set ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {φ | IsTestFunction I φ}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  smul_mem' := fun c φ hφ =>
    ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left (f := fun _ => c),
      (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.2.2⟩

theorem mem_testSpace {I : Set ℝ} {φ : ℝ → ℂ} : φ ∈ testSpace I ↔ IsTestFunction I φ := Iff.rfl

/-- Test functions in the sense of DLMF are exactly Mathlib's `𝓓(Ω, ℂ)` on `Ω = I`. -/
theorem isTestFunction_iff_testFunction {I : Set ℝ} (hI : IsOpen I) (φ : ℝ → ℂ) :
    IsTestFunction I φ ↔ ∃ ψ : TestFunction ⟨I, hI⟩ ℂ ⊤, ⇑ψ = φ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨φ, h1, h2, h3⟩, rfl⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩

theorem iteratedDeriv_eq_zero_of_notMem_tsupport {φ : ℝ → ℂ} {p : ℝ} (hp : p ∉ tsupport φ)
    (k : ℕ) : iteratedDeriv k φ p = 0 := by
  rw [(notMem_tsupport_iff_eventuallyEq.mp hp).iteratedDeriv_eq k]
  simp

/-- A nonempty open subset of `ℝ` is not contained in a compact set lying inside it. -/
theorem exists_mem_diff_of_isCompact {I K : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty)
    (hK : IsCompact K) (hKI : K ⊆ I) : ∃ p ∈ I, p ∉ K := by
  by_contra h
  push Not at h
  have hIK : I = K := Subset.antisymm h hKI
  have hc : IsClopen I := ⟨by rw [hIK]; exact hK.isClosed, hI⟩
  rcases isClopen_iff.mp hc with h0 | h1
  · exact hne.ne_empty h0
  · rw [hIK] at h1
    exact noncompact_univ ℝ (h1 ▸ hK)

/-! ### Convergence of test functions -/

/-- DLMF's convergence of test functions, taken literally: the supports of all `φₙ` lie in a
fixed compact `K ⊆ I`, and `φₙ⁽ᵏ⁾ → φ⁽ᵏ⁾` uniformly on `K` for every `k`. -/
def TestConvergesDLMF (I : Set ℝ) (φs : ℕ → ℝ → ℂ) (φ : ℝ → ℂ) : Prop :=
  ∃ K, IsCompact K ∧ K ⊆ I ∧ (∀ n, tsupport (φs n) ⊆ K) ∧
    ∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedDeriv k (φs n)) (iteratedDeriv k φ) atTop K

/-- Convergence in `𝒟(I)`, corrected: as in `TestConvergesDLMF`, and also the support of the
limit `φ` lies in `K`. -/
def TestConverges (I : Set ℝ) (φs : ℕ → ℝ → ℂ) (φ : ℝ → ℂ) : Prop :=
  ∃ K, IsCompact K ∧ K ⊆ I ∧ (∀ n, tsupport (φs n) ⊆ K) ∧ tsupport φ ⊆ K ∧
    ∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedDeriv k (φs n)) (iteratedDeriv k φ) atTop K

theorem TestConverges.testConvergesDLMF {I : Set ℝ} {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (h : TestConverges I φs φ) : TestConvergesDLMF I φs φ := by
  obtain ⟨K, hK, hKI, hs, -, hu⟩ := h
  exact ⟨K, hK, hKI, hs, hu⟩

/-- Under DLMF's literal definition the zero sequence converges to every test function. -/
theorem testConvergesDLMF_zero {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty) {φ : ℝ → ℂ}
    (hφ : IsTestFunction I φ) : TestConvergesDLMF I (fun _ => 0) φ := by
  obtain ⟨p, hpI, hp⟩ := exists_mem_diff_of_isCompact hI hne hφ.2.1 hφ.2.2
  refine ⟨{p}, isCompact_singleton, singleton_subset_iff.mpr hpI, fun n => by simp, fun k => ?_⟩
  rw [tendstoUniformlyOn_singleton_iff_tendsto, iteratedDeriv_eq_zero_of_notMem_tsupport hp k]
  simp

/-- Limits are unique for the corrected convergence. -/
theorem TestConverges.unique {I : Set ℝ} {φs : ℕ → ℝ → ℂ} {φ ψ : ℝ → ℂ}
    (h₁ : TestConverges I φs φ) (h₂ : TestConverges I φs ψ) : φ = ψ := by
  obtain ⟨K₁, -, -, hs₁, hφ, hu₁⟩ := h₁
  obtain ⟨K₂, -, -, hs₂, hψ, hu₂⟩ := h₂
  have hz : ∀ (L : Set ℝ) (x : ℝ), x ∉ L → (∀ n, tsupport (φs n) ⊆ L) → ∀ n, φs n x = 0 :=
    fun L x hx hs n => image_eq_zero_of_notMem_tsupport fun h => hx (hs n h)
  funext x
  by_cases h1 : x ∈ K₁ <;> by_cases h2 : x ∈ K₂
  · have l1 := (hu₁ 0).tendsto_at h1
    have l2 := (hu₂ 0).tendsto_at h2
    simp only [iteratedDeriv_zero] at l1 l2
    exact tendsto_nhds_unique l1 l2
  · have l1 := (hu₁ 0).tendsto_at h1
    simp only [iteratedDeriv_zero, hz K₂ x h2 hs₂] at l1
    rw [tendsto_nhds_unique l1 tendsto_const_nhds,
      image_eq_zero_of_notMem_tsupport fun h => h2 (hψ h)]
  · have l2 := (hu₂ 0).tendsto_at h2
    simp only [iteratedDeriv_zero, hz K₁ x h1 hs₁] at l2
    rw [tendsto_nhds_unique l2 tendsto_const_nhds,
      image_eq_zero_of_notMem_tsupport fun h => h1 (hφ h)]
  · rw [image_eq_zero_of_notMem_tsupport fun h => h1 (hφ h),
      image_eq_zero_of_notMem_tsupport fun h => h2 (hψ h)]

/-! ### Distributions (1.16.1–1.16.2) -/

/-- DLMF 1.16.1: a linear functional `Λ : 𝒟(I) → ℂ` satisfies
`Λ(α₁φ₁ + α₂φ₂) = α₁Λ(φ₁) + α₂Λ(φ₂)`. -/
theorem dlmf_1_16_1 {I : Set ℝ} (Λ : testSpace I →ₗ[ℂ] ℂ) (α₁ α₂ : ℂ) (φ₁ φ₂ : testSpace I) :
    Λ (α₁ • φ₁ + α₂ • φ₂) = α₁ * Λ φ₁ + α₂ * Λ φ₂ := by simp

/-- DLMF 1.16.2: a distribution is a linear functional with `Λ(φₙ) → Λ(φ)` whenever `φₙ → φ` in
`𝒟(I)`. -/
def IsDistribution (I : Set ℝ) (Λ : testSpace I →ₗ[ℂ] ℂ) : Prop :=
  ∀ (φs : ℕ → testSpace I) (φ : testSpace I), TestConverges I (fun n => φs n) φ →
    Tendsto (fun n => Λ (φs n)) atTop (𝓝 (Λ φ))

/-- The same notion with DLMF's literal convergence `TestConvergesDLMF`. -/
def IsDistributionDLMF (I : Set ℝ) (Λ : testSpace I →ₗ[ℂ] ℂ) : Prop :=
  ∀ (φs : ℕ → testSpace I) (φ : testSpace I), TestConvergesDLMF I (fun n => φs n) φ →
    Tendsto (fun n => Λ (φs n)) atTop (𝓝 (Λ φ))

/-- With DLMF's literal definition of convergence in `𝒟(I)`, the only "distribution" is `0`:
the zero sequence converges to every test function. -/
theorem dlmf_1_16_2_literal {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty)
    {Λ : testSpace I →ₗ[ℂ] ℂ} (h : IsDistributionDLMF I Λ) : Λ = 0 := by
  ext φ
  have hc : TestConvergesDLMF I (fun _ => ((0 : testSpace I) : ℝ → ℂ)) φ := by
    simpa using testConvergesDLMF_zero hI hne φ.2
  have := h (fun _ => 0) φ hc
  simp only [map_zero] at this
  exact (tendsto_nhds_unique tendsto_const_nhds this).symm

/-- The space `𝒟*(I)` of distributions. -/
def distributionSpace (I : Set ℝ) : Submodule ℂ (testSpace I →ₗ[ℂ] ℂ) where
  carrier := {Λ | IsDistribution I Λ}
  add_mem' := fun hΛ hM φs φ h => by
    simpa only [LinearMap.add_apply] using (hΛ φs φ h).add (hM φs φ h)
  zero_mem' := fun φs φ _ => by simp
  smul_mem' := fun c Λ hΛ φs φ h => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using (hΛ φs φ h).const_mul c

theorem mem_distributionSpace {I : Set ℝ} {Λ : testSpace I →ₗ[ℂ] ℂ} :
    Λ ∈ distributionSpace I ↔ IsDistribution I Λ := Iff.rfl

/-- DLMF 1.16.4: `⟨Λ₁ + Λ₂, φ⟩ = ⟨Λ₁, φ⟩ + ⟨Λ₂, φ⟩`. -/
theorem dlmf_1_16_4 {I : Set ℝ} (Λ₁ Λ₂ : distributionSpace I) (φ : testSpace I) :
    (((Λ₁ + Λ₂ : distributionSpace I) : testSpace I →ₗ[ℂ] ℂ)) φ =
      (Λ₁ : testSpace I →ₗ[ℂ] ℂ) φ + (Λ₂ : testSpace I →ₗ[ℂ] ℂ) φ := rfl

/-- DLMF 1.16.5: `⟨cΛ, φ⟩ = c⟨Λ, φ⟩ = ⟨Λ, cφ⟩`. -/
theorem dlmf_1_16_5 {I : Set ℝ} (c : ℂ) (Λ : distributionSpace I) (φ : testSpace I) :
    (((c • Λ : distributionSpace I) : testSpace I →ₗ[ℂ] ℂ)) φ =
        c * (Λ : testSpace I →ₗ[ℂ] ℂ) φ ∧
      c * (Λ : testSpace I →ₗ[ℂ] ℂ) φ = (Λ : testSpace I →ₗ[ℂ] ℂ) (c • φ) :=
  ⟨rfl, by rw [map_smul, smul_eq_mul]⟩

/-! ### Regular distributions and measures (1.16.3, 1.16.3_5) -/

section Weighted

variable {I : Set ℝ} {μ : Measure ℝ} {f : ℝ → ℂ}

theorem integrableOn_mul_testFunction (hI : IsOpen I) (hf : LocallyIntegrableOn f I μ)
    {φ : ℝ → ℂ} (hφ : IsTestFunction I φ) : IntegrableOn (fun x => f x * φ x) I μ := by
  have hK := hφ.2.1
  have hfK : IntegrableOn f (tsupport φ) μ := hf.integrableOn_compact_subset hφ.2.2 hK
  refine (hfK.mul_continuousOn hφ.1.continuous.continuousOn hK).of_forall_sdiff_eq_zero
    hI.measurableSet fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx.2, mul_zero]

theorem setIntegral_mul_testFunction_eq (hI : IsOpen I) {φ : ℝ → ℂ} {K : Set ℝ} (hKI : K ⊆ I)
    (hφK : tsupport φ ⊆ K) :
    ∫ x in I, f x * φ x ∂μ = ∫ x in K, f x * φ x ∂μ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := μ) (f := fun x => f x * φ x)
    hI.measurableSet hKI fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx.2 (hφK h), mul_zero]

/-- The functional `φ ↦ ∫_I f φ dμ` for `f` locally integrable on `I` with respect to `μ`. -/
noncomputable def weightedDist (hI : IsOpen I) (hf : LocallyIntegrableOn f I μ) :
    testSpace I →ₗ[ℂ] ℂ where
  toFun φ := ∫ x in I, f x * (φ : ℝ → ℂ) x ∂μ
  map_add' φ ψ := by
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add (integrableOn_mul_testFunction hI hf φ.2)
      (integrableOn_mul_testFunction hI hf ψ.2)
  map_smul' c φ := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1; funext x; ring

theorem weightedDist_apply (hI : IsOpen I) (hf : LocallyIntegrableOn f I μ) (φ : testSpace I) :
    weightedDist hI hf φ = ∫ x in I, f x * (φ : ℝ → ℂ) x ∂μ := rfl

/-- `φ ↦ ∫_I f φ dμ` is a distribution. -/
theorem isDistribution_weightedDist (hI : IsOpen I) (hf : LocallyIntegrableOn f I μ) :
    IsDistribution I (weightedDist hI hf) := by
  intro φs φ ⟨K, hK, hKI, hs, hφK, hu⟩
  have hfK : IntegrableOn f K μ := hf.integrableOn_compact_subset hKI hK
  set C := ∫ x in K, ‖f x‖ ∂μ
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (C + 1) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp (hu 0) _ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, weightedDist_apply, weightedDist_apply,
    ← integral_sub (integrableOn_mul_testFunction hI hf (φs n).2)
      (integrableOn_mul_testFunction hI hf φ.2)]
  have e : ∫ x in I, (f x * (φs n : ℝ → ℂ) x - f x * (φ : ℝ → ℂ) x) ∂μ =
      ∫ x in K, f x * ((φs n : ℝ → ℂ) x - (φ : ℝ → ℂ) x) ∂μ := by
    simp_rw [← mul_sub]
    exact setIntegral_mul_testFunction_eq hI hKI
      ((tsupport_sub _ _).trans (union_subset (hs n) hφK))
  rw [e]
  have hb : ‖∫ x in K, f x * ((φs n : ℝ → ℂ) x - (φ : ℝ → ℂ) x) ∂μ‖ ≤
      ∫ x in K, ‖f x‖ * (ε / (C + 1)) ∂μ := by
    refine norm_integral_le_of_norm_le (hfK.norm.mul_const _) ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have h1 := hN n hn x hx
    simp only [iteratedDeriv_zero] at h1
    rw [norm_mul, dist_comm, dist_eq_norm] at *
    exact mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
  rw [integral_mul_const] at hb
  calc _ ≤ C * (ε / (C + 1)) := hb
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

end Weighted

/-- DLMF 1.16.3: the regular distribution `⟨Λ_f, φ⟩ = ∫_I f(x) φ(x) dx` of a locally integrable
`f`. -/
noncomputable def regularDist {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f I) : testSpace I →ₗ[ℂ] ℂ :=
  weightedDist (μ := volume) hI hf

theorem dlmf_1_16_3 {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℂ} (hf : LocallyIntegrableOn f I)
    (φ : testSpace I) : regularDist hI hf φ = ∫ x in I, f x * (φ : ℝ → ℂ) x := rfl

theorem isDistribution_regularDist {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f I) : IsDistribution I (regularDist hI hf) :=
  isDistribution_weightedDist hI hf

/-- A distribution is regular if it is `Λ_f` for a locally integrable `f`, and singular
otherwise. -/
def IsRegularDist {I : Set ℝ} (hI : IsOpen I) (Λ : testSpace I →ₗ[ℂ] ℂ) : Prop :=
  ∃ (f : ℝ → ℂ) (hf : LocallyIntegrableOn f I volume), Λ = regularDist (f := f) hI hf

/-- A regular distribution determines its function almost everywhere on `I`. -/
theorem regularDist_ae_eq {I : Set ℝ} (hI : IsOpen I) {f g : ℝ → ℂ}
    (hf : LocallyIntegrableOn f I) (hg : LocallyIntegrableOn g I)
    (h : regularDist hI hf = regularDist hI hg) : ∀ᵐ x, x ∈ I → f x = g x := by
  have key := hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hf.sub hg)
    fun ψ hψ hψs hψI => ?_
  · filter_upwards [key] with x hx hxI
    exact sub_eq_zero.mp (hx hxI)
  · have hT : IsTestFunction I fun x => ((ψ x : ℝ) : ℂ) :=
      ⟨Complex.ofRealCLM.contDiff.comp hψ, hψs.comp_left Complex.ofReal_zero,
        (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψI⟩
    have h1 := LinearMap.congr_fun h ⟨_, hT⟩
    rw [dlmf_1_16_3, dlmf_1_16_3] at h1
    have e : ∫ x, ψ x • (f - g) x = ∫ x in I, (f x * ((ψ x : ℝ) : ℂ) - g x * ((ψ x : ℝ) : ℂ)) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hψI h), zero_smul]]
      refine setIntegral_congr_fun hI.measurableSet fun x _ => ?_
      simp only [Pi.sub_apply, Complex.real_smul]
      ring
    rw [e, integral_sub (integrableOn_mul_testFunction hI hf hT)
      (integrableOn_mul_testFunction hI hg hT)]
    exact sub_eq_zero.mpr h1

/-- DLMF 1.16.3_5: the Lebesgue–Stieltjes measure `μ_α` of a Stieltjes function as a distribution,
`⟨μ_α, φ⟩ = ∫_I φ(x) dα(x)`. -/
noncomputable def stieltjesDist {I : Set ℝ} (hI : IsOpen I) (α : StieltjesFunction ℝ) :
    testSpace I →ₗ[ℂ] ℂ :=
  weightedDist (μ := α.measure) (f := fun _ => 1) hI
    ((locallyIntegrable_const (1 : ℂ)).locallyIntegrableOn I)

theorem dlmf_1_16_3_5 {I : Set ℝ} (hI : IsOpen I) (α : StieltjesFunction ℝ) (φ : testSpace I) :
    stieltjesDist hI α φ = ∫ x in I, (φ : ℝ → ℂ) x ∂α.measure := by
  simp [stieltjesDist, weightedDist_apply]

theorem isDistribution_stieltjesDist {I : Set ℝ} (hI : IsOpen I) (α : StieltjesFunction ℝ) :
    IsDistribution I (stieltjesDist hI α) :=
  isDistribution_weightedDist _ _

/-! ### Multiplication by smooth functions (1.16.6) -/

section Mul

variable {I : Set ℝ}

theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- `α φ` is smooth when `α` is smooth on the open set `I` containing the support of `φ`. -/
theorem contDiff_mul_of_contDiffOn {α φ : ℝ → ℂ} (hI : IsOpen I) (hα : ContDiffOn ℝ ∞ α I)
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ I) : ContDiff ℝ ∞ fun x => α x * φ x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ I
  · exact (hα.contDiffAt (hI.mem_nhds hx)).mul hφ.contDiffAt
  · have hev : (fun y => α y * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hs h)] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem isTestFunction_mul {α φ : ℝ → ℂ} (hI : IsOpen I) (hα : ContDiffOn ℝ ∞ α I)
    (hφ : IsTestFunction I φ) : IsTestFunction I fun x => α x * φ x :=
  ⟨contDiff_mul_of_contDiffOn hI hα hφ.1 hφ.2.2, hφ.2.1.mul_left,
    (tsupport_mul_subset_right (f := α) (g := φ)).trans hφ.2.2⟩

/-- The Leibniz bound `|(α g)⁽ᵏ⁾(x)| ≤ ∑ C(k,i) |α⁽ⁱ⁾(x)| |g⁽ᵏ⁻ⁱ⁾(x)|` at points of `I`. -/
theorem norm_iteratedDeriv_mul_le {α g : ℝ → ℂ} (hI : IsOpen I) (hα : ContDiffOn ℝ ∞ α I)
    (hg : ContDiff ℝ ∞ g) {x : ℝ} (hx : x ∈ I) (k : ℕ) :
    ‖iteratedDeriv k (fun y => α y * g y) x‖ ≤ ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i α I x‖ * ‖iteratedDeriv (k - i) g x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_of_isOpen k hI hx]
  have h := norm_iteratedFDerivWithin_mul_le hα hg.contDiffOn hI.uniqueDiffOn hx
    (n := k) (by exact_mod_cast le_top)
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [iteratedFDerivWithin_of_isOpen (k - i) hI hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- Multiplication by `α` (smooth on `I`) preserves convergence in `𝒟(I)`. -/
theorem TestConverges.mul {α : ℝ → ℂ} (hI : IsOpen I) (hα : ContDiffOn ℝ ∞ α I)
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ} (hφs : ∀ n, IsTestFunction I (φs n))
    (hφ : IsTestFunction I φ) (h : TestConverges I φs φ) :
    TestConverges I (fun n x => α x * φs n x) (fun x => α x * φ x) := by
  obtain ⟨K, hK, hKI, hs, hφK, hu⟩ := h
  refine ⟨K, hK, hKI, fun n => (tsupport_mul_subset_right (f := α) (g := φs n)).trans (hs n),
    (tsupport_mul_subset_right (f := α) (g := φ)).trans hφK, fun k => ?_⟩
  have hB : ∀ i : ℕ, ∃ C, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ i α I x‖ ≤ C := fun i =>
    hK.exists_bound_of_continuousOn ((hα.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast le_top) hI.uniqueDiffOn).mono hKI)
  choose B hB using hB
  set S := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |B i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε / (S + 1) := by positivity
  have hev : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1), ∀ x ∈ K,
      dist (iteratedDeriv j φ x) (iteratedDeriv j (φs n) x) < ε / (S + 1) :=
    (Finset.eventually_all _).mpr fun j _ => Metric.tendstoUniformlyOn_iff.mp (hu j) _ hδ
  filter_upwards [hev] with n hn x hx
  have hxI := hKI hx
  have hsub : iteratedDeriv k (fun y => α y * φ y) x - iteratedDeriv k (fun y => α y * φs n y) x =
      iteratedDeriv k (fun y => α y * (φ y - φs n y)) x := by
    rw [← iteratedDeriv_sub
      ((contDiff_mul_of_contDiffOn hI hα hφ.1 hφ.2.2).contDiffAt.of_le
        (by exact_mod_cast le_top))
      ((contDiff_mul_of_contDiffOn hI hα (hφs n).1 (hφs n).2.2).contDiffAt.of_le
        (by exact_mod_cast le_top))]
    congr 1; funext y; simp only [Pi.sub_apply]; ring
  have hg : ContDiff ℝ ∞ fun y => φ y - φs n y := hφ.1.sub (hφs n).1
  rw [dist_eq_norm, hsub]
  refine (norm_iteratedDeriv_mul_le hI hα hg hxI k).trans_lt ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i α I x‖ *
        ‖iteratedDeriv (k - i) (fun y => φ y - φs n y) x‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |B i| * (ε / (S + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hki : k - i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        have h1 := hn (k - i) hki x hx
        rw [dist_eq_norm, ← iteratedDeriv_sub (hφ.1.contDiffAt.of_le (natCast_le_infty _))
          ((hφs n).1.contDiffAt.of_le (natCast_le_infty _))] at h1
        have h2 : ‖iteratedFDerivWithin ℝ i α I x‖ ≤ |B i| := (hB i x hx).trans (le_abs_self _)
        have h3 : ‖iteratedDeriv (k - i) (fun y => φ y - φs n y) x‖ ≤ ε / (S + 1) := h1.le
        gcongr
    _ = S * (ε / (S + 1)) := by rw [hS, Finset.sum_mul]
    _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

/-- Multiplication `φ ↦ αφ` on `𝒟(I)`, for `α` infinitely differentiable on `I`. -/
noncomputable def mulTest (hI : IsOpen I) {α : ℝ → ℂ} (hα : ContDiffOn ℝ ∞ α I) :
    testSpace I →ₗ[ℂ] testSpace I where
  toFun φ := ⟨fun x => α x * (φ : ℝ → ℂ) x, isTestFunction_mul hI hα φ.2⟩
  map_add' φ ψ := by
    ext x; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c φ := by
    ext x; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The distribution `αΛ`, defined by DLMF 1.16.6. -/
noncomputable def mulDist (hI : IsOpen I) {α : ℝ → ℂ} (hα : ContDiffOn ℝ ∞ α I)
    (Λ : testSpace I →ₗ[ℂ] ℂ) : testSpace I →ₗ[ℂ] ℂ :=
  Λ ∘ₗ mulTest hI hα

/-- DLMF 1.16.6: `⟨αΛ, φ⟩ = ⟨Λ, αφ⟩`. -/
theorem dlmf_1_16_6 (hI : IsOpen I) {α : ℝ → ℂ} (hα : ContDiffOn ℝ ∞ α I)
    (Λ : testSpace I →ₗ[ℂ] ℂ) (φ : testSpace I) :
    mulDist hI hα Λ φ = Λ ⟨fun x => α x * (φ : ℝ → ℂ) x, isTestFunction_mul hI hα φ.2⟩ := rfl

theorem isDistribution_mulDist (hI : IsOpen I) {α : ℝ → ℂ} (hα : ContDiffOn ℝ ∞ α I)
    {Λ : testSpace I →ₗ[ℂ] ℂ} (hΛ : IsDistribution I Λ) : IsDistribution I (mulDist hI hα Λ) :=
  fun φs φ h => hΛ (fun n => mulTest hI hα (φs n)) (mulTest hI hα φ)
    (h.mul hI hα (fun n => (φs n).2) φ.2)

end Mul

/-! ### Convergence of distributions (1.16.7) -/

/-- DLMF 1.16.7: `Λₙ → Λ` in `𝒟*(I)` when `⟨Λₙ, φ⟩ → ⟨Λ, φ⟩` for every test function `φ`. -/
def DistConverges (I : Set ℝ) (Λs : ℕ → testSpace I →ₗ[ℂ] ℂ) (Λ : testSpace I →ₗ[ℂ] ℂ) :
    Prop :=
  ∀ φ : testSpace I, Tendsto (fun n => Λs n φ) atTop (𝓝 (Λ φ))

theorem dlmf_1_16_7 {I : Set ℝ} (Λs : ℕ → testSpace I →ₗ[ℂ] ℂ) (Λ : testSpace I →ₗ[ℂ] ℂ) :
    DistConverges I Λs Λ ↔ ∀ φ : testSpace I, Tendsto (fun n => Λs n φ) atTop (𝓝 (Λ φ)) :=
  Iff.rfl

/-- Example of 1.16.7: if `∫_K |fₙ − f| → 0` on every compact `K ⊆ I`, then `Λ_{fₙ} → Λ_f`. -/
theorem distConverges_regularDist {I : Set ℝ} (hI : IsOpen I) {fs : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hfs : ∀ n, LocallyIntegrableOn (fs n) I) (hf : LocallyIntegrableOn f I)
    (hlim : ∀ K, IsCompact K → K ⊆ I →
      Tendsto (fun n => ∫ x in K, ‖fs n x - f x‖) atTop (𝓝 0)) :
    DistConverges I (fun n => regularDist hI (hfs n)) (regularDist hI hf) := by
  intro φ
  set K := tsupport (φ : ℝ → ℂ)
  have hK : IsCompact K := φ.2.2.1
  have hKI : K ⊆ I := φ.2.2.2
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn φ.2.1.continuous.continuousOn
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using (hlim K hK hKI).const_mul (max M 0))
  rw [dlmf_1_16_3, dlmf_1_16_3,
    setIntegral_mul_testFunction_eq (f := fs n) hI hKI subset_rfl,
    setIntegral_mul_testFunction_eq (f := f) hI hKI subset_rfl,
    ← integral_sub ((hfs n).integrableOn_compact_subset hKI hK |>.mul_continuousOn
      φ.2.1.continuous.continuousOn hK)
      (hf.integrableOn_compact_subset hKI hK |>.mul_continuousOn
        φ.2.1.continuous.continuousOn hK)]
  have hint : IntegrableOn (fun x => ‖fs n x - f x‖) K :=
    (((hfs n).integrableOn_compact_subset hKI hK).sub
      (hf.integrableOn_compact_subset hKI hK)).norm
  calc ‖∫ x in K, (fs n x * (φ : ℝ → ℂ) x - f x * (φ : ℝ → ℂ) x)‖
      ≤ ∫ x in K, max M 0 * ‖fs n x - f x‖ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        rw [← sub_mul, norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _)
    _ = max M 0 * ∫ x in K, ‖fs n x - f x‖ := integral_const_mul _ _

end Azurite.DLMF
