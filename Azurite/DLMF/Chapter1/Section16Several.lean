/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16Tempered
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# DLMF §1.16(vi): Distributions of several variables

https://dlmf.nist.gov/1.16.vi

Here `ℝⁿ` is `Fin n → ℝ` (with the sup norm), and functions are complex-valued.

* Partial derivatives `partialDeriv i` (`∂/∂xᵢ`) commute on smooth functions (Schwarz,
  `partialDeriv_comm`), so iterated partials along any word depend only on the multiplicities
  (`partialWord_perm`). DLMF's `φ⁽ᵏ⁾` is `mDeriv k`.
* `𝒟ₙ` (`IsTestFunctionN`, `testSpaceN`) is Mathlib's `𝓓(ℝⁿ, ℂ)`
  (`isTestFunctionN_iff_testFunction`).
* Convergence in `𝒟ₙ`: DLMF's literal `TestConvergesNDLMF` and the corrected `TestConvergesN`,
  which has unique limits.
* Distributions (`IsDistributionN`, `distSpaceN`). Partial derivatives of distributions
  `⟨∂ᵢΛ, φ⟩ = −⟨Λ, ∂ᵢφ⟩` (`partialDist`) and `⟨Λ⁽ᵏ⁾, φ⟩ = (−1)^{|k|}⟨Λ, φ⁽ᵏ⁾⟩`
  (`mDerivDist_apply`).
* 1.16.26–1.16.27: `regularDistN` (`Λ_f`) and `distDerivN` (`Dᵏf`).
* 1.16.28: `𝒯ₙ` (`IsTempTestN`, with monomials `xᵐ`). It is Mathlib's Schwartz space
  `𝓢(ℝⁿ, ℂ)` (`isTempTestN_iff_schwartz`), via `D^Nφ(x)(e_{τ₀}, …) = ∂_{τ₀} ⋯ φ(x)`
  (`iteratedFDeriv_unitVec`) and `‖f‖ ≤ ∑_τ ‖f(e_τ)‖` for multilinear maps
  (`norm_multilinear_le_sum`). Also `𝒟ₙ ⊆ 𝒯ₙ`.
* `𝒯*ₙ` (`IsTempDistN`, `temperedSpaceN`): continuous linear functionals on `𝒯ₙ` for the topology
  of the bounds 1.16.28 (that of `𝓢(ℝⁿ, ℂ)`), the elements of Mathlib's `𝓢'(ℝⁿ, ℂ)`
  (`isTempDistN_iff_exists_clm`).

DLMF discrepancy (as in §1.16(i)): the convergence in `𝒟ₙ` asks the supports of the `φₘ` to lie
in a fixed compact `K` with `φₘ⁽ᵏ⁾ → φ⁽ᵏ⁾` uniformly on `K`, and puts no condition on the limit.
For `n ≥ 1` the zero sequence then converges to every `φ ∈ 𝒟ₙ` (`testConvergesNDLMF_zero`), so
the only distribution is `0` (`dlmf_1_16_vi_literal`). `TestConvergesN` adds `supp φ ⊆ K`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff SchwartzMap

namespace Azurite.DLMF

variable {n : ℕ}

/-! ### Partial derivatives and multi-indices -/

/-- The partial derivative `∂φ/∂xᵢ` of `φ : ℝⁿ → ℂ`. -/
noncomputable def partialDeriv (i : Fin n) (φ : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun x => fderiv ℝ φ x (Pi.single i 1)

theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_of_eq rfl

theorem contDiff_partialDeriv {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (i : Fin n) :
    ContDiff ℝ ∞ (partialDeriv i φ) :=
  (hφ.fderiv_right infty_add_one_le).clm_apply contDiff_const

theorem fderiv_apply_const_eq {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (v w : Fin n → ℝ)
    (x : Fin n → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ φ y w) x v = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right infty_add_one_le).differentiable (by simp)) x
  rw [show (fun y => fderiv ℝ φ y w) =
    (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ φ from rfl,
    fderiv_comp x (ContinuousLinearMap.differentiableAt _) hd]
  simp

/-- Schwarz: partial derivatives of a smooth function commute. -/
theorem partialDeriv_comm {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin n) :
    partialDeriv i (partialDeriv j φ) = partialDeriv j (partialDeriv i φ) := by
  funext x
  show fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single i 1)) x (Pi.single j 1)
  rw [fderiv_apply_const_eq hφ, fderiv_apply_const_eq hφ]
  exact ContDiffAt.isSymmSndFDerivAt (hφ.contDiffAt (x := x)) (by simp) _ _

/-- The iterated partial derivative along a word `l = [i₁, …, i_r]`: `∂_{i₁} ⋯ ∂_{i_r} φ`. -/
noncomputable def partialWord (l : List (Fin n)) (φ : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  l.foldr partialDeriv φ

theorem contDiff_partialWord {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (l : List (Fin n)) :
    ContDiff ℝ ∞ (partialWord l φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact contDiff_partialDeriv ih i

theorem partialWord_append (l₁ l₂ : List (Fin n)) (φ : (Fin n → ℝ) → ℂ) :
    partialWord (l₁ ++ l₂) φ = partialWord l₁ (partialWord l₂ φ) := by
  simp [partialWord, List.foldr_append]

/-- Smooth functions, on which the partial derivatives commute. -/
abbrev SmoothFn (n : ℕ) := {φ : (Fin n → ℝ) → ℂ // ContDiff ℝ ∞ φ}

noncomputable def SmoothFn.partial (i : Fin n) (φ : SmoothFn n) : SmoothFn n :=
  ⟨partialDeriv i φ.1, contDiff_partialDeriv φ.2 i⟩

instance : LeftCommutative (SmoothFn.partial (n := n)) where
  left_comm i j φ := Subtype.ext (partialDeriv_comm φ.2 i j)

theorem partialWord_eq_foldr {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (l : List (Fin n)) :
    partialWord l φ = (l.foldr SmoothFn.partial ⟨φ, hφ⟩).1 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [partialWord, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- The order of differentiation is irrelevant for smooth functions. -/
theorem partialWord_perm {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) {l₁ l₂ : List (Fin n)}
    (h : l₁.Perm l₂) : partialWord l₁ φ = partialWord l₂ φ := by
  rw [partialWord_eq_foldr hφ, partialWord_eq_foldr hφ]
  exact congrArg Subtype.val (h.foldr_eq _)

/-- The word `[1, …, 1, 2, …, 2, …]` with `kᵢ` copies of `i`. -/
def wordOf (k : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun i => List.replicate (k i) i

theorem count_wordOf (k : Fin n → ℕ) (a : Fin n) : (wordOf k).count a = k a := by
  rw [wordOf, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [List.sum_map_eq_nsmul_single a]
  · simp
  · intro i hne _; simp [hne]

/-- The multi-index derivative `φ⁽ᵏ⁾ = ∂^{|k|}φ/(∂x₁^{k₁} ⋯ ∂xₙ^{kₙ})`. -/
noncomputable def mDeriv (k : Fin n → ℕ) (φ : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  partialWord (wordOf k) φ

theorem partialWord_eq_mDeriv {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (l : List (Fin n)) :
    partialWord l φ = mDeriv (fun i => l.count i) φ :=
  partialWord_perm hφ (List.perm_iff_count.mpr fun a =>
    (count_wordOf (fun i => l.count i) a).symm)

theorem length_wordOf (k : Fin n → ℕ) : (wordOf k).length = ∑ i, k i := by
  rw [wordOf, List.length_flatMap, Fin.sum_univ_def]
  simp

theorem mDeriv_zero (φ : (Fin n → ℝ) → ℂ) : mDeriv (fun _ => 0) φ = φ := by
  have : wordOf (fun _ : Fin n => 0) = [] := List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
  simp [mDeriv, this, partialWord]

theorem tsupport_partialDeriv_subset (i : Fin n) (φ : (Fin n → ℝ) → ℂ) :
    tsupport (partialDeriv i φ) ⊆ tsupport φ :=
  (tsupport_comp_subset (g := fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single i 1))
    (by simp) (fderiv ℝ φ)).trans (tsupport_fderiv_subset (𝕜 := ℝ))

theorem eventuallyEq_zero_partialWord {φ : (Fin n → ℝ) → ℂ} {p : Fin n → ℝ}
    (h : φ =ᶠ[𝓝 p] 0) (l : List (Fin n)) : partialWord l φ =ᶠ[𝓝 p] 0 := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    simp only [partialWord, List.foldr_cons] at hy ⊢
    rw [partialDeriv, (Filter.EventuallyEq.fderiv_eq hy)]
    simp

/-! ### The test function space `𝒟ₙ` -/

/-- DLMF §1.16(vi): `𝒟(ℝⁿ)`: infinitely differentiable functions with compact support. -/
def IsTestFunctionN (φ : (Fin n → ℝ) → ℂ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

theorem IsTestFunctionN.partialDeriv {φ : (Fin n → ℝ) → ℂ} (hφ : IsTestFunctionN φ)
    (i : Fin n) : IsTestFunctionN (partialDeriv i φ) :=
  ⟨contDiff_partialDeriv hφ.1 i, (hφ.2.fderiv (𝕜 := ℝ)).comp_left
    (g := fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single i 1)) (by simp)⟩

theorem IsTestFunctionN.partialWord {φ : (Fin n → ℝ) → ℂ} (hφ : IsTestFunctionN φ)
    (l : List (Fin n)) : IsTestFunctionN (Azurite.DLMF.partialWord l φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact ih.partialDeriv i

/-- The space `𝒟ₙ`. -/
def testSpaceN (n : ℕ) : Submodule ℂ ((Fin n → ℝ) → ℂ) where
  carrier := {φ | IsTestFunctionN φ}
  add_mem' := fun hφ hψ => ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hφ => ⟨contDiff_const.smul hφ.1, hφ.2.smul_left (f := fun _ => c)⟩

/-- `𝒟ₙ` is Mathlib's `𝓓(ℝⁿ, ℂ)`. -/
theorem isTestFunctionN_iff_testFunction (φ : (Fin n → ℝ) → ℂ) :
    IsTestFunctionN φ ↔ ∃ ψ : TestFunction (⊤ : TopologicalSpace.Opens (Fin n → ℝ)) ℂ ⊤,
      ⇑ψ = φ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨φ, h1, h2, by simp⟩, rfl⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ.contDiff, ψ.hasCompactSupport⟩

/-- `∂/∂xᵢ` as a linear map on `𝒟ₙ`. -/
noncomputable def partialTest (i : Fin n) : testSpaceN n →ₗ[ℂ] testSpaceN n where
  toFun φ := ⟨partialDeriv i φ, φ.2.partialDeriv i⟩
  map_add' φ ψ := by
    ext x
    simp only [Submodule.coe_add, Pi.add_apply, Azurite.DLMF.partialDeriv]
    rw [fderiv_add ((φ.2.1.differentiable (by simp)) x) ((ψ.2.1.differentiable (by simp)) x)]
    rfl
  map_smul' c φ := by
    ext x
    simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, Azurite.DLMF.partialDeriv]
    rw [fderiv_const_smul ((φ.2.1.differentiable (by simp)) x)]
    rfl

/-- Iterated partial derivatives along a word, as a linear map on `𝒟ₙ`. -/
noncomputable def wordTest (l : List (Fin n)) : testSpaceN n →ₗ[ℂ] testSpaceN n :=
  l.foldr (fun i T => partialTest i ∘ₗ T) LinearMap.id

theorem coe_wordTest (l : List (Fin n)) (φ : testSpaceN n) :
    (wordTest l φ : (Fin n → ℝ) → ℂ) = partialWord l φ := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [wordTest, List.foldr_cons, LinearMap.comp_apply] at ih ⊢
    change partialDeriv i _ = partialDeriv i (partialWord l φ)
    rw [← ih]

/-! ### Convergence in `𝒟ₙ` -/

/-- DLMF's convergence in `𝒟ₙ`, taken literally: the supports of the `φₘ` lie in a fixed compact
`K`, and `φₘ⁽ᵏ⁾ → φ⁽ᵏ⁾` uniformly on `K` for every multi-index `k`. -/
def TestConvergesNDLMF (φs : ℕ → (Fin n → ℝ) → ℂ) (φ : (Fin n → ℝ) → ℂ) : Prop :=
  ∃ K, IsCompact K ∧ (∀ m, tsupport (φs m) ⊆ K) ∧
    ∀ k : Fin n → ℕ, TendstoUniformlyOn (fun m => mDeriv k (φs m)) (mDeriv k φ) atTop K

/-- Convergence in `𝒟ₙ`, corrected: also `supp φ ⊆ K`. -/
def TestConvergesN (φs : ℕ → (Fin n → ℝ) → ℂ) (φ : (Fin n → ℝ) → ℂ) : Prop :=
  ∃ K, IsCompact K ∧ (∀ m, tsupport (φs m) ⊆ K) ∧ tsupport φ ⊆ K ∧
    ∀ k : Fin n → ℕ, TendstoUniformlyOn (fun m => mDeriv k (φs m)) (mDeriv k φ) atTop K

theorem exists_notMem_of_isCompact (hn : 0 < n) {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∃ p, p ∉ K := by
  by_contra h
  push Not at h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact noncompact_univ (Fin n → ℝ) (by rwa [eq_univ_of_forall h] at hK)

/-- For `n ≥ 1`, under the literal definition the zero sequence converges to every test
function. -/
theorem testConvergesNDLMF_zero (hn : 0 < n) {φ : (Fin n → ℝ) → ℂ} (hφ : IsTestFunctionN φ) :
    TestConvergesNDLMF (fun _ => 0) φ := by
  obtain ⟨p, hp⟩ := exists_notMem_of_isCompact hn hφ.2
  refine ⟨{p}, isCompact_singleton, fun m => by simp, fun k => ?_⟩
  rw [tendstoUniformlyOn_singleton_iff_tendsto]
  have h0 := (eventuallyEq_zero_partialWord (notMem_tsupport_iff_eventuallyEq.mp hp)
    (wordOf k)).eq_of_nhds
  have h1 : mDeriv k (fun _ : Fin n → ℝ => (0 : ℂ)) p = 0 :=
    (eventuallyEq_zero_partialWord (φ := fun _ => 0) (p := p) (Eventually.of_forall
      fun _ => rfl) (wordOf k)).eq_of_nhds
  simp only [mDeriv] at h1 ⊢
  rw [h0]
  have h1' : partialWord (wordOf k) (0 : (Fin n → ℝ) → ℂ) p = 0 := h1
  simp only [h1', Pi.zero_apply]
  exact tendsto_const_nhds

theorem TestConvergesN.unique {φs : ℕ → (Fin n → ℝ) → ℂ} {φ ψ : (Fin n → ℝ) → ℂ}
    (h₁ : TestConvergesN φs φ) (h₂ : TestConvergesN φs ψ) : φ = ψ := by
  obtain ⟨K₁, -, hs₁, hφ, hu₁⟩ := h₁
  obtain ⟨K₂, -, hs₂, hψ, hu₂⟩ := h₂
  have hz : ∀ (L : Set (Fin n → ℝ)) x, x ∉ L → (∀ m, tsupport (φs m) ⊆ L) → ∀ m, φs m x = 0 :=
    fun L x hx hs m => image_eq_zero_of_notMem_tsupport fun h => hx (hs m h)
  have hu₁' := hu₁ fun _ => 0
  have hu₂' := hu₂ fun _ => 0
  simp only [mDeriv_zero] at hu₁' hu₂'
  funext x
  by_cases h1 : x ∈ K₁ <;> by_cases h2 : x ∈ K₂
  · exact tendsto_nhds_unique (hu₁'.tendsto_at h1) (hu₂'.tendsto_at h2)
  · have l1 := hu₁'.tendsto_at h1
    simp only [hz K₂ x h2 hs₂] at l1
    rw [tendsto_nhds_unique l1 tendsto_const_nhds,
      image_eq_zero_of_notMem_tsupport fun h => h2 (hψ h)]
  · have l2 := hu₂'.tendsto_at h2
    simp only [hz K₁ x h1 hs₁] at l2
    rw [tendsto_nhds_unique l2 tendsto_const_nhds,
      image_eq_zero_of_notMem_tsupport fun h => h1 (hφ h)]
  · rw [image_eq_zero_of_notMem_tsupport fun h => h1 (hφ h),
      image_eq_zero_of_notMem_tsupport fun h => h2 (hψ h)]

/-! ### Distributions in `ℝⁿ` -/

/-- DLMF §1.16(vi): a distribution in `ℝⁿ` is a (sequentially) continuous linear functional on
`𝒟ₙ`. -/
def IsDistributionN (Λ : testSpaceN n →ₗ[ℂ] ℂ) : Prop :=
  ∀ (φs : ℕ → testSpaceN n) (φ : testSpaceN n),
    TestConvergesN (fun m => (φs m : (Fin n → ℝ) → ℂ)) (φ : (Fin n → ℝ) → ℂ) →
    Tendsto (fun m => Λ (φs m)) atTop (𝓝 (Λ φ))

/-- The same with DLMF's literal convergence. -/
def IsDistributionNDLMF (Λ : testSpaceN n →ₗ[ℂ] ℂ) : Prop :=
  ∀ (φs : ℕ → testSpaceN n) (φ : testSpaceN n),
    TestConvergesNDLMF (fun m => (φs m : (Fin n → ℝ) → ℂ)) (φ : (Fin n → ℝ) → ℂ) →
    Tendsto (fun m => Λ (φs m)) atTop (𝓝 (Λ φ))

/-- With DLMF's literal convergence in `𝒟ₙ` (`n ≥ 1`) the only distribution is `0`. -/
theorem dlmf_1_16_vi_literal (hn : 0 < n) {Λ : testSpaceN n →ₗ[ℂ] ℂ}
    (h : IsDistributionNDLMF Λ) : Λ = 0 := by
  ext φ
  have hc : TestConvergesNDLMF (fun _ => ((0 : testSpaceN n) : (Fin n → ℝ) → ℂ)) φ := by
    simpa using testConvergesNDLMF_zero hn φ.2
  have := h (fun _ => 0) φ hc
  simp only [map_zero] at this
  exact (tendsto_nhds_unique tendsto_const_nhds this).symm

/-- The space of distributions in `ℝⁿ`. -/
def distSpaceN (n : ℕ) : Submodule ℂ (testSpaceN n →ₗ[ℂ] ℂ) where
  carrier := {Λ | IsDistributionN Λ}
  add_mem' := fun hΛ hM φs φ h => by
    simpa only [LinearMap.add_apply] using (hΛ φs φ h).add (hM φs φ h)
  zero_mem' := fun φs φ _ => by simp
  smul_mem' := fun c Λ hΛ φs φ h => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using (hΛ φs φ h).const_mul c

theorem mDeriv_partialDeriv {ψ : (Fin n → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) (k : Fin n → ℕ)
    (i : Fin n) :
    mDeriv k (partialDeriv i ψ) = mDeriv (fun j => (wordOf k ++ [i]).count j) ψ := by
  rw [mDeriv, show partialDeriv i ψ = partialWord [i] ψ from rfl, ← partialWord_append,
    partialWord_eq_mDeriv hψ]

theorem TestConvergesN.partialDeriv {φs : ℕ → (Fin n → ℝ) → ℂ} {φ : (Fin n → ℝ) → ℂ}
    (hφs : ∀ m, IsTestFunctionN (φs m)) (hφ : IsTestFunctionN φ) (h : TestConvergesN φs φ)
    (i : Fin n) :
    TestConvergesN (fun m => Azurite.DLMF.partialDeriv i (φs m))
      (Azurite.DLMF.partialDeriv i φ) := by
  obtain ⟨K, hK, hs, hφK, hu⟩ := h
  refine ⟨K, hK, fun m => (tsupport_partialDeriv_subset i _).trans (hs m),
    (tsupport_partialDeriv_subset i _).trans hφK, fun k => ?_⟩
  have e : (fun m => mDeriv k (Azurite.DLMF.partialDeriv i (φs m))) =
      fun m => mDeriv (fun j => (wordOf k ++ [i]).count j) (φs m) :=
    funext fun m => mDeriv_partialDeriv (hφs m).1 k i
  rw [e, mDeriv_partialDeriv hφ.1 k i]
  exact hu _

/-- The partial derivative `⟨∂Λ/∂xᵢ, φ⟩ = −⟨Λ, ∂φ/∂xᵢ⟩` of a distribution (as in §1.16(ii)). -/
noncomputable def partialDist (i : Fin n) (Λ : testSpaceN n →ₗ[ℂ] ℂ) : testSpaceN n →ₗ[ℂ] ℂ :=
  -(Λ ∘ₗ partialTest i)

theorem partialDist_apply (i : Fin n) (Λ : testSpaceN n →ₗ[ℂ] ℂ) (φ : testSpaceN n) :
    partialDist i Λ φ = -Λ (partialTest i φ) := rfl

theorem isDistributionN_partialDist (i : Fin n) {Λ : testSpaceN n →ₗ[ℂ] ℂ}
    (hΛ : IsDistributionN Λ) : IsDistributionN (partialDist i Λ) :=
  fun φs φ h => (hΛ (fun m => partialTest i (φs m)) (partialTest i φ)
    (h.partialDeriv (fun m => (φs m).2) φ.2 i)).neg

theorem wordTest_append (l₁ l₂ : List (Fin n)) :
    wordTest (l₁ ++ l₂) = wordTest l₁ ∘ₗ wordTest l₂ := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp only [wordTest, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih]; rfl

theorem foldr_partialDist (l : List (Fin n)) (Λ : testSpaceN n →ₗ[ℂ] ℂ) (φ : testSpaceN n) :
    (l.foldr partialDist Λ) φ = (-1) ^ l.length * Λ (wordTest l.reverse φ) := by
  induction l generalizing φ with
  | nil => simp [wordTest]
  | cons i l ih =>
    rw [List.foldr_cons, partialDist_apply, ih, List.reverse_cons, wordTest_append,
      List.length_cons]
    have : wordTest [i] = partialTest i := LinearMap.ext fun ψ => rfl
    rw [this, LinearMap.comp_apply]
    ring

/-- The multi-index derivative `Λ⁽ᵏ⁾` of a distribution. -/
noncomputable def mDerivDist (k : Fin n → ℕ) (Λ : testSpaceN n →ₗ[ℂ] ℂ) :
    testSpaceN n →ₗ[ℂ] ℂ :=
  (wordOf k).foldr partialDist Λ

/-- `⟨Λ⁽ᵏ⁾, φ⟩ = (−1)^{|k|} ⟨Λ, φ⁽ᵏ⁾⟩`, with `φ⁽ᵏ⁾ = wordTest (wordOf k) φ = mDeriv k φ`. -/
theorem mDerivDist_apply (k : Fin n → ℕ) (Λ : testSpaceN n →ₗ[ℂ] ℂ) (φ : testSpaceN n) :
    mDerivDist k Λ φ = (-1) ^ (∑ i, k i) * Λ (wordTest (wordOf k) φ) ∧
      (wordTest (wordOf k) φ : (Fin n → ℝ) → ℂ) = mDeriv k φ := by
  refine ⟨?_, coe_wordTest _ φ⟩
  rw [mDerivDist, foldr_partialDist, length_wordOf]
  congr 2
  apply Subtype.ext
  rw [coe_wordTest, coe_wordTest]
  exact partialWord_perm φ.2.1 (List.reverse_perm _)

theorem isDistributionN_mDerivDist (k : Fin n → ℕ) {Λ : testSpaceN n →ₗ[ℂ] ℂ}
    (hΛ : IsDistributionN Λ) : IsDistributionN (mDerivDist k Λ) := by
  unfold mDerivDist
  induction wordOf k with
  | nil => exact hΛ
  | cons i l ih => exact isDistributionN_partialDist i ih

/-! ### Regular distributions (1.16.26–1.16.27) -/

theorem integrable_mul_testFunctionN {f : (Fin n → ℝ) → ℂ} (hf : LocallyIntegrable f volume)
    {φ : (Fin n → ℝ) → ℂ} (hφ : IsTestFunctionN φ) : Integrable fun x => f x * φ x :=
  ((hf.integrableOn_isCompact hφ.2).mul_continuousOn hφ.1.continuous.continuousOn
    hφ.2).integrable_of_forall_notMem_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- DLMF 1.16.26: the distribution `⟨Λ_f, φ⟩ = ∫_{ℝⁿ} f(x) φ(x) dx` of a locally integrable `f`. -/
noncomputable def regularDistN {f : (Fin n → ℝ) → ℂ} (hf : LocallyIntegrable f volume) :
    testSpaceN n →ₗ[ℂ] ℂ where
  toFun φ := ∫ x, f x * (φ : (Fin n → ℝ) → ℂ) x
  map_add' φ ψ := by
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add (integrable_mul_testFunctionN hf φ.2)
      (integrable_mul_testFunctionN hf ψ.2)
  map_smul' c φ := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1; funext x; ring

theorem dlmf_1_16_26 {f : (Fin n → ℝ) → ℂ} (hf : LocallyIntegrable f volume)
    (φ : testSpaceN n) : regularDistN hf φ = ∫ x, f x * (φ : (Fin n → ℝ) → ℂ) x := rfl

theorem isDistributionN_regularDistN {f : (Fin n → ℝ) → ℂ} (hf : LocallyIntegrable f volume) :
    IsDistributionN (regularDistN hf) := by
  rintro φs φ ⟨K, hK, hs, hφK, hu⟩
  simp only at hs
  have hu0 := hu fun _ => 0
  simp only [mDeriv_zero] at hu0
  have hfK : IntegrableOn f K := hf.integrableOn_isCompact hK
  set C := ∫ x in K, ‖f x‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (C + 1) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu0 _ hδ)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm, dlmf_1_16_26, dlmf_1_16_26,
    ← integral_sub (integrable_mul_testFunctionN hf (φs m).2)
      (integrable_mul_testFunctionN hf φ.2)]
  simp_rw [← mul_sub]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (f := (φs m : (Fin n → ℝ) → ℂ)) fun h => hx (hs m h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hφK h), sub_zero, mul_zero]]
  have hb : ‖∫ x in K, f x * ((φs m : (Fin n → ℝ) → ℂ) x - (φ : (Fin n → ℝ) → ℂ) x)‖ ≤
      ∫ x in K, ‖f x‖ * (ε / (C + 1)) := by
    refine norm_integral_le_of_norm_le (hfK.norm.mul_const _) ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have h1 := hN m hm x hx
    rw [norm_mul, dist_comm, dist_eq_norm] at *
    exact mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
  rw [integral_mul_const] at hb
  calc _ ≤ C * (ε / (C + 1)) := hb
    _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

/-- The distributional derivative `Dᵏf` of a locally integrable `f`. -/
noncomputable def distDerivN (k : Fin n → ℕ) {f : (Fin n → ℝ) → ℂ}
    (hf : LocallyIntegrable f volume) : testSpaceN n →ₗ[ℂ] ℂ :=
  mDerivDist k (regularDistN hf)

/-- DLMF 1.16.27: `⟨Dᵏf, φ⟩ = (−1)^{|k|} ∫_{ℝⁿ} f(x) φ⁽ᵏ⁾(x) dx`. -/
theorem dlmf_1_16_27 (k : Fin n → ℕ) {f : (Fin n → ℝ) → ℂ} (hf : LocallyIntegrable f volume)
    (φ : testSpaceN n) :
    distDerivN k hf φ = (-1) ^ (∑ i, k i) * ∫ x, f x * mDeriv k (φ : (Fin n → ℝ) → ℂ) x := by
  obtain ⟨h1, h2⟩ := mDerivDist_apply k (regularDistN hf) φ
  rw [distDerivN, h1, dlmf_1_16_26, h2]

/-! ### Iterated derivatives on the coordinate basis -/

/-- The unit vector `eᵢ`. -/
noncomputable abbrev unitVec (i : Fin n) : Fin n → ℝ := Pi.single i 1

theorem norm_unitVec_le (i : Fin n) : ‖unitVec i‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
    by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- `D^N φ(x)(e_{τ₀}, …, e_{τ_{N−1}}) = ∂_{τ₀} ⋯ ∂_{τ_{N−1}} φ(x)`. -/
theorem iteratedFDeriv_unitVec {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ∀ (N : ℕ) (τ : Fin N → Fin n) (x : Fin n → ℝ),
      iteratedFDeriv ℝ N φ x (fun j => unitVec (τ j)) = partialWord (List.ofFn τ) φ x := by
  intro N
  induction N with
  | zero => intro τ x; simp [partialWord]
  | succ N ih =>
    intro τ x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ N φ) x :=
      (hφ.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
    have e : (fun y => iteratedFDeriv ℝ N φ y (fun j => unitVec (τ j.succ))) =
        partialWord (List.ofFn fun j => τ j.succ) φ := funext (ih _)
    rw [← fderiv_continuousMultilinear_apply_const_apply hd]
    change fderiv ℝ (fun y => iteratedFDeriv ℝ N φ y (fun j => unitVec (τ j.succ))) x
      (unitVec (τ 0)) = _
    rw [e]
    rfl

theorem norm_partialWord_le {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (l : List (Fin n))
    (x : Fin n → ℝ) : ‖partialWord l φ x‖ ≤ ‖iteratedFDeriv ℝ l.length φ x‖ := by
  have h := iteratedFDeriv_unitVec hφ l.length l.get x
  rw [List.ofFn_get] at h
  rw [← h]
  refine ((iteratedFDeriv ℝ l.length φ x).le_opNorm _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    fun j _ => norm_unitVec_le _)

/-- `‖f‖ ≤ ∑_τ ‖f(e_{τ₀}, …)‖` for a multilinear map on `ℝⁿ` with the sup norm. -/
theorem norm_multilinear_le_sum {N : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin N => Fin n → ℝ) ℂ) :
    ‖f‖ ≤ ∑ τ : Fin N → Fin n, ‖f fun j => unitVec (τ j)‖ := by
  refine f.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun j => ∑ i, v j i • unitVec i := funext fun j => by
    ext a
    simp [unitVec, Finset.sum_apply, Pi.single_apply]
  calc ‖f v‖ = ‖f fun j => ∑ i, v j i • unitVec i‖ := by rw [← hv]
    _ = ‖∑ τ : Fin N → Fin n, (∏ j, v j (τ j)) • f fun j => unitVec (τ j)‖ := by
        rw [f.map_sum]; simp only [f.map_smul_univ]
    _ ≤ ∑ τ : Fin N → Fin n, ‖(∏ j, v j (τ j)) • f fun j => unitVec (τ j)‖ := norm_sum_le _ _
    _ ≤ ∑ τ : Fin N → Fin n, ‖f fun j => unitVec (τ j)‖ * ∏ j, ‖v j‖ := by
        refine Finset.sum_le_sum fun τ _ => ?_
        rw [norm_smul, mul_comm, norm_prod]
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          fun j _ => ?_) (norm_nonneg _)
        have := norm_le_pi_norm (v j) (τ j)
        simpa using this
    _ = _ := (Finset.sum_mul _ _ _).symm

/-! ### Tempered test functions in `ℝⁿ` (1.16.28) -/

/-- The monomial `x^m = x₁^{m₁} ⋯ xₙ^{mₙ}`. -/
noncomputable def monomialN (m : Fin n → ℕ) (x : Fin n → ℝ) : ℂ := ∏ i, ((x i : ℂ) ^ m i)

theorem norm_monomial_le (m : Fin n → ℕ) (x : Fin n → ℝ) : ‖monomialN m x‖ ≤ ‖x‖ ^ ∑ i, m i := by
  rw [monomialN, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow, Complex.norm_real]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) _

theorem norm_monomial_single (i : Fin n) (K : ℕ) (x : Fin n → ℝ) :
    ‖monomialN (Pi.single i K) x‖ = ‖x i‖ ^ K := by
  rw [monomialN, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (by simp), Pi.single_eq_same, norm_pow, Complex.norm_real]

theorem norm_pow_le_one_add_sum (x : Fin n → ℝ) (K : ℕ) :
    ‖x‖ ^ K ≤ 1 + ∑ i, ‖x i‖ ^ K := by
  have hs : 0 ≤ ∑ i, ‖x i‖ ^ K := Finset.sum_nonneg fun _ _ => by positivity
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have : ‖x‖ = 0 := by
      rw [norm_eq_zero]; exact funext fun i => (IsEmpty.false i).elim
    rw [this]
    rcases K with _ | K <;> simp
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      fun i => ‖x i‖₊
    have hx : ‖x‖ = ‖x i‖ := by
      rw [Pi.norm_def, hi]; rfl
    rw [hx]
    have := Finset.single_le_sum (f := fun j => ‖x j‖ ^ K) (fun j _ => by positivity)
      (Finset.mem_univ i)
    linarith

/-- DLMF 1.16.28: the test functions `𝒯ₙ` for tempered distributions in `ℝⁿ`:
infinitely differentiable `φ` with `|x^m φ⁽ᵏ⁾(x)| ≤ c_{m,k}` for all multi-indices `m`, `k`. -/
def IsTempTestN (φ : (Fin n → ℝ) → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ ∀ m k : Fin n → ℕ, ∃ c, ∀ x, ‖monomialN m x * mDeriv k φ x‖ ≤ c

/-- `𝒯ₙ` is Mathlib's Schwartz space `𝓢(ℝⁿ, ℂ)`. -/
theorem isTempTestN_iff_schwartz {φ : (Fin n → ℝ) → ℂ} :
    IsTempTestN φ ↔ ∃ ψ : 𝓢(Fin n → ℝ, ℂ), ⇑ψ = φ := by
  constructor
  · rintro ⟨hφ, hb⟩
    refine ⟨⟨φ, hφ, fun K N => ?_⟩, rfl⟩
    have hb' : ∀ (τ : Fin N → Fin n) (m : Fin n → ℕ), ∃ c, ∀ x,
        ‖monomialN m x‖ * ‖partialWord (List.ofFn τ) φ x‖ ≤ c := fun τ m => by
      obtain ⟨c, hc⟩ := hb m (fun i => (List.ofFn τ).count i)
      exact ⟨c, fun x => by rw [partialWord_eq_mDeriv hφ, ← norm_mul]; exact hc x⟩
    choose c hc using hb'
    refine ⟨∑ τ : Fin N → Fin n, (c τ 0 + ∑ i, c τ (Pi.single i K)), fun x => ?_⟩
    calc ‖x‖ ^ K * ‖iteratedFDeriv ℝ N φ x‖
        ≤ ‖x‖ ^ K * ∑ τ : Fin N → Fin n, ‖partialWord (List.ofFn τ) φ x‖ := by
          refine mul_le_mul_of_nonneg_left ((norm_multilinear_le_sum _).trans
            (le_of_eq ?_)) (by positivity)
          exact Finset.sum_congr rfl fun τ _ => by rw [iteratedFDeriv_unitVec hφ]
      _ ≤ ∑ τ : Fin N → Fin n, (1 + ∑ i, ‖x i‖ ^ K) * ‖partialWord (List.ofFn τ) φ x‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun τ _ =>
            mul_le_mul_of_nonneg_right (norm_pow_le_one_add_sum x K) (norm_nonneg _)
      _ ≤ _ := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [add_mul, Finset.sum_mul]
          refine add_le_add ?_ (Finset.sum_le_sum fun i _ => ?_)
          · have := hc τ 0 x
            simpa [monomialN] using this
          · have := hc τ (Pi.single i K) x
            rwa [norm_monomial_single] at this
  · rintro ⟨ψ, rfl⟩
    refine ⟨ψ.smooth ⊤, fun m k => ?_⟩
    obtain ⟨C, hC⟩ := ψ.decay (∑ i, m i) (wordOf k).length
    refine ⟨C, fun x => ?_⟩
    rw [norm_mul]
    calc ‖monomialN m x‖ * ‖mDeriv k ψ x‖
        ≤ (‖x‖ ^ ∑ i, m i) * ‖iteratedFDeriv ℝ (wordOf k).length ψ x‖ :=
          mul_le_mul (norm_monomial_le m x) (norm_partialWord_le (ψ.smooth ⊤) (wordOf k) x)
            (norm_nonneg _) (by positivity)
      _ ≤ C := hC.2 x

/-- `𝒟ₙ ⊆ 𝒯ₙ`. -/
theorem isTempTestN_of_isTestFunctionN {φ : (Fin n → ℝ) → ℂ} (hφ : IsTestFunctionN φ) :
    IsTempTestN φ := by
  refine ⟨hφ.1, fun m k => ?_⟩
  have hk := hφ.partialWord (wordOf k)
  have hc : Continuous fun x => monomialN m x * mDeriv k φ x :=
    (continuous_finsetProd _ fun i _ =>
      (Complex.continuous_ofReal.comp (continuous_apply i)).pow _).mul hk.1.continuous
  exact hc.bounded_above_of_compact_support hk.2.mul_left

/-- The space `𝒯ₙ`. -/
def tempSpaceN (n : ℕ) : Submodule ℂ ((Fin n → ℝ) → ℂ) where
  carrier := {φ | IsTempTestN φ}
  add_mem' := fun {φ ψ} hφ hψ => by
    obtain ⟨f, rfl⟩ := isTempTestN_iff_schwartz.mp hφ
    obtain ⟨g, rfl⟩ := isTempTestN_iff_schwartz.mp hψ
    exact isTempTestN_iff_schwartz.mpr ⟨f + g, rfl⟩
  zero_mem' := isTempTestN_iff_schwartz.mpr ⟨0, rfl⟩
  smul_mem' := fun c φ hφ => by
    obtain ⟨f, rfl⟩ := isTempTestN_iff_schwartz.mp hφ
    exact isTempTestN_iff_schwartz.mpr ⟨c • f, rfl⟩

/-- The identification `𝒯ₙ ≃ 𝓢(ℝⁿ, ℂ)`. -/
noncomputable def tempEquivN (n : ℕ) : tempSpaceN n ≃ₗ[ℂ] 𝓢(Fin n → ℝ, ℂ) where
  toFun φ := (isTempTestN_iff_schwartz.mp φ.2).choose
  invFun ψ := ⟨ψ, isTempTestN_iff_schwartz.mpr ⟨ψ, rfl⟩⟩
  map_add' φ ψ := by
    ext x
    simp only [add_apply, (isTempTestN_iff_schwartz.mp (φ + ψ).2).choose_spec,
      (isTempTestN_iff_schwartz.mp φ.2).choose_spec, (isTempTestN_iff_schwartz.mp ψ.2).choose_spec]
    rfl
  map_smul' c φ := by
    ext x
    simp only [smul_apply, (isTempTestN_iff_schwartz.mp (c • φ).2).choose_spec,
      (isTempTestN_iff_schwartz.mp φ.2).choose_spec, RingHom.id_apply]
    rfl
  left_inv φ := by
    ext x
    simp [(isTempTestN_iff_schwartz.mp φ.2).choose_spec]
  right_inv ψ := by
    ext x
    exact congrFun (isTempTestN_iff_schwartz.mp
      (isTempTestN_iff_schwartz.mpr ⟨ψ, rfl⟩)).choose_spec x

/-- DLMF §1.16(vi): a tempered distribution in `ℝⁿ` is a continuous linear functional on `𝒯ₙ`,
for the topology defined by the bounds 1.16.28, i.e. that of `𝓢(ℝⁿ, ℂ)`. -/
def IsTempDistN (Λ : tempSpaceN n →ₗ[ℂ] ℂ) : Prop :=
  Continuous (Λ ∘ₗ (tempEquivN n).symm.toLinearMap)

/-- The space `𝒯*ₙ` of tempered distributions in `ℝⁿ`. -/
def temperedSpaceN (n : ℕ) : Submodule ℂ (tempSpaceN n →ₗ[ℂ] ℂ) where
  carrier := {Λ | IsTempDistN Λ}
  add_mem' := fun {a b} hΛ hM => by
    change Continuous _
    rw [LinearMap.add_comp, LinearMap.coe_add]
    exact Continuous.add hΛ hM
  zero_mem' := by
    change Continuous _
    rw [LinearMap.zero_comp]
    exact continuous_zero
  smul_mem' := fun c Λ hΛ => by
    change Continuous _
    rw [LinearMap.smul_comp, LinearMap.coe_smul]
    exact Continuous.const_smul hΛ c

theorem isTempDistN_iff_exists_clm (Λ : tempSpaceN n →ₗ[ℂ] ℂ) :
    IsTempDistN Λ ↔ ∃ T : 𝓢(Fin n → ℝ, ℂ) →L[ℂ] ℂ, ∀ φ, T (tempEquivN n φ) = Λ φ := by
  constructor
  · intro h
    unfold IsTempDistN at h
    refine ⟨⟨Λ ∘ₗ (tempEquivN n).symm.toLinearMap, h⟩, fun φ => ?_⟩
    change Λ ((tempEquivN n).symm (tempEquivN n φ)) = Λ φ
    simp
  · rintro ⟨T, hT⟩
    have : Λ ∘ₗ (tempEquivN n).symm.toLinearMap = T.toLinearMap := by
      ext ψ
      simpa using (hT ((tempEquivN n).symm ψ)).symm
    rw [IsTempDistN, this]
    exact T.continuous

end Azurite.DLMF
