/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Unbounded
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# DLMF §1.18(ix): the spectrum of an operator

https://dlmf.nist.gov/1.18.ix

DLMF's "Spectrum of an Operator" paragraph, for a partially defined `T`.

* `resolventSetDLMF`: `z − T` (`shiftOp`) is injective, has dense range, and has bounded
  inverse (`ResolventBounded`). `spectrumDLMF` is the complement, with point, continuous and
  residual parts. `mem_pointSpectrumDLMF_iff` says the point spectrum consists of the
  eigenvalues. `spectrumDLMF_eq_union` and `spectrumDLMF_disjoint` give the disjoint union.
* Bounded `T`: DLMF's spectrum is the Banach-algebra spectrum (`spectrumDLMF_toPMap`), hence
  closed and bounded (`spectrumDLMF_bounded`).
* Self-adjoint `T`: `z ∈ ρ(T)` iff `z − T` is bounded below (`mem_resolventSetDLMF_iff`).
  `IsSelfAdjoint.spectrumDLMF_real` shows `σ(T) ⊆ ℝ`, `σ(T)` closed, residual spectrum empty.
* Eigenfunctions of distinct eigenvalues are orthogonal (`inner_eq_zero_of_eigen`). Eigenspaces
  of closed operators are closed and have Hilbert bases (`exists_hilbertBasis_eigenspace`).
-/

open LinearPMap
open scoped ComplexConjugate InnerProductSpace

namespace Azurite.DLMF

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- `z − T` on `D(T)`. -/
noncomputable def shiftOp (T : V →ₗ.[ℂ] V) (z : ℂ) : T.domain →ₗ[ℂ] V :=
  z • T.domain.subtype - T.toFun

omit [CompleteSpace V] in
@[simp] theorem shiftOp_apply (T : V →ₗ.[ℂ] V) (z : ℂ) (x : T.domain) :
    shiftOp T z x = z • (x : V) - T x := rfl

/-- The resolvent `(z − T)⁻¹` is bounded on `R(z − T)`: `‖v‖ ≤ C ‖(z − T)v‖`. -/
def ResolventBounded (T : V →ₗ.[ℂ] V) (z : ℂ) : Prop :=
  ∃ C : ℝ, ∀ x : T.domain, ‖(x : V)‖ ≤ C * ‖shiftOp T z x‖

/-- DLMF §1.18(ix): the resolvent set `ρ(T)`: `z − T` is injective, has dense range, and has a
bounded inverse. -/
def resolventSetDLMF (T : V →ₗ.[ℂ] V) : Set ℂ :=
  {z | Function.Injective (shiftOp T z) ∧ Dense (LinearMap.range (shiftOp T z) : Set V) ∧
    ResolventBounded T z}

/-- DLMF §1.18(ix): the spectrum `σ(T) = ℂ ∖ ρ(T)`. -/
def spectrumDLMF (T : V →ₗ.[ℂ] V) : Set ℂ := (resolventSetDLMF T)ᶜ

/-- The point spectrum: `z − T` is not injective. -/
def pointSpectrumDLMF (T : V →ₗ.[ℂ] V) : Set ℂ := {z | ¬Function.Injective (shiftOp T z)}

/-- The continuous spectrum: `z − T` is injective with dense range but unbounded inverse. -/
def continuousSpectrumDLMF (T : V →ₗ.[ℂ] V) : Set ℂ :=
  {z | Function.Injective (shiftOp T z) ∧ Dense (LinearMap.range (shiftOp T z) : Set V) ∧
    ¬ResolventBounded T z}

/-- The residual spectrum: `z − T` is injective without dense range. -/
def residualSpectrumDLMF (T : V →ₗ.[ℂ] V) : Set ℂ :=
  {z | Function.Injective (shiftOp T z) ∧ ¬Dense (LinearMap.range (shiftOp T z) : Set V)}

omit [CompleteSpace V] in
/-- DLMF §1.18(ix): `z ∈ σ_p` iff `z` is an eigenvalue: `Tv = zv` for some `v ∈ D(T) ∖ {0}`. -/
theorem mem_pointSpectrumDLMF_iff (T : V →ₗ.[ℂ] V) (z : ℂ) :
    z ∈ pointSpectrumDLMF T ↔ ∃ v : T.domain, (v : V) ≠ 0 ∧ T v = z • (v : V) := by
  simp only [pointSpectrumDLMF, Set.mem_ofPred_eq, injective_iff_map_eq_zero, not_forall,
    exists_prop, shiftOp_apply, sub_eq_zero]
  constructor
  · rintro ⟨v, hv, hne⟩
    exact ⟨v, fun h => hne (Subtype.ext h), hv.symm⟩
  · rintro ⟨v, hne, hv⟩
    exact ⟨v, hv.symm, fun h => hne (by rw [h]; rfl)⟩

omit [CompleteSpace V] in
/-- DLMF §1.18(ix): `σ(T) = σ_p ∪ σ_c ∪ σ_r`. -/
theorem spectrumDLMF_eq_union (T : V →ₗ.[ℂ] V) :
    spectrumDLMF T =
      pointSpectrumDLMF T ∪ continuousSpectrumDLMF T ∪ residualSpectrumDLMF T := by
  ext z
  simp only [spectrumDLMF, resolventSetDLMF, pointSpectrumDLMF, continuousSpectrumDLMF,
    residualSpectrumDLMF, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
  tauto

omit [CompleteSpace V] in
/-- DLMF §1.18(ix): the union is disjoint. -/
theorem spectrumDLMF_disjoint (T : V →ₗ.[ℂ] V) :
    Disjoint (pointSpectrumDLMF T) (continuousSpectrumDLMF T) ∧
      Disjoint (pointSpectrumDLMF T) (residualSpectrumDLMF T) ∧
      Disjoint (continuousSpectrumDLMF T) (residualSpectrumDLMF T) := by
  refine ⟨Set.disjoint_left.mpr fun z h1 h2 => h1 h2.1,
    Set.disjoint_left.mpr fun z h1 h2 => h1 h2.1,
    Set.disjoint_left.mpr fun z h1 h2 => h2.2 h1.2.1⟩

/-! ### Bounded operators -/

/-- For a bounded operator, DLMF's spectrum is the Banach-algebra spectrum. -/
theorem spectrumDLMF_toPMap (A : V →L[ℂ] V) :
    spectrumDLMF ((A : V →ₗ[ℂ] V).toPMap ⊤) = spectrum ℂ A := by
  ext z
  set f : V →L[ℂ] V := algebraMap ℂ (V →L[ℂ] V) z - A
  have hf : ∀ x, f x = z • x - A x := fun x => by
    simp [f, Algebra.algebraMap_eq_smul_one]
  have hs : ∀ x : ((A : V →ₗ[ℂ] V).toPMap ⊤).domain,
      shiftOp ((A : V →ₗ[ℂ] V).toPMap ⊤) z x = f x := fun x => by
    rw [shiftOp_apply, hf]; rfl
  have hrange : (LinearMap.range (shiftOp ((A : V →ₗ[ℂ] V).toPMap ⊤) z) : Set V) =
      Set.range f := by
    ext y
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range, hs]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨⟨x, trivial⟩, hx⟩⟩
  rw [spectrumDLMF, Set.mem_compl_iff, spectrum.mem_iff, not_iff_not,
    ContinuousLinearMap.isUnit_iff_bijective]
  simp only [resolventSetDLMF, Set.mem_ofPred_eq, ResolventBounded, hrange]
  constructor
  · rintro ⟨hinj, hdense, C, hC⟩
    have hinj' : Function.Injective f := fun x y hxy => by
      have := @hinj ⟨x, trivial⟩ ⟨y, trivial⟩ (by rw [hs, hs]; exact hxy)
      exact congrArg Subtype.val this
    have hC' : ∀ x, ‖x‖ ≤ (max C 0) * ‖f x‖ := fun x =>
      ((hC ⟨x, trivial⟩).trans_eq (by rw [hs])).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hanti := ContinuousLinearMap.antilipschitz_of_bound f (K := ⟨max C 0, le_max_right _ _⟩)
      hC'
    have hcl := hanti.isClosed_range f.uniformContinuous
    refine ⟨hinj', fun y => ?_⟩
    have : y ∈ closure (Set.range f) := hdense y
    rwa [hcl.closure_eq] at this
  · rintro ⟨hinj, hsurj⟩
    obtain ⟨g, hg⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩)
    refine ⟨fun x y hxy => Subtype.ext (hinj (by rw [← hs, ← hs]; exact hxy)), ?_,
      ⟨‖(↑g⁻¹ : V →L[ℂ] V)‖, fun x => ?_⟩⟩
    · rw [hsurj.range_eq]; exact dense_univ
    · have h1 : (↑g⁻¹ : V →L[ℂ] V) (f x) = x := by
        have h2 := congrArg (fun F : V →L[ℂ] V => F x) (Units.inv_mul g)
        simp only [mul_apply_eq_comp, one_apply_eq_self] at h2
        rwa [hg] at h2
      calc ‖(x : V)‖ = ‖(↑g⁻¹ : V →L[ℂ] V) (f x)‖ := by rw [h1]
        _ ≤ ‖(↑g⁻¹ : V →L[ℂ] V)‖ * ‖f x‖ := ContinuousLinearMap.le_opNorm _ _
        _ = _ := by rw [hs]

/-- DLMF §1.18(ix): the spectrum of a bounded operator is closed and bounded. -/
theorem spectrumDLMF_bounded (A : V →L[ℂ] V) :
    IsClosed (spectrumDLMF ((A : V →ₗ[ℂ] V).toPMap ⊤)) ∧
      Bornology.IsBounded (spectrumDLMF ((A : V →ₗ[ℂ] V).toPMap ⊤)) := by
  rw [spectrumDLMF_toPMap]
  exact ⟨(spectrum.isCompact A).isClosed, (spectrum.isCompact A).isBounded⟩

/-! ### Symmetric and self-adjoint operators -/

omit [CompleteSpace V] in
theorem apply_of_eq {S T : V →ₗ.[ℂ] V} (h : S = T) (x : S.domain) :
    S x = T ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

omit [CompleteSpace V] in
theorem IsSymmetricDLMF.inner_self_im {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) (x : T.domain) :
    (⟪(x : V), T x⟫_ℂ).im = 0 := by
  have h := hT.isFormalAdjoint x x
  rw [← inner_conj_symm] at h
  exact Complex.conj_eq_iff_im.mp h

omit [CompleteSpace V] in
/-- `‖(z − T)v‖ ≥ |ℑz| ‖v‖` for symmetric `T`. -/
theorem IsSymmetricDLMF.norm_shiftOp_ge {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) (z : ℂ)
    (x : T.domain) : |z.im| * ‖(x : V)‖ ≤ ‖shiftOp T z x‖ := by
  have him : (⟪(x : V), shiftOp T z x⟫_ℂ).im = z.im * ‖(x : V)‖ ^ 2 := by
    have hxx : ⟪(x : V), (x : V)⟫_ℂ = ((‖(x : V)‖ ^ 2 : ℝ) : ℂ) := dlmfInner_self _
    rw [shiftOp_apply, inner_sub_right, inner_smul_right, hxx, Complex.sub_im,
      hT.inner_self_im x, sub_zero, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
    ring
  have h1 : |z.im| * ‖(x : V)‖ ^ 2 ≤ ‖(x : V)‖ * ‖shiftOp T z x‖ := by
    calc |z.im| * ‖(x : V)‖ ^ 2 = |(⟪(x : V), shiftOp T z x⟫_ℂ).im| := by
          rw [him, abs_mul, abs_of_nonneg (sq_nonneg ‖(x : V)‖)]
      _ ≤ ‖⟪(x : V), shiftOp T z x⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖(x : V)‖ * ‖shiftOp T z x‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (x : V)) with h0 | h0
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc h0]

/-- `w ⊥ R(z − T)` iff `w ∈ D(T*)` with `T*w = z̄ w`. -/
theorem orthogonal_range_shiftOp {T : V →ₗ.[ℂ] V} (hT : Dense (T.domain : Set V)) (z : ℂ)
    (w : V) : (∀ x : T.domain, ⟪w, shiftOp T z x⟫_ℂ = 0) ↔
      ∃ h : w ∈ T†.domain, T† ⟨w, h⟩ = conj z • w := by
  constructor
  · intro hw
    have key : ∀ x : T.domain, ⟪conj z • w, (x : V)⟫_ℂ = ⟪w, T x⟫_ℂ := fun x => by
      have := hw x
      rw [shiftOp_apply, inner_sub_right, inner_smul_right, sub_eq_zero] at this
      rw [inner_smul_left, Complex.conj_conj, this]
    have hmem : w ∈ T†.domain := mem_adjoint_domain_of_exists w ⟨_, key⟩
    exact ⟨hmem, adjoint_apply_eq hT ⟨w, hmem⟩ key⟩
  · rintro ⟨h, hw⟩ x
    have := (adjoint_isFormalAdjoint hT) ⟨w, h⟩ x
    rw [hw, inner_smul_left, Complex.conj_conj] at this
    rw [shiftOp_apply, inner_sub_right, inner_smul_right, ← this]
    simp

omit [CompleteSpace V] in
theorem dense_range_iff_orthogonal {D : Submodule ℂ V} [CompleteSpace V] (f : D →ₗ[ℂ] V) :
    Dense (LinearMap.range f : Set V) ↔ ∀ w : V, (∀ x, ⟪w, f x⟫_ℂ = 0) → w = 0 := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  simp only [Submodule.mem_orthogonal, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  exact ⟨fun h w hw => h w fun x => by rw [inner_eq_zero_symm]; exact hw x,
    fun h w hw => h w fun x => by rw [inner_eq_zero_symm]; exact hw x⟩

omit [CompleteSpace V] in
/-- Eigenvalues of a symmetric operator are real. -/
theorem IsSymmetricDLMF.eigenvalue_conj {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T)
    {v : T.domain} (hv : (v : V) ≠ 0) {a : ℂ} (h : T v = a • (v : V)) : conj a = a := by
  have him := hT.inner_self_im v
  have hxx : ⟪(v : V), (v : V)⟫_ℂ = ((‖(v : V)‖ ^ 2 : ℝ) : ℂ) := dlmfInner_self _
  rw [h, inner_smul_right, hxx] at him
  have hn : (0 : ℝ) < ‖(v : V)‖ ^ 2 := by positivity
  have : a.im * ‖(v : V)‖ ^ 2 = 0 := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add] at him
    exact him
  exact Complex.conj_eq_iff_im.mpr ((mul_eq_zero.mp this).resolve_right hn.ne')

/-- For self-adjoint `T`, an injective `z − T` has dense range. -/
theorem IsSelfAdjoint.dense_range_shiftOp {T : V →ₗ.[ℂ] V} (hT : IsSelfAdjoint T) {z : ℂ}
    (hinj : Function.Injective (shiftOp T z)) :
    Dense (LinearMap.range (shiftOp T z) : Set V) := by
  have hTe : T† = T := isSelfAdjoint_def.mp hT
  rw [dense_range_iff_orthogonal]
  intro w hw
  obtain ⟨h, hTw⟩ := (orthogonal_range_shiftOp hT.dense_domain z w).mp hw
  set v : T.domain := ⟨w, hTe ▸ h⟩
  have hv : T v = conj z • (v : V) := by rw [← hTw, apply_of_eq hTe]
  by_contra hw0
  have hc := (IsSelfAdjoint.isSymmetricDLMF hT).eigenvalue_conj (v := v) hw0 hv
  rw [Complex.conj_conj] at hc
  rw [← hc] at hv
  have : shiftOp T z v = shiftOp T z 0 := by
    rw [shiftOp_apply, hv, _root_.map_zero, sub_self]
  exact hw0 (congrArg Subtype.val (hinj this))

/-- For self-adjoint `T`, `z ∈ ρ(T)` iff `z − T` is bounded below. -/
theorem IsSelfAdjoint.mem_resolventSetDLMF_iff {T : V →ₗ.[ℂ] V} (hT : IsSelfAdjoint T) (z : ℂ) :
    z ∈ resolventSetDLMF T ↔ ResolventBounded T z := by
  refine ⟨fun h => h.2.2, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h
  have hinj : Function.Injective (shiftOp T z) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := hC x
    rw [hx, norm_zero, mul_zero] at this
    exact Subtype.ext (norm_le_zero_iff.mp this)
  exact ⟨hinj, IsSelfAdjoint.dense_range_shiftOp hT hinj, C, hC⟩

/-- **DLMF §1.18(ix)**: the spectrum of a self-adjoint operator is a closed subset of `ℝ`, and
its residual spectrum is empty. -/
theorem IsSelfAdjoint.spectrumDLMF_real {T : V →ₗ.[ℂ] V} (hT : IsSelfAdjoint T) :
    spectrumDLMF T ⊆ {z | z.im = 0} ∧ IsClosed (spectrumDLMF T) ∧
      residualSpectrumDLMF T = ∅ := by
  have hsym := IsSelfAdjoint.isSymmetricDLMF hT
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · by_contra him
    apply hz
    rw [IsSelfAdjoint.mem_resolventSetDLMF_iff hT]
    have hpos : 0 < |z.im| := abs_pos.mpr him
    refine ⟨|z.im|⁻¹, fun x => ?_⟩
    rw [le_inv_mul_iff₀ hpos]
    exact hsym.norm_shiftOp_ge z x
  · rw [spectrumDLMF, isClosed_compl_iff, Metric.isOpen_iff]
    intro z0 hz0
    obtain ⟨C, hC⟩ := (IsSelfAdjoint.mem_resolventSetDLMF_iff hT z0).mp hz0
    set C' := max C 1
    have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨1 / (2 * C'), by positivity, fun z hz => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    show z ∈ resolventSetDLMF T
    rw [IsSelfAdjoint.mem_resolventSetDLMF_iff hT]
    refine ⟨2 * C', fun x => ?_⟩
    have h1 := hC x
    have h2 : shiftOp T z0 x = shiftOp T z x + (z0 - z) • (x : V) := by
      simp only [shiftOp_apply, sub_smul]; abel
    have h3 : ‖shiftOp T z0 x‖ ≤ ‖shiftOp T z x‖ + ‖z - z0‖ * ‖(x : V)‖ := by
      rw [h2, ← norm_neg (z - z0), neg_sub]
      exact (norm_add_le _ _).trans (by rw [norm_smul])
    have h4 : ‖(x : V)‖ ≤ C' * ‖shiftOp T z0 x‖ :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have h5 : C' * ‖z - z0‖ ≤ 1 / 2 := by
      have := mul_lt_mul_of_pos_left hz hC'
      rw [show C' * (1 / (2 * C')) = 1 / 2 by field_simp] at this
      exact this.le
    nlinarith [norm_nonneg (x : V), norm_nonneg (shiftOp T z x), norm_nonneg (z - z0)]
  · ext z
    simp only [residualSpectrumDLMF, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_not]
    exact fun hinj => IsSelfAdjoint.dense_range_shiftOp hT hinj

omit [CompleteSpace V] in
/-- DLMF §1.18(ix): eigenfunctions of a symmetric operator for distinct eigenvalues are
orthogonal. -/
theorem IsSymmetricDLMF.inner_eq_zero_of_eigen {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T)
    {v w : T.domain} {a b : ℂ} (hv : T v = a • (v : V)) (hw : T w = b • (w : V)) (hab : a ≠ b) :
    dlmfInner (v : V) w = 0 := by
  by_cases hv0 : (v : V) = 0
  · simp [dlmfInner, hv0]
  by_cases hw0 : (w : V) = 0
  · simp [dlmfInner, hw0]
  have ha := hT.eigenvalue_conj hv0 hv
  have h := hT.isFormalAdjoint v w
  rw [hv, hw, inner_smul_left, inner_smul_right, ha] at h
  have : (a - b) * ⟪(v : V), (w : V)⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  have h2 := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hab)
  simp [dlmfInner, inner_eq_zero_symm.mp h2]

/-- The eigenspace `{v ∈ D(T) | Tv = zv}`. -/
noncomputable def eigenspaceDLMF (T : V →ₗ.[ℂ] V) (z : ℂ) : Submodule ℂ V :=
  (LinearMap.ker (shiftOp T z)).map T.domain.subtype

omit [CompleteSpace V] in
theorem mem_eigenspaceDLMF {T : V →ₗ.[ℂ] V} {z : ℂ} {v : V} :
    v ∈ eigenspaceDLMF T z ↔ ∃ h : v ∈ T.domain, T ⟨v, h⟩ = z • v := by
  simp only [eigenspaceDLMF, Submodule.mem_map, LinearMap.mem_ker, shiftOp_apply, sub_eq_zero,
    Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx.symm⟩
  · rintro ⟨h, hv⟩; exact ⟨⟨v, h⟩, hv.symm, rfl⟩

omit [CompleteSpace V] in
/-- The eigenspaces of a closed operator are closed. -/
theorem isClosed_eigenspaceDLMF {T : V →ₗ.[ℂ] V} (hT : T.IsClosed) (z : ℂ) :
    IsClosed (eigenspaceDLMF T z : Set V) := by
  have : (eigenspaceDLMF T z : Set V) = (fun v => (v, z • v)) ⁻¹' (T.graph : Set (V × V)) := by
    ext v
    simp only [SetLike.mem_coe, mem_eigenspaceDLMF, Set.mem_preimage, mem_graph_iff]
    constructor
    · rintro ⟨h, hv⟩; exact ⟨⟨v, h⟩, rfl, hv⟩
    · rintro ⟨y, hy, hTy⟩
      subst hy
      exact ⟨y.2, hTy⟩
  rw [this]
  exact hT.preimage (continuous_id.prodMk (continuous_const_smul z))

/-- DLMF §1.18(ix): an eigenspace of a self-adjoint operator has an orthonormal (Hilbert)
basis of eigenfunctions. -/
theorem IsSelfAdjoint.exists_hilbertBasis_eigenspace {T : V →ₗ.[ℂ] V} (hT : IsSelfAdjoint T)
    (z : ℂ) : ∃ (w : Set (eigenspaceDLMF T z)) (b : HilbertBasis w ℂ (eigenspaceDLMF T z)),
      ⇑b = Subtype.val := by
  have : IsClosed (eigenspaceDLMF T z : Set V) := isClosed_eigenspaceDLMF hT.isClosed z
  have : CompleteSpace (eigenspaceDLMF T z) := IsClosed.completeSpace_coe
  exact exists_hilbertBasis ℂ (eigenspaceDLMF T z)

end Azurite.DLMF
