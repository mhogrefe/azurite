/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Deficiency

/-!
# DLMF §1.18(ix): von Neumann's theory of self-adjoint extensions

https://dlmf.nist.gov/1.18.ix

DLMF's "Self-adjoint extensions of a symmetric Operator" paragraph, in full.

* `isClosed_range_shiftOp`: `R(z − A)` is closed for closed symmetric `A` and `ℑz ≠ 0`.
* `vonNeumann_decomp`, `vonNeumann_unique`: `D(T*) = D(T**) ⊕ N_i ⊕ N_{−i}`.
* `boundaryForm`: `⟪T*x, y⟫ − ⟪x, T*y⟫ = 2i(⟪b, b'⟫ − ⟪a, a'⟫)` in that decomposition.
* `vonNeumannExt`: the restriction of `T*` to `{v + w + Uw}` for a linear isometry
  `U : N_i → N_{−i}`. It is symmetric (`vonNeumannExt_symmetric`), and self-adjoint iff `U` is
  surjective (`vonNeumannExt_isSelfAdjoint_iff`).
* `eq_vonNeumannExt_of_selfAdjoint`: every self-adjoint extension is of this form, with `U` the
  Cayley map `w ↦ (A + i)⁻¹(2iw) − w` (`cayleyIsometry`).
* `exists_selfAdjoint_ext_iff`: self-adjoint extensions exist iff `N_i ≅ N_{−i}` isometrically.
  `exists_selfAdjoint_ext_iff_finrank` gives the finite-index form `n₊ = n₋`, and
  `rank_eq_of_selfAdjoint_ext` gives `dim N_i = dim N_{−i}`.

DLMF imprecisions: the isometry `U` must be onto (a unitary), and `n₊ = n₋` must be read as
equality of Hilbert dimensions (unitary equivalence). For infinite indices, equal algebraic
dimension does not give a unitary.
-/

open LinearPMap Topology Filter Complex
open scoped ComplexConjugate InnerProductSpace

namespace Azurite.DLMF

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem shiftOp_of_le {A B : V →ₗ.[ℂ] V} (h : A ≤ B) (z : ℂ) (x : A.domain) :
    shiftOp A z x = shiftOp B z ⟨x, h.1 x.2⟩ := by
  simp only [shiftOp_apply, h.2 (x := x) (y := ⟨x, h.1 x.2⟩) rfl]

/-- A densely defined `A` with `A ⊂ A*` is symmetric. -/
theorem isSymmetricDLMF_of_le_adjoint {A : V →ₗ.[ℂ] V} (hd : Dense (A.domain : Set V))
    (h : A ≤ A†) : IsSymmetricDLMF A := by
  refine isSymmetricDLMF_iff.mpr ⟨hd, fun x y => ?_⟩
  have h1 := (adjoint_isFormalAdjoint hd) ⟨y, h.1 y.2⟩ x
  rw [← h.2 (x := y) (y := ⟨y, h.1 y.2⟩) rfl] at h1
  rw [← inner_conj_symm, ← h1, inner_conj_symm]

/-- `T**` is a closed symmetric extension of `T`, with `(T**)* = T*`. -/
theorem IsSymmetricDLMF.adjoint_adjoint {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) :
    IsSymmetricDLMF T†† := by
  have h := hT.le_adjoint_adjoint
  refine isSymmetricDLMF_of_le_adjoint (hT.1.mono h.1.1) ?_
  rw [hT.adjoint_adjoint_adjoint]
  exact h.2

/-- A closed symmetric `A` has closed `R(z − A)` for `ℑz ≠ 0`. -/
theorem isClosed_range_shiftOp {A : V →ₗ.[ℂ] V} (hA : A.IsClosed) (hs : IsSymmetricDLMF A)
    {z : ℂ} (hz : z.im ≠ 0) : IsClosed (LinearMap.range (shiftOp A z) : Set V) := by
  have hzim : 0 < |z.im| := abs_pos.mpr hz
  refine IsSeqClosed.isClosed fun ys p hys hp => ?_
  choose xs hxs using fun n => LinearMap.mem_range.mp (hys n)
  have hdist : ∀ m n, dist (xs m : V) (xs n) ≤ dist (ys m) (ys n) / |z.im| := fun m n => by
    rw [le_div_iff₀ hzim, dist_eq_norm, dist_eq_norm, mul_comm, ← hxs, ← hxs, ← _root_.map_sub]
    exact hs.norm_shiftOp_ge z (xs m - xs n)
  have hc : CauchySeq fun n => (xs n : V) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hp.cauchySeq (ε * |z.im|) (by positivity)
    refine ⟨N, fun n hn => (hdist n N).trans_lt ?_⟩
    rw [div_lt_iff₀ hzim]
    exact hN n hn
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hAx : Tendsto (fun n => A (xs n)) atTop (𝓝 (z • x - p)) := by
    have : ∀ n, A (xs n) = z • (xs n : V) - ys n := fun n => by
      rw [← hxs, shiftOp_apply]; abel
    simp_rw [this]
    exact (hx.const_smul z).sub hp
  have hg : (x, z • x - p) ∈ (A.graph : Set (V × V)) :=
    hA.mem_of_tendsto (hx.prodMk_nhds hAx)
      (Eventually.of_forall fun n => (mem_graph_iff A).mpr ⟨xs n, rfl, rfl⟩)
  obtain ⟨y, hy, hAy⟩ := (mem_graph_iff A).mp hg
  refine ⟨y, ?_⟩
  rw [shiftOp_apply, hAy, hy]
  module

variable {T : V →ₗ.[ℂ] V}

theorem IsSymmetricDLMF.deficiencySpace_adjoint_adjoint (hT : IsSymmetricDLMF T) (z : ℂ) :
    deficiencySpace T†† z = deficiencySpace T z := by
  rw [deficiencySpace, deficiencySpace, hT.adjoint_adjoint_adjoint]

/-- `R(T** + i)^⊥ = N_i`. -/
theorem IsSymmetricDLMF.orthogonal_range_eq (hT : IsSymmetricDLMF T) :
    (LinearMap.range (shiftOp T†† (-I)))ᗮ = deficiencySpace T I := by
  rw [← hT.deficiencySpace_adjoint_adjoint, deficiencySpace_eq_orthogonal hT.adjoint_adjoint.1,
    Complex.conj_I]

/-- **DLMF §1.18(ix)**, von Neumann's formula (existence):
`D(T*) = D(T**) + N_i + N_{−i}`. -/
theorem IsSymmetricDLMF.vonNeumann_decomp (hT : IsSymmetricDLMF T) (f : T†.domain) :
    ∃ g : (T††).domain, ∃ a ∈ deficiencySpace T I, ∃ b ∈ deficiencySpace T (-I),
      (f : V) = g + a + b := by
  have hS := hT.adjoint_adjoint
  have hle := hT.le_adjoint_adjoint.2
  set K := LinearMap.range (shiftOp T†† (-I))
  have hK : IsClosed (K : Set V) := isClosed_range_shiftOp (adjoint_isClosed hT.dense_adjoint) hS
    (by simp)
  have : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨y1, ⟨g, rfl⟩, h, hh, hy⟩ := K.exists_add_mem_mem_orthogonal (shiftOp T† (-I) f)
  rw [hT.orthogonal_range_eq] at hh
  obtain ⟨hhd, hTh⟩ := mem_eigenspaceDLMF.mp hh
  set gD : T†.domain := ⟨g, hle.1 g.2⟩
  have hSg : T†† g = T† gD := hle.2 rfl
  refine ⟨g, (I / 2) • h, Submodule.smul_mem _ _ hh, (f : V) - g - (I / 2) • h, ?_, by abel⟩
  have hmem : (f : V) - g - (I / 2) • h ∈ T†.domain :=
    Submodule.sub_mem _ (Submodule.sub_mem _ f.2 gD.2) (Submodule.smul_mem _ _ hhd)
  refine mem_eigenspaceDLMF.mpr ⟨hmem, ?_⟩
  have he : (⟨(f : V) - g - (I / 2) • h, hmem⟩ : T†.domain) =
      f - gD - (I / 2) • (⟨h, hhd⟩ : T†.domain) := rfl
  rw [he, LinearPMap.map_sub, LinearPMap.map_sub, LinearPMap.map_smul, hTh, ← hSg]
  rw [shiftOp_apply, shiftOp_apply] at hy
  linear_combination (norm := module) (-1 : ℂ) • hy + ((-1 : ℂ) * I_sq) • h

/-- **DLMF §1.18(ix)**, von Neumann's formula (directness): the sum is direct. -/
theorem IsSymmetricDLMF.vonNeumann_unique (hT : IsSymmetricDLMF T) (g : (T††).domain)
    {a b : V} (ha : a ∈ deficiencySpace T I) (hb : b ∈ deficiencySpace T (-I))
    (hsum : (g : V) + a + b = 0) : (g : V) = 0 ∧ a = 0 ∧ b = 0 := by
  have hS := hT.adjoint_adjoint
  have hle := hT.le_adjoint_adjoint.2
  obtain ⟨had, hTa⟩ := mem_eigenspaceDLMF.mp ha
  obtain ⟨hbd, hTb⟩ := mem_eigenspaceDLMF.mp hb
  set gD : T†.domain := ⟨g, hle.1 g.2⟩
  have hzero : gD + ⟨a, had⟩ + ⟨b, hbd⟩ = 0 := Subtype.ext hsum
  have h1 := congrArg (shiftOp T† (-I)) hzero
  rw [_root_.map_add, _root_.map_add, _root_.map_zero, ← shiftOp_of_le hle] at h1
  simp only [shiftOp_apply, hTa, hTb] at h1
  -- `(T** + i)g = 2i a` lies in `R ∩ R^⊥`
  have h2 : shiftOp T†† (-I) g = (2 * I) • a := by
    rw [shiftOp_apply]
    linear_combination (norm := module) h1
  have hmemK : (2 * I) • a ∈ LinearMap.range (shiftOp T†† (-I)) := ⟨g, h2⟩
  have hmemKp : (2 * I) • a ∈ (LinearMap.range (shiftOp T†† (-I)))ᗮ := by
    rw [hT.orthogonal_range_eq]; exact Submodule.smul_mem _ _ ha
  have h3 : (2 * I) • a = 0 := by
    have := Submodule.mem_inf.mpr ⟨hmemK, hmemKp⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  have ha0 : a = 0 := (smul_eq_zero.mp h3).resolve_left (by simp)
  have hg0 : (g : V) = 0 := by
    have := hS.norm_shiftOp_ge (-I) g
    rw [h2, h3, norm_zero] at this
    simpa using this
  refine ⟨hg0, ha0, ?_⟩
  rw [hg0, ha0, zero_add, zero_add] at hsum
  exact hsum

/-! ### The boundary form -/

/-- `⟨T** g, y⟩ = ⟨g, T* y⟩` for `g ∈ D(T**)`, `y ∈ D(T*)` (Mathlib's inner product). -/
theorem IsSymmetricDLMF.inner_adjoint_adjoint (hT : IsSymmetricDLMF T) (g : (T††).domain)
    (y : T†.domain) : ⟪T†† g, (y : V)⟫_ℂ = ⟪(g : V), T† y⟫_ℂ := by
  have h3 := hT.adjoint_adjoint_adjoint
  have hfa := (adjoint_isFormalAdjoint (T := T††) hT.adjoint_adjoint.1)
    ⟨y, by rw [h3]; exact y.2⟩ g
  rw [apply_of_eq h3] at hfa
  rw [← inner_conj_symm, ← hfa, inner_conj_symm]

/-- **The boundary form**: for `x = g + a + b` and `y = g' + a' + b'` in
`D(T*) = D(T**) + N_i + N_{−i}`, `⟪T*x, y⟫ − ⟪x, T*y⟫ = 2i(⟪b, b'⟫ − ⟪a, a'⟫)`. -/
theorem IsSymmetricDLMF.boundaryForm (hT : IsSymmetricDLMF T) (x y : T†.domain)
    (g g' : (T††).domain) {a a' b b' : V} (ha : a ∈ deficiencySpace T I)
    (ha' : a' ∈ deficiencySpace T I) (hb : b ∈ deficiencySpace T (-I))
    (hb' : b' ∈ deficiencySpace T (-I)) (hx : (x : V) = g + a + b) (hy : (y : V) = g' + a' + b') :
    ⟪T† x, (y : V)⟫_ℂ - ⟪(x : V), T† y⟫_ℂ = 2 * I * (⟪b, b'⟫_ℂ - ⟪a, a'⟫_ℂ) := by
  have hle := hT.le_adjoint_adjoint.2
  have hS := hT.adjoint_adjoint
  obtain ⟨had, hTa⟩ := mem_eigenspaceDLMF.mp ha
  obtain ⟨had', hTa'⟩ := mem_eigenspaceDLMF.mp ha'
  obtain ⟨hbd, hTb⟩ := mem_eigenspaceDLMF.mp hb
  obtain ⟨hbd', hTb'⟩ := mem_eigenspaceDLMF.mp hb'
  set gD : T†.domain := ⟨g, hle.1 g.2⟩
  set gD' : T†.domain := ⟨g', hle.1 g'.2⟩
  have hTx : T† x = T†† g + I • a - I • b := by
    have : x = gD + ⟨a, had⟩ + ⟨b, hbd⟩ := Subtype.ext hx
    rw [this, LinearPMap.map_add, LinearPMap.map_add, hTa, hTb, ← hle.2 (x := g) rfl]
    module
  have hTy : T† y = T†† g' + I • a' - I • b' := by
    have : y = gD' + ⟨a', had'⟩ + ⟨b', hbd'⟩ := Subtype.ext hy
    rw [this, LinearPMap.map_add, LinearPMap.map_add, hTa', hTb', ← hle.2 (x := g') rfl]
    module
  -- the cross terms with `D(T**)`
  have F1 : ⟪T†† g, a'⟫_ℂ = I * ⟪(g : V), a'⟫_ℂ := by
    have h := hT.inner_adjoint_adjoint g ⟨a', had'⟩
    rwa [hTa', inner_smul_right] at h
  have F2 : ⟪T†† g, b'⟫_ℂ = -I * ⟪(g : V), b'⟫_ℂ := by
    have h := hT.inner_adjoint_adjoint g ⟨b', hbd'⟩
    rwa [hTb', inner_smul_right] at h
  have F3 : ⟪a, T†† g'⟫_ℂ = -I * ⟪a, (g' : V)⟫_ℂ := by
    have h := hT.inner_adjoint_adjoint g' ⟨a, had⟩
    rw [hTa, inner_smul_right] at h
    rw [← inner_conj_symm, h, map_mul, conj_I, inner_conj_symm]
  have F4 : ⟪b, T†† g'⟫_ℂ = I * ⟪b, (g' : V)⟫_ℂ := by
    have h := hT.inner_adjoint_adjoint g' ⟨b, hbd⟩
    rw [hTb, inner_smul_right] at h
    rw [← inner_conj_symm, h, map_mul, _root_.map_neg, conj_I, neg_neg, inner_conj_symm]
  have F5 := hS.isFormalAdjoint g g'
  rw [hTx, hTy, hx, hy]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_I]
  linear_combination F5 + F1 + F2 - F3 - F4

/-! ### Self-adjoint extensions from isometries `N_i → N_{−i}` -/

variable (T) in
/-- The domain `{v + w + Uw | v ∈ D(T**), w ∈ N_i}` of DLMF's extension. -/
noncomputable def vonNeumannDomain (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) :
    Submodule ℂ V :=
  T††.domain ⊔ LinearMap.range ((deficiencySpace T I).subtype +
    (deficiencySpace T (-I)).subtype ∘ₗ U.toLinearMap)

theorem mem_vonNeumannDomain {U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)} {v : V} :
    v ∈ vonNeumannDomain T U ↔
      ∃ g : (T††).domain, ∃ w : deficiencySpace T I, v = g + w + U w := by
  simp only [vonNeumannDomain, Submodule.mem_sup, LinearMap.mem_range, LinearMap.add_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, LinearIsometry.coe_toLinearMap]
  constructor
  · rintro ⟨y, hy, z, ⟨w, rfl⟩, rfl⟩
    exact ⟨⟨y, hy⟩, w, by rw [add_assoc]⟩
  · rintro ⟨g, w, rfl⟩
    exact ⟨g, g.2, _, ⟨w, rfl⟩, by rw [add_assoc]⟩

theorem IsSymmetricDLMF.vonNeumannDomain_le (hT : IsSymmetricDLMF T)
    (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) :
    vonNeumannDomain T U ≤ T†.domain := by
  intro v hv
  obtain ⟨g, w, rfl⟩ := mem_vonNeumannDomain.mp hv
  exact add_mem (add_mem (hT.le_adjoint_adjoint.2.1 g.2) (mem_eigenspaceDLMF.mp w.2).1)
    (mem_eigenspaceDLMF.mp (U w).2).1

variable (T) in
/-- DLMF §1.18(ix): the restriction of `T*` to `{v + w + Uw}`. -/
noncomputable def vonNeumannExt (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) :
    V →ₗ.[ℂ] V :=
  T†.domRestrict (vonNeumannDomain T U)

theorem vonNeumannExt_le (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) :
    vonNeumannExt T U ≤ T† :=
  domRestrict_le

theorem IsSymmetricDLMF.le_vonNeumannExt (hT : IsSymmetricDLMF T)
    (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) : T ≤ vonNeumannExt T U := by
  refine ⟨fun x hx => ⟨mem_vonNeumannDomain.mpr
    ⟨⟨x, hT.le_adjoint_adjoint.1.1 hx⟩, 0, by simp⟩, hT.le_adjoint.1 hx⟩, fun x y hxy => ?_⟩
  rw [hT.le_adjoint.2 (x := x) (y := ⟨y, y.2.2⟩) hxy]
  exact ((vonNeumannExt_le U).2 (x := y) rfl).symm

/-- For `u = g + w + Uw` in `D(A_U)`, the boundary form vanishes. -/
theorem IsSymmetricDLMF.vonNeumannExt_symmetric (hT : IsSymmetricDLMF T)
    (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) :
    IsSymmetricDLMF (vonNeumannExt T U) := by
  have hTA := hT.le_vonNeumannExt U
  refine isSymmetricDLMF_iff.mpr ⟨hT.1.mono hTA.1, fun x y => ?_⟩
  obtain ⟨g, w, hx⟩ := mem_vonNeumannDomain.mp x.2.1
  obtain ⟨g', w', hy⟩ := mem_vonNeumannDomain.mp y.2.1
  set xD : T†.domain := ⟨x, x.2.2⟩
  set yD : T†.domain := ⟨y, y.2.2⟩
  have hb := hT.boundaryForm xD yD g g' w.2 w'.2 (U w).2 (U w').2 hx hy
  have hiso : ⟪((U w : deficiencySpace T (-I)) : V), ((U w' : deficiencySpace T (-I)) : V)⟫_ℂ =
      ⟪(w : V), (w' : V)⟫_ℂ := by
    rw [← Submodule.coe_inner, ← Submodule.coe_inner, LinearIsometry.inner_map_map]
  rw [hiso, sub_self, mul_zero, sub_eq_zero] at hb
  rw [(vonNeumannExt_le U).2 (x := x) (y := xD) rfl, (vonNeumannExt_le U).2 (x := y) (y := yD) rfl]
  exact hb

/-- **DLMF §1.18(ix)**: for a surjective linear isometry `U : N_i → N_{−i}`, the restriction of
`T*` to `{v + w + Uw | v ∈ D(T**), w ∈ N_i}` is a self-adjoint extension of `T`. -/
theorem IsSymmetricDLMF.vonNeumannExt_isSelfAdjoint (hT : IsSymmetricDLMF T)
    (U : deficiencySpace T I ≃ₗᵢ[ℂ] deficiencySpace T (-I)) :
    IsSelfAdjoint (vonNeumannExt T U.toLinearIsometry) := by
  set A := vonNeumannExt T U.toLinearIsometry
  have hA := hT.vonNeumannExt_symmetric U.toLinearIsometry
  have hTA := hT.le_vonNeumannExt U.toLinearIsometry
  have hAT : A† ≤ T† := adjoint_antitone hT.1 hTA
  have key : A† ≤ A := by
    refine ⟨fun f hf => ?_, fun x y hxy => ?_⟩
    · set fD : T†.domain := ⟨f, hAT.1 hf⟩
      obtain ⟨g, a, ha, b, hb, hfd⟩ := hT.vonNeumann_decomp fD
      -- `⟪a, w⟫ = ⟪b, Uw⟫` for all `w ∈ N_i`
      have hab : ∀ w : deficiencySpace T I,
          ⟪b, ((U w : deficiencySpace T (-I)) : V)⟫_ℂ = ⟪a, (w : V)⟫_ℂ := by
        intro w
        have hmem : (w : V) + (U w : V) ∈ A.domain :=
          ⟨mem_vonNeumannDomain.mpr ⟨0, w, by simp⟩,
            hT.vonNeumannDomain_le U.toLinearIsometry
              (mem_vonNeumannDomain.mpr ⟨0, w, by simp⟩)⟩
        have hfa := (adjoint_isFormalAdjoint hA.1) ⟨f, hf⟩ ⟨_, hmem⟩
        rw [hAT.2 (x := ⟨f, hf⟩) (y := fD) rfl,
          (vonNeumannExt_le U.toLinearIsometry).2 (x := ⟨_, hmem⟩) (y := ⟨_, hmem.2⟩) rfl]
          at hfa
        have hbf := hT.boundaryForm fD ⟨_, hmem.2⟩ g 0 ha w.2 hb (U w).2 hfd (by simp)
        rw [hfa, sub_self] at hbf
        have h2 : (2 * I : ℂ) ≠ 0 := by simp
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hbf.symm).resolve_left h2))
      set c := U.symm ⟨b, hb⟩
      have hUc : ((U c : deficiencySpace T (-I)) : V) = b := by simp [c]
      have hac : a = (c : V) := by
        have h1 : ∀ w : deficiencySpace T I, ⟪a - (c : V), (w : V)⟫_ℂ = 0 := fun w => by
          rw [inner_sub_left, ← hab w, ← hUc, ← Submodule.coe_inner, ← Submodule.coe_inner,
            LinearIsometryEquiv.inner_map_map, sub_self]
        have h2 := h1 (⟨a, ha⟩ - c)
        simp only [Submodule.coe_sub] at h2
        exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)
      refine ⟨mem_vonNeumannDomain.mpr ⟨g, c, ?_⟩, hAT.1 hf⟩
      have hfd' : f = g + a + b := hfd
      rw [hfd', hac, LinearIsometryEquiv.coe_toLinearIsometry, hUc]
    · rw [hAT.2 (x := x) (y := ⟨y, y.2.2⟩) hxy]
      exact ((vonNeumannExt_le U.toLinearIsometry).2 (x := y) rfl).symm
  exact isSelfAdjoint_def.mpr (le_antisymm key hA.le_adjoint)

/-! ### Every self-adjoint extension is of this form -/

omit [CompleteSpace V] in
/-- `‖(A + i)v‖ = ‖(A − i)v‖` for symmetric `A`. -/
theorem IsSymmetricDLMF.norm_shiftOp_neg_I {A : V →ₗ.[ℂ] V} (hA : IsSymmetricDLMF A)
    (x : A.domain) : ‖shiftOp A (-I) x‖ = ‖shiftOp A I x‖ := by
  have hre : RCLike.re ⟪A x, I • (x : V)⟫_ℂ = 0 := by
    have him := hA.inner_self_im x
    have him2 : (⟪A x, (x : V)⟫_ℂ).im = 0 := by
      rw [← inner_conj_symm, Complex.conj_im, him, neg_zero]
    rw [inner_smul_right]
    simp [him2]
  have h1 : shiftOp A (-I) x = -(A x + I • (x : V)) := by rw [shiftOp_apply]; module
  have h2 : shiftOp A I x = -(A x - I • (x : V)) := by rw [shiftOp_apply]; module
  have hsq : ‖shiftOp A (-I) x‖ ^ 2 = ‖shiftOp A I x‖ ^ 2 := by
    rw [h1, h2, norm_neg, norm_neg, norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hre]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem IsSelfAdjoint.surjective_shiftOp {A : V →ₗ.[ℂ] V} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : Function.Bijective (shiftOp A z) := by
  have hs := IsSelfAdjoint.isSymmetricDLMF hA
  have hinj : Function.Injective (shiftOp A z) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := hs.norm_shiftOp_ge z x
    rw [hx, norm_zero] at this
    have h0 : ‖(x : V)‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra h
      push Not at h
      have := mul_pos (abs_pos.mpr hz) h
      linarith
    exact Subtype.ext (norm_eq_zero.mp h0)
  refine ⟨hinj, fun y => ?_⟩
  have hcl := isClosed_range_shiftOp hA.isClosed hs hz
  have hd := IsSelfAdjoint.dense_range_shiftOp hA hinj
  have : y ∈ closure (LinearMap.range (shiftOp A z) : Set V) := hd y
  rw [hcl.closure_eq] at this
  exact this

section Converse

variable {A : V →ₗ.[ℂ] V}

/-- The isometry `N_i → N_{−i}` attached to a self-adjoint extension `A`:
`w ↦ (A + i)⁻¹(2iw) − w`, i.e. `w + Uw ∈ D(A)`. -/
noncomputable def cayleyMap (hA : IsSelfAdjoint A) : deficiencySpace T I →ₗ[ℂ] V :=
  (A.domain.subtype ∘ₗ (LinearEquiv.ofBijective (shiftOp A (-I))
    (IsSelfAdjoint.surjective_shiftOp hA (by simp))).symm.toLinearMap ∘ₗ
    ((-2 * I) • (deficiencySpace T I).subtype)) - (deficiencySpace T I).subtype

theorem cayleyMap_spec (hA : IsSelfAdjoint A) (w : deficiencySpace T I) :
    ∃ h : A.domain, cayleyMap hA w = (h : V) - w ∧ shiftOp A (-I) h = (-2 * I) • (w : V) := by
  refine ⟨(LinearEquiv.ofBijective (shiftOp A (-I))
    (IsSelfAdjoint.surjective_shiftOp hA (by simp))).symm ((-2 * I) • (w : V)), rfl, ?_⟩
  exact (LinearEquiv.ofBijective (shiftOp A (-I)) _).apply_symm_apply _

variable (hT : IsSymmetricDLMF T) (hA : IsSelfAdjoint A) (hTA : T ≤ A)
include hT hA hTA

theorem le_adjoint_of_selfAdjoint_ext : A ≤ T† := by
  have h := adjoint_antitone hT.1 hTA
  rwa [isSelfAdjoint_def.mp hA] at h

theorem adjoint_adjoint_le_of_selfAdjoint_ext : T†† ≤ A := by
  have h := adjoint_antitone hA.dense_domain (le_adjoint_of_selfAdjoint_ext hT hA hTA)
  rwa [isSelfAdjoint_def.mp hA] at h

theorem cayleyMap_mem (w : deficiencySpace T I) : cayleyMap hA w ∈ deficiencySpace T (-I) := by
  have hAT := le_adjoint_of_selfAdjoint_ext hT hA hTA
  obtain ⟨h, hU, hh⟩ := cayleyMap_spec hA w
  obtain ⟨hwd, hTw⟩ := mem_eigenspaceDLMF.mp w.2
  rw [hU]
  refine mem_eigenspaceDLMF.mpr ⟨Submodule.sub_mem _ (hAT.1 h.2) hwd, ?_⟩
  have he : (⟨(h : V) - w, Submodule.sub_mem _ (hAT.1 h.2) hwd⟩ : T†.domain) =
      ⟨h, hAT.1 h.2⟩ - ⟨w, hwd⟩ := rfl
  rw [he, LinearPMap.map_sub, hTw, ← hAT.2 (x := h) rfl]
  rw [shiftOp_apply] at hh
  linear_combination (norm := module) (-1 : ℂ) • hh

/-- DLMF §1.18(ix): the isometry `U : N_i → N_{−i}` of a self-adjoint extension. -/
noncomputable def cayleyIsometry : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I) where
  toLinearMap := LinearMap.codRestrict _ (cayleyMap hA) (cayleyMap_mem hT hA hTA)
  norm_map' w := by
    obtain ⟨h, hU, hh⟩ := cayleyMap_spec hA w
    change ‖cayleyMap hA w‖ = ‖(w : V)‖
    have h2 : shiftOp A I h = (2 * I) • ((h : V) - w) := by
      rw [shiftOp_apply] at hh ⊢
      linear_combination (norm := module) hh
    have := (IsSelfAdjoint.isSymmetricDLMF hA).norm_shiftOp_neg_I h
    rw [hh, h2, norm_smul, norm_smul] at this
    rw [hU]
    have h2I : ‖(2 * I : ℂ)‖ ≠ 0 := by simp
    have h2I' : ‖(-2 * I : ℂ)‖ = ‖(2 * I : ℂ)‖ := by rw [neg_mul, norm_neg]
    rw [h2I'] at this
    exact (mul_left_cancel₀ h2I this).symm

theorem cayleyIsometry_surjective : Function.Surjective (cayleyIsometry hT hA hTA) := by
  have hAT := le_adjoint_of_selfAdjoint_ext hT hA hTA
  intro b
  obtain ⟨hbd, hTb⟩ := mem_eigenspaceDLMF.mp b.2
  have hbij := IsSelfAdjoint.surjective_shiftOp hA (z := I) (by simp)
  obtain ⟨h', hh'⟩ := hbij.2 ((2 * I) • (b : V))
  rw [shiftOp_apply] at hh'
  have hAh' : A h' = I • (h' : V) - (2 * I) • (b : V) := by
    linear_combination (norm := module) (-1 : ℂ) • hh'
  have hmem : (h' : V) - b ∈ deficiencySpace T I := by
    refine mem_eigenspaceDLMF.mpr ⟨Submodule.sub_mem _ (hAT.1 h'.2) hbd, ?_⟩
    have he : (⟨(h' : V) - b, Submodule.sub_mem _ (hAT.1 h'.2) hbd⟩ : T†.domain) =
        ⟨h', hAT.1 h'.2⟩ - ⟨b, hbd⟩ := rfl
    rw [he, LinearPMap.map_sub, hTb, ← hAT.2 (x := h') rfl, hAh']
    module
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  change cayleyMap hA ⟨_, hmem⟩ = b
  obtain ⟨h, hU, hh⟩ := cayleyMap_spec hA ⟨_, hmem⟩
  have hhh : h = h' := by
    refine (IsSelfAdjoint.surjective_shiftOp hA (z := -I) (by simp)).1 ?_
    rw [hh, shiftOp_apply, hAh']
    simp only
    module
  rw [hU, hhh]
  simp

/-- **DLMF §1.18(ix)**: every self-adjoint extension `A` of `T` is the restriction of `T*` to
`{v + w + Uw}` for a surjective linear isometry `U : N_i → N_{−i}`. -/
theorem eq_vonNeumannExt_of_selfAdjoint :
    ∃ U : deficiencySpace T I ≃ₗᵢ[ℂ] deficiencySpace T (-I),
      A = vonNeumannExt T U.toLinearIsometry := by
  set U := LinearIsometryEquiv.ofSurjective (cayleyIsometry hT hA hTA)
    (cayleyIsometry_surjective hT hA hTA)
  refine ⟨U, ?_⟩
  set B := vonNeumannExt T U.toLinearIsometry
  have hB := hT.vonNeumannExt_isSelfAdjoint U
  have hAT := le_adjoint_of_selfAdjoint_ext hT hA hTA
  have hSA := adjoint_adjoint_le_of_selfAdjoint_ext hT hA hTA
  have hBA : B ≤ A := by
    refine ⟨fun v hv => ?_, fun x y hxy => ?_⟩
    · obtain ⟨g, w, rfl⟩ := mem_vonNeumannDomain.mp hv.1
      obtain ⟨h, hU, -⟩ := cayleyMap_spec hA w
      have : ((U.toLinearIsometry w : deficiencySpace T (-I)) : V) = cayleyMap hA w := rfl
      rw [add_assoc, this, hU, add_sub_cancel]
      exact add_mem (hSA.1 g.2) h.2
    · rw [(vonNeumannExt_le U.toLinearIsometry).2 (x := x) (y := ⟨y, hAT.1 y.2⟩) hxy]
      exact (hAT.2 (x := y) rfl).symm
  have hAB : A ≤ B := by
    have h := adjoint_antitone hB.dense_domain hBA
    rwa [isSelfAdjoint_def.mp hA, isSelfAdjoint_def.mp hB] at h
  exact le_antisymm hAB hBA

end Converse

/-- **DLMF §1.18(ix)**: `T` has self-adjoint extensions iff `N_i` and `N_{−i}` are isometrically
isomorphic (`n₊ = n₋` as Hilbert dimensions); then `dim N_i = dim N_{−i}`. -/
theorem IsSymmetricDLMF.exists_selfAdjoint_ext_iff (hT : IsSymmetricDLMF T) :
    (∃ A : V →ₗ.[ℂ] V, IsSelfAdjoint A ∧ T ≤ A) ↔
      Nonempty (deficiencySpace T I ≃ₗᵢ[ℂ] deficiencySpace T (-I)) := by
  constructor
  · rintro ⟨A, hA, hTA⟩
    exact ⟨(eq_vonNeumannExt_of_selfAdjoint hT hA hTA).choose⟩
  · rintro ⟨U⟩
    exact ⟨_, hT.vonNeumannExt_isSelfAdjoint U, hT.le_vonNeumannExt _⟩

theorem IsSymmetricDLMF.rank_eq_of_selfAdjoint_ext (hT : IsSymmetricDLMF T) {A : V →ₗ.[ℂ] V}
    (hA : IsSelfAdjoint A) (hTA : T ≤ A) :
    Module.rank ℂ (deficiencySpace T I) = Module.rank ℂ (deficiencySpace T (-I)) :=
  (eq_vonNeumannExt_of_selfAdjoint hT hA hTA).choose.toLinearEquiv.rank_eq

/-- For finite deficiency indices, self-adjoint extensions exist iff `n₊ = n₋`. -/
theorem IsSymmetricDLMF.exists_selfAdjoint_ext_iff_finrank (hT : IsSymmetricDLMF T)
    [FiniteDimensional ℂ (deficiencySpace T I)] [FiniteDimensional ℂ (deficiencySpace T (-I))] :
    (∃ A : V →ₗ.[ℂ] V, IsSelfAdjoint A ∧ T ≤ A) ↔
      Module.finrank ℂ (deficiencySpace T I) = Module.finrank ℂ (deficiencySpace T (-I)) := by
  rw [hT.exists_selfAdjoint_ext_iff]
  constructor
  · rintro ⟨U⟩
    exact U.toLinearEquiv.finrank_eq
  · intro h
    exact ⟨((stdOrthonormalBasis ℂ (deficiencySpace T I)).reindex (finCongr h)).repr.trans
      (stdOrthonormalBasis ℂ (deficiencySpace T (-I))).repr.symm⟩

/-- `A_U` is self-adjoint iff the isometry `U` is surjective: DLMF's "linear isometry" must be
onto. -/
theorem IsSymmetricDLMF.vonNeumannExt_isSelfAdjoint_iff (hT : IsSymmetricDLMF T)
    (U : deficiencySpace T I →ₗᵢ[ℂ] deficiencySpace T (-I)) :
    IsSelfAdjoint (vonNeumannExt T U) ↔ Function.Surjective U := by
  constructor
  · intro hA
    obtain ⟨U', hU'⟩ := eq_vonNeumannExt_of_selfAdjoint hT hA (hT.le_vonNeumannExt U)
    have hUU' : ∀ w, U w = U' w := by
      intro w
      have hmem : (w : V) + U w ∈ vonNeumannDomain T U'.toLinearIsometry := by
        have h1 : (w : V) + U w ∈ (vonNeumannExt T U).domain :=
          ⟨mem_vonNeumannDomain.mpr ⟨0, w, by simp⟩,
            hT.vonNeumannDomain_le U (mem_vonNeumannDomain.mpr ⟨0, w, by simp⟩)⟩
        rw [hU'] at h1
        exact h1.1
      obtain ⟨g', w', hw'⟩ := mem_vonNeumannDomain.mp hmem
      have hsum : ((-g' : (T††).domain) : V) + ((w : V) - w') +
          ((U w : V) - (U' w' : V)) = 0 := by
        simp only [Submodule.coe_neg]
        rw [LinearIsometryEquiv.coe_toLinearIsometry] at hw'
        linear_combination (norm := module) hw'
      obtain ⟨-, hww, hUw⟩ := hT.vonNeumann_unique (-g')
        (Submodule.sub_mem _ w.2 w'.2) (Submodule.sub_mem _ (U w).2 (U' w').2) hsum
      have : w = w' := Subtype.ext (sub_eq_zero.mp hww)
      subst this
      exact Subtype.ext (sub_eq_zero.mp hUw)
    intro b
    obtain ⟨w, hw⟩ := U'.surjective b
    exact ⟨w, by rw [hUU']; exact hw⟩
  · intro hs
    have := hT.vonNeumannExt_isSelfAdjoint (LinearIsometryEquiv.ofSurjective U hs)
    exact this

end Azurite.DLMF
