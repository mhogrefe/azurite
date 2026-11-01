/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

/-!
# DLMF §1.18(iii): Linear operators on a Hilbert space

https://dlmf.nist.gov/1.18.iii

Abstract operator theory, in DLMF's convention `⟨u, v⟩ = dlmfInner u v`, linear in `u`.
The differential operator `d²/dx²` is in `Section18DiffOp.lean`.

* 1.18.21: linear operators (`IsLinearOperator` ↔ Mathlib's `LinearMap`).
* 1.18.22: bounded operators (`IsBoundedOperator`, `sup_{‖v‖=1} ‖Tv‖ < ∞`) are the continuous ones
  (`isBoundedOperator_iff`), and `opNormDLMF` is the operator norm (`opNormDLMF_eq`).
* Dense domains: density as limits of sequences (`dense_iff_seq`). A bounded operator on a dense
  domain extends uniquely to `V` (`existsUnique_extension`).
* 1.18.23: the adjoint (`dlmf_1_18_23`, characterized by `eq_adjoint_of_dlmf`), self-adjointness
  (`isSelfAdjoint_iff_dlmf`), and symmetric operators on a domain (`IsSymmetricOn`).
* 1.18.24: eigenvalues of symmetric operators are real (`IsSymmetricOn.eigenvalue_real`), and
  eigenfunctions for distinct eigenvalues are orthogonal (`dlmf_1_18_24`). Degenerate
  eigenfunctions may be orthogonalized by Gram–Schmidt within the eigenspace
  (`orthogonalize_eigenfunctions`).

No discrepancies with the DLMF were found here.
-/

open Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
open InnerProductSpace

namespace Azurite.DLMF

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ### Bounded and unbounded linear operators (1.18.21–1.18.22) -/

/-- DLMF 1.18.21: `T(αv + βw) = αTv + βTw`. -/
def IsLinearOperator (T : V → V) : Prop :=
  ∀ (α β : ℂ) (v w : V), T (α • v + β • w) = α • T v + β • T w

theorem isLinearOperator_iff (T : V → V) :
    IsLinearOperator T ↔ ∃ L : V →ₗ[ℂ] V, ⇑L = T := by
  constructor
  · intro h
    have h0 : T 0 = 0 := by simpa using h 0 0 0 0
    refine ⟨{ toFun := T, map_add' := fun v w => ?_, map_smul' := fun c v => ?_ }, rfl⟩
    · simpa using h 1 1 v w
    · simpa [h0] using h c 0 v 0
  · rintro ⟨L, rfl⟩ α β v w
    simp

/-- DLMF 1.18.22: `‖T‖ = sup_{‖v‖ = 1} ‖Tv‖`. -/
noncomputable def opNormDLMF (T : V →ₗ[ℂ] V) : ℝ :=
  sSup ((fun v => ‖T v‖) '' Metric.sphere 0 1)

/-- DLMF 1.18.22: `T` is bounded if `sup_{‖v‖ = 1} ‖Tv‖ < ∞`. -/
def IsBoundedOperator (T : V →ₗ[ℂ] V) : Prop :=
  BddAbove ((fun v => ‖T v‖) '' Metric.sphere 0 1)

theorem norm_le_of_bddAbove_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] V) {M : ℝ} (hM : ∀ v : E, ‖v‖ = 1 → ‖T v‖ ≤ M) (v : E) :
    ‖T v‖ ≤ M * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hM ((‖v‖⁻¹ : ℂ) • v) (by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le, inv_mul_cancel₀ hn.ne'])
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le] at h1
  rw [inv_mul_eq_div, div_le_iff₀ hn] at h1
  exact h1

/-- Bounded operators are exactly the continuous ones. -/
theorem isBoundedOperator_iff (T : V →ₗ[ℂ] V) : IsBoundedOperator T ↔ Continuous T := by
  constructor
  · rintro ⟨M, hM⟩
    exact (T.mkContinuous M (norm_le_of_bddAbove_sphere T fun v hv =>
      hM ⟨v, by simpa using hv, rfl⟩)).continuous
  · intro hc
    let Tc : V →L[ℂ] V := ⟨T, hc⟩
    refine ⟨‖Tc‖, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have := Tc.le_opNorm v
    rw [mem_sphere_zero_iff_norm.mp hv, mul_one] at this
    exact this

/-- DLMF 1.18.22: for bounded `T`, `sup_{‖v‖ = 1} ‖Tv‖` is the operator norm. -/
theorem opNormDLMF_eq [Nontrivial V] (T : V →L[ℂ] V) : opNormDLMF (T : V →ₗ[ℂ] V) = ‖T‖ :=
  T.sSup_sphere_eq_norm

/-! ### Densely defined operators -/

/-- DLMF §1.18(iii): `𝒟` is dense iff every `v` is the limit of a sequence in `𝒟`. -/
theorem dense_iff_seq (D : Submodule ℂ V) :
    Dense (D : Set V) ↔ ∀ v : V, ∃ u : ℕ → V, (∀ n, u n ∈ D) ∧
      Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
  refine ⟨fun h v => ?_, fun h => fun v => ?_⟩
  · obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.mp (h v)
    exact ⟨u, hu, tendsto_iff_norm_sub_tendsto_zero.mp hl⟩
  · obtain ⟨u, hu, hl⟩ := h v
    exact mem_closure_iff_seq_limit.mpr ⟨u, hu, tendsto_iff_norm_sub_tendsto_zero.mpr hl⟩

/-- DLMF §1.18(iii): an operator `T : 𝒟(T) → V` is bounded if
`sup_{v ∈ 𝒟(T), ‖v‖ = 1} ‖Tv‖ < ∞`, and unbounded otherwise. -/
def IsBoundedOn {D : Submodule ℂ V} (T : D →ₗ[ℂ] V) : Prop :=
  BddAbove ((fun v : D => ‖T v‖) '' {v | ‖v‖ = 1})

/-- DLMF §1.18(iii): a bounded operator on a dense domain extends uniquely to a bounded operator
on `V`. -/
theorem existsUnique_extension [CompleteSpace V] {D : Submodule ℂ V} (hD : Dense (D : Set V))
    (T : D →ₗ[ℂ] V) (hT : IsBoundedOn T) :
    ∃! S : V →L[ℂ] V, ∀ v : D, S v = T v := by
  obtain ⟨M, hM⟩ := hT
  have hb := norm_le_of_bddAbove_sphere T fun v hv => hM ⟨v, hv, rfl⟩
  let Tc : D →L[ℂ] V := T.mkContinuous M hb
  have hdr : DenseRange (D.subtypeL : D → V) := by
    rw [DenseRange, Submodule.coe_subtypeL, Submodule.coe_subtype, Subtype.range_coe]
    exact hD
  have hui : IsUniformInducing (D.subtypeL : D → V) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨Tc.extend D.subtypeL, fun v => ?_, fun S hS => ?_⟩
  · have := Tc.extend_eq hdr hui v
    simpa [Tc] using this
  · have he : ⇑S = ⇑(Tc.extend D.subtypeL) := Continuous.ext_on hD S.continuous
      (Tc.extend D.subtypeL).continuous fun x hx => by
        have h1 := hS ⟨x, hx⟩
        have h2 := Tc.extend_eq hdr hui ⟨x, hx⟩
        simp only [Submodule.subtypeL_apply] at h2
        simp only at h1
        rw [h1, h2]
        simp [Tc]
    exact ContinuousLinearMap.ext fun x => congrFun he x

/-! ### Adjoint, self-adjoint and symmetric operators (1.18.23–1.18.24) -/

/-- DLMF 1.18.23: `⟨Tv, w⟩ = ⟨v, T*w⟩` for the adjoint `T*` of a bounded `T`. -/
theorem dlmf_1_18_23 [CompleteSpace V] (T : V →L[ℂ] V) (v w : V) :
    dlmfInner (T v) w = dlmfInner v (ContinuousLinearMap.adjoint T w) := by
  simp only [dlmfInner, ContinuousLinearMap.adjoint_inner_left]

/-- DLMF 1.18.23 characterizes the adjoint. -/
theorem eq_adjoint_of_dlmf [CompleteSpace V] (T S : V →L[ℂ] V)
    (h : ∀ v w, dlmfInner (T v) w = dlmfInner v (S w)) : S = ContinuousLinearMap.adjoint T :=
  (ContinuousLinearMap.eq_adjoint_iff S T).mpr fun x y => (h y x).symm

/-- DLMF §1.18(iii): `T` is self-adjoint if `T* = T`. -/
theorem isSelfAdjoint_iff_dlmf [CompleteSpace V] (T : V →L[ℂ] V) :
    IsSelfAdjoint T ↔ ContinuousLinearMap.adjoint T = T :=
  ContinuousLinearMap.isSelfAdjoint_iff'

/-- DLMF §1.18(iii): `T` is symmetric if 1.18.23 holds with `T* = T` on its (dense) domain. -/
def IsSymmetricOn {D : Submodule ℂ V} (T : D →ₗ[ℂ] V) : Prop :=
  ∀ v w : D, dlmfInner (T v) (w : V) = dlmfInner (v : V) (T w)

variable {D : Submodule ℂ V} {T : D →ₗ[ℂ] V}

theorem dlmfInner_smul_left (c : ℂ) (u v : V) : dlmfInner (c • u) v = c * dlmfInner u v := by
  simp [dlmfInner, inner_smul_right]

theorem dlmfInner_smul_right (c : ℂ) (u v : V) :
    dlmfInner u (c • v) = conj c * dlmfInner u v := by
  simp [dlmfInner, inner_smul_left]

/-- DLMF §1.18(iii): eigenvalues of symmetric operators are real. -/
theorem IsSymmetricOn.eigenvalue_real (hT : IsSymmetricOn T) {u : D} (hu : (u : V) ≠ 0) {l : ℂ}
    (h : T u = l • (u : V)) : conj l = l := by
  have e := hT u u
  rw [h, dlmfInner_smul_left, dlmfInner_smul_right] at e
  have hne : dlmfInner (u : V) u ≠ 0 := fun h0 => hu (dlmf_1_18_i_definite h0)
  exact (mul_right_cancel₀ hne e).symm

/-- DLMF 1.18.24: eigenfunctions of a symmetric operator for distinct eigenvalues are
orthogonal. -/
theorem dlmf_1_18_24 (hT : IsSymmetricOn T) {u u' : D} (hu' : (u' : V) ≠ 0) {l l' : ℂ}
    (h : T u = l • (u : V)) (h' : T u' = l' • (u' : V)) (hl : l ≠ l') :
    dlmfInner (u : V) u' = 0 := by
  have hr := hT.eigenvalue_real hu' h'
  have e := hT u u'
  rw [h, h', dlmfInner_smul_left, dlmfInner_smul_right, hr] at e
  have : (l - l') * dlmfInner (u : V) u' = 0 := by rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl)

/-- The eigenspace `{u ∈ 𝒟(T) : Tu = λu}` as a subspace of `V`. -/
def eigenSubmodule (T : D →ₗ[ℂ] V) (l : ℂ) : Submodule ℂ V where
  carrier := {x | ∃ h : x ∈ D, T ⟨x, h⟩ = l • x}
  add_mem' := by
    rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
    refine ⟨D.add_mem hx hy, ?_⟩
    have : (⟨x + y, D.add_mem hx hy⟩ : D) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, ex, ey, smul_add]
  zero_mem' := ⟨D.zero_mem, by
    have : (⟨0, D.zero_mem⟩ : D) = 0 := rfl
    rw [this, map_zero, smul_zero]⟩
  smul_mem' := by
    rintro c x ⟨hx, ex⟩
    refine ⟨D.smul_mem c hx, ?_⟩
    have : (⟨c • x, D.smul_mem c hx⟩ : D) = c • ⟨x, hx⟩ := rfl
    rw [this, map_smul, ex, smul_comm]

/-- DLMF §1.18(iii): eigenfunctions of a degenerate eigenvalue may be orthogonalized: the
Gram–Schmidt process turns linearly independent eigenfunctions `uₙ` for `λ` into orthonormal
eigenfunctions for `λ` with the same span. -/
theorem orthogonalize_eigenfunctions {u : ℕ → V} (hli : LinearIndependent ℂ u) {l : ℂ}
    (hu : ∀ n, ∃ h : u n ∈ D, T ⟨u n, h⟩ = l • u n) :
    Orthonormal ℂ (gramSchmidtNormed ℂ u) ∧
      Submodule.span ℂ (range (gramSchmidtNormed ℂ u)) = Submodule.span ℂ (range u) ∧
      ∀ n, ∃ h : gramSchmidtNormed ℂ u n ∈ D, T ⟨_, h⟩ = l • gramSchmidtNormed ℂ u n := by
  have hsp : Submodule.span ℂ (range (gramSchmidtNormed ℂ u)) = Submodule.span ℂ (range u) :=
    (span_gramSchmidtNormed_range u).trans (span_gramSchmidt ℂ u)
  refine ⟨gramSchmidtNormed_orthonormal hli, hsp, fun n => ?_⟩
  have hle : Submodule.span ℂ (range u) ≤ eigenSubmodule T l :=
    Submodule.span_le.mpr (by rintro _ ⟨m, rfl⟩; exact hu m)
  have hmem : gramSchmidtNormed ℂ u n ∈ Submodule.span ℂ (range u) := by
    rw [← hsp]
    exact Submodule.subset_span ⟨n, rfl⟩
  exact hle hmem

end Azurite.DLMF
