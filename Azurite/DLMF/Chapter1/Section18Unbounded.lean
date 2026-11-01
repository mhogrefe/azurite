/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# DLMF §1.18(ix): adjoints and self-adjoint operators

https://dlmf.nist.gov/1.18.ix

Unbounded operators are Mathlib's partially defined linear maps `V →ₗ.[ℂ] V`, with adjoint `T†`
(`LinearPMap.adjoint`). This file covers DLMF's "Self-Adjoint Operators" paragraph.

* `dlmf_1_18_68`: `D(T*) = {w | sup_{‖v‖ = 1} |⟨Tv, w⟩| < ∞}`, matching Mathlib's adjoint domain.
* `dlmf_1_18_69`: `⟨Tv, w⟩ = ⟨v, T*w⟩`.
* `IsSymmetricDLMF` (1.18.70); `IsSymmetricDLMF.le_adjoint` (`T ⊂ T*`);
  `IsSymmetricDLMF.le_adjoint_adjoint` (`T ⊂ T** ⊂ T*`); `adjoint_antitone`; `T*** = T*`.
* `IsEssentiallySelfAdjointDLMF` (`T ⊂ T** = T*`), equivalent to `T**` being self-adjoint.
  Self-adjoint (`T = T*`) is Mathlib's `IsSelfAdjoint`.

DLMF's inner product is linear in the first slot (`dlmfInner`).
-/

open LinearPMap
open scoped ComplexConjugate

namespace Azurite.DLMF

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem norm_le_of_sphere_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E →ₗ[ℂ] ℂ) {M : ℝ} (hM : ∀ v : E, ‖v‖ = 1 → ‖f v‖ ≤ M) (v : E) :
    ‖f v‖ ≤ M * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hM ((‖v‖⁻¹ : ℂ) • v) (by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le, inv_mul_cancel₀ hn.ne'])
  rw [_root_.map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le] at h1
  rw [inv_mul_eq_div, div_le_iff₀ hn] at h1
  exact h1

/-- DLMF (1.18.68): `D(T*) = {w | sup_{v ∈ D(T), ‖v‖ = 1} |⟨Tv, w⟩| < ∞}`. -/
theorem dlmf_1_18_68 (T : V →ₗ.[ℂ] V) (w : V) :
    w ∈ T†.domain ↔
      BddAbove ((fun v : T.domain => ‖dlmfInner (T v) w‖) '' {v | ‖(v : V)‖ = 1}) := by
  set f : T.domain →ₗ[ℂ] ℂ := (innerₛₗ ℂ w).comp T.toFun
  have hf : ∀ v, f v = dlmfInner (T v) w := fun v => rfl
  rw [mem_adjoint_domain_iff]
  change Continuous f ↔ _
  constructor
  · intro hc
    let F : T.domain →L[ℂ] ℂ := ⟨f, hc⟩
    refine ⟨‖F‖, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have := F.le_opNorm v
    rw [show ‖v‖ = 1 from hv, mul_one] at this
    show ‖dlmfInner (T v) w‖ ≤ ‖F‖
    rw [← hf]
    exact this
  · rintro ⟨M, hM⟩
    exact (f.mkContinuous M fun v => norm_le_of_sphere_bound f
      (fun v hv => hM ⟨v, hv, congrArg norm (hf v).symm⟩) v).continuous

/-- DLMF (1.18.69): `⟨Tv, w⟩ = ⟨v, T*w⟩` for `v ∈ D(T)`, `w ∈ D(T*)`. -/
theorem dlmf_1_18_69 {T : V →ₗ.[ℂ] V} (hT : Dense (T.domain : Set V)) (v : T.domain)
    (w : T†.domain) : dlmfInner (T v) w = dlmfInner (v : V) (T† w) :=
  ((adjoint_isFormalAdjoint hT) w v).symm

/-- DLMF (1.18.70): `T` is symmetric if its domain is dense and `⟨Tv, w⟩ = ⟨v, Tw⟩`. -/
def IsSymmetricDLMF (T : V →ₗ.[ℂ] V) : Prop :=
  Dense (T.domain : Set V) ∧ ∀ v w : T.domain, dlmfInner (T v) w = dlmfInner (v : V) (T w)

omit [CompleteSpace V] in
theorem IsSymmetricDLMF.isFormalAdjoint {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) :
    T.IsFormalAdjoint T := fun v w => by
  have := hT.2 w v
  simp only [dlmfInner] at this
  exact this.symm

omit [CompleteSpace V] in
theorem isSymmetricDLMF_iff {T : V →ₗ.[ℂ] V} :
    IsSymmetricDLMF T ↔ Dense (T.domain : Set V) ∧ T.IsFormalAdjoint T :=
  ⟨fun h => ⟨h.1, h.isFormalAdjoint⟩, fun h => ⟨h.1, fun v w => (h.2 w v).symm⟩⟩

/-- DLMF §1.18(ix): if `T` is symmetric then `T ⊂ T*`. -/
theorem IsSymmetricDLMF.le_adjoint {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) : T ≤ T† :=
  hT.isFormalAdjoint.le_adjoint hT.1

/-- Taking adjoints reverses inclusions of densely defined operators. -/
theorem adjoint_antitone {S T : V →ₗ.[ℂ] V} (hS : Dense (S.domain : Set V)) (h : S ≤ T) :
    T† ≤ S† := by
  have hT : Dense (T.domain : Set V) := hS.mono h.1
  have hfa : S.IsFormalAdjoint T† := fun x y => by
    have h1 := (adjoint_isFormalAdjoint hT) y ⟨x, h.1 x.2⟩
    rw [← h.2 (x := x) (y := ⟨x, h.1 x.2⟩) rfl] at h1
    rw [← inner_conj_symm, ← h1, inner_conj_symm]
  exact hfa.le_adjoint hS

theorem IsSymmetricDLMF.dense_adjoint {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) :
    Dense (T†.domain : Set V) :=
  hT.1.mono hT.le_adjoint.1

/-- DLMF §1.18(ix): if `T` is symmetric then `T ⊂ T** ⊂ T*`. -/
theorem IsSymmetricDLMF.le_adjoint_adjoint {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) :
    T ≤ T†† ∧ T†† ≤ T† :=
  ⟨(adjoint_isFormalAdjoint hT.1).le_adjoint hT.dense_adjoint,
    adjoint_antitone hT.1 hT.le_adjoint⟩

/-- `T*** = T*` for symmetric `T`. -/
theorem IsSymmetricDLMF.adjoint_adjoint_adjoint {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) :
    T††† = T† := by
  have h1 := hT.le_adjoint_adjoint
  refine le_antisymm (adjoint_antitone hT.1 h1.1) ?_
  exact (adjoint_isFormalAdjoint hT.dense_adjoint).le_adjoint (hT.1.mono h1.1.1)

/-- DLMF §1.18(ix): `T` is essentially self-adjoint if `T ⊂ T** = T*`. -/
def IsEssentiallySelfAdjointDLMF (T : V →ₗ.[ℂ] V) : Prop :=
  T ≤ T†† ∧ T†† = T†

/-- A symmetric operator is essentially self-adjoint iff `T**` is self-adjoint. -/
theorem IsSymmetricDLMF.isEssentiallySelfAdjoint_iff {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) :
    IsEssentiallySelfAdjointDLMF T ↔ IsSelfAdjoint T†† := by
  rw [isSelfAdjoint_def, hT.adjoint_adjoint_adjoint]
  exact ⟨fun h => h.2.symm, fun h => ⟨hT.le_adjoint_adjoint.1, h.symm⟩⟩

/-- A self-adjoint operator (`T = T*`) is symmetric. -/
theorem IsSelfAdjoint.isSymmetricDLMF {T : V →ₗ.[ℂ] V} (hT : IsSelfAdjoint T) :
    IsSymmetricDLMF T := by
  refine isSymmetricDLMF_iff.mpr ⟨hT.dense_domain, ?_⟩
  have h := adjoint_isFormalAdjoint hT.dense_domain (T := T)
  rw [isSelfAdjoint_def.mp hT] at h
  exact h

/-- A self-adjoint operator is essentially self-adjoint. -/
theorem IsSelfAdjoint.isEssentiallySelfAdjointDLMF {T : V →ₗ.[ℂ] V} (hT : IsSelfAdjoint T) :
    IsEssentiallySelfAdjointDLMF T := by
  have h : T† = T := isSelfAdjoint_def.mp hT
  refine ⟨?_, ?_⟩ <;> rw [h, h]

end Azurite.DLMF
