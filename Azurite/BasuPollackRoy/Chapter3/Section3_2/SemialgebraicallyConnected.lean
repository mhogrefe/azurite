/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.ClosureInterior
import Mathlib.Topology.ContinuousOn

/-! # BPR §3.2 — semialgebraically connected sets

Over a real closed field `R`, a semialgebraic set `S ⊆ R^k` is **semialgebraically connected** if it
is not the disjoint union of two non-empty semialgebraic sets both closed in `S`. Equivalently, `S`
contains no non-empty semialgebraic *strict* subset that is both open and closed in `S`.

We take the disjoint-union form as the definition and prove the clopen reformulation
(`isSemialgebraicallyConnected_iff`), and record the relative-topology preimage lemma
(`isClosedIn_preimage`) used to transfer connectedness along continuous maps. -/

namespace Azurite.BPR

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR definition (semialgebraically connected set).** A semialgebraic set `S ⊆ R^k` is
*semialgebraically connected* if it is not the disjoint union of two non-empty semialgebraic sets
each closed in `S`. -/
def IsSemialgebraicallyConnected (S : Set (Fin k → R)) : Prop :=
  ¬ ∃ A B : Set (Fin k → R), A.Nonempty ∧ B.Nonempty ∧
      IsSemialgebraicSet A ∧ IsSemialgebraicSet B ∧
      IsClosedIn S A ∧ IsClosedIn S B ∧ A ∩ B = ∅ ∧ A ∪ B = S

/-- The complement (within `S`) of a set closed in `S` is open in `S`. -/
theorem isOpenIn_sdiff_of_isClosedIn {S B : Set (Fin k → R)} (h : IsClosedIn S B) :
    IsOpenIn S (S \ B) := by
  obtain ⟨F, hF, rfl⟩ := h
  refine ⟨Fᶜ, hF.isOpen_compl, ?_⟩
  ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]; tauto

/-- The complement (within `S`) of a set open in `S` is closed in `S`. -/
theorem isClosedIn_sdiff_of_isOpenIn {S U : Set (Fin k → R)} (h : IsOpenIn S U) :
    IsClosedIn S (S \ U) := by
  obtain ⟨V, hV, rfl⟩ := h
  refine ⟨Vᶜ, hV.isClosed_compl, ?_⟩
  ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]; tauto

/-- **Preimage of a relatively-closed set under a `ContinuousOn` map is relatively closed.** If
`f : A → B` is continuous on `A` and maps `A` into `B`, then the preimage in `A` of a set closed in
`B` is closed in `A`. (`A` need not be closed in `R^k`, so this goes through the subspace, not
`ContinuousOn.preimage_isClosed_of_isClosed`.) -/
theorem isClosedIn_preimage {A : Set (Fin k → R)} {B : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {U : Set (Fin ℓ → R)}
    (hf : ContinuousOn f A) (hmaps : Set.MapsTo f A B) (hU : IsClosedIn B U) :
    IsClosedIn A (A ∩ f ⁻¹' U) := by
  obtain ⟨F, hF, rfl⟩ := hU
  have hseteq : A ∩ f ⁻¹' (F ∩ B) = A ∩ f ⁻¹' F := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun ⟨haA, hfF, _⟩ => ⟨haA, hfF⟩, fun ⟨haA, hfF⟩ => ⟨haA, hfF, hmaps haA⟩⟩
  rw [hseteq, isClosedIn_iff_isClosed_subtype Set.inter_subset_left]
  have hcont : Continuous (A.domRestrict f) := continuousOn_iff_continuous_domRestrict.mp hf
  have hpre : (Subtype.val ⁻¹' (A ∩ f ⁻¹' F) : Set A) = (A.domRestrict f) ⁻¹' F := by
    ext a
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.domRestrict_apply]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  rw [hpre]
  exact hF.preimage hcont

/-- **Clopen reformulation.** A semialgebraic set `S` is semialgebraically connected iff it has no
non-empty semialgebraic strict subset that is both open and closed in `S`. -/
theorem isSemialgebraicallyConnected_iff {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicallyConnected S ↔
      ¬ ∃ U : Set (Fin k → R), U.Nonempty ∧ U ≠ S ∧ U ⊆ S ∧
        IsSemialgebraicSet U ∧ IsOpenIn S U ∧ IsClosedIn S U := by
  unfold IsSemialgebraicallyConnected
  rw [not_iff_not]
  constructor
  · rintro ⟨A, B, hA, hB, hAsa, _, hAcl, hBcl, hAB, hABS⟩
    have hAsub : A ⊆ S := by rw [← hABS]; exact Set.subset_union_left
    have hAeq : A = S \ B := by
      rw [← hABS]; ext x
      simp only [Set.mem_union, Set.mem_sdiff]
      constructor
      · exact fun hx => ⟨Or.inl hx, fun hxB => Set.notMem_empty x (hAB ▸ Set.mem_inter hx hxB)⟩
      · rintro ⟨hx | hx, hxB⟩
        · exact hx
        · exact absurd hx hxB
    refine ⟨A, hA, ?_, hAsub, hAsa, ?_, hAcl⟩
    · intro hAeqS
      obtain ⟨b, hb⟩ := hB
      have hbA : b ∈ A := by rw [hAeqS, ← hABS]; exact Set.mem_union_right _ hb
      exact Set.notMem_empty b (hAB ▸ Set.mem_inter hbA hb)
    · rw [hAeq]; exact isOpenIn_sdiff_of_isClosedIn hBcl
  · rintro ⟨U, hU, hUS, hUsub, hUsa, hUop, hUcl⟩
    refine ⟨U, S \ U, hU, ?_, hUsa, ?_, hUcl, isClosedIn_sdiff_of_isOpenIn hUop,
      Set.inter_sdiff_self U S, Set.union_sdiff_cancel hUsub⟩
    · rw [Set.sdiff_nonempty]; exact fun hSU => hUS (Set.Subset.antisymm hUsub hSU)
    · rw [Set.sdiff_eq]; exact hS.inter hUsa.compl

end Azurite.BPR
