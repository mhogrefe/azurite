/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_2.SemialgebraicallyConnected
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_1
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_4

/-! # BPR §3.2, Proposition 3.6 — `R` and its intervals are semialgebraically connected

A real closed field `R` (and all its intervals) is semialgebraically connected. We work on the line
`R^1 = Fin 1 → R`; an "interval" is a set `S` whose section `constPt ⁻¹' S ⊆ R` is order-connected.

The proof uses the 1-dimensional structure theorem (Proposition 3.4): a semialgebraic subset of `R`
is *constant on the gaps* between finitely many breakpoints, so the relevant suprema exist
(`ConstOnGaps.exists_isLUB`). Given a hypothetical splitting `S = A ⊔ B` into two non-empty
semialgebraic sets closed in `S`, pick `α ∈ A`, `β ∈ B` with `α < β`, and let `c` be the supremum of
the `A`-points below `β`. Then `c` lies in the interval, hence in `A` or `B`; either way the
closedness of the *other* piece forces `c` into it as a limit point (`mem_closure_iff_ball`),
contradicting disjointness. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A relatively-closed set contains its relative closure points. -/
theorem mem_of_mem_closure_of_isClosedIn {k : ℕ} {S A : Set (Fin k → R)} (h : IsClosedIn S A)
    {x : Fin k → R} (hxS : x ∈ S) (hxcl : x ∈ closure A) : x ∈ A := by
  obtain ⟨F, hF, rfl⟩ := h
  exact ⟨hF.closure_eq ▸ closure_mono Set.inter_subset_left hxcl, hxS⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Squared euclidean distance between two constant points on the line. -/
theorem euclideanNormSq_constPt_sub (w c : R) :
    euclideanNormSq (constPt w - constPt c) = (w - c) ^ 2 := by
  have h : constPt w - constPt c = constPt (w - c) := by
    funext i; simp only [constPt, Pi.sub_apply]
  rw [h, euclideanNormSq, Fin.sum_univ_one]; simp only [constPt]

omit [Field R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The lower-closed ray `(-∞, β]` is constant on the gaps between the single breakpoint `β`. -/
theorem constOnGaps_Iic (β : R) : ConstOnGaps (Set.Iic β) := by
  refine ⟨{β}, fun x y hxy hgap => ?_⟩
  simp only [Finset.mem_singleton, forall_eq] at hgap
  simp only [Set.mem_Iic]
  rcases hgap with h | h
  · exact ⟨fun hx => absurd hx (not_le.mpr h), fun hy => absurd hy (not_le.mpr (h.trans hxy))⟩
  · exact ⟨fun _ => le_of_lt h, fun _ => le_of_lt (hxy.trans h)⟩

/-- The core supremum argument: a section that is order-connected cannot have its line-set `S` split
into `A ⊔ B` with witnesses `α ∈ A`, `β ∈ B`, `α < β`. -/
private theorem not_decomp_aux {S A B : Set (Fin 1 → R)}
    (hord : (constPt ⁻¹' S).OrdConnected)
    (hAsa : IsSemialgebraicSet A) (hAcl : IsClosedIn S A) (hBcl : IsClosedIn S B)
    (hAB : A ∩ B = ∅) (hABS : A ∪ B = S)
    {α β : R} (hαA : constPt α ∈ A) (hβB : constPt β ∈ B) (hlt : α < β) : False := by
  have hαS : α ∈ constPt ⁻¹' S := hABS ▸ Set.mem_union_left _ hαA
  have hβS : β ∈ constPt ⁻¹' S := hABS ▸ Set.mem_union_right _ hβB
  set Ta := constPt ⁻¹' A with hTa
  have hTaCOG : ConstOnGaps Ta := isSemialgebraicSet_sect_constOnGaps hAsa
  set W := Ta ∩ Set.Iic β with hW
  have hWCOG : ConstOnGaps W := hTaCOG.inter (constOnGaps_Iic β)
  have hαW : α ∈ W := ⟨hαA, le_of_lt hlt⟩
  have hWub : β ∈ upperBounds W := fun x hx => hx.2
  obtain ⟨c, hc⟩ := hWCOG.exists_isLUB ⟨α, hαW⟩ ⟨β, hWub⟩
  have hcα : α ≤ c := hc.1 hαW
  have hcβ : c ≤ β := hc.2 hWub
  have hcS : constPt c ∈ S := hord.out hαS hβS ⟨hcα, hcβ⟩
  have hcAB : constPt c ∈ A ∨ constPt c ∈ B := by rw [← Set.mem_union, hABS]; exact hcS
  rcases hcAB with hcA | hcB
  · -- `c ∈ A`: points of `B` lie just above `c`, so `constPt c ∈ closure B ⊆ B`, contradiction.
    have hcβ' : c < β := lt_of_le_of_ne hcβ
      (fun h => Set.eq_empty_iff_forall_notMem.mp hAB _ ⟨h ▸ hcA, hβB⟩)
    have hclos : constPt c ∈ closure B := by
      rw [mem_closure_iff_ball]
      intro r hr
      obtain ⟨x, hcx, hxlt⟩ := exists_between (lt_min hcβ' (show c < c + r by linarith))
      have hxβ : x < β := lt_of_lt_of_le hxlt (min_le_left _ _)
      have hxr : x < c + r := lt_of_lt_of_le hxlt (min_le_right _ _)
      have hxS : constPt x ∈ S :=
        hord.out hαS hβS ⟨le_of_lt (lt_of_le_of_lt hcα hcx), le_of_lt hxβ⟩
      have hxnotA : constPt x ∉ A := fun hxA =>
        absurd (hc.1 (⟨hxA, le_of_lt hxβ⟩ : x ∈ W)) (not_le.mpr hcx)
      have hxB : constPt x ∈ B := by
        rcases (show constPt x ∈ A ∨ constPt x ∈ B by rw [← Set.mem_union, hABS]; exact hxS)
          with h | h
        · exact absurd h hxnotA
        · exact h
      refine ⟨constPt x, hxB, ?_⟩
      rw [euclideanNormSq_constPt_sub]
      exact sq_lt_sq' (by linarith) (by linarith)
    exact Set.eq_empty_iff_forall_notMem.mp hAB _
      ⟨hcA, mem_of_mem_closure_of_isClosedIn hBcl hcS hclos⟩
  · -- `c ∈ B`: points of `A` lie just below `c`, so `constPt c ∈ closure A ⊆ A`, contradiction.
    have hclos : constPt c ∈ closure A := by
      rw [mem_closure_iff_ball]
      intro r hr
      have hnub : c - r ∉ upperBounds W := fun hub => by have := hc.2 hub; linarith
      rw [mem_upperBounds] at hnub
      push Not at hnub
      obtain ⟨w, hwW, hwc⟩ := hnub
      have hwleq : w ≤ c := hc.1 hwW
      refine ⟨constPt w, hwW.1, ?_⟩
      rw [euclideanNormSq_constPt_sub]
      exact sq_lt_sq' (by linarith) (by linarith)
    exact Set.eq_empty_iff_forall_notMem.mp hAB _
      ⟨mem_of_mem_closure_of_isClosedIn hAcl hcS hclos, hcB⟩

/-- **A line-set with order-connected section is semialgebraically connected.** -/
theorem isSemialgebraicallyConnected_of_ordConnected_sect {S : Set (Fin 1 → R)}
    (hord : (constPt ⁻¹' S).OrdConnected) : IsSemialgebraicallyConnected S := by
  rintro ⟨A, B, hA, hB, hAsa, hBsa, hAcl, hBcl, hAB, hABS⟩
  obtain ⟨pa, hpa⟩ := hA
  obtain ⟨pb, hpb⟩ := hB
  have hpaeq : constPt (pa 0) ∈ A := by
    rwa [show constPt (pa 0) = pa from funext fun i => by fin_cases i; rfl]
  have hpbeq : constPt (pb 0) ∈ B := by
    rwa [show constPt (pb 0) = pb from funext fun i => by fin_cases i; rfl]
  rcases lt_trichotomy (pa 0) (pb 0) with hlt | heq | hgt
  · exact not_decomp_aux hord hAsa hAcl hBcl hAB hABS hpaeq hpbeq hlt
  · exact Set.eq_empty_iff_forall_notMem.mp hAB _ ⟨hpaeq, heq ▸ hpbeq⟩
  · exact not_decomp_aux hord hBsa hBcl hAcl (by rw [Set.inter_comm]; exact hAB)
      (by rw [Set.union_comm]; exact hABS) hpbeq hpaeq hgt

/-- **Proposition 3.6 (the field `R`).** A real closed field is semialgebraically connected. -/
theorem isSemialgebraicallyConnected_univ :
    IsSemialgebraicallyConnected (Set.univ : Set (Fin 1 → R)) :=
  isSemialgebraicallyConnected_of_ordConnected_sect
    (by rw [Set.preimage_univ]; exact Set.ordConnected_univ)

/-- **Proposition 3.6 (intervals).** Any interval of `R` — a line-set `{v | v₀ ∈ I}` with `I`
order-connected — is semialgebraically connected. -/
theorem isSemialgebraicallyConnected_interval {I : Set R} (hI : I.OrdConnected) :
    IsSemialgebraicallyConnected {v : Fin 1 → R | v 0 ∈ I} := by
  refine isSemialgebraicallyConnected_of_ordConnected_sect ?_
  have hpre : constPt ⁻¹' {v : Fin 1 → R | v 0 ∈ I} = I := by
    ext t; simp only [Set.mem_preimage, Set.mem_ofPred_eq, constPt]
  rw [hpre]; exact hI

end Azurite.BPR
