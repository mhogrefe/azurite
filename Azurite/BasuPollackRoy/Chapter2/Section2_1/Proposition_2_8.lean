/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_9
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_6
import Mathlib.Order.Zorn

/-! # BPR Section 2.1 — Proposition 2.8

> Let `C` be a proper cone of `F`. Then `C` is contained in the
> positive cone of some order on `F`.

Equivalently, there exists a `RingCone` (= proper cone with antisymmetry)
containing `C` that also satisfies totality (`HasMemOrNegMem`).

The proof uses Zorn's lemma to obtain a maximal proper cone `C̄ ⊇ C`,
then Lemma 2.9 to show `C̄ ∪ (−C̄) = F`.
-/

namespace Azurite.BPR

variable {F : Type*} [Field F]

/-- The sSup of a chain of proper cones is a proper cone (when the chain is nonempty). -/
lemma chain_ub_isProperCone {c : Set (Subsemiring F)}
    (hc : IsChain (· ≤ ·) c) (hpc : ∀ T ∈ c, IsProperCone T)
    {T₀ : Subsemiring F} (hT₀ : T₀ ∈ c) :
    IsProperCone (sSup c) := by
  constructor
  · -- IsCone: x² ∈ sSup c because x² ∈ T₀ ≤ sSup c
    intro x
    exact le_sSup hT₀ ((hpc T₀ hT₀).1 x)
  · -- -1 ∉ sSup c: if -1 ∈ sSup c then -1 ∈ some T ∈ c
    intro hmem
    rw [Subsemiring.mem_sSup_of_directedOn ⟨T₀, hT₀⟩ hc.directedOn] at hmem
    obtain ⟨T, hT, hmT⟩ := hmem
    exact (hpc T hT).2 hmT

/-- `C[a]` contains `C`. -/
lemma le_coneExt (C : Subsemiring F) (hCone : IsCone C) (a : F) :
    C ≤ coneExt C hCone a :=
  fun x hx => ⟨x, hx, 0, C.zero_mem, by ring⟩

/-- **BPR Proposition 2.8.** Every proper cone is contained in a `RingCone`
    with totality (i.e., the positive cone of some order). -/
theorem prop_2_8 {C : Subsemiring F} (hC : IsProperCone C) :
    ∃ T : RingCone F, (C : Set F) ⊆ T ∧ HasMemOrNegMem T := by
  -- Apply Zorn's lemma to the set of proper cones containing C, ordered by ≤
  let S := {T : Subsemiring F | IsProperCone T ∧ C ≤ T}
  have hCS : C ∈ S := ⟨hC, le_refl C⟩
  -- Chain condition: every nonempty chain in S has an upper bound in S
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | ⟨T₀, hT₀⟩
    · exact ⟨C, hCS, fun z hz => hz.elim⟩
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun T hT => le_sSup hT⟩
      · exact chain_ub_isProperCone hc (fun T hT => (hcS hT).1) hT₀
      · exact le_trans (hcS hT₀).2 (le_sSup hT₀)
  -- Obtain a maximal element M ∈ S
  obtain ⟨M, hMS, hMax⟩ := zorn_le₀ S hchain
  -- M contains C
  have hCM : C ≤ M := hMS.2
  -- Show M gives a RingCone with totality
  refine ⟨hMS.1.toRingCone, fun x hx => hCM hx, ⟨fun a => ?_⟩⟩
  -- Need: a ∈ M ∨ -a ∈ M
  by_contra hboth
  push Not at hboth
  obtain ⟨ha, hna⟩ := hboth
  -- By Lemma 2.9, M[a] is a proper cone extending M
  have hMa : IsProperCone (coneExt M hMS.1.1 a) :=
    lemma_2_9 hMS.1 hna
  -- M[a] contains M and a ∈ M[a]
  have hMle : M ≤ coneExt M hMS.1.1 a := le_coneExt M hMS.1.1 a
  have hMaS : coneExt M hMS.1.1 a ∈ S :=
    ⟨hMa, le_trans hCM hMle⟩
  -- By maximality of M, M = M[a], so a ∈ M — contradiction
  have heq : coneExt M hMS.1.1 a ≤ M := hMax hMaS hMle
  -- a = a + M.0 * 0 ∈ coneExt M ... a
  have ha' : a ∈ coneExt M hMS.1.1 a :=
    ⟨0, M.zero_mem, 1, M.one_mem, by ring⟩
  exact ha (heq ha')

end Azurite.BPR
