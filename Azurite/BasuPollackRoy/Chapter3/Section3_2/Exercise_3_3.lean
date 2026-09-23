/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_2.SemialgebraicallyConnected
import Azurite.BasuPollackRoy.Chapter3.Section3_1.SemialgebraicHomeomorphism
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR §3.2, Exercise 3.3 — semialgebraic connectedness is a homeomorphism invariant

If `A` is semialgebraically connected and `B` is semialgebraically homeomorphic to `A`, then `B` is
semialgebraically connected. A disjoint decomposition of `B` into two non-empty semialgebraic sets
closed in `B` pulls back along the (continuous, semialgebraic) homeomorphism to such a decomposition
of `A`, contradicting the connectedness of `A`. -/

namespace Azurite.BPR

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Exercise 3.3.** If `A` is semialgebraically connected and `B` is semialgebraically
homeomorphic to `A` (via `f : A → B` with inverse `g`), then `B` is semialgebraically connected. -/
theorem exercise_3_3 {A : Set (Fin k → R)} {B : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    (hAconn : IsSemialgebraicallyConnected A)
    (hsah : IsSemialgebraicHomeomorphism A B f g) :
    IsSemialgebraicallyConnected B := by
  intro hBdecomp
  obtain ⟨U, V, hU, hV, hUsa, hVsa, hUcl, hVcl, hUV, hUVB⟩ := hBdecomp
  have hf := hsah.isSemialgebraicFunction
  have hcont := hsah.continuousOn
  have hmaps := hsah.bijOn.mapsTo
  have hsurj := hsah.bijOn.surjOn
  have hUB : U ⊆ B := hUVB ▸ Set.subset_union_left
  have hVB : V ⊆ B := hUVB ▸ Set.subset_union_right
  apply hAconn
  refine ⟨A ∩ f ⁻¹' U, A ∩ f ⁻¹' V, ?_, ?_,
    (proposition_2_83 hf).2 hUsa, (proposition_2_83 hf).2 hVsa,
    isClosedIn_preimage hcont hmaps hUcl, isClosedIn_preimage hcont hmaps hVcl, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hU
    obtain ⟨a, haA, hfa⟩ := hsurj (hUB hu)
    exact ⟨a, haA, by rw [Set.mem_preimage, hfa]; exact hu⟩
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨a, haA, hfa⟩ := hsurj (hVB hv)
    exact ⟨a, haA, by rw [Set.mem_preimage, hfa]; exact hv⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨⟨_, haU⟩, _, haV⟩
    rw [Set.mem_preimage] at haU haV
    exact absurd (hUV ▸ Set.mem_inter haU haV) (Set.notMem_empty _)
  · ext a
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro (⟨haA, _⟩ | ⟨haA, _⟩) <;> exact haA
    · intro haA
      rcases (hUVB ▸ hmaps haA : f a ∈ U ∪ V) with h | h
      · exact Or.inl ⟨haA, h⟩
      · exact Or.inr ⟨haA, h⟩

end Azurite.BPR
