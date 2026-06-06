import Azurite.BasuPollackRoy.Chapter3.Section3_2.SemialgebraicallyConnected
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR §3.2 — the image of a semialgebraically connected set is semialgebraically connected

If `S` is semialgebraically connected and `f` is a continuous semialgebraic function on `S`, then the
image `f(S)` is semialgebraically connected. A disjoint decomposition of `f(S)` into two non-empty
semialgebraic sets closed in `f(S)` pulls back along `f` to such a decomposition of `S` — exactly the
argument of Exercise 3.3, but now `f` need not be injective. -/

namespace Azurite.BPR

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **The continuous semialgebraic image of a semialgebraically connected set is semialgebraically
connected.** -/
theorem isSemialgebraicallyConnected_image {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    (hSconn : IsSemialgebraicallyConnected S) (hf : IsSemialgebraicFunction S f)
    (hcont : ContinuousOn f S) :
    IsSemialgebraicallyConnected (f '' S) := by
  intro hdecomp
  obtain ⟨U, V, hU, hV, hUsa, hVsa, hUcl, hVcl, hUV, hUVT⟩ := hdecomp
  have hmaps : Set.MapsTo f S (f '' S) := Set.mapsTo_image f S
  have hUT : U ⊆ f '' S := hUVT ▸ Set.subset_union_left
  have hVT : V ⊆ f '' S := hUVT ▸ Set.subset_union_right
  apply hSconn
  refine ⟨S ∩ f ⁻¹' U, S ∩ f ⁻¹' V, ?_, ?_,
    (proposition_2_83 hf).2 hUsa, (proposition_2_83 hf).2 hVsa,
    isClosedIn_preimage hcont hmaps hUcl, isClosedIn_preimage hcont hmaps hVcl, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hU
    obtain ⟨a, haS, hfa⟩ := hUT hu
    exact ⟨a, haS, by rw [Set.mem_preimage, hfa]; exact hu⟩
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨a, haS, hfa⟩ := hVT hv
    exact ⟨a, haS, by rw [Set.mem_preimage, hfa]; exact hv⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨⟨_, haU⟩, _, haV⟩
    rw [Set.mem_preimage] at haU haV
    exact absurd (hUV ▸ Set.mem_inter haU haV) (Set.notMem_empty _)
  · ext a
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro (⟨haS, _⟩ | ⟨haS, _⟩) <;> exact haS
    · intro haS
      rcases (hUVT ▸ hmaps haS : f a ∈ U ∪ V) with h | h
      · exact Or.inl ⟨haS, h⟩
      · exact Or.inr ⟨haS, h⟩

end Azurite.BPR
