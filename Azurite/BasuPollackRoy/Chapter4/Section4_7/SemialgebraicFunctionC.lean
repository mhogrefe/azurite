import Azurite.BasuPollackRoy.Chapter4.Section4_7.SemialgebraicC

/-!
# BPR §4.7: semialgebraic maps over `C`

A map `f : Cᵏ → Cˡ` is **semialgebraic over `C`** (on a domain `S`) when its graph
`{(x, f x) | x ∈ S} ⊆ C^{k+ℓ}` is a semialgebraic subset of `C^{k+ℓ}`. This is the exact complex
analogue of the real definition `IsSemialgebraicFunction S f := IsSemialgebraicSet (funGraph S f)`,
and reduces questions about complex maps (including rational ones, via cleared denominators) to
complex polynomial loci.
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k ℓ : ℕ}

/-- The graph of a complex map `f : Cᵏ → Cˡ` over a domain `S`, as a subset of `C^{k+ℓ}`: the first
`k` coordinates run over `S` and the last `ℓ` are `f` of them. -/
def complexFunGraph (S : Set (Fin k → Ri R)) (f : (Fin k → Ri R) → (Fin ℓ → Ri R)) :
    Set (Fin (k + ℓ) → Ri R) :=
  {p | (p ∘ Fin.castAdd ℓ) ∈ S ∧ p ∘ Fin.natAdd k = f (p ∘ Fin.castAdd ℓ)}

set_option linter.unusedSectionVars false in
theorem mem_complexFunGraph {S : Set (Fin k → Ri R)} {f : (Fin k → Ri R) → (Fin ℓ → Ri R)}
    (p : Fin (k + ℓ) → Ri R) :
    p ∈ complexFunGraph S f ↔
      (p ∘ Fin.castAdd ℓ) ∈ S ∧ p ∘ Fin.natAdd k = f (p ∘ Fin.castAdd ℓ) :=
  Iff.rfl

/-- **Semialgebraic map over `C`.** `f : Cᵏ → Cˡ` is semialgebraic on `S ⊆ Cᵏ` when its graph is a
semialgebraic subset of `C^{k+ℓ}`. -/
def IsSemialgebraicFunctionC (S : Set (Fin k → Ri R)) (f : (Fin k → Ri R) → (Fin ℓ → Ri R)) :
    Prop :=
  IsSemialgebraicSetC (complexFunGraph S f)

end Azurite.BPR.Chapter4
