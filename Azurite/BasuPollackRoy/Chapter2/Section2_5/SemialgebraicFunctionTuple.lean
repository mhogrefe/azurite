/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83
import Azurite.BasuPollackRoy.Chapter2.Section2_5.PNormIsSemialgebraic

/-! # A vector of semialgebraic coordinate functions is semialgebraic

The pairing lemma `pair_isSemialgebraicFunction` assembles two scalar semialgebraic functions into a
`Fin 2`-valued one. Here we give the general `n`-ary version: a function `f : Rᵏ → Rˡ` is
semialgebraic whenever each of its coordinate functions `x ↦ f x j` is semialgebraic. The graph of
`f` is the intersection over `j` of reindexed copies of the `j`-th coordinate graph, each
semialgebraic by `IsSemialgebraicSet.comap`. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Reindexing `Fin (k + 1) → Fin (k + ℓ)` that maps the domain block `Fin k` identically and the
single extra coordinate to the `j`-th codomain coordinate. -/
def coordReindex (k ℓ : ℕ) (j : Fin ℓ) : Fin (k + 1) → Fin (k + ℓ) :=
  Fin.addCases (fun i : Fin k => Fin.castAdd ℓ i) (fun _ : Fin 1 => Fin.natAdd k j)

omit [IsRealClosed R] in
/-- **A vector of semialgebraic coordinate functions is semialgebraic.** If `A` is nonempty in
codomain dimension (`Fin ℓ` nonempty) and each coordinate `x ↦ f x j` is semialgebraic on `A`, then
`f : A → Rˡ` is a semialgebraic function. -/
theorem isSemialgebraicFunction_of_coords {k ℓ : ℕ} [Nonempty (Fin ℓ)] {A : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin ℓ → R)}
    (h : ∀ j : Fin ℓ, IsSemialgebraicFunction A (fun x : Fin k → R => fun _ : Fin 1 => f x j)) :
    IsSemialgebraicFunction A f := by
  show IsSemialgebraicSet (funGraph A f)
  have memcoord : ∀ (j : Fin ℓ) (z : Fin (k + ℓ) → R),
      (z ∘ coordReindex k ℓ j ∈ funGraph A (fun x : Fin k → R => fun _ : Fin 1 => f x j)) ↔
        (z ∘ Fin.castAdd ℓ ∈ A ∧ z (Fin.natAdd k j) = f (z ∘ Fin.castAdd ℓ) j) := by
    intro j z
    have hcast : (z ∘ coordReindex k ℓ j) ∘ Fin.castAdd 1 = z ∘ Fin.castAdd ℓ := by
      funext i; show z (coordReindex k ℓ j (Fin.castAdd 1 i)) = z (Fin.castAdd ℓ i)
      simp only [coordReindex, Fin.addCases_left]
    have hnat : (z ∘ coordReindex k ℓ j) ∘ Fin.natAdd k = fun _ : Fin 1 => z (Fin.natAdd k j) := by
      funext a; show z (coordReindex k ℓ j (Fin.natAdd k a)) = z (Fin.natAdd k j)
      rw [Subsingleton.elim a 0]; simp only [coordReindex, Fin.addCases_right]
    rw [mem_funGraph, hcast, hnat]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro hh; exact congrFun hh 0
    · intro hh; funext _; exact hh
  have hgraph : funGraph A f = ⋂ j ∈ (Finset.univ : Finset (Fin ℓ)),
      {z : Fin (k + ℓ) → R |
        z ∘ coordReindex k ℓ j ∈ funGraph A (fun x : Fin k → R => fun _ : Fin 1 => f x j)} := by
    ext z
    rw [mem_funGraph]
    constructor
    · rintro ⟨hA, hf⟩
      rw [Set.mem_iInter₂]
      intro j _
      rw [Set.mem_ofPred_eq, memcoord]
      exact ⟨hA, congrFun hf j⟩
    · intro H
      rw [Set.mem_iInter₂] at H
      obtain ⟨j₀⟩ := ‹Nonempty (Fin ℓ)›
      refine ⟨((memcoord j₀ z).mp (H j₀ (Finset.mem_univ j₀))).1, ?_⟩
      funext j
      exact ((memcoord j z).mp (H j (Finset.mem_univ j))).2
  rw [hgraph]
  exact IsSemialgebraicSet.iInter_finset _ fun j _ => IsSemialgebraicSet.comap (coordReindex k ℓ j)
    (h j)

end Azurite.BPR
