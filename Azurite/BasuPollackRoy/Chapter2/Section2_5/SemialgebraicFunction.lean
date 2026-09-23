/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicSets

/-! # BPR Section 2.5.2: Semialgebraic functions

Let `S ⊆ Rᵏ` and `T ⊆ Rˡ` be semialgebraic sets. A function `f : S → T` is
*semialgebraic* if its graph `Graph(f) ⊆ R^{k+ℓ}` is a semialgebraic set.

We model `f : S → T` by a total function `f : (Fin k → R) → (Fin ℓ → R)` together with the
domain `S` on which it is considered. Its graph over `S` is the set of points of `R^{k+ℓ}`
whose first `k` coordinates lie in `S` and whose last `ℓ` coordinates equal `f` applied to
the first `k`. The codomain `T` plays no role in the definition of semialgebraicity: if the
graph is semialgebraic then so is the domain `S` (it is a projection of the graph, BPR
Theorem 2.76).
-/

namespace Azurite.BPR

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The **graph** of `f` over `S`, as a subset of `R^{k+ℓ}`: the points `z` whose first `k`
coordinates `z ∘ castAdd` lie in `S` and whose last `ℓ` coordinates `z ∘ natAdd` equal
`f (z ∘ castAdd)`. -/
def funGraph (S : Set (Fin k → R)) (f : (Fin k → R) → (Fin ℓ → R)) :
    Set (Fin (k + ℓ) → R) :=
  { z | (z ∘ Fin.castAdd ℓ) ∈ S ∧ z ∘ Fin.natAdd k = f (z ∘ Fin.castAdd ℓ) }

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem mem_funGraph (S : Set (Fin k → R)) (f : (Fin k → R) → (Fin ℓ → R))
    (z : Fin (k + ℓ) → R) :
    z ∈ funGraph S f ↔
      (z ∘ Fin.castAdd ℓ) ∈ S ∧ z ∘ Fin.natAdd k = f (z ∘ Fin.castAdd ℓ) :=
  Iff.rfl

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The graph of `f` over `S` is the image of `S` under `x ↦ (x, f x)` (encoded by
`Fin.append`). -/
theorem funGraph_eq_image (S : Set (Fin k → R)) (f : (Fin k → R) → (Fin ℓ → R)) :
    funGraph S f = (fun x => Fin.append x (f x)) '' S := by
  ext z
  simp only [mem_funGraph, Set.mem_image]
  constructor
  · rintro ⟨hS, hf⟩
    refine ⟨z ∘ Fin.castAdd ℓ, hS, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right, ← hf]; rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have : (Fin.append x (f x)) ∘ Fin.castAdd ℓ = x := by
        funext i; rw [Function.comp_apply, Fin.append_left]
      rwa [this]
    · funext j
      have hl : (Fin.append x (f x)) ∘ Fin.castAdd ℓ = x := by
        funext i; rw [Function.comp_apply, Fin.append_left]
      rw [hl, Function.comp_apply, Fin.append_right]

/-- **BPR definition (semialgebraic function).** A function `f : S → T` with `S ⊆ Rᵏ` and
`T ⊆ Rˡ` semialgebraic is *semialgebraic* if its graph is a semialgebraic subset of
`R^{k+ℓ}`. -/
def IsSemialgebraicFunction (S : Set (Fin k → R)) (f : (Fin k → R) → (Fin ℓ → R)) : Prop :=
  IsSemialgebraicSet (funGraph S f)

end Azurite.BPR
