/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR Proposition 2.84: composition of semialgebraic functions

If `f : A → B` and `g : B → C` are semialgebraic, so is `g ∘ f : A → C`. The graph of
`g ∘ f` is the projection to `R^{k+m}` of `(F × R^m) ∩ (R^k × G)` (where `F`, `G` are the
graphs of `f`, `g`), hence semialgebraic by the projection theorem (BPR Theorem 2.76).

We arrange the ambient space as `R^{(k+m)+ℓ}` — the `B`-coordinates (the middle block) last —
so that the projection dropping them is `IsSemialgebraicSet.exists_append_right`. The two
graphs are pulled into this layout by coordinate reindexings (`comap`).
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Proposition 2.84.** The composite of semialgebraic functions is semialgebraic.
The hypothesis `Set.MapsTo f A B` records that `f : A → B` (its values on `A` lie in `B`),
which is what makes the projection equal the graph of `g ∘ f`. -/
theorem proposition_2_84 {k ℓ m : ℕ}
    {A : Set (Fin k → R)} {B : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin m → R)}
    (hf : IsSemialgebraicFunction A f) (hg : IsSemialgebraicFunction B g)
    (hmaps : Set.MapsTo f A B) :
    IsSemialgebraicFunction A (g ∘ f) := by
  -- The two coordinate reindexings into the `(x, w, y)` layout of `R^{(k+m)+ℓ}`.
  set gF : Fin (k + ℓ) → Fin ((k + m) + ℓ) :=
    Fin.addCases (fun i : Fin k => Fin.castAdd ℓ (Fin.castAdd m i))
      (fun jy : Fin ℓ => Fin.natAdd (k + m) jy) with hgF
  set gG : Fin (ℓ + m) → Fin ((k + m) + ℓ) :=
    Fin.addCases (fun jy : Fin ℓ => Fin.natAdd (k + m) jy)
      (fun j : Fin m => Fin.castAdd ℓ (Fin.natAdd k j)) with hgG
  have hcF : ∀ (p : Fin (k + m) → R) (y : Fin ℓ → R),
      (Fin.append p y) ∘ gF = Fin.append (p ∘ Fin.castAdd m) y := by
    intro p y; rw [hgF]; funext i
    induction i using Fin.addCases with
    | left i => simp only [Function.comp_apply, Fin.addCases_left, Fin.append_left]
    | right jy => simp only [Function.comp_apply, Fin.addCases_right, Fin.append_right]
  have hcG : ∀ (p : Fin (k + m) → R) (y : Fin ℓ → R),
      (Fin.append p y) ∘ gG = Fin.append y (p ∘ Fin.natAdd k) := by
    intro p y; rw [hgG]; funext i
    induction i using Fin.addCases with
    | left jy =>
      simp only [Function.comp_apply, Fin.addCases_left, Fin.append_right, Fin.append_left]
    | right j =>
      simp only [Function.comp_apply, Fin.addCases_right, Fin.append_left, Fin.append_right]
  -- `F × R^m` and `R^k × G` in this layout, intersected.
  have hFpart : IsSemialgebraicSet
      {v : Fin ((k + m) + ℓ) → R | v ∘ gF ∈ funGraph A f} :=
    IsSemialgebraicSet.comap gF hf
  have hGpart : IsSemialgebraicSet
      {v : Fin ((k + m) + ℓ) → R | v ∘ gG ∈ funGraph B g} :=
    IsSemialgebraicSet.comap gG hg
  have hproj := (hFpart.inter hGpart).exists_append_right
  -- The graph of `g ∘ f` is this projection.
  have hthis : funGraph A (g ∘ f) =
      {p : Fin (k + m) → R | ∃ y : Fin ℓ → R, Fin.append p y ∈
        ({v | v ∘ gF ∈ funGraph A f} ∩ {v | v ∘ gG ∈ funGraph B g})} := by
    ext p
    simp only [mem_funGraph, Set.mem_ofPred_eq, Set.mem_inter_iff, hcF, hcG,
      append_comp_castAdd, append_comp_natAdd, Function.comp_apply]
    constructor
    · rintro ⟨hA, hw⟩
      exact ⟨f (p ∘ Fin.castAdd m), ⟨hA, rfl⟩, hmaps hA, hw⟩
    · rintro ⟨y, ⟨hA, hyf⟩, _hyB, hwg⟩
      exact ⟨hA, by rw [hwg, hyf]⟩
  show IsSemialgebraicSet (funGraph A (g ∘ f))
  rw [hthis]; exact hproj

end Azurite.BPR
