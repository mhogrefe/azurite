/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.MonomialOrder
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Minimal

/-!
# BPR Lemma 4.62: Dickson's lemma

Every subset `B` of `M_k ≅ ℕ^k` closed under multiplication (upward closed under the
divisibility order) has a finite number of minimal elements for the divisibility order.

BPR proves this by induction on `k`. Here we deduce it from Mathlib's well-quasi-ordering of
`ℕ^k` (`Fin k →₀ ℕ`, `Set.univ.IsPWO`), which encapsulates the same induction: the minimal
elements form an antichain, and a partially-well-ordered set has only finite antichains
(`IsAntichain.finite_of_partiallyWellOrderedOn`). The upward-closure hypothesis (BPR's
"closed under multiplication") is recorded to match the statement, though finiteness of the
minimal elements in fact holds for an arbitrary subset.
-/

namespace Azurite.BPR.Chapter4

variable {k : ℕ}

/-- **BPR Lemma 4.62 (Dickson's lemma).** Every subset `B ⊆ M_k ≅ ℕ^k` closed under
multiplication (upward closed under divisibility) has a finite set of minimal elements with
respect to the divisibility (componentwise) order. -/
theorem lemma_4_62 (B : Set (Fin k →₀ ℕ)) (_hB : ∀ a ∈ B, ∀ b, a ≤ b → b ∈ B) :
    {a | Minimal (· ∈ B) a}.Finite := by
  -- The minimal elements form an antichain: two distinct minimal elements are incomparable.
  have hanti : IsAntichain (· ≤ ·) {a | Minimal (· ∈ B) a} := by
    intro a ha b hb hne hle
    simp only [Set.mem_ofPred_eq] at ha hb
    exact hne (le_antisymm hle (hb.2 ha.1 hle))
  -- `ℕ^k` is partially well-ordered (Dickson / well-quasi-order), hence so is any subset.
  have hpwo : {a | Minimal (· ∈ B) a}.IsPWO :=
    (Set.isPWO_of_wellQuasiOrderedLE Set.univ).mono (Set.subset_univ _)
  -- A finite antichain in a partially-well-ordered set.
  exact hanti.finite_of_partiallyWellOrderedOn hpwo

end Azurite.BPR.Chapter4
