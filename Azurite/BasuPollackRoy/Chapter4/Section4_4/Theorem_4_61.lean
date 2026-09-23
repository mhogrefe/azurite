/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_70
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_69
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-!
# BPR Theorem 4.61: Hilbert's basis theorem

Any ideal `I ⊆ K[X₁, …, X_k]` is finitely generated: there is a finite set `𝒫` with
`I = Ideal(𝒫, K)`. This is immediate from the existence of a Gröbner basis
(Proposition 4.70) — fixing any monomial ordering on `Fin k` (we use the degree-lexicographic
order) — together with the fact that a Gröbner basis generates its ideal (Proposition 4.69).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **BPR Theorem 4.61 (Hilbert's basis theorem).** Any ideal `I ⊆ K[X₁, …, X_k]` is finitely
generated: there exists a finite set `𝒫` such that `I = Ideal(𝒫, K)`. -/
theorem theorem_4_61 (I : Ideal (MvPolynomial (Fin k) K)) :
    ∃ P : Finset (MvPolynomial (Fin k) K), I = idealOfPolys P := by
  obtain ⟨𝒢, hG⟩ := proposition_4_70 (MonomialOrder.degLex) I
  exact ⟨𝒢, (proposition_4_69 MonomialOrder.degLex hG).symm⟩

end Azurite.BPR.Chapter4
