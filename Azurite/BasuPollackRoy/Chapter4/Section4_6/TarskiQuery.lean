/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.FiniteMapping
import Mathlib.Basic.Sign.Basic

/-!
# BPR §4.6: the Tarski-query

For a real closed field `R` (an ordered extension of `K`), the **Tarski-query** of `Q` for `𝒫` is
\[
  \mathrm{TaQ}(Q, \mathcal{P}) = \sum_{x \in \mathrm{Zer}(\mathcal{P}, R^k)} \mathrm{sign}(Q(x)) \in \mathbb{Z},
\]
the sum of the signs of `Q` over the real solutions of `𝒫`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]
  (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra K R]

/-- **The Tarski-query** of `Q` for `𝒫` (over the ordered field `R`):
`TaQ(Q, 𝒫) = ∑_{x ∈ Zer(𝒫, Rᵏ)} sign(Q(x))`, the sum over the real zeros of `𝒫` of the sign of
`Q` evaluated there. -/
noncomputable def tarskiQuery (Q : MvPolynomial (Fin k) K)
    (Ps : Finset (MvPolynomial (Fin k) K)) (hfin : (zerOfFinset R Ps).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, (SignType.sign (MvPolynomial.aeval x Q) : ℤ)

end Azurite.BPR.Chapter4
