/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87

/-!
# BPR §4.6: the ring `A_rad`

We write `A_rad` for the quotient `K[X₁, …, X_k] / √(Ideal(𝒫, K))` of the polynomial ring by the
radical of `Ideal(𝒫, K)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- `A_rad = K[X₁, …, X_k] / √(Ideal(𝒫, K))`. -/
abbrev quotPolysRad (Ps : Finset (MvPolynomial (Fin k) K)) : Type _ :=
  MvPolynomial (Fin k) K ⧸ (idealOfPolys Ps).radical

end Azurite.BPR.Chapter4
