/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.FieldTheory.IntermediateField.Basic

/-! # BPR Section 2.1 — Archimedean ordered fields

> An ordered field `F` is *archimedean* if, whenever `a, b` are positive
> elements of `F`, there exists a natural number `n ∈ ℕ` so that `n · a > b`.

**Mathlib correspondence.** This is `Archimedean` from
`Mathlib.Algebra.Order.Archimedean.Defs`, defined as
`∀ (x : R) {y : R}, 0 < y → ∃ n : ℕ, x ≤ n • y`.

`ℝ` is archimedean via `Real.instArchimedean`.

This file additionally records that any intermediate field of an archimedean
ordered field is archimedean, via `Archimedean.comap` along the subtype
inclusion. (Used by Exercise 2.11 to upgrade `ℝ_alg` from a Mathlib
intermediate field of `ℝ` to an archimedean ordered field.)
-/

namespace Azurite.BPR

/-- Any intermediate field of an archimedean ordered field is archimedean,
    via `Archimedean.comap` along the subtype inclusion. -/
theorem IntermediateField.archimedean {F E : Type*} [Field F] [Field E]
    [Algebra F E] [LinearOrder E] [IsStrictOrderedRing E] [Archimedean E]
    (S : IntermediateField F E) : Archimedean ↥S :=
  Archimedean.comap S.subtype.toAddMonoidHom (fun _ _ h => h)

end Azurite.BPR
