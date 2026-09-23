/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Derivative

/-! # BPR Section 2.1 — Notation 2.26: Derivative list

> For `P ∈ R[X]` of degree `p`, `Der(P)` denotes the list `[P, P', P'', …,
> P⁽ᵖ⁾]` of `P` and all its successive derivatives up to order `p`.

The list has `p + 1` entries. Used together with the sign-condition machinery
of Definition 2.25 (`Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_25`)
to formulate Thom's lemma and its consequences.
-/

namespace Azurite.BPR

open Polynomial

/-- **BPR Notation 2.26.** `Der(P)` is the list `[P, P', P'', …, P⁽ᵖ⁾]` where
    `p = natDegree P`. The list has `p + 1` entries. -/
noncomputable def der {R : Type*} [CommSemiring R] (P : R[X]) : List R[X] :=
  (List.range (P.natDegree + 1)).map (fun i => (⇑derivative)^[i] P)

end Azurite.BPR
