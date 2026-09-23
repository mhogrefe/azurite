/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.Idempotents

/-!
# BPR §4.5: the idempotent associated to `x` and its corner ring

The element `e_x` of Proposition 4.92 is called the *idempotent associated to* `x` (it satisfies
`e_x^2 = e_x`, i.e. `IsIdempotentElem e_x`). Since `e_x^2 = e_x`, the set `e_x Ā`, equipped with the
restriction of the addition and multiplication of `Ā`, is a commutative ring with identity `e_x`.

This is Mathlib's `IsIdempotentElem.Corner`: for an idempotent `e` of a commutative ring `R`, the
corner `e R` (the elements `r` with `e * r = r`, `mem_corner_iff_mul_eq`) carries a `CommRing`
structure whose identity is `e` (`corner_one_val`).
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [CommRing R] {e : R}

/-- For a commutative ring, the corner `e R` consists of the elements `r` with `e * r = r`. -/
theorem mem_corner_iff_mul_eq (he : IsIdempotentElem e) {r : R} :
    r ∈ Subsemigroup.corner e ↔ e * r = r := by
  rw [Subsemigroup.mem_corner_iff he]
  exact ⟨And.left, fun h => ⟨h, by rw [mul_comm]; exact h⟩⟩

/-- **The corner `e R` is a commutative ring** (with the operations of `R`). -/
example (he : IsIdempotentElem e) : CommRing he.Corner := inferInstance

/-- **The identity of the corner ring `e R` is `e`.** -/
theorem corner_one_val (he : IsIdempotentElem e) : (1 : he.Corner).1 = e := rfl

end Azurite.BPR.Chapter4
