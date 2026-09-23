/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.LinearCombination

/-!
# BPR §4.5: the ring of fractions `S⁻¹A`

Given a multiplicative subset `S` of a ring `A` (a subset closed under multiplication; in Mathlib
a `Submonoid A`, which moreover contains `1`), the *ring of fractions* `S⁻¹A` is Mathlib's
`Localization S`. Its elements are classes `a/s = Localization.mk a s` of pairs `(a, s)` with
`a ∈ A`, `s ∈ S`, under the relation `(a, s) ∼ (a', s')` iff there is `t ∈ S` with
`t (a s' − a' s) = 0` (`localization_mk_eq_iff`), and it carries the ring operations

* `a/s + a'/s' = (a s' + a' s)/(s s')` (`localization_add`),
* `(a/s)(a'/s') = (a a')/(s s')` (`localization_mul`).
-/

namespace Azurite.BPR.Chapter4

variable {A : Type*} [CommRing A] {S : Submonoid A}

/-- **The defining equivalence relation.** `a/s = a'/s'` in `S⁻¹A` iff there is `t ∈ S` with
`t (a s' − a' s) = 0`. -/
theorem localization_mk_eq_iff (a a' : A) (s s' : S) :
    Localization.mk a s = Localization.mk a' s' ↔
      ∃ t : S, (t : A) * (a * (s' : A) - a' * (s : A)) = 0 := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    dsimp only at hc
    linear_combination hc
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    dsimp only
    linear_combination ht

/-- **Addition in `S⁻¹A`**: `a/s + a'/s' = (a s' + a' s)/(s s')`. -/
theorem localization_add (a a' : A) (s s' : S) :
    Localization.mk a s + Localization.mk a' s'
      = Localization.mk (a * (s' : A) + a' * (s : A)) (s * s') := by
  rw [Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by dsimp only; push_cast; ring⟩

/-- **Multiplication in `S⁻¹A`**: `(a/s)(a'/s') = (a a')/(s s')`. -/
theorem localization_mul (a a' : A) (s s' : S) :
    Localization.mk a s * Localization.mk a' s' = Localization.mk (a * a') (s * s') :=
  Localization.mk_mul a a' s s'

end Azurite.BPR.Chapter4
