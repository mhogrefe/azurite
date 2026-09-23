/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # BPR §2.6 — valuation rings of a field

**Definition (unnumbered).** A *valuation ring* of a field `F` is a subring of `F` such that either
`x` or its inverse `x⁻¹` is in the ring for every nonzero `x`.

This is exactly Mathlib's `ValuationSubring F` (a `Subring` together with
`mem_or_inv_mem' : ∀ x, x ∈ carrier ∨ x⁻¹ ∈ carrier`). We record the predicate `IsValuationRing` on a
`Subring F` matching BPR's phrasing and the bridge to Mathlib's bundled `ValuationSubring`, so the
order valuation of the Puiseux series (and Mathlib's valuation-ring theory) can be used downstream. -/

namespace Azurite.BPR

variable {F : Type*} [Field F]

/-- **Valuation ring (BPR).** A *valuation ring* of a field `F` is a subring `S` of `F` such that for
every nonzero `x ∈ F`, either `x` or its inverse `x⁻¹` lies in `S`. -/
def IsValuationRing (S : Subring F) : Prop := ∀ x : F, x ≠ 0 → x ∈ S ∨ x⁻¹ ∈ S

/-- The "nonzero `x`" hypothesis is harmless: a subring is a valuation ring exactly when
`x ∈ S ∨ x⁻¹ ∈ S` holds for *all* `x` (the `x = 0` case is automatic, since `0 ∈ S`). This is exactly
Mathlib's `mem_or_inv_mem'`. -/
theorem isValuationRing_iff (S : Subring F) :
    IsValuationRing S ↔ ∀ x : F, x ∈ S ∨ x⁻¹ ∈ S := by
  refine ⟨fun h x => ?_, fun h x _ => h x⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl S.zero_mem
  · exact h x hx

/-- A BPR valuation ring of `F` is precisely a `ValuationSubring F` (Mathlib's bundled valuation
ring): the underlying subring with the `mem_or_inv_mem` property. -/
def IsValuationRing.toValuationSubring {S : Subring F} (h : IsValuationRing S) :
    ValuationSubring F :=
  ValuationSubring.ofSubring S ((isValuationRing_iff S).mp h)

@[simp] theorem IsValuationRing.mem_toValuationSubring {S : Subring F} (h : IsValuationRing S)
    (x : F) : x ∈ h.toValuationSubring ↔ x ∈ S := Iff.rfl

/-- Conversely, every `ValuationSubring F` is a BPR valuation ring of `F`. -/
theorem isValuationRing_valuationSubring (V : ValuationSubring F) :
    IsValuationRing V.toSubring :=
  fun x _ => V.mem_or_inv_mem x

end Azurite.BPR
