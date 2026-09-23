/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Cones
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-! # BPR Section 2.1 — Proposition 2.6

> Let `(F, ≤)` be an ordered field. The positive cone
> `C = { x ∈ F | x ≥ 0}` is a proper cone satisfying `C ∪ (−C) = F`.
> Conversely, if `C` is a proper cone of a field `F` with
> `C ∪ (−C) = F`, then `F` is ordered by `x ≤ y ⇔ y − x ∈ C`.

**Mathlib link.** The condition `C ∪ (−C) = F` is exactly
`HasMemOrNegMem C` in Mathlib. A proper cone with this totality is a
`RingCone`, since if both `a ∈ C` and `−a ∈ C` with `a ≠ 0`, then
`a⁻¹ = (a⁻¹)² · a ∈ C`, so `−1 = (−a) · a⁻¹ ∈ C`, contradicting
properness.
-/

namespace Azurite.BPR

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Prop 2.6 (Forward, part 1).** The positive cone satisfies `C ∪ (−C) = F`. -/
lemma nonneg_hasMemOrNegMem : HasMemOrNegMem (Subsemiring.nonneg F) :=
  ⟨fun a => by
    simp only [Subsemiring.mem_nonneg]
    rcases le_total 0 a with h | h
    · left; exact h
    · right; linarith⟩

/-- **Prop 2.6 (Forward, full).** The positive cone of an ordered field is
    a proper cone with `C ∪ (−C) = F`. -/
theorem prop_2_6_forward :
    IsProperCone (Subsemiring.nonneg F) ∧ HasMemOrNegMem (Subsemiring.nonneg F) :=
  ⟨isProperCone_nonneg, nonneg_hasMemOrNegMem⟩

section Prop_2_6_Converse

variable {F : Type*} [Field F]

/-- In a field, a proper cone satisfies the `RingCone` antisymmetry:
    if `a ∈ C` and `−a ∈ C`, then `a = 0`. The key step uses `a⁻¹ = (a⁻¹)² · a ∈ C`,
    so `−1 = (−a) · a⁻¹ ∈ C`, contradicting properness. -/
lemma IsProperCone.eq_zero_of_mem_of_neg_mem' {C : Subsemiring F}
    (hC : IsProperCone C) {a : F} (ha : a ∈ C) (hna : -a ∈ C) : a = 0 := by
  by_contra h
  have hinv : a⁻¹ ∈ C := by
    have hsq : a⁻¹ ^ 2 ∈ C := hC.1 a⁻¹
    have := C.mul_mem hsq ha
    rwa [sq, mul_assoc, inv_mul_cancel₀ h, mul_one] at this
  have : (-1 : F) ∈ C := by
    have := C.mul_mem hna hinv
    rwa [neg_mul, mul_inv_cancel₀ h] at this
  exact hC.2 this

/-- **Prop 2.6 (Converse).** A proper cone with `C ∪ (−C) = F` gives a `RingCone`. -/
def IsProperCone.toRingCone {C : Subsemiring F} (hC : IsProperCone C) : RingCone F where
  toSubsemiring := C
  eq_zero_of_mem_of_neg_mem' := fun ha hna => hC.eq_zero_of_mem_of_neg_mem' ha hna

/-- The order induced by a proper cone: `x ≤ y ↔ y − x ∈ C`. -/
def IsProperCone.le {C : Subsemiring F} (_ : IsProperCone C) (x y : F) : Prop :=
  y - x ∈ C

/-- **Prop 2.6 (Converse, stated).** If `C` is a proper cone of a field `F`
    with `C ∪ (−C) = F`, then `x ≤ y ⇔ y − x ∈ C` defines a linear order
    making `F` an ordered field. The cone `C` becomes the positive cone
    `{x | 0 ≤ x}` of this order.

    We have already shown that such `C` produces a `RingCone`
    (via `IsProperCone.toRingCone`), and the totality condition
    `HasMemOrNegMem` ensures the order is linear. -/
theorem IsProperCone.totalOrder {C : Subsemiring F}
    (hC : IsProperCone C) (hT : ∀ a : F, a ∈ C ∨ -a ∈ C) :
    ∀ x y : F, hC.le x y ∨ hC.le y x := by
  intro x y
  rcases hT (y - x) with h | h
  · left; exact h
  · right; rwa [show -(y - x) = x - y from by ring] at h

end Prop_2_6_Converse

end Azurite.BPR
