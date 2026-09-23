/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomial.Basic

open Azurite

namespace Azurite.AzPolynomialQ

/-- Negating an array of numbers pointwise preserves that if you map it with neg,
    the listIntGcd stays the same because `(-x).natAbs = x.natAbs`. -/
lemma listIntGcd_map_neg (l : List ℤ) :
    listIntGcd (l.map (fun x => -x)) = listIntGcd l := by
  dsimp [listIntGcd]
  suffices h : ∀ acc : ℕ,
      (l.map (fun x => -x)).foldl (fun acc n => Nat.gcd acc n.natAbs) acc =
      l.foldl (fun acc n => Nat.gcd acc n.natAbs) acc by
    exact h 0
  intro acc
  induction l generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp [ih]

/-- Negates an `AzPolynomialQ` by negating all integer numerators,
    leaving the denominator unchanged. This preserves the canonical invariants. -/
instance instNegAzPolynomialQ : Neg AzPolynomialQ where
  neg p :=
    let arr := p.numerators.map (fun x => -x)
    ⟨arr, p.denom, p.denom_pos,
      -- last_ne_zero
      by
        have hw : arr.back? = p.numerators.back?.map (fun x => -x) := by
          exact AzPolynomial.Array_back?_map p.numerators (fun x => -x)
        rw [hw]
        intro h
        rcases hp : p.numerators.back? with _ | c
        · revert h
          simp [hp]
        · rw [hp] at h
          injection h with h_eq
          have h2 : c = 0 := neg_eq_zero.mp h_eq
          exact p.last_ne_zero (by rw [hp, h2]),
      -- coprime
      by
        have ht : arr.toList = p.numerators.toList.map (fun x => -x) := by
          dsimp [arr]; rw [Array.toList_map]
        rw [ht, listIntGcd_map_neg]
        exact p.coprime
    ⟩

@[simp] lemma coeff_neg (p : AzPolynomialQ) (i : ℕ) :
    (-p).coeff i = - p.coeff i := by
  dsimp [coeff, Neg.neg, instNegAzPolynomialQ]
  rcases hp : p.numerators[i]? with _ | c
  · have hw : (p.numerators.map (fun x => -x))[i]? = none := by
      rw [Array.getElem?_map, hp]; rfl
    change ((((p.numerators.map (fun x => -x))[i]?).getD 0 : ℤ) : ℚ) / p.denom = _
    rw [hw]
    simp
    exact neg_zero.symm
  · have hw : (p.numerators.map (fun x => -x))[i]? = some (-c) := by
      rw [Array.getElem?_map, hp]; rfl
    change ((((p.numerators.map (fun x => -x))[i]?).getD 0 : ℤ) : ℚ) / p.denom = _
    rw [hw]
    simp
    exact neg_div _ _

end Azurite.AzPolynomialQ
