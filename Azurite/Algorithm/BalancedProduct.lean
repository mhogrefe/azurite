/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
## Balanced products

`balancedProduct l` multiplies a list by pairing adjacent elements until one remains: a balanced
binary tree of products.  For big numbers (or polynomials) of similar size this keeps every
multiplication balanced, so the subquadratic multiplication algorithms apply at every level,
whereas a left fold multiplies a growing accumulator by small factors.  The tree is driven by a
fuel of `l.length` pairing rounds — more than the `⌈log₂ l.length⌉` needed — with a fold as the
fallback, so the result is the product for every fuel (`balancedProduct_eq_prod`, in any monoid).
-/

namespace Azurite

/-- Multiply adjacent pairs; an odd last element is kept. -/
def mulAdjacentPairs {α : Type*} [Mul α] : List α → List α
  | x :: y :: rest => (x * y) :: mulAdjacentPairs rest
  | l => l

/-- The product of a list by `fuel` rounds of pairing; a left fold finishes if the fuel runs
out. -/
def prodTree {α : Type*} [Mul α] [One α] : Nat → List α → α
  | 0, l => l.foldl (· * ·) 1
  | fuel + 1, l =>
    match l with
    | [] => 1
    | [x] => x
    | _ => prodTree fuel (mulAdjacentPairs l)

/-- **The product of a list by a balanced tree** of pairwise products. -/
def balancedProduct {α : Type*} [Mul α] [One α] (l : List α) : α := prodTree l.length l

variable {α : Type*} [Monoid α]

theorem mulAdjacentPairs_prod : ∀ l : List α, (mulAdjacentPairs l).prod = l.prod
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [mulAdjacentPairs, List.prod_cons, mulAdjacentPairs_prod rest, List.prod_cons, List.prod_cons, mul_assoc]

theorem foldl_mul_eq_mul_prod (l : List α) (acc : α) : l.foldl (· * ·) acc = acc * l.prod := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem prodTree_eq_prod : ∀ (fuel : ℕ) (l : List α), prodTree fuel l = l.prod
  | 0, l => by rw [prodTree, foldl_mul_eq_mul_prod, one_mul]
  | _ + 1, [] => by simp [prodTree]
  | _ + 1, [x] => by simp [prodTree]
  | fuel + 1, x :: y :: rest => by
    show prodTree fuel (mulAdjacentPairs (x :: y :: rest)) = _
    rw [prodTree_eq_prod fuel, mulAdjacentPairs_prod]

/-- **The balanced product is the product**, for every fuel and in any monoid. -/
theorem balancedProduct_eq_prod (l : List α) : balancedProduct l = l.prod :=
  prodTree_eq_prod _ _

end Azurite
