/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixMul

/-!
# BPR §8.1: Bitsize of a product of several matrices

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact accompanying Algorithm 8.14: for `m` matrices
`M_1, …, M_m : Matrix n n ℤ` whose entry bitsizes are bounded by `τ`,
the entries of the product `M_1 ⋯ M_m` have bitsize bounded by
`m * (τ + bit(n))`.

The proof is induction on the list of matrices, applying the binary
matrix-product bitsize bound (`Matrix.bitsize_mul_le`) at each step.
The base case is at length 1 (a single matrix); length 0 (the empty
product, which is the identity) is excluded since identity entries of
value 1 violate the bound when `n ≥ 1`.
-/

namespace Azurite.BPR

/-- **BPR §8.1 (unnumbered lemma).** The product of `m ≥ 1` matrices
    over `ℤ` of size `n × n`, each with entry bitsizes bounded by `τ`,
    has every entry bounded in bitsize by `m * (τ + Nat.size n)`, where
    `n := Fintype.card ν` is the matrix dimension. -/
theorem Matrix.bitsize_list_prod_le {ν : Type _} [Fintype ν] [DecidableEq ν]
    {Ms : List (Matrix ν ν ℤ)} {τ : ℕ}
    (h_ne : Ms ≠ [])
    (hMs : ∀ M ∈ Ms, ∀ i j, (M i j).natAbs.size ≤ τ) :
    ∀ i j, ((Ms.prod) i j).natAbs.size ≤
      Ms.length * (τ + Nat.size (Fintype.card ν)) := by
  induction Ms with
  | nil => exact absurd rfl h_ne
  | cons M rest ih =>
    intro i j
    by_cases h_rest : rest = []
    · -- Ms = [M]: product is M itself (after the trailing identity).
      subst h_rest
      have h_prod : ([M] : List (Matrix ν ν ℤ)).prod = M := by simp
      rw [h_prod]
      have hM := hMs M List.mem_cons_self i j
      show (M i j).natAbs.size ≤ 1 * (τ + Nat.size (Fintype.card ν))
      rw [Nat.one_mul]
      exact le_trans hM (Nat.le_add_right _ _)
    · -- Ms = M :: rest with rest ≠ []: peel off M, apply IH on rest.
      have hM_rest : ∀ M' ∈ rest, ∀ i j, (M' i j).natAbs.size ≤ τ :=
        fun M' hM' i j => hMs M' (List.mem_cons_of_mem _ hM') i j
      have ih_rest := ih h_rest hM_rest
      have hM_bound : ∀ i j, (M i j).natAbs.size ≤ τ :=
        fun i j => hMs M List.mem_cons_self i j
      -- ((M :: rest).prod) i j = (M * rest.prod) i j; apply binary bound.
      have h_prod_eq : (M :: rest : List (Matrix ν ν ℤ)).prod = M * rest.prod :=
        List.prod_cons
      rw [h_prod_eq]
      have h_mul_bound := Matrix.bitsize_mul_le
        (M := M) (N := rest.prod) (τ := τ)
        (σ := rest.length * (τ + Nat.size (Fintype.card ν)))
        hM_bound ih_rest i j
      -- h_mul_bound: ((M * rest.prod) i j).natAbs.size ≤ τ + rest.length *
      --   (τ + Nat.size (Fintype.card ν)) + Nat.size (Fintype.card ν).
      -- Want: ≤ (rest.length + 1) * (τ + Nat.size (Fintype.card ν)).
      refine le_trans h_mul_bound ?_
      show τ + rest.length * (τ + Nat.size (Fintype.card ν)) +
            Nat.size (Fintype.card ν) ≤
          (M :: rest).length * (τ + Nat.size (Fintype.card ν))
      show _ ≤ (rest.length + 1) * (τ + Nat.size (Fintype.card ν))
      have : (rest.length + 1) * (τ + Nat.size (Fintype.card ν)) =
          rest.length * (τ + Nat.size (Fintype.card ν)) +
            (τ + Nat.size (Fintype.card ν)) := by ring
      omega

end Azurite.BPR
