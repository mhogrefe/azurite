/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# BPR §8.2.1 Proposition 8.14: degree of a determinant of polynomial entries

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.

**Proposition 8.14.** Let `M` be an `n × n` matrix with entries that are
polynomials in `Y₁, …, Y_k` of degrees `≤ d`. Then `det(M)`, considered as a
polynomial in `Y₁, …, Y_k`, has degree bounded by `d · n`.

The proof is the Leibniz expansion
`det(M) = ∑_{σ ∈ Sₙ} sign(σ) · ∏ᵢ m_{σ(i),i}`: each product of `n` entries has
total degree `≤ ∑ᵢ d = d·n`, the signs are units (degree `0`), and the total
degree of a sum is bounded by the maximum of the summands' degrees.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [CommRing R] {n k : ℕ}

/-- **BPR Proposition 8.14.** The determinant of an `n × n` matrix whose entries
are polynomials in `Y₁, …, Y_k` of total degree `≤ d` has total degree `≤ d · n`. -/
theorem proposition_8_14 (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) R)) {d : ℕ}
    (hd : ∀ i j, (M i j).totalDegree ≤ d) :
    M.det.totalDegree ≤ d * n := by
  rw [Matrix.det_apply']
  refine MvPolynomial.totalDegree_finsetSum_le (fun σ _ => ?_)
  -- Each Leibniz term `sign(σ) · ∏ᵢ m_{σ(i),i}` has total degree `≤ d · n`.
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hsign : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin k) R).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;>
      simp [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_neg]
  rw [hsign, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : Fin n, d :=
        Finset.sum_le_sum (fun i _ => hd (σ i) i)
    _ = d * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

end Azurite.BPR
