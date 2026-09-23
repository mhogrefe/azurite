/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.Polynomial.Basic

/-!
# BPR §8.3.2.1: Polynomial Determinants — the matrix `Mat(𝒫)`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.3.2.1.

Let `K` be a field of characteristic `0` (only `[Semiring K]` is needed for the
definitions here). Consider the `K`-vector space `𝓕_n` of polynomials of degree
`< n` (Mathlib's `Polynomial.degreeLT K n`), equipped with the basis

`𝓑 = Xⁿ⁻¹, …, X, 1`.

To a family `𝒫 = P₀, …, P_{m-1}` of polynomials (with `m ≤ n`) we associate the
matrix `Mat(𝒫)` whose rows are the coordinates of the `Pᵢ` in the basis `𝓑`:
the `(i, j)` entry is the coordinate of `Pᵢ` along `Xⁿ⁻¹⁻ʲ`, namely the
coefficient of `Xⁿ⁻¹⁻ʲ` in `Pᵢ`.

Note that `Mat(𝓑)` is the identity matrix of size `n` (`Mat_basisB`).
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Semiring K] {m n : ℕ}

/-- The reverse-power basis `𝓑 = (Xⁿ⁻¹, …, X, 1)` of `𝓕_n = degreeLT K n`,
    indexed so that `basisB n i = Xⁿ⁻¹⁻ⁱ` (row/column `i` carries `Xⁿ⁻¹⁻ⁱ`). -/
noncomputable def basisB (n : ℕ) (i : Fin n) : K[X] := X ^ (n - 1 - (i : ℕ))

/-- **BPR §8.3.2.1.** The matrix `Mat(𝒫)` of a family of polynomials
    `P : Fin m → K[X]` in the basis `𝓑 = (Xⁿ⁻¹, …, X, 1)`: row `i` holds the
    coordinates of `P i`, so the `(i, j)` entry is the coefficient of `Xⁿ⁻¹⁻ʲ`
    in `P i`. -/
noncomputable def Mat (n : ℕ) (P : Fin m → K[X]) : Matrix (Fin m) (Fin n) K :=
  fun i j => (P i).coeff (n - 1 - (j : ℕ))

@[simp] theorem Mat_apply (P : Fin m → K[X]) (i : Fin m) (j : Fin n) :
    Mat n P i j = (P i).coeff (n - 1 - (j : ℕ)) := rfl

/-- **`Mat(𝓑)` is the identity matrix of size `n`.** -/
theorem Mat_basisB : Mat n (basisB (K := K) n) = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Mat_apply, basisB, coeff_X_pow, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have hne : ¬ (n - 1 - (j : ℕ) = n - 1 - (i : ℕ)) := by
      rw [Fin.ext_iff] at h; omega
    rw [ite_eq_right hne, ite_eq_right h]

end Azurite.BPR.Chapter8
