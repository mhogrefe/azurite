/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Correctness of `AzMatrix.kronecker`.

  We show it agrees with Mathlib's Kronecker product `Matrix.kroneckerMap`
  (notation `⊗ₖ`) over the product index types, transported to the flat
  index types `Fin (m*p)`, `Fin (n*q)` via `finProdFinEquiv`.
-/
import Azurite.AzMatrix.Kronecker
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMatrix.Parse
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace Azurite

open scoped Kronecker

variable {R : Type _} [Mul R] {m n p q : Nat}

/-- Pointwise value of the Kronecker product: the `(r, c)`-entry is the
product of the entries of `A` and `B` at the split indices. -/
@[simp]
theorem AzMatrix.toFn_kronecker_apply (A : AzMatrix R m n) (B : AzMatrix R p q)
    (r : Fin (m * p)) (c : Fin (n * q)) :
    (A.kronecker B).toFn r c =
      A.toFn (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm c).1 *
        B.toFn (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm c).2 := by
  simp [kronecker]

/-- `AzMatrix.kronecker` is the Kronecker product: its function form is
Mathlib's `A.toFn ⊗ₖ B.toFn` reindexed from the product index types to
the flat index types by `finProdFinEquiv`. -/
theorem AzMatrix.toFn_kronecker (A : AzMatrix R m n) (B : AzMatrix R p q) :
    (A.kronecker B).toFn =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (A.toFn ⊗ₖ B.toFn) := by
  funext r c
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

/-! ### Guards -/

private def kA : AzMatrix AzInt 2 2 := AzMatrix.ofLists [[1, 2], [3, 4]]
private def kB : AzMatrix AzInt 2 2 := AzMatrix.ofLists [[0, 5], [6, 7]]

-- `[aᵢⱼ B]`: block `(i,j)` is `aᵢⱼ • B`.
#guard toString (kA.kronecker kB) =
  "[0, 5, 0, 10; 6, 7, 12, 14; 0, 15, 0, 20; 18, 21, 24, 28]"

end Azurite
