/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Example_2_67
import Azurite.AzMatrix.Equiv.Kronecker

/-!
# BPR Example 2.70: the matrix of signs as a tensor product

Let `M = M'` be the single-polynomial `3 × 3` matrix of signs

`M = !![1, 1, 1; 0, 1, -1; 0, 1, 1]`

(BPR Example 2.69 / the single-polynomial case of Proposition 2.68). Its
tensor product `M ⊗ M'` is the `9 × 9` matrix that **coincides with the
matrix of signs** of `A = {0,1,2}^{Q₁,Q₂}` on `Σ = {0,1,-1}^{Q₁,Q₂}`
(Example 2.67).

This is the `s = 2` instance of the general fact that the matrix of signs
of a union family is the tensor product of the per-block matrices: the
Kronecker index splitting `finProdFinEquiv` (`Q₁` outer) matches the BPR
lexicographic order on `A` and `Σ` (`Q₁` most significant).

We use the computable `AzMatrix.kronecker`; the equalities are checked by
kernel `decide`.
-/

namespace Azurite.BPR

open Polynomial

/-- `M = M'`: the single-polynomial `3 × 3` matrix of signs, as a
computable `AzMatrix`. -/
def exampleM : AzMatrix SignType 3 3 :=
  AzMatrix.ofLists [[1, 1, 1], [0, 1, -1], [0, 1, 1]]

/-- `M ⊗ M'` is the displayed `9 × 9` matrix of BPR Example 2.70. -/
theorem exampleM_kronecker_exampleM :
    exampleM.kronecker exampleM =
      AzMatrix.ofLists
        [[1, 1, 1, 1, 1, 1, 1, 1, 1],
         [0, 1, -1, 0, 1, -1, 0, 1, -1],
         [0, 1, 1, 0, 1, 1, 0, 1, 1],
         [0, 0, 0, 1, 1, 1, -1, -1, -1],
         [0, 0, 0, 0, 1, -1, 0, -1, 1],
         [0, 0, 0, 0, 1, 1, 0, -1, -1],
         [0, 0, 0, 1, 1, 1, 1, 1, 1],
         [0, 0, 0, 0, 1, -1, 0, 1, -1],
         [0, 0, 0, 0, 1, 1, 0, 1, 1]] := by
  decide

/-- **BPR Example 2.70.** `M ⊗ M'` coincides with the matrix of signs of
`A = {0,1,2}^{Q₁,Q₂}` on `Σ = {0,1,-1}^{Q₁,Q₂}` (Example 2.67). -/
theorem exampleM_kronecker_eq_matrixOfSigns :
    (exampleM.kronecker exampleM).toFn =
      matrixOfSigns exampleExponents exampleSignConditions := by
  have h : ∀ i j : Fin (3 * 3),
      (exampleM.kronecker exampleM).toFn i j
        = matrixOfSigns exampleExponents exampleSignConditions
            (Fin.cast (by decide) i) (Fin.cast (by decide) j) := by decide
  funext i j
  exact h i j

end Azurite.BPR
