/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMatrix.Operations
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzMatrix.Parse
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Correctness of `AzMatrix.isSymmetricB`

The computable symmetry test `AzMatrix.isSymmetricB` agrees with Mathlib's
`Matrix.IsSymm` of the underlying matrix `toMat M`. This bridges the decidable
`Bool` check to the `Matrix.IsSymm` hypotheses used throughout the BPR
symmetric-matrix / quadratic-form theory (Chapter 4, §8.2.4).
-/

namespace Azurite.AzMatrix

variable {R : Type _} {n : ℕ}

/-- **Correctness of `isSymmetricB`.** The computable test returns `true` exactly
when the underlying Mathlib matrix is symmetric. -/
theorem isSymmetricB_iff [DecidableEq R] (M : AzMatrix R n n) :
    M.isSymmetricB = true ↔ (toMat M).IsSymm := by
  rw [isSymmetricB, decide_eq_true_iff, Matrix.IsSymm.ext_iff]
  exact ⟨fun h i j => (h i j).symm, fun h i j => (h i j).symm⟩

/-- Convenience: `isSymmetricB M = true` gives `(toMat M).IsSymm`. -/
theorem isSymm_toMat_of_isSymmetricB [DecidableEq R] {M : AzMatrix R n n}
    (h : M.isSymmetricB = true) : (toMat M).IsSymm :=
  (isSymmetricB_iff M).mp h

/-! ## Worked examples -/

section Tests

-- `[[1, 2], [2, 3]]` is symmetric; `[[1, 2], [3, 4]]` is not.
#guard (AzMatrix.parseStr "[1, 2; 2, 3]" : Option (AzMatrix AzInt 2 2)).map (·.isSymmetricB)
  == some true
#guard (AzMatrix.parseStr "[1, 2; 3, 4]" : Option (AzMatrix AzInt 2 2)).map (·.isSymmetricB)
  == some false

-- A `3 × 3` symmetric matrix.
#guard (AzMatrix.parseStr "[2, 1, 1; 1, 3, 0; 1, 0, 5]" :
  Option (AzMatrix AzInt 3 3)).map (·.isSymmetricB) == some true

-- The identity is symmetric.
#guard (1 : AzMatrix AzInt 3 3).isSymmetricB == true

end Tests

end Azurite.AzMatrix
