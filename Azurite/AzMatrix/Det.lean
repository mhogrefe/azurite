/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Determinant via Gaussian elimination (BPR Algorithm 8.15, final output,
  equation 8.4).

  Builds on `AzMatrix.gauss` from `Azurite/AzMatrix/RowEchelon.lean` (the
  early-abort variant of BPR Algorithm 8.15): after running the elimination,
  the determinant is the signed product of the diagonal entries, where the
  sign is `(-1)^s` with `s` = the number of column swaps performed.
-/
import Azurite.AzMatrix.RowEchelon
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement
import Azurite.AzRat.ToString

namespace Azurite

variable {K : Type _} {n : Nat}

/-- **BPR Algorithm 8.15 (final output, equation 8.4).** The determinant of
    `M`, computed by Gaussian elimination:

      `det(M) = (-1)^s · U[0][0] · U[1][1] ⋯ U[n-1][n-1]`,

    where `(U, s) = M.gauss`. The bundled-typeclass dispatcher
    `AzMatrix.det` (in `AzMatrix.DetDispatch`) picks this over a field. -/
def AzMatrix.gaussDet [Field K] [DecidableEq K] (M : AzMatrix K n n) : K :=
  let (U, s) := M.gauss
  (-1 : K) ^ s * ∏ i, U.get i i

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- 2×2 over AzRat: det [[1, 2], [3, 4]] = 1·4 − 2·3 = −2.
#guard
  match (AzMatrix.parseStr "[1, 2; 3, 4]" : Option (AzMatrix AzRat 2 2)) with
  | some M => Azurite.AzRat.toString M.gaussDet == "-2"
  | none => False

-- 3×3 over AzRat: det [[2, 1, 1], [1, 3, 2], [1, 0, 0]] = −1.
#guard
  match (AzMatrix.parseStr "[2, 1, 1; 1, 3, 2; 1, 0, 0]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => Azurite.AzRat.toString M.gaussDet == "-1"
  | none => False

-- Identity over AzRat has determinant 1.
#guard Azurite.AzRat.toString ((1 : AzMatrix AzRat 4 4).gaussDet) == "1"

-- Singular matrix (rank-deficient): determinant 0.
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => Azurite.AzRat.toString M.gaussDet == "0"
  | none => False

-- Column-pivoting test: zero in the (0,0) position forces a swap.
#guard
  match (AzMatrix.parseStr "[0, 1; 1, 0]" : Option (AzMatrix AzRat 2 2)) with
  | some M => Azurite.AzRat.toString M.gaussDet == "-1"
  | none => False

end Tests

end Azurite
