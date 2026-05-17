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

namespace Azurite

variable {K : Type _} {n : Nat}

/-- **BPR Algorithm 8.15 (final output, equation 8.4).** The determinant of
    `M`, computed by Gaussian elimination:

      `det(M) = (-1)^s · U[0][0] · U[1][1] ⋯ U[n-1][n-1]`,

    where `(U, s) = M.gauss`. -/
def AzMatrix.det [Field K] [DecidableEq K] (M : AzMatrix K n n) : K :=
  let (U, s) := M.gauss
  (-1 : K) ^ s * ∏ i, U.get i i

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- 2×2 over ℚ: det [[1, 2], [3, 4]] = 1·4 − 2·3 = −2.
#guard
  (AzMatrix.ofLists [[(1 : ℚ), 2], [3, 4]] : AzMatrix ℚ 2 2).det = -2

-- 3×3 over ℚ: det [[2, 1, 1], [1, 3, 2], [1, 0, 0]] = −1.
#guard
  (AzMatrix.ofLists
    [[(2 : ℚ), 1, 1], [1, 3, 2], [1, 0, 0]] : AzMatrix ℚ 3 3).det = -1

-- Identity over ℚ has determinant 1.
#guard (1 : AzMatrix ℚ 4 4).det = 1

-- Singular matrix (rank-deficient): determinant 0.
#guard
  (AzMatrix.ofLists
    [[(1 : ℚ), 2, 3], [2, 4, 6], [1, 1, 1]] : AzMatrix ℚ 3 3).det = 0

-- Column-pivoting test: zero in the (0,0) position forces a swap.
#guard
  (AzMatrix.ofLists [[(0 : ℚ), 1], [1, 0]] : AzMatrix ℚ 2 2).det = -1

end Tests

end Azurite
