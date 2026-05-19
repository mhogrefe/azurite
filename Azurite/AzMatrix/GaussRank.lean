/-
  Rank of a square matrix via Gaussian elimination over a field
  (BPR Exercise 8.1, Gauss variant).

  At each step the algorithm finds a nonzero entry in the lower-right
  submatrix (rows and columns `≥ start`), swaps it to the diagonal position
  `(start, start)` via row and column swaps, then runs `eliminateBelow` to
  zero out the rest of that column. When no nonzero entry remains, the
  rank equals the number of pivot rounds completed.

  This is the field-version variant. The Bareiss-style (fraction-free)
  counterpart is `AzMatrix.bareissRank`.
-/
import Azurite.AzMatrix.RowEchelon
import Mathlib.Data.Rat.Defs

namespace Azurite

variable {K : Type _} {n : Nat}

/-! ### Recursive helper -/

/-- At step `start`, count one more pivot if a nonzero entry exists in the
    lower-right `(n - start) × (n - start)` submatrix; otherwise stop and
    return `start` as the final rank. -/
def AzMatrix.gaussRankAux [Field K] [DecidableEq K]
    (M : AzMatrix K n n) (start : Nat) : Nat :=
  if h : start + 1 < n then
    let kp : Fin n := ⟨start, by omega⟩
    match M.findFirstNonzero start start with
    | none => start
    | some (i, j) =>
      let M_row := if i = kp then M else M.swapRows kp i
      let M_swapped := if j = kp then M_row else M_row.swapCols kp j
      AzMatrix.gaussRankAux (M_swapped.eliminateBelow kp) (start + 1)
  else
    if hn : 0 < n then
      let kp : Fin n := ⟨n - 1, by omega⟩
      match M.findFirstNonzero (n - 1) (n - 1) with
      | none => n - 1
      | some _ => n
    else
      0
termination_by n - start

/-- **BPR Exercise 8.1 (Gauss variant).** The rank of a square matrix `M`
    computed by Gaussian elimination with full pivoting (row + column
    swaps): the number of nonzero diagonal pivots encountered before the
    elimination "stalls" on a zero submatrix. -/
def AzMatrix.gaussRank [Field K] [DecidableEq K] (M : AzMatrix K n n) : Nat :=
  AzMatrix.gaussRankAux M 0

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- 2×2 invertible over ℚ: rank 2.
#guard
  match (AzMatrix.parseStr "[1, 2; 3, 4]" : Option (AzMatrix ℚ 2 2)) with
  | some M => M.gaussRank = 2
  | none => False

-- 2×2 singular: rank 1.
#guard
  match (AzMatrix.parseStr "[1, 2; 2, 4]" : Option (AzMatrix ℚ 2 2)) with
  | some M => M.gaussRank = 1
  | none => False

-- 3×3 rank 3 (full).
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 4, 5, 6; 7, 8, 10]" :
      Option (AzMatrix ℚ 3 3)) with
  | some M => M.gaussRank = 3
  | none => False

-- 3×3 rank 2 (one dependent row).
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix ℚ 3 3)) with
  | some M => M.gaussRank = 2
  | none => False

-- Zero matrix: rank 0.
#guard (0 : AzMatrix ℚ 3 3).gaussRank = 0

-- Identity: rank n.
#guard (1 : AzMatrix ℚ 5 5).gaussRank = 5

end Tests

end Azurite
