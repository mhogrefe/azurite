/-
  Rank of a square matrix via the fraction-free Dodgson-Jordan-Bareiss
  recurrence (BPR Exercise 8.1, Bareiss variant).

  Structurally parallel to `AzMatrix.gaussRank` but uses `bareissEliminate`
  for the row-reduction step, keeping intermediate quotients inside the
  ring `D`. Requires `[Azurite.ExactDiv D]` (bundled with lawfulness) to
  perform the exact divisions of BPR equation (8.9).
-/
import Azurite.AzMatrix.BareissDet
import Azurite.AzMatrix.RowEchelon
import Azurite.Algorithm.ExactDiv
import Azurite.AzInt.ExactDiv
import Azurite.AzInt.Instances
import Azurite.AzInt.Conversion
import Azurite.AzInt.ParsableElement
import Azurite.AzPolynomial.ExactDiv
import Azurite.AzPolynomial.Equiv.ExactDiv
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.ParsableElement
import Azurite.AzMvPolynomial.ExactDivCommRing
import Azurite.AzMvPolynomial.Equiv.ExactDivCR
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt

namespace Azurite

variable {D : Type _} {n : Nat}

/-! ### Recursive helper -/

/-- At step `start` with previous-level divisor `b_prev`, count one more
    pivot if a nonzero entry exists in the lower-right `(n - start) × (n -
    start)` submatrix; otherwise stop and return `start` as the rank. -/
def AzMatrix.bareissRankAux [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    (M : AzMatrix D n n) (start : Nat) (b_prev : D) : Nat :=
  if h : start + 1 < n then
    let kp : Fin n := ⟨start, by omega⟩
    match M.findFirstNonzero start start with
    | none => start
    | some (i, j) =>
      let M_row := if i = kp then M else M.swapRows kp i
      let M_swapped := if j = kp then M_row else M_row.swapCols kp j
      AzMatrix.bareissRankAux
        (M_swapped.bareissEliminate kp b_prev) (start + 1) (M_swapped.get kp kp)
  else
    if hn : 0 < n then
      let kp : Fin n := ⟨n - 1, by omega⟩
      match M.findFirstNonzero (n - 1) (n - 1) with
      | none => n - 1
      | some _ => n
    else
      0
termination_by n - start

/-- **BPR Exercise 8.1 (Bareiss variant).** The rank of a square matrix
    `M` computed by the fraction-free Dodgson-Jordan-Bareiss recurrence
    with full pivoting (row + column swaps). Keeps all intermediate
    quotients inside `D` — no fraction-field detour. -/
def AzMatrix.bareissRank [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    (M : AzMatrix D n n) : Nat :=
  AzMatrix.bareissRankAux M 0 1

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

/-! #### Over `AzInt` -/

-- 3×3 rank 3 (full).
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 4, 5, 6; 7, 8, 10]" :
      Option (AzMatrix AzInt 3 3)) with
  | some M => M.bareissRank = 3
  | none => False

-- 3×3 rank 2 (rows 1, 2 collinear).
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix AzInt 3 3)) with
  | some M => M.bareissRank = 2
  | none => False

-- Zero matrix: rank 0.
#guard (0 : AzMatrix AzInt 4 4).bareissRank = 0

-- Identity: rank n.
#guard (1 : AzMatrix AzInt 5 5).bareissRank = 5

/-! #### Over `AzPolynomial AzInt` -/

-- det [[x, 1], [2, x]] = x² − 2, generically rank 2.
#guard
  match (AzMatrix.parseStr "[x, 1; 2, x]" :
      Option (AzMatrix (AzPolynomial AzInt) 2 2)) with
  | some M => M.bareissRank = 2
  | none => False

/-! #### Over `AzMvPolynomial 4 AzInt _` -/

-- Generic 2×2 with distinct multivariate entries: rank 2.
#guard
  match (AzMatrix.parseStr "[x₀, x₁; x₂, x₃]" :
      Option (AzMatrix
        (AzMvPolynomial 4 AzInt MonomialOrder.Degrevlex) 2 2)) with
  | some M => M.bareissRank = 2
  | none => False

end Tests

end Azurite
