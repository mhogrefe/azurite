/-
  Row-echelon reduction by Gaussian elimination over a field.

  Two variants live here:

  * `rowEchelon` — Always produces an upper-triangular matrix. Uses *row*
    pivoting (search column `k` from row `k` down for a nonzero entry);
    when the column is already zero below the diagonal, leaves it alone
    and proceeds to the next column. The output is guaranteed
    upper-triangular regardless of singularity. This is the variant whose
    semantics match the mathematical definition of "row echelon form."

  * `gauss` — BPR Algorithm 8.15. Searches for a column pivot in the
    current row; aborts early (returning the partially-reduced state)
    when the row is zero from the pivot column onward. The partial output
    has a zero on its diagonal at the abort point, so the determinant
    formula in `Azurite/AzMatrix/Det.lean` still yields `0` without a
    separate case-split. This is the variant used by `det`.
-/
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzMatrix.Parse
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.Defs
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement

namespace Azurite

variable {K : Type _} {n : Nat}

/-! ### Column-pivot search (used by `gauss`) -/

/-- Helper for `findPivot`: search row `k` starting from column `j` for the
    smallest column index with a nonzero entry. -/
def AzMatrix.findPivotAux [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) (j : Nat) : Option (Fin n) :=
  if h : j < n then
    if M.get k ⟨j, h⟩ = 0 then AzMatrix.findPivotAux M k (j + 1)
    else some ⟨j, h⟩
  else none
termination_by n - j

/-- Find the smallest column index `j ≥ k.val` such that `M[k][j] ≠ 0`.
    Returns `none` if every entry of row `k` at column `≥ k.val` is zero
    (the trigger for `det(M) = 0` in BPR Algorithm 8.15). -/
def AzMatrix.findPivot [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) : Option (Fin n) :=
  M.findPivotAux k k.val

/-! ### 2D pivot search (for rank algorithms) -/

/-- Helper for `findFirstNonzero`: search rows `≥ i` for a row whose entry
    in columns `≥ c_start` is nonzero. Iterates row-by-row, using
    `findPivotAux` to scan each row. -/
def AzMatrix.findFirstNonzeroAux [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (i : Nat) (c_start : Nat) : Option (Fin n × Fin n) :=
  if h : i < n then
    match M.findPivotAux ⟨i, h⟩ c_start with
    | some j => some (⟨i, h⟩, j)
    | none => AzMatrix.findFirstNonzeroAux M (i + 1) c_start
  else
    none
termination_by n - i

/-- Find a pivot `(i, j)` with `i ≥ r_start`, `j ≥ c_start`, and `M[i][j] ≠ 0`.
    Iterates rows top-down, scanning each row left-to-right from column
    `c_start`. Returns `none` if the submatrix rows `≥ r_start`, columns
    `≥ c_start` is all zero. Used by rank algorithms (BPR Exercise 8.1)
    to find the next pivot when row and column indices may diverge. -/
def AzMatrix.findFirstNonzero [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (r_start c_start : Nat) : Option (Fin n × Fin n) :=
  AzMatrix.findFirstNonzeroAux M r_start c_start

/-! ### Column swap -/

/-- Swap columns `j₁` and `j₂` of `M`. -/
def AzMatrix.swapCols (M : AzMatrix K n n) (j₁ j₂ : Fin n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j =>
    if j = j₁ then M.get i j₂
    else if j = j₂ then M.get i j₁
    else M.get i j

/-! ### Row elimination (BPR equation 8.3) -/

/-- One step of Gaussian row reduction. Assumes `M[k][k] ≠ 0`; for every row
    `i > k` and column `j > k`,

      `M'[i][j] := M[i][j] − (M[i][k] / M[k][k]) · M[k][j]`     (BPR eq. 8.3)

    Column `k` itself is set to zero for every row below `k`. Rows `≤ k` and
    columns `< k` (which the invariant of the surrounding loop keeps at zero
    below the diagonal) are left unchanged. -/
def AzMatrix.eliminateBelow [Field K]
    (M : AzMatrix K n n) (k : Fin n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j =>
    if i.val ≤ k.val then M.get i j
    else if j.val < k.val then M.get i j
    else if j = k then 0
    else M.get i j - (M.get i k / M.get k k) * M.get k j

/-! ### BPR Algorithm 8.15: `gauss` (early-abort variant) -/

/-- Recursive helper for `gauss`: at step `start`, search row `start` for
    a pivot in columns `≥ start`; swap the pivot column into position
    `(start, start)`; eliminate column `start` below the pivot; recurse on
    `start + 1`. Stops early (returning the current state) when no pivot
    exists — that case leaves a zero on the diagonal and `det` evaluates to
    `0` via formula (8.4). -/
def AzMatrix.gaussAux [Field K] [DecidableEq K]
    (M : AzMatrix K n n) (start : Nat) (s : Nat) : AzMatrix K n n × Nat :=
  if h : start + 1 < n then
    let kp : Fin n := ⟨start, by omega⟩
    match M.findPivot kp with
    | none => (M, s)
    | some j =>
      if j = kp then
        AzMatrix.gaussAux (M.eliminateBelow kp) (start + 1) s
      else
        AzMatrix.gaussAux ((M.swapCols kp j).eliminateBelow kp) (start + 1) (s + 1)
  else
    (M, s)
termination_by n - start

/-- **BPR Algorithm 8.15: Gaussian row reduction (early-abort variant).**
    Returns the partially-reduced matrix `U` of `M` together with the number
    of column swaps `s` performed. If the algorithm aborts early on an
    all-zero pivot row, the returned `U` has a zero on its diagonal (so the
    determinant formula (8.4) still correctly yields `0`).

    Used by `AzMatrix.det`. For a guaranteed upper-triangular result, see
    the companion `rowEchelon`. -/
def AzMatrix.gauss [Field K] [DecidableEq K]
    (M : AzMatrix K n n) : AzMatrix K n n × Nat :=
  AzMatrix.gaussAux M 0 0

/-! ### Row-pivot search (used by `rowEchelon`) -/

/-- Helper for `findRowPivot`: search column `k` starting from row `i` for
    the smallest row index with a nonzero entry. -/
def AzMatrix.findRowPivotAux [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) (i : Nat) : Option (Fin n) :=
  if h : i < n then
    if M.get ⟨i, h⟩ k = 0 then AzMatrix.findRowPivotAux M k (i + 1)
    else some ⟨i, h⟩
  else none
termination_by n - i

/-- Find the smallest row index `i ≥ k.val` such that `M[i][k] ≠ 0`.
    Returns `none` when column `k` is zero from row `k` downward (in which
    case `rowEchelon` can skip this step — the column is already in
    upper-triangular shape). -/
def AzMatrix.findRowPivot [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) : Option (Fin n) :=
  M.findRowPivotAux k k.val

/-- Swap rows `i₁` and `i₂` of `M`. -/
def AzMatrix.swapRows (M : AzMatrix K n n) (i₁ i₂ : Fin n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j =>
    if i = i₁ then M.get i₂ j
    else if i = i₂ then M.get i₁ j
    else M.get i j

/-! ### Row echelon reduction (always-triangular variant) -/

/-- Recursive helper for `rowEchelon`: at step `start`, search column
    `start` for a row pivot at or below row `start`; if found, swap rows
    (when not already at the pivot row), then eliminate column `start`
    below the pivot; recurse on `start + 1`. When column `start` is already
    zero at and below the diagonal, leaves the matrix alone and recurses. -/
def AzMatrix.rowEchelonAux [Field K] [DecidableEq K]
    (M : AzMatrix K n n) (start : Nat) (s : Nat) : AzMatrix K n n × Nat :=
  if h : start + 1 < n then
    let kp : Fin n := ⟨start, by omega⟩
    match M.findRowPivot kp with
    | none => AzMatrix.rowEchelonAux M (start + 1) s
    | some i =>
      if i = kp then
        AzMatrix.rowEchelonAux (M.eliminateBelow kp) (start + 1) s
      else
        AzMatrix.rowEchelonAux
          ((M.swapRows kp i).eliminateBelow kp) (start + 1) (s + 1)
  else
    (M, s)
termination_by n - start

/-- **Row echelon reduction.** Produces an upper-triangular matrix `U`
    together with the number of row swaps `s` performed. Never aborts:
    when column `k` is zero at and below the diagonal, leaves that column
    alone and proceeds. The output is upper-triangular regardless of
    whether `M` is singular.

    This is the variant whose semantics match the mathematical definition
    of "row echelon form." For BPR Algorithm 8.15 (early-abort, used by
    `det`), see the companion `gauss`. -/
def AzMatrix.rowEchelon [Field K] [DecidableEq K]
    (M : AzMatrix K n n) : AzMatrix K n n × Nat :=
  AzMatrix.rowEchelonAux M 0 0

/-! ### Indexed Gauss iteration: `gaussSteps M k` -/

/-- Apply exactly `k` Gauss elimination steps to `M`, with NO column swaps.
    Step `ℓ` uses the pivot at `(ℓ, ℓ)` directly; if the pivot is zero the
    step's `eliminateBelow` still zeros column `ℓ` below the diagonal but
    leaves columns `> ℓ` unchanged (since `x / 0 = 0` in a field). This
    matches BPR's `g_{i,j}^{(k)}` notation: `(gaussSteps M k).toFn i j` is
    `g_{i+1, j+1}^{(k)}` in `1`-indexed BPR conventions.

    Steps `k ≥ n` are no-ops (the matrix is already triangular by then). -/
def AzMatrix.gaussSteps [Field K] (M : AzMatrix K n n) :
    Nat → AzMatrix K n n
  | 0 => M
  | k + 1 =>
    if h : k < n then
      (M.gaussSteps k).eliminateBelow ⟨k, h⟩
    else
      M.gaussSteps k

@[simp]
theorem AzMatrix.gaussSteps_zero [Field K] (M : AzMatrix K n n) :
    M.gaussSteps 0 = M := rfl

theorem AzMatrix.gaussSteps_succ [Field K] (M : AzMatrix K n n)
    (k : Nat) (hk : k < n) :
    M.gaussSteps (k + 1) = (M.gaussSteps k).eliminateBelow ⟨k, hk⟩ := by
  show (if h : k < n then (M.gaussSteps k).eliminateBelow ⟨k, h⟩
        else M.gaussSteps k) = _
  rw [dif_pos hk]

/-- For step counts beyond `n`, `gaussSteps` stabilizes: no rows remain
    below the pivot, so the step is a no-op. -/
theorem AzMatrix.gaussSteps_of_ge [Field K] (M : AzMatrix K n n)
    (k : Nat) (hk : ¬ k < n) :
    M.gaussSteps (k + 1) = M.gaussSteps k := by
  show (if h : k < n then (M.gaussSteps k).eliminateBelow ⟨k, h⟩
        else M.gaussSteps k) = _
  rw [dif_neg hk]

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

/-! #### `gauss` (early-abort, BPR Alg. 8.15) -/

-- No swap needed: pivots are already nonzero on the diagonal.
#guard
  match (AzMatrix.parseStr "[2, 1, 1; 4, 3, 3; 8, 7, 9]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.gauss
              toString U = "[2, 1, 1; 0, 1, 1; 0, 0, 2]" ∧ s = 0
  | none => False

-- Column swap forced at step 0 (zero in the (0, 0) entry); s = 1.
#guard
  match (AzMatrix.parseStr "[0, 1, 2; 1, 2, 3; 2, 3, 5]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.gauss
              toString U = "[1, 0, 2; 0, 1, -1; 0, 0, 1]" ∧ s = 1
  | none => False

-- Singular: row 1 zeros out at step 0; algorithm aborts at step 1, leaving
-- the matrix as-is (with the all-zero row visible on the diagonal at (1, 1)).
-- Note that the output here is NOT upper-triangular (row 2 has `-1` at col 1).
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.gauss
              toString U = "[1, 2, 3; 0, 0, 0; 0, -1, -2]" ∧ s = 0
  | none => False

/-! #### `rowEchelon` (always upper-triangular) -/

-- Nonsingular, no row swap needed: same shape as `gauss`.
#guard
  match (AzMatrix.parseStr "[2, 1, 1; 4, 3, 3; 8, 7, 9]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.rowEchelon
              toString U = "[2, 1, 1; 0, 1, 1; 0, 0, 2]" ∧ s = 0
  | none => False

-- Zero in (0, 0): a row swap (not a column swap) brings the pivot up.
#guard
  match (AzMatrix.parseStr "[0, 1, 2; 1, 2, 3; 2, 3, 5]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.rowEchelon
              toString U = "[1, 2, 3; 0, 1, 2; 0, 0, 1]" ∧ s = 1
  | none => False

-- Singular: same input as the third `gauss` test. Here the algorithm swaps
-- the all-zero row to the bottom and finishes — output IS triangular.
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.rowEchelon
              toString U = "[1, 2, 3; 0, -1, -2; 0, 0, 0]" ∧ s = 1
  | none => False

-- Column 1 has no pivot at or below the diagonal at step 1; the algorithm
-- skips that column. Since `rowEchelon` only zeros the current pivot column
-- (not the next row's leading column), the result remains upper triangular
-- but is *not* in strict echelon form: the diagonal `[1, 0, 1]` exposes the
-- singular column, and row 2 keeps its leading `1` at col 2.
#guard
  match (AzMatrix.parseStr "[1, 0, 1; 0, 0, 1; 0, 0, 1]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => let (U, s) := M.rowEchelon
              toString U = "[1, 0, 1; 0, 0, 1; 0, 0, 1]" ∧ s = 0
  | none => False

end Tests

end Azurite
