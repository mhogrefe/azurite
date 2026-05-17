/-
  BPR Notation 8.19 [Bareiss]: the matrix `M_{i,j}^{(k)}` and the minor
  `b_{i,j}^{(k)} = det(M_{i,j}^{(k)})`.

  For an `n × n` matrix `M`, indices `i, j : Fin n`, and a size parameter
  `k ≤ n`, the block `M_{i,j}^{(k)}` is the `(k+1) × (k+1)` submatrix of `M`
  whose first `k` rows (resp. columns) are rows (resp. columns) `0, …, k-1`
  of `M`, and whose last row (resp. column) is row `i` (resp. column `j`)
  of `M`. The minor `b_{i,j}^{(k)}` is its determinant. Because `Matrix.det`
  is a polynomial in the matrix entries, `b_{i,j}^{(k)}` lives in the same
  commutative ring as the entries — in particular, in any integral domain `D`
  containing the entries of `M`, no extra fraction-free machinery is needed.

  Setting `i = j = ⟨k, _⟩` selects rows and columns `0, …, k`, recovering
  the principal `(k+1)`-th minor of `M` (`bareissMinor_eq_principalMinor`).
-/
import Azurite.AzMatrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Azurite

variable {R : Type _} {n : Nat}

/-! ### The Bareiss block `M_{i,j}^{(k)}` -/

/-- The row/column indexing function for `bareissBlock`: maps `Fin (k+1)` to
    `Fin n` by sending the first `k` indices to `⟨0, _⟩, …, ⟨k-1, _⟩` and
    the last index (`Fin.last k`) to the external index `i`. -/
def AzMatrix.bareissIdx (k : Nat) (hk : k ≤ n) (i : Fin n) : Fin (k + 1) → Fin n :=
  Fin.snoc (fun l : Fin k => ⟨l.val, lt_of_lt_of_le l.isLt hk⟩) i

/-- **BPR Notation 8.19.** The Bareiss block `M_{i,j}^{(k)}`: the
    `(k+1) × (k+1)` submatrix of `M` whose first `k` rows/columns come from
    `M`'s first `k` rows/columns and whose last row/column is row `i` /
    column `j` of `M`.

    Concretely, for `i', j' : Fin (k+1)`:
    * If `i'.val < k` and `j'.val < k`: entry is `M[i'][j']`.
    * If `i'.val = k` and `j'.val < k`: entry is `M[i][j']`.
    * If `i'.val < k` and `j'.val = k`: entry is `M[i'][j]`.
    * If `i'.val = k` and `j'.val = k`: entry is `M[i][j]`. -/
def AzMatrix.bareissBlock (M : AzMatrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin n) : AzMatrix R (k + 1) (k + 1) :=
  AzMatrix.ofFn fun i' j' =>
    M.get (AzMatrix.bareissIdx k hk i i') (AzMatrix.bareissIdx k hk j j')

/-- Entrywise `toFn` form of `bareissBlock`: it agrees with
    `Matrix.submatrix` along the row/column index maps. -/
theorem AzMatrix.toFn_bareissBlock (M : AzMatrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin n) :
    (M.bareissBlock k hk i j).toFn =
      Matrix.submatrix M.toFn (AzMatrix.bareissIdx k hk i)
        (AzMatrix.bareissIdx k hk j) := by
  funext i' j'
  show (AzMatrix.bareissBlock M k hk i j).toFn i' j' = _
  unfold AzMatrix.bareissBlock
  rw [AzMatrix.toFn_ofFn]
  rfl

/-! ### The Bareiss minor `b_{i,j}^{(k)}` -/

/-- **BPR Notation 8.19.** The Bareiss minor `b_{i,j}^{(k)}`, the determinant
    of `M_{i,j}^{(k)}`.

    Because `Matrix.det` is a polynomial in the matrix entries, the resulting
    value lives in the commutative ring of entries — in particular, an
    integral domain entry ring keeps the minors inside that integral domain
    without any fraction-field detour. -/
def AzMatrix.bareissMinor [CommRing R] (M : AzMatrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin n) : R :=
  Matrix.det (M.bareissBlock k hk i j).toFn

/-! ### Principal `k`-th minor -/

/-- Specialization `i = j = ⟨k, _⟩` recovers the principal `(k+1)`-th minor:
    the determinant of the top-left `(k+1) × (k+1)` submatrix of `M`. -/
def AzMatrix.principalMinor [CommRing R] (M : AzMatrix R n n) (k : Nat)
    (hk : k < n) : R :=
  M.bareissMinor k (le_of_lt hk) ⟨k, hk⟩ ⟨k, hk⟩

/-- **BPR Notation 8.19 (final claim).** `b_{k+1, k+1}^{(k)}` is the principal
    `(k+1)`-th minor of `M` (BPR's `b_{k,k}^{(k-1)}` in 1-indexed notation). -/
theorem AzMatrix.bareissMinor_eq_principalMinor [CommRing R]
    (M : AzMatrix R n n) (k : Nat) (hk : k < n) :
    M.bareissMinor k (le_of_lt hk) ⟨k, hk⟩ ⟨k, hk⟩ = M.principalMinor k hk :=
  rfl

/-- The principal `(k+1)`-th minor equals `det(Matrix.submatrix · ·)` with
    both index maps being `Fin.castLE`, i.e., the top-left `(k+1)`-block. -/
theorem AzMatrix.principalMinor_eq_top_left_det [CommRing R]
    (M : AzMatrix R n n) (k : Nat) (hk : k < n) :
    M.principalMinor k hk =
      Matrix.det
        (Matrix.submatrix M.toFn (Fin.castLE (Nat.succ_le_of_lt hk))
          (Fin.castLE (Nat.succ_le_of_lt hk))) := by
  unfold AzMatrix.principalMinor AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock]
  have h_idx : AzMatrix.bareissIdx k (le_of_lt hk) ⟨k, hk⟩ =
      Fin.castLE (Nat.succ_le_of_lt hk) := by
    funext l
    unfold AzMatrix.bareissIdx
    by_cases h : l.val < k
    · rw [show l = (⟨l.val, h⟩ : Fin k).castSucc by ext; rfl]
      rw [Fin.snoc_castSucc]
      rfl
    · have h_eq : l.val = k := by
        have := l.isLt
        omega
      rw [show l = Fin.last k by ext; exact h_eq]
      rw [Fin.snoc_last]
      rfl
  rw [h_idx]

end Azurite
