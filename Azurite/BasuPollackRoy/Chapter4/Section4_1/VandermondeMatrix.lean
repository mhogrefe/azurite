import Mathlib.LinearAlgebra.Vandermonde

/-!
# BPR Vandermonde matrix

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For `x_1, …, x_r` in a commutative ring `R` (BPR works over a field, but
the definition makes sense in any `CommRing`), the **Vandermonde matrix**
`V(x_1, …, x_r)` is the `r × r` matrix with entry `x_{j+1}^i` in row `i`
and column `j` (0-indexed: `i, j ∈ {0, …, r-1}`). The **Vandermonde
determinant** is its determinant.

This is the transpose of Mathlib's `Matrix.vandermonde`, which uses
`v i ^ j` (element-by-row). Since `det M = det Mᵀ`, the two
determinants agree.
-/

namespace Azurite.BPR.Chapter4

open Matrix

variable {R : Type*} [CommRing R]

/-- **BPR Vandermonde matrix** (unnumbered definition, §4.1). The
    `r × r` matrix with entry `x_j ^ i` in row `i`, column `j`
    (0-indexed). In BPR's notation this is `V(x_1, …, x_r)` with
    `x_{j+1}^i` at row `i`, column `j` (1-indexing the elements). -/
def vandermondeMat {r : ℕ} (x : Fin r → R) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => x j ^ i.val

/-- The Vandermonde matrix in BPR's convention equals the transpose of
    Mathlib's `Matrix.vandermonde`. -/
lemma vandermondeMat_eq_transpose {r : ℕ} (x : Fin r → R) :
    vandermondeMat x = (Matrix.vandermonde x).transpose := by
  ext i j
  simp [vandermondeMat, Matrix.vandermonde_apply, Matrix.transpose_apply]

/-- **BPR Vandermonde determinant** (unnumbered definition, §4.1). The
    determinant of `vandermondeMat x`. -/
def vandermondeDet {r : ℕ} (x : Fin r → R) : R :=
  (vandermondeMat x).det

/-- The Vandermonde determinant in BPR's convention equals Mathlib's. -/
lemma vandermondeDet_eq_mathlib {r : ℕ} (x : Fin r → R) :
    vandermondeDet x = (Matrix.vandermonde x).det := by
  rw [vandermondeDet, vandermondeMat_eq_transpose, Matrix.det_transpose]

end Azurite.BPR.Chapter4
