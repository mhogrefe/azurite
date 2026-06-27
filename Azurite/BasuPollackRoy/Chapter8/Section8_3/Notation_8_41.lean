import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_22

/-!
# BPR Notation 8.41: Subresultant cofactors `sResU_j(P, Q)`, `sResV_j(P, Q)`

The `j`-th signed subresultant cofactors are the determinants of the square matrices `M_j`
(resp. `N_j`) obtained from the Sylvester-Habicht matrix `SyHa_j(P, Q)` (Notation 4.22, a
`(p+q-2j) × (p+q-j)` matrix over `D`, with `p := deg P`, `q := deg Q`) by

* keeping its first `p + q - 2j - 1` columns (as constants), and
* appending a last column equal to
  `(X^{q-1-j}, …, X, 1, 0, …, 0)ᵀ` for `M_j`
  (resp. `(0, …, 0, 1, X, …, X^{p-1-j})ᵀ` for `N_j`).

Both matrices are square of size `p + q - 2j`, over `D[X]` (the first columns are constants
`C(·)` and the last column carries the monomials).  Their determinants `sResU_j(P,Q)`,
`sResV_j(P,Q)` therefore lie in `D[X]` — for `P, Q ∈ D[X]` the cofactors are genuine
polynomials over `D`, which is exactly the point of the determinant description (no division
into the fraction field is needed).

These are the Bézout cofactors of the signed subresultant polynomial:
`sResP_j = sResU_j · P + sResV_j · Q` (proved elsewhere).
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {D : Type*} [CommRing D]

/-- The matrix `M_j(P, Q)` of **BPR Notation 8.41** for the `U`-cofactor: the first
    `p + q - 2j - 1` columns of `SyHa_j(P, Q)` (lifted to constants via `C`), with last column
    `(X^{q-1-j}, …, X, 1, 0, …, 0)ᵀ` (the `P`-block rows carry the descending monomials, the
    `Q`-block rows are `0`). -/
noncomputable def sResUMat (P Q : D[X]) (j : ℕ) :
    Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
           (Fin (P.natDegree + Q.natDegree - 2 * j)) D[X] :=
  Matrix.of fun i k =>
    if (k : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j then
      C (Chapter4.SyHa P Q j i (Fin.castLE (by omega) k))
    else if (i : ℕ) < Q.natDegree - j then
      X ^ (Q.natDegree - 1 - j - (i : ℕ))
    else 0

/-- The matrix `N_j(P, Q)` of **BPR Notation 8.41** for the `V`-cofactor: the first
    `p + q - 2j - 1` columns of `SyHa_j(P, Q)` (lifted to constants via `C`), with last column
    `(0, …, 0, 1, X, …, X^{p-1-j})ᵀ` (the `P`-block rows are `0`, the `Q`-block rows carry the
    ascending monomials). -/
noncomputable def sResVMat (P Q : D[X]) (j : ℕ) :
    Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
           (Fin (P.natDegree + Q.natDegree - 2 * j)) D[X] :=
  Matrix.of fun i k =>
    if (k : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j then
      C (Chapter4.SyHa P Q j i (Fin.castLE (by omega) k))
    else if (i : ℕ) < Q.natDegree - j then 0
    else X ^ ((i : ℕ) - (Q.natDegree - j))

/-- **BPR Notation 8.41.** The `j`-th subresultant cofactor `sResU_j(P, Q) := det(M_j)`. -/
noncomputable def sResU (P Q : D[X]) (j : ℕ) : D[X] := (sResUMat P Q j).det

/-- **BPR Notation 8.41.** The `j`-th subresultant cofactor `sResV_j(P, Q) := det(N_j)`. -/
noncomputable def sResV (P Q : D[X]) (j : ℕ) : D[X] := (sResVMat P Q j).det

end Azurite.BPR.Chapter8
