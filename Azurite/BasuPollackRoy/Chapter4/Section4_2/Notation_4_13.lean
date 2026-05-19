import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# BPR Notation 4.13: Sylvester matrix and resultant

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.2.1.

Let `P` and `Q` be non-zero polynomials of degree `p` and `q` in `D[X]`,
where `D` is a (commutative) ring. With

  `P = a_p X^p + a_{p-1} X^{p-1} + ⋯ + a_0`,
  `Q = b_q X^q + b_{q-1} X^{q-1} + ⋯ + b_0`,

the **Sylvester matrix** `Syl(P, Q)` is the `(p + q) × (p + q)` matrix
whose rows, written in the descending power basis
`X^{p+q-1}, …, X, 1`, are

  `X^{q-1} P, …, P, X^{p-1} Q, …, Q`.

The **resultant** `Res(P, Q)` is `det(Syl(P, Q))`.

The degrees `p` and `q` are passed explicitly so the matrix size is a
syntactic `Fin (p + q)` (avoiding the dependent type `Fin (P.natDegree +
Q.natDegree)`). For the BPR-faithful interpretation, instantiate
`p := P.natDegree` and `q := Q.natDegree`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Notation 4.13** (Sylvester matrix). For polynomials `P, Q :
    D[X]` and stated degrees `p, q : ℕ`, the `(p + q) × (p + q)`
    Sylvester matrix with rows `X^{q-1} P, …, P, X^{p-1} Q, …, Q`
    written in the basis `X^{p+q-1}, …, X, 1`.

    Row `i ∈ [0, q)` is `X^{q-1-i} · P`, so the entry at column `j` is
    the coefficient of `X^{p+q-1-j}` in `X^{q-1-i} · P`, namely
    `P.coeff (p+i-j)` when `j ≤ p+i` and `0` otherwise.

    Row `i ∈ [q, p+q)` is `X^{p+q-1-i} · Q`, so the entry at column `j`
    is `Q.coeff (i-j)` when `j ≤ i` and `0` otherwise. -/
noncomputable def Syl (P : D[X]) (p : ℕ) (Q : D[X]) (q : ℕ) :
    Matrix (Fin (p + q)) (Fin (p + q)) D :=
  Matrix.of fun i j =>
    if i.val < q then
      (X ^ (q - 1 - i.val) * P).coeff (p + q - 1 - j.val)
    else
      (X ^ (p + q - 1 - i.val) * Q).coeff (p + q - 1 - j.val)

/-- **BPR Notation 4.13** (Resultant). `Res(P, Q) := det(Syl(P, Q))`. -/
noncomputable def Res (P : D[X]) (p : ℕ) (Q : D[X]) (q : ℕ) : D :=
  (Syl P p Q q).det

end Azurite.BPR.Chapter4
