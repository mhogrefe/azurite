import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
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

The degrees `p` and `q` are read off as `P.natDegree` and `Q.natDegree`,
giving the BPR-faithful signature `Syl P Q` and `Res P Q` (no explicit
formal-degree parameters). For consumers needing flexible formal
degrees (typically those mediating through Mathlib's
`Polynomial.resultant`, which carries explicit `(m, n)` arguments),
work with `Polynomial.resultant P Q m n` directly and bridge to `Res`
at the boundary.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Notation 4.13** (Sylvester matrix). For polynomials
    `P, Q : D[X]`, the `(p + q) × (p + q)` Sylvester matrix (with
    `p := P.natDegree`, `q := Q.natDegree`) with rows
    `X^{q-1} P, …, P, X^{p-1} Q, …, Q` written in the basis
    `X^{p+q-1}, …, X, 1`.

    Row `i ∈ [0, q)` is `X^{q-1-i} · P`, so the entry at column `j` is
    the coefficient of `X^{p+q-1-j}` in `X^{q-1-i} · P`.

    Row `i ∈ [q, p+q)` is `X^{p+q-1-i} · Q`, so the entry at column `j`
    is the coefficient of `X^{p+q-1-j}` in `X^{p+q-1-i} · Q`. -/
noncomputable def Syl (P Q : D[X]) :
    Matrix (Fin (P.natDegree + Q.natDegree))
           (Fin (P.natDegree + Q.natDegree)) D :=
  Matrix.of fun i j =>
    if i.val < Q.natDegree then
      (X ^ (Q.natDegree - 1 - i.val) * P).coeff
        (P.natDegree + Q.natDegree - 1 - j.val)
    else
      (X ^ (P.natDegree + Q.natDegree - 1 - i.val) * Q).coeff
        (P.natDegree + Q.natDegree - 1 - j.val)

/-- **BPR Notation 4.13** (Resultant). `Res(P, Q) := det(Syl(P, Q))`. -/
noncomputable def Res (P Q : D[X]) : D :=
  (Syl P Q).det

end Azurite.BPR.Chapter4
