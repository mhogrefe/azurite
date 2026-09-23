/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_13
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# BPR Notation 4.22: Sylvester-Habicht matrix `SyHa_j(P, Q)`

For polynomials `P, Q : D[X]` and an index `j ∈ ℕ` (with BPR's
intended range `0 ≤ j ≤ min(Q.natDegree, P.natDegree - 1)`), the
**`j`-th Sylvester-Habicht matrix** of `P` and `Q` is the
`(p + q - 2j) × (p + q - j)` matrix (with `p := P.natDegree` and
`q := Q.natDegree`) whose rows are the polynomials

  `X^{q - j - 1} P, …, X^0 P = P, Q, X·Q, …, X^{p - j - 1} Q`

expressed in the descending power basis `X^{p + q - j - 1}, …, X, 1`.

Reading off:
* the first `q - j` rows are P-shifts with **decreasing** exponent from
  `q - j - 1` down to `0` (so the top row is `X^{q - j - 1} P`, with
  leading entry `a_p` at column `0`);
* the last `p - j` rows are Q-shifts with **increasing** exponent from
  `0` up to `p - j - 1` (so the bottom row is `X^{p - j - 1} Q`, with
  leading entry `b_q` at column `0`).

Unlike `Syl` (Notation 4.13), which carries explicit formal-degree
parameters `p, q` to keep the matrix size a non-dependent
`Fin (p + q)`, `SyHa` is parameterized only by `P, Q, j`: the degrees
are read off as `P.natDegree`, `Q.natDegree`, so the size is the
dependent `Fin (P.natDegree + Q.natDegree - 2j)` etc. This keeps the
BPR-faithful interpretation literal and avoids consumers needing to
thread degree witnesses.

Sizes use natural-number subtraction (saturating at `0`), so the
definition is total: outside BPR's intended range the corresponding
`Fin n` types become empty and the matrix is trivial.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Notation 4.22.** The `j`-th Sylvester-Habicht matrix of
    `P` and `Q`, as defined above.

    With `p := P.natDegree` and `q := Q.natDegree`, the entry at row
    `i ∈ Fin (p + q - 2j)` and column `k ∈ Fin (p + q - j)`:
    * if `i.val < q - j` (P-row block): the coefficient of
      `X^{p + q - j - 1 - k}` in `X^{q - j - 1 - i} · P`,
    * otherwise (Q-row block): the coefficient of `X^{p + q - j - 1 - k}`
      in `X^{i - (q - j)} · Q`. -/
noncomputable def SyHa (P Q : D[X]) (j : ℕ) :
    Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
           (Fin (P.natDegree + Q.natDegree - j)) D :=
  Matrix.of fun i k =>
    if i.val < Q.natDegree - j then
      (X ^ (Q.natDegree - j - 1 - i.val) * P).coeff
        (P.natDegree + Q.natDegree - j - 1 - k.val)
    else
      (X ^ (i.val - (Q.natDegree - j)) * Q).coeff
        (P.natDegree + Q.natDegree - j - 1 - k.val)

/-! ### Signed subresultant coefficient -/

/-- The square submatrix `SyHa_{j,j}(P, Q)` of `SyHa_j(P, Q)` consisting
    of its first `P.natDegree + Q.natDegree - 2 j` columns. The
    remaining `j` columns of `SyHa_j` are dropped to make the matrix
    square. -/
noncomputable def SyHaSquare (P Q : D[X]) (j : ℕ) :
    Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
           (Fin (P.natDegree + Q.natDegree - 2 * j)) D :=
  (SyHa P Q j).submatrix id (Fin.castLE (by omega))

/-- BPR's **j-th signed subresultant coefficient** `sRes_j(P, Q)`.

    With `p := P.natDegree` and `q := Q.natDegree`:
    * for `j ≤ q`, the determinant of the square Sylvester-Habicht
      submatrix `SyHa_{j,j}(P, Q)`;
    * when `q < p`, the gap is filled by `sRes_p(P, Q) := a_p` (leading
      coefficient of `P`) and `sRes_j(P, Q) := 0` for `q < j < p` (the
      defective subresultants in the degree gap vanish). Note: in the
      non-defective boundary case `q = p - 1` the value `sRes_{p-1} = b_q`
      is already produced by the determinant branch (`j = p - 1 ≤ q`);
    * outside both ranges (`j > p`, or `q ≥ p` with `j > q`), we default
      to `0` so the function is total. -/
noncomputable def sRes (P Q : D[X]) (j : ℕ) : D :=
  if j ≤ Q.natDegree then (SyHaSquare P Q j).det
  else if Q.natDegree < P.natDegree then
    if j = P.natDegree then P.leadingCoeff
    else 0
  else 0

end Azurite.BPR.Chapter4
