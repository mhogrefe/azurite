/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.ResEqResultant

/-!
# BPR Proposition 4.19: resultant lies in the ideal `(P, Q)`

For polynomials `P, Q : D[X]` over a commutative ring `D`, the resultant
`Res(P, Q)` can be written as a `D[X]`-linear combination of `P` and `Q`
with small-degree cofactors:

  there exist `U, V : D[X]` with `deg U < Q.natDegree`,
  `deg V < P.natDegree`, and `Res(P, Q) = U·P + V·Q`.

BPR's proof modifies the Sylvester matrix's last column to hold the
polynomials `X^{q-1} P, …, P, X^{p-1} Q, …, Q` (instead of their leading
coefficient values), expands the determinant of the modified matrix by
this last column to read `Res(P, Q) + ∑_{j ≥ 1} d_j X^j`, and observes
that each `d_j` is the determinant of a matrix with two equal columns
(hence zero), reducing the determinant to `Res(P, Q)`. The cofactor
expansion along the last column then gives the desired identity.

Mathlib's `Polynomial.exists_mul_add_mul_eq_C_resultant` already
establishes this for its `resultant`. We transport it across our
`Res = Polynomial.resultant` bridge.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Proposition 4.19.** For `P, Q : D[X]` with `(P.natDegree,
    Q.natDegree) ≠ (0, 0)`, there exist `U, V : D[X]` with
    `deg U < Q.natDegree` and `deg V < P.natDegree` such that

      `C (Res(P, Q)) = U · P + V · Q`

    in `D[X]` (where `C` embeds the scalar `Res(P, Q) ∈ D` as a constant
    polynomial). -/
theorem Proposition_4_19 (P Q : D[X])
    (H : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    ∃ U V : D[X], U.degree < Q.natDegree ∧ V.degree < P.natDegree ∧
      C (Res P Q) = U * P + V * Q := by
  rw [Res_eq_resultant P Q]
  obtain ⟨U, V, hU, hV, h_eq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant P Q le_rfl le_rfl H
  refine ⟨U, V, hU, hV, ?_⟩
  linear_combination -h_eq

end Azurite.BPR.Chapter4
