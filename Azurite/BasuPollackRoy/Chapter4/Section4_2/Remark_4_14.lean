/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_13
import Mathlib.Algebra.Polynomial.Coeff

/-!
# BPR Remark 4.14: Sylvester matrix as transposed multiplication map

For polynomials `P, Q : D[X]` (over a commutative ring `D`), the linear
map
  `μ : (U, V) ↦ U · P + V · Q`,
acting on pairs `(U, V)` with `deg U < Q.natDegree` and
`deg V < P.natDegree`, becomes a linear map between free `D`-modules of
rank `P.natDegree + Q.natDegree`. Identifying

  domain ≅ D^{p+q}    via the basis `X^{q-1}, …, 1` ⊕ `X^{p-1}, …, 1`,
  codomain ≅ D^{p+q}  via the basis `X^{p+q-1}, …, X, 1`,

the matrix of `μ` is the transpose of the Sylvester matrix `Syl(P, Q)`:
its `j`-th column is the coordinate vector of the image of the `j`-th
basis vector of the domain, which is `X^{q-1-j} · P` for `j < q` and
`X^{p+q-1-j} · Q` for `j ≥ q` — these are precisely the **rows** of
`Syl(P, Q)`.

We formalize this by giving the explicit polynomial form of
`(Syl P Q).transpose.mulVec uv`: the coefficient of `X^{p+q-1-i}`
of the polynomial `μ(uv)`, where `μ(uv)` is the single-sum form
combining both `U·P` and `V·Q` directly.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- The polynomial output of the multiplication map `μ : (U, V) ↦ U·P + V·Q`,
    expressed directly on the coordinate vector
    `uv : Fin (P.natDegree + Q.natDegree) → D`. Each coordinate `uv j`
    contributes either to `U · P` (when `j < Q.natDegree`, multiplying
    the basis vector `X^{q-1-j}` by `P`) or to `V · Q`
    (when `j ≥ Q.natDegree`, multiplying `X^{p+q-1-j}` by `Q`). -/
noncomputable def Syl.mulMap (P Q : D[X])
    (uv : Fin (P.natDegree + Q.natDegree) → D) : D[X] :=
  ∑ j : Fin (P.natDegree + Q.natDegree),
    C (uv j) *
      (if j.val < Q.natDegree then X ^ (Q.natDegree - 1 - j.val) * P
        else X ^ (P.natDegree + Q.natDegree - 1 - j.val) * Q)

/-- **BPR Remark 4.14.** Applying the transpose of the Sylvester matrix
    to a coordinate vector `uv` produces the coefficient vector (in the
    descending power basis) of the polynomial `μ(uv) = U·P + V·Q`. -/
theorem Syl.transpose_mulVec_apply (P Q : D[X])
    (uv : Fin (P.natDegree + Q.natDegree) → D)
    (i : Fin (P.natDegree + Q.natDegree)) :
    (Syl P Q).transpose.mulVec uv i =
      (Syl.mulMap P Q uv).coeff (P.natDegree + Q.natDegree - 1 - i.val) := by
  show ∑ j, (Syl P Q).transpose i j * uv j = _
  unfold Syl.mulMap
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.transpose_apply, Polynomial.coeff_C_mul,
      apply_ite (Polynomial.coeff · (P.natDegree + Q.natDegree - 1 - i.val))]
  show (Syl P Q) j i * uv j = _
  unfold Syl
  rw [Matrix.of_apply, mul_comm]

end Azurite.BPR.Chapter4
