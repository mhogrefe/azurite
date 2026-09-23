/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Kronecker (tensor) product for AzMatrix.

  `A.kronecker B` is the `(m*p) × (n*q)` block matrix `[aᵢⱼ B]`: the
  block in position `(i, j)` is the scalar multiple `aᵢⱼ • B`. Rows and
  columns are flattened with `finProdFinEquiv` (`(i, i') ↦ i' + p*i`), so
  block `i` occupies rows `[p*i, p*i + p)`.
-/
import Azurite.AzMatrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Azurite
variable {R : Type _} {m n p q : Nat}

/-- The Kronecker (tensor) product of `A : AzMatrix R m n` and
`B : AzMatrix R p q`: the `(m*p) × (n*q)` block matrix `[aᵢⱼ B]`. The
entry at `(r, c)` is `A iⱼ * B i'ⱼ'`, where `finProdFinEquiv` splits the
flat row index `r = i' + p*i` into the block index `i` and the
within-block index `i'` (and likewise for `c`). -/
def AzMatrix.kronecker [Mul R] (A : AzMatrix R m n) (B : AzMatrix R p q) :
    AzMatrix R (m * p) (n * q) :=
  AzMatrix.ofFn fun r c =>
    A.toFn (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm c).1 *
      B.toFn (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm c).2

end Azurite
