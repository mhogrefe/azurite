/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Eval2
import Azurite.AzMvPolynomial.Rename
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra
import Azurite.AzMvPolynomial.Equiv.RenameHom

/-!
# `sumAlgEquiv` for AzMvPolynomial

Converts a polynomial in `m + n` variables into a multivariate polynomial in
`m` variables whose coefficients are themselves multivariate polynomials in
`n` variables:

```
AzMvPolynomial (m+n) R ord  ↔  AzMvPolynomial m (AzMvPolynomial n R ord) ord
```

The first `m` variables (indexed via `Fin.castAdd n`) become outer `X j`
variables; the last `n` variables (indexed via `Fin.natAdd m`) become `C (X j)`
— constant outer polynomials whose inner coefficient is an inner variable.

This is the Fin-only counterpart of Mathlib's
`MvPolynomial.sumAlgEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R)`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-! ### Forward direction -/

/-- Convert a polynomial in `m + n` variables into a multivariate polynomial
    in the first `m` variables whose coefficients are multivariate polynomials
    in the last `n` variables.

    Matches `MvPolynomial.sumAlgEquiv` from Mathlib (forward direction, after
    identifying `Fin m ⊕ Fin n ≃ Fin (m+n)` via `Fin.addCases`). -/
def AzMvPolynomial.sumEquiv {m n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (m+n) R ord) :
    AzMvPolynomial m (AzMvPolynomial n R ord) ord :=
  p.eval₂
    ((AzMvPolynomial.CHom : AzMvPolynomial n R ord →+*
        AzMvPolynomial m (AzMvPolynomial n R ord) ord).comp
      (AzMvPolynomial.CHom : R →+* AzMvPolynomial n R ord))
    (fun i : Fin (m+n) => Fin.addCases
      (fun j : Fin m => AzMvPolynomial.X (ord := ord) j)
      (fun j : Fin n =>
        AzMvPolynomial.C (ord := ord)
          (AzMvPolynomial.X (ord := ord) j : AzMvPolynomial n R ord))
      i)

/-! ### Reverse direction -/

/-- Inverse direction of `sumEquiv`: convert a multivariate polynomial in `m`
    variables whose coefficients are multivariate polynomials in `n` variables
    back into a polynomial in `m + n` variables.

    The inner coefficient ring `AzMvPolynomial n R ord` embeds via
    `renameMonotoneHom (Fin.natAdd m)`, and the outer variables `i : Fin m`
    map to `AzMvPolynomial.X (Fin.castAdd n i)`. -/
def AzMvPolynomial.sumEquivSymm {m n : ℕ} {ord : MonomialOrder}
    (q : AzMvPolynomial m (AzMvPolynomial n R ord) ord) :
    AzMvPolynomial (m+n) R ord :=
  q.eval₂
    (AzMvPolynomial.renameMonotoneHom (R := R) (ord := ord)
      (Fin.natAdd m : Fin n → Fin (m+n)) (Fin.strictMono_natAdd m))
    (fun i : Fin m =>
      AzMvPolynomial.X (ord := ord) (Fin.castAdd n i : Fin (m+n)))

end Azurite
