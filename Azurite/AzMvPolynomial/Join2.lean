/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Bind2
import Azurite.AzMvPolynomial.Equiv.Algebra

/-!
# Join₂ for AzMvPolynomial

Implements `join₂`, the operation that flattens a polynomial whose coefficients
are themselves polynomials into a single polynomial.

Given `p : AzMvPolynomial n (AzMvPolynomial n R ord) ord`, `join₂ p`
treats each coefficient (itself a polynomial) as an element of `R[Fin n]` and
multiplies it by the corresponding monic monomial, summing the results.

Matches `MvPolynomial.join₂` from Mathlib, defined as `bind₂ (RingHom.id _)`.

## Relationship to bind₂

`join₂ = bind₂ id`
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Flatten a polynomial whose coefficients are polynomials.
    Each term `(c, m)` where `c : AzMvPolynomial n R ord` contributes `c * m`
    to the result. -/
def AzMvPolynomial.join₂
    (p : AzMvPolynomial n (AzMvPolynomial n R ord) ord) :
    AzMvPolynomial n R ord :=
  p.bind₂ id

end Azurite
