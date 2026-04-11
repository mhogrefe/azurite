import Azurite.AzMvPolynomial.New.Bind2
import Azurite.AzMvPolynomial.New.Equiv.Algebra

/-!
# Join₂ for AzMvPolynomialNew

Implements `join₂`, the operation that flattens a polynomial whose coefficients
are themselves polynomials into a single polynomial.

Given `p : AzMvPolynomialNew n (AzMvPolynomialNew n R ord) ord`, `join₂ p`
treats each coefficient (itself a polynomial) as an element of `R[Fin n]` and
multiplies it by the corresponding monic monomial, summing the results.

Matches `MvPolynomial.join₂` from Mathlib, defined as `bind₂ (RingHom.id _)`.

## Relationship to bind₂

`join₂ = bind₂ id`
-/

namespace Azurite

open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Flatten a polynomial whose coefficients are polynomials.
    Each term `(c, m)` where `c : AzMvPolynomialNew n R ord` contributes `c * m`
    to the result. -/
def AzMvPolynomialNew.join₂
    (p : AzMvPolynomialNew n (AzMvPolynomialNew n R ord) ord) :
    AzMvPolynomialNew n R ord :=
  p.bind₂ id

end Azurite
