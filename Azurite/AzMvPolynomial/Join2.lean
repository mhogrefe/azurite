import Azurite.AzMvPolynomial.Bind2
import Azurite.AzMvPolynomial.Equiv.Algebra

/-!
# Join₂ for AzMvPolynomial

Implements `join₂`, the operation that flattens a polynomial whose coefficients
are themselves polynomials into a single polynomial.

Given `p : AzMvPolynomial σ (AzMvPolynomial σ R ord) ord`, `join₂ p` treats each
coefficient (itself a polynomial) as an element of `R[σ]` and multiplies it by
the corresponding monic monomial, summing the results.

Matches `MvPolynomial.join₂` from Mathlib, which is defined as `bind₂ (RingHom.id _)`.

## Relationship to bind₂

`join₂ = bind₂ id`
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Flatten a polynomial whose coefficients are polynomials.
    Each term `(c, m)` where `c : AzMvPolynomial σ R ord` contributes `c * m`
    to the result. -/
def AzMvPolynomial.join₂
    (p : AzMvPolynomial σ (AzMvPolynomial σ R ord) ord) :
    AzMvPolynomial σ R ord :=
  p.bind₂ id

end Azurite
