/-
  Coefficient substitution (bind₂) for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.Add

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R S : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
  {n : ℕ} {ord : MonomialOrder}

/-- Create a single-term polynomial from a monic monomial with coefficient 1. -/
def MonicMonomial.toAzMvPoly [DecidableEq S]
    (m : MonicMonomial n ord) : AzMvPolynomial n S ord :=
  if h : (1 : S) = 0 then 0
  else AzMvPolynomial.ofMonomial ⟨⟨1, h⟩, m⟩

/-- Apply `bind₂` to a single monomial. -/
def Monomial.bind₂ (f : R → AzMvPolynomial n S ord)
    (m : Monomial n R ord) : AzMvPolynomial n S ord :=
  f m.coeff.val * m.monic.toAzMvPoly

/-- Substitute coefficients in a multivariate polynomial using `f`. -/
def AzMvPolynomial.bind₂ (f : R → AzMvPolynomial n S ord)
    (p : AzMvPolynomial n R ord) : AzMvPolynomial n S ord :=
  p.terms.foldl (init := 0) fun acc m => acc + m.bind₂ f

end Azurite
