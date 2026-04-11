/-
  Coefficient substitution (bind₂) for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Mul
import Azurite.AzMvPolynomial.New.Add

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew

variable {R S : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
  {n : ℕ} {ord : MonomialOrder}

/-- Create a single-term polynomial from a monic monomial with coefficient 1. -/
def MonicMonomialNew.toAzMvPoly [DecidableEq S]
    (m : MonicMonomialNew n ord) : AzMvPolynomialNew n S ord :=
  if h : (1 : S) = 0 then 0
  else AzMvPolynomialNew.ofMonomial ⟨⟨1, h⟩, m⟩

/-- Apply `bind₂` to a single monomial. -/
def MonomialNew.bind₂ (f : R → AzMvPolynomialNew n S ord)
    (m : MonomialNew n R ord) : AzMvPolynomialNew n S ord :=
  f m.coeff.val * m.monic.toAzMvPoly

/-- Substitute coefficients in a multivariate polynomial using `f`. -/
def AzMvPolynomialNew.bind₂ (f : R → AzMvPolynomialNew n S ord)
    (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n S ord :=
  p.terms.foldl (init := 0) fun acc m => acc + m.bind₂ f

end Azurite
