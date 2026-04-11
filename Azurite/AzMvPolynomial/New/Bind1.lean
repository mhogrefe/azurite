/-
  Variable substitution (bind₁) for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Pow
import Azurite.AzMvPolynomial.New.Mul
import Azurite.AzMvPolynomial.New.SMul
import Azurite.AzMvPolynomial.New.Add

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Auxiliary fold for `MonicMonomialNew.bind₁`. -/
def monicBind₁AuxNew (m : MonicMonomialNew n ord)
    (f : Fin n → AzMvPolynomialNew n R ord) (i : ℕ) (acc : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew n R ord :=
  if h : i < n then
    let e := m.exponents[i]
    monicBind₁AuxNew m f (i + 1) (acc * (f ⟨i, h⟩).pow e)
  else acc
termination_by n - i

/-- Substitute polynomials for variables in a monic monomial. -/
def MonicMonomialNew.bind₁ (m : MonicMonomialNew n ord)
    (f : Fin n → AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  monicBind₁AuxNew m f 0 1

/-- Substitute polynomials for variables in a monomial. -/
def MonomialNew.bind₁ (m : MonomialNew n R ord)
    (f : Fin n → AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  m.coeff.val • m.monic.bind₁ f

/-- Substitute polynomials for variables in a multivariate polynomial. -/
def AzMvPolynomialNew.bind₁ (p : AzMvPolynomialNew n R ord)
    (f : Fin n → AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  p.terms.foldl (init := 0) fun acc m => acc + m.bind₁ f

end Azurite
