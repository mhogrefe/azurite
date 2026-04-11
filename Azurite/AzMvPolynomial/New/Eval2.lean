/-
  Generic evaluation (eval₂, aeval) for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Evaluate a monomial via a coefficient embedding `φ : R →+* S`. -/
def MonomialNew.eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (f : Fin n → S) (m : MonomialNew n R ord) : S :=
  φ m.coeff.val * m.monic.eval f

/-- Evaluate a multivariate polynomial at values `f : Fin n → S` via
    coefficient embedding `φ : R →+* S`. -/
def AzMvPolynomialNew.eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (f : Fin n → S) (p : AzMvPolynomialNew n R ord) : S :=
  p.terms.foldl (init := 0) fun acc m => acc + m.eval₂ φ f

/-- Evaluate a multivariate polynomial as an `R`-algebra homomorphism. -/
def AzMvPolynomialNew.aeval {S : Type _} [CommSemiring S] [Algebra R S]
    (f : Fin n → S) (p : AzMvPolynomialNew n R ord) : S :=
  p.eval₂ (algebraMap R S) f

end Azurite
