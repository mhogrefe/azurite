/-
  Generic evaluation (eval₂, aeval) for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Basic
import Mathlib.Algebra.Algebra.Basic

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Evaluate a monomial via a coefficient embedding `φ : R →+* S`. -/
def Monomial.eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (f : Fin n → S) (m : Monomial n R ord) : S :=
  φ m.coeff.val * m.monic.eval f

/-- Evaluate a multivariate polynomial at values `f : Fin n → S` via
    coefficient embedding `φ : R →+* S`. -/
def AzMvPolynomial.eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (f : Fin n → S) (p : AzMvPolynomial n R ord) : S :=
  p.terms.foldl (init := 0) fun acc m => acc + m.eval₂ φ f

/-- Evaluate a multivariate polynomial as an `R`-algebra homomorphism. -/
def AzMvPolynomial.aeval {S : Type _} [CommSemiring S] [Algebra R S]
    (f : Fin n → S) (p : AzMvPolynomial n R ord) : S :=
  p.eval₂ (algebraMap R S) f

end Azurite
