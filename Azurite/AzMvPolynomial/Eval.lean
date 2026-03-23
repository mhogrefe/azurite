/-
  Evaluation of multivariate polynomials.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open MonomialOrder MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- Evaluate an `AzMvPolynomial` at a point given by `f : σ → R`.
    Sums the evaluation of each monomial term. -/
def AzMvPolynomial.eval (p : AzMvPolynomial σ R ord) (f : σ → R) : R :=
  p.terms.foldl (fun acc m => acc + m.eval f) 0

end Azurite
