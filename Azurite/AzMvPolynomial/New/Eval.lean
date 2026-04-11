/-
  Evaluation for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite

open MonomialOrder MonicMonomialNew MonomialNew

variable {R : Type _} [CommSemiring R] {n : ℕ} {ord : MonomialOrder}

/-- Evaluate an `AzMvPolynomialNew` at a point given by `f : Fin n → R`. -/
def AzMvPolynomialNew.eval (p : AzMvPolynomialNew n R ord) (f : Fin n → R) : R :=
  p.terms.foldl (fun acc m => acc + m.eval f) 0

end Azurite
