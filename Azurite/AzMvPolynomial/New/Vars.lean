/-
  Variables occurring in `AzMvPolynomialNew` terms — indexed by `Fin n`.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [Semiring R] {n : ℕ} {ord : MonomialOrder}

/-- The set of variable indices with nonzero exponent in a monic monomial. -/
def MonicMonomialNew.vars (m : MonicMonomialNew n ord) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => m.exponents[i] ≠ 0)

/-- The set of variable indices occurring in a monomial. -/
def MonomialNew.vars (m : MonomialNew n R ord) : Finset (Fin n) :=
  m.monic.vars

/-- The set of variable indices occurring in any term of the polynomial. -/
def AzMvPolynomialNew.vars (p : AzMvPolynomialNew n R ord) : Finset (Fin n) :=
  p.terms.foldl (init := ∅) fun acc m => acc ∪ m.vars

end Azurite
