/-
  Negation for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Map

namespace Azurite

variable {R : Type _} [Ring R]
         {n : ℕ} {ord : MonomialOrder}

/-- Negates an `AzMvPolynomialNew` by mapping negation over its coefficients. -/
instance instNegAzMvPolynomialNew : Neg (AzMvPolynomialNew n R ord) where
  neg p := AzMvPolynomialNew.mapZeroInjective (fun x => -x)
    (fun r => ⟨fun hr => neg_eq_zero.mp hr, fun hr => by simp [hr]⟩) p

end Azurite
