/-
  Negation for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Map

namespace Azurite

variable {R : Type _} [Ring R]
         {n : ℕ} {ord : MonomialOrder}

/-- Negates an `AzMvPolynomial` by mapping negation over its coefficients. -/
instance instNegAzMvPolynomial : Neg (AzMvPolynomial n R ord) where
  neg p := AzMvPolynomial.mapZeroInjective (fun x => -x)
    (fun r => ⟨fun hr => neg_eq_zero.mp hr, fun hr => by simp [hr]⟩) p

end Azurite
