/-
  Negation for AzMvPolynomial.
  Analogous to AzPolynomial/Neg.lean.
-/
import Azurite.AzMvPolynomial.Map

namespace Azurite

variable {R : Type _} [Ring R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Negates an `AzMvPolynomial` by mapping negation over its coefficients. -/
instance instNegAzMvPolynomial : Neg (AzMvPolynomial σ R ord) where
  neg p := AzMvPolynomial.mapZeroInjective (fun x => -x)
    (fun r => ⟨fun hr => neg_eq_zero.mp hr, fun hr => by simp [hr]⟩) p

end Azurite
