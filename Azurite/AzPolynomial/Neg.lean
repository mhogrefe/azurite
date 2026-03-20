import Azurite.AzPolynomial.Basic


variable {R : Type _} [Ring R]

namespace Azurite
namespace AzPolynomial

/-- Negates a `AzPolynomial R` by mapping negation over its coefficients. -/
instance instNegAzPolynomial : Neg (AzPolynomial R) where
  neg p := mapZeroInjective (fun x => -x) (fun r => ⟨fun hr => neg_eq_zero.mp hr, fun hr => by simp [hr]⟩) p


end AzPolynomial
end Azurite
