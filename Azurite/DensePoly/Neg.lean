import Azurite.DensePoly.Basic


variable {R : Type _} [Ring R]

namespace Azurite
namespace DensePoly

/-- Negates a `DensePoly R` by mapping negation over its coefficients. -/
instance instNegDensePoly : Neg (DensePoly R) where
  neg p := mapZeroInjective (fun x => -x) (fun r => ⟨fun hr => neg_eq_zero.mp hr, fun hr => by simp [hr]⟩) p


end DensePoly
end Azurite
