/-
  Equivalence proofs for AzMatrix zero.
-/
import Azurite.AzMatrix.Operations

namespace Azurite
variable {R : Type _} [Zero R] {m n : Nat}

/-- Zero commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_zero :
    AzMatrix.ofFn (fun (_ : Fin m) (_ : Fin n) => (0 : R)) = (0 : AzMatrix R m n) := rfl

end Azurite
