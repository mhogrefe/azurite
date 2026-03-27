/-
  Equivalence proofs for AzMatrix scalar multiplication.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Scalar multiplication commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_smul [SMul α R] (c : α) (f : Fin m → Fin n → R) :
    c • AzMatrix.ofFn f = AzMatrix.ofFn (fun i j => c • f i j) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
