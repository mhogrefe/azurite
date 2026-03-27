/-
  Equivalence proofs for AzMatrix negation.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Neg R] {m n : Nat}

/-- Negation commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_neg (f : Fin m → Fin n → R) :
    -(AzMatrix.ofFn f) = AzMatrix.ofFn (fun i j => -(f i j)) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
