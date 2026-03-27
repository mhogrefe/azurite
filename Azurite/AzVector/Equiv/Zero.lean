/-
  Equivalence proof for AzVector zero.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Zero R] {n : Nat}

/-- Zero commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_zero' :
    (0 : AzVector R n).toFn = 0 := AzVector.toFn_zero

/-- Zero commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_zero :
    AzVector.ofFn (0 : Fin n → R) = (0 : AzVector R n) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
