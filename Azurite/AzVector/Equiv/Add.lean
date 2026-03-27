/-
  Equivalence proof for AzVector addition.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Add R] {n : Nat}

/-- Addition commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_add' (v w : AzVector R n) :
    (v + w).toFn = v.toFn + w.toFn := AzVector.toFn_add v w

/-- Addition commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_add (f g : Fin n → R) :
    AzVector.ofFn (f + g) = AzVector.ofFn f + AzVector.ofFn g := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
