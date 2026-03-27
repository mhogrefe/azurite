/-
  Equivalence proof for AzVector subtraction.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Sub R] {n : Nat}

/-- Subtraction commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_sub' (v w : AzVector R n) :
    (v - w).toFn = v.toFn - w.toFn := AzVector.toFn_sub v w

/-- Subtraction commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_sub (f g : Fin n → R) :
    AzVector.ofFn (f - g) = AzVector.ofFn f - AzVector.ofFn g := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
