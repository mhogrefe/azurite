/-
  Equivalence proof for AzVector negation.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Neg R] {n : Nat}

/-- Negation commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_neg' (v : AzVector R n) :
    (-v).toFn = -v.toFn := AzVector.toFn_neg v

/-- Negation commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_neg (f : Fin n → R) :
    AzVector.ofFn (-f) = -(AzVector.ofFn f) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
