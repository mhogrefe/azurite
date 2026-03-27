/-
  Equivalence proofs for AzVector cross product.

  Links `AzVector.cross` to Mathlib's `crossProduct` bilinear map.
-/
import Azurite.AzVector.Cross
import Azurite.AzVector.Operations
import Mathlib.LinearAlgebra.CrossProduct

namespace Azurite
variable {R : Type _} [CommRing R]

/-- Cross product commutes with `toFn`, yielding Mathlib's `crossProduct`. -/
theorem AzVector.toFn_cross (v w : AzVector R 3) :
    (v.cross w).toFn = (crossProduct v.toFn) w.toFn := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => simp [cross, crossProduct, AzVector.toFn, Vector.get, Matrix.cons_val_zero]
  | 1, _ => simp [cross, crossProduct, AzVector.toFn, Vector.get, Matrix.cons_val_zero,
                   Matrix.cons_val_one]
  | 2, _ => simp [cross, crossProduct, AzVector.toFn, Vector.get]

/-- Cross product commutes with `ofFn`. -/
theorem AzVector.ofFn_cross (f g : Fin 3 → R) :
    (AzVector.ofFn f).cross (AzVector.ofFn g) = AzVector.ofFn ((crossProduct f) g) := by
  apply AzVector.toFn_injective
  rw [toFn_cross]
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => simp [crossProduct, AzVector.toFn, AzVector.ofFn, Vector.get, Matrix.cons_val_zero]
  | 1, _ => simp [crossProduct, AzVector.toFn, AzVector.ofFn, Vector.get, Matrix.cons_val_zero,
                   Matrix.cons_val_one]
  | 2, _ => simp [crossProduct, AzVector.toFn, AzVector.ofFn, Vector.get]

end Azurite
