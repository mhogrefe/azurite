/-
  Equivalence proofs for AzMatrix transpose.

  Links `AzMatrix.transpose` to Mathlib's `Matrix.transpose`.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Data.Matrix.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Transpose commutes with `toFn`: `transpose M` yields
    `fun j i => M.toFn i j`, which is `Mᵀ` in Mathlib. -/
theorem AzMatrix.toFn_transpose' (M : AzMatrix R m n) (j : Fin n) (i : Fin m) :
    M.transpose.toFn j i = M.toFn i j := by
  simp [transpose, toFn, ofFn, get, Vector.get]

/-- Transpose commutes with `ofFn`. -/
theorem AzMatrix.ofFn_transpose (f : Fin m → Fin n → R) :
    (AzMatrix.ofFn f).transpose = AzMatrix.ofFn (fun j i => f i j) := by
  ext j i; simp [transpose, ofFn, get, Vector.get]

end Azurite
