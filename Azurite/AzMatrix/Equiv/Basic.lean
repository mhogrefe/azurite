/-
  Equivalence proofs for AzMatrix: ofFn injectivity.
-/
import Azurite.AzMatrix.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- `ofFn` is injective. -/
theorem AzMatrix.ofFn_injective :
    Function.Injective (AzMatrix.ofFn (R := R) (m := m) (n := n)) := by
  intro f g h
  funext i j
  have := congrArg (fun M => M.toFn i j) h
  simp [AzMatrix.toFn, AzMatrix.ofFn, Vector.get] at this
  exact this

end Azurite
