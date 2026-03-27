/-
  Equivalence proofs for AzVector: ofFn injectivity.
-/
import Azurite.AzVector.Basic

namespace Azurite
variable {R : Type _} {n : Nat}

/-- `ofFn` is injective. -/
theorem AzVector.ofFn_injective :
    Function.Injective (AzVector.ofFn (R := R) (n := n)) := by
  intro f g h
  funext i
  have := congrArg (fun v => v.toFn i) h
  simp [AzVector.toFn, AzVector.ofFn, Vector.get] at this
  exact this

end Azurite
