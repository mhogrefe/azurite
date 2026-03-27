/-
  Dot product, squared norm for AzVector.
-/
import Azurite.AzVector.Operations

namespace Azurite
variable {R : Type _} {n : Nat}

/-- Dot product of two vectors. -/
def AzVector.dot [Mul R] [Add R] [Zero R] (v w : AzVector R n) : R :=
  (Vector.zipWith (· * ·) v.data w.data).toArray.foldl (· + ·) 0

/-- Squared norm of a vector: `‖v‖² = v · v`. -/
def AzVector.normSq [Mul R] [Add R] [Zero R] (v : AzVector R n) : R :=
  v.dot v

end Azurite
