/-
  Matrix multiplication for AzMatrix.
  `mulBasecase` is the naive O(m·n·p) algorithm.
  `mul` delegates to `mulBasecase`.
-/
import Azurite.AzMatrix.MulVec

namespace Azurite
variable {R : Type _} {m n p : Nat}

/-- Naive O(m·n·p) matrix multiplication via row-column dot products. -/
def AzMatrix.mulBasecase [Mul R] [Add R] [Zero R]
    (A : AzMatrix R m n) (B : AzMatrix R n p) : AzMatrix R m p :=
  AzMatrix.ofFn (fun i k => (A.row i).dot (B.col k))

/-- Matrix multiplication, delegating to the basecase. -/
def AzMatrix.mul [Mul R] [Add R] [Zero R]
    (A : AzMatrix R m n) (B : AzMatrix R n p) : AzMatrix R m p :=
  A.mulBasecase B

instance instAzMatrixHMul [Mul R] [Add R] [Zero R] : HMul (AzMatrix R m n) (AzMatrix R n p) (AzMatrix R m p) :=
  ⟨AzMatrix.mul⟩

end Azurite
