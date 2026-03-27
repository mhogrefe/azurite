/-
  Equivalence proofs for AzMatrix multiplication.

  Core proofs are on `mulBasecase`; `mul` delegates to them.
  This makes it easy to swap the algorithm behind `mul` later.
-/
import Azurite.AzMatrix.Mul
import Azurite.AzVector.Equiv.Dot
import Azurite.AzMatrix.Equiv.RowCol
import Mathlib.Data.Matrix.Mul

namespace Azurite
variable {R : Type _} [CommSemiring R] {m n p : Nat}

omit [CommSemiring R] in
private theorem AzVector.toFn_ofFn' (f : Fin n → R) :
    (AzVector.ofFn f).toFn = f := by ext i; simp [AzVector.toFn_ofFn]

omit [CommSemiring R] in
private theorem AzMatrix.toFn_ofFn' (f : Fin m → Fin n → R) :
    (AzMatrix.ofFn f).toFn = f := by ext i j; simp

/-! ### mulBasecase proofs -/

/-- `mulBasecase` commutes with `toFn`. -/
@[simp]
theorem AzMatrix.toFn_mulBasecase (A : AzMatrix R m n) (B : AzMatrix R n p)
    (i : Fin m) (k : Fin p) :
    (A.mulBasecase B).toFn i k = ∑ j, A.toFn i j * B.toFn j k := by
  simp only [mulBasecase, AzMatrix.toFn_ofFn]
  rw [AzVector.dot_eq_dotProduct]
  unfold dotProduct
  apply Finset.sum_congr rfl; intro j _
  simp [row, col, AzVector.toFn, AzMatrix.toFn, AzMatrix.get, Vector.get]

/-- `mulBasecase` commutes with `ofFn`. -/
theorem AzMatrix.ofFn_mulBasecase (f : Fin m → Fin n → R) (g : Fin n → Fin p → R) :
    (AzMatrix.ofFn f).mulBasecase (AzMatrix.ofFn g) =
      AzMatrix.ofFn (fun i k => ∑ j, f i j * g j k) := by
  apply AzMatrix.toFn_injective; funext i k
  rw [toFn_mulBasecase, AzMatrix.toFn_ofFn', AzMatrix.toFn_ofFn']; simp

/-! ### mul proofs (delegate to mulBasecase) -/

/-- `mul` commutes with `toFn`:
    `(A * B).toFn i k = ∑ j, A.toFn i j * B.toFn j k`. -/
@[simp]
theorem AzMatrix.toFn_mul (A : AzMatrix R m n) (B : AzMatrix R n p) (i : Fin m) (k : Fin p) :
    (A * B).toFn i k = ∑ j, A.toFn i j * B.toFn j k :=
  toFn_mulBasecase A B i k

/-- `mul` commutes with `ofFn`. -/
theorem AzMatrix.ofFn_mul (f : Fin m → Fin n → R) (g : Fin n → Fin p → R) :
    AzMatrix.ofFn f * AzMatrix.ofFn g =
      AzMatrix.ofFn (fun i k => ∑ j, f i j * g j k) :=
  ofFn_mulBasecase f g

/-! ### Guards -/

private def testA : AzMatrix Int 2 2 := AzMatrix.ofLists [[1, 2], [3, 4]]
private def testB : AzMatrix Int 2 2 := AzMatrix.ofLists [[5, 6], [7, 8]]

-- [1 2; 3 4] * [5 6; 7 8] = [19 22; 43 50]
#guard (testA * testB).data.toList.map Vector.toList = [[19, 22], [43, 50]]

end Azurite
