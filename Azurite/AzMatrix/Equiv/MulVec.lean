/-
  Equivalence proofs for matrix-vector and vector-matrix multiplication.

  Links `AzMatrix.mulVec` to Mathlib's `dotProduct` (`⬝ᵥ`) and
  `AzMatrix.vecMul` to Mathlib's `dotProduct` (`⬝ᵥ`).
-/
import Azurite.AzMatrix.MulVec
import Azurite.AzVector.Equiv.Dot
import Azurite.AzMatrix.Equiv.RowCol
import Mathlib.Data.Matrix.Mul

namespace Azurite
variable {R : Type _} [CommSemiring R] {m n : Nat}

/-! ### Function-level toFn_ofFn helpers -/

omit [CommSemiring R] in
private theorem AzVector.toFn_ofFn' (f : Fin n → R) :
    (AzVector.ofFn f).toFn = f := by ext i; simp [AzVector.toFn_ofFn]

omit [CommSemiring R] in
private theorem AzMatrix.toFn_ofFn' (f : Fin m → Fin n → R) :
    (AzMatrix.ofFn f).toFn = f := by ext i j; simp

/-! ### mulVec -/

/-- `mulVec` commutes with `toFn`:
    `(M.mulVec v).toFn i = (M.toFn i) ⬝ᵥ v.toFn`. -/
@[simp]
theorem AzMatrix.toFn_mulVec (M : AzMatrix R m n) (v : AzVector R n) (i : Fin m) :
    (M.mulVec v).toFn i = M.toFn i ⬝ᵥ v.toFn := by
  unfold mulVec; simp only [AzVector.toFn_ofFn]
  rw [AzVector.dot_eq_dotProduct]; unfold dotProduct
  apply Finset.sum_congr rfl; intro j _
  simp [row, AzVector.toFn, AzMatrix.toFn, Vector.get]

/-- `mulVec` commutes with `ofFn`. -/
theorem AzMatrix.ofFn_mulVec (f : Fin m → Fin n → R) (g : Fin n → R) :
    (AzMatrix.ofFn f).mulVec (AzVector.ofFn g) =
      AzVector.ofFn (fun i => f i ⬝ᵥ g) := by
  apply AzVector.toFn_injective; funext i
  rw [toFn_mulVec, AzMatrix.toFn_ofFn', AzVector.toFn_ofFn']; simp

/-! ### vecMul -/

/-- `vecMul` commutes with `toFn`:
    `(M.vecMul v).toFn j = v.toFn ⬝ᵥ (fun i => M.toFn i j)`. -/
@[simp]
theorem AzMatrix.toFn_vecMul (v : AzVector R m) (M : AzMatrix R m n) (j : Fin n) :
    (M.vecMul v).toFn j = v.toFn ⬝ᵥ (fun i => M.toFn i j) := by
  unfold vecMul; simp only [AzVector.toFn_ofFn]
  rw [AzVector.dot_eq_dotProduct]; unfold dotProduct
  apply Finset.sum_congr rfl; intro i _
  simp [col, AzVector.toFn, AzMatrix.toFn, AzMatrix.get, Vector.get]

/-- `vecMul` commutes with `ofFn`. -/
theorem AzMatrix.ofFn_vecMul (g : Fin m → R) (f : Fin m → Fin n → R) :
    (AzMatrix.ofFn f).vecMul (AzVector.ofFn g) =
      AzVector.ofFn (fun j => g ⬝ᵥ (fun i => f i j)) := by
  apply AzVector.toFn_injective; funext j
  rw [toFn_vecMul, AzVector.toFn_ofFn', AzMatrix.toFn_ofFn']; simp

/-! ### Guards -/

private def testM : AzMatrix Int 2 2 := AzMatrix.ofLists [[1, 2], [3, 4]]
private def testV : AzVector Int 2 := AzVector.ofList [5, 6]

-- [1 2; 3 4] * [5; 6] = [17; 39]
#guard (testM.mulVec testV).data.toList = [17, 39]

-- [5; 6] * [1 2; 3 4] = [23; 34]
#guard (testM.vecMul testV).data.toList = [23, 34]

end Azurite
