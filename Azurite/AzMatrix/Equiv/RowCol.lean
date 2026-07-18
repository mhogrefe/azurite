/-
  Equivalence proofs for AzMatrix row and column access.
-/
import Azurite.AzMatrix.RowCol
import Azurite.AzVector.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Row extraction commutes with `toFn`: the `i`-th row of `M`
    is `M.toFn i` as a function `Fin n → R`. -/
theorem AzMatrix.toFn_row (M : AzMatrix R m n) (i : Fin m) :
    (M.row i).toFn = M.toFn i := by
  ext j; simp [row, AzVector.toFn, AzMatrix.toFn, Vector.get]

/-- Column extraction commutes with `toFn`: the `j`-th column of `M`
    is `fun i => M.toFn i j` as a function `Fin m → R`. -/
theorem AzMatrix.toFn_col (M : AzMatrix R m n) (j : Fin n) :
    (M.col j).toFn = fun i => M.toFn i j := by
  ext i; simp [col, AzVector.toFn, AzMatrix.toFn, get, Vector.get]
  rfl

/-- `ofRows` commutes with `toFn`. -/
theorem AzMatrix.toFn_ofRows (rows : Vector (AzVector R n) m) (i : Fin m) (j : Fin n) :
    (AzMatrix.ofRows rows).toFn i j = (rows.get i).data.get j := by
  simp [ofRows, AzMatrix.toFn, Vector.get, Vector.map]
  rfl

/-- `ofCols` commutes with `toFn`. -/
theorem AzMatrix.toFn_ofCols (cols : Vector (AzVector R m) n) (i : Fin m) (j : Fin n) :
    (AzMatrix.ofCols cols).toFn i j = (cols.get j).data.get i := by
  simp [ofCols, AzMatrix.toFn, AzMatrix.ofFn, Vector.get]
  rfl

end Azurite
