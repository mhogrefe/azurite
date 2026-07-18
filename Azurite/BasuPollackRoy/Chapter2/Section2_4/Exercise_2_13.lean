import Azurite.BasuPollackRoy.Chapter2.Section2_4.Notation_2_71
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# BPR Exercise 2.13: `Mₛ` is invertible

The matrices `Mₛ` (Notation 2.71) have entries in `SignType`, which is not
a ring, so "invertible" is interpreted over a field: we cast `Mₛ` to a
rational matrix `signMatrixQ s` (entries `SignType → ℚ`) and show it is a
unit.

The proof is by induction on `s`. Since `M_{s+1} = Mₛ ⊗ M₁`, the
determinant multiplies as
`det(M_{s+1}) = det(Mₛ)^3 · det(M₁)^{3^s}` (`Matrix.det_kronecker`, the
reindexing to flat indices not affecting the determinant). The base
`det(M₁) = 2 ≠ 0`, so `det(Mₛ) ≠ 0` for all `s`, hence `Mₛ` is invertible.
-/

namespace Azurite.BPR

open scoped Kronecker

/-- `Mₛ` as a rational matrix (entries cast `SignType → ℚ`). -/
def signMatrixQ (s : Nat) : Matrix (Fin (3 ^ s)) (Fin (3 ^ s)) ℚ :=
  Matrix.map (Matrix.of (signMatrix s).toFn) (fun x : SignType => (x : ℚ))

/-- The base matrix `M₁` over `ℚ`. -/
def baseQ : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.map (Matrix.of exampleM.toFn) (fun x : SignType => (x : ℚ))

/-- `M_{s+1}` over `ℚ` is `Mₛ ⊗ M₁` reindexed to flat indices. -/
theorem signMatrixQ_succ (s : Nat) :
    signMatrixQ (s + 1) =
      Matrix.reindex (finProdFinEquiv.trans (finCongr (by ring)))
        (finProdFinEquiv.trans (finCongr (by ring)))
        (signMatrixQ s ⊗ₖ baseQ) := by
  ext i j
  simp only [signMatrixQ, signMatrix, baseQ, Matrix.map_apply, Matrix.of_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.symm_trans_apply, finCongr_symm, finCongr_apply]
  erw [AzMatrix.toFn_kronecker_apply, SignType.coe_mul]
  simp only [finProdFinEquiv_symm_apply]
  rfl

/-- `det(M₁) = 2`. -/
theorem baseQ_det : baseQ.det = 2 := by
  have hb : baseQ = !![(1 : ℚ), 1, 1; 0, 1, -1; 0, 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hb]
  simp [Matrix.det_fin_three]; norm_num

/-- The determinant of `Mₛ` (over `ℚ`) is nonzero, by induction on `s`. -/
theorem signMatrixQ_det_ne_zero (s : Nat) : (signMatrixQ s).det ≠ 0 := by
  induction s with
  | zero =>
    rw [Matrix.det_fin_one]
    decide
  | succ s ih =>
    have hbase : baseQ.det ≠ 0 := by rw [baseQ_det]; norm_num
    rw [signMatrixQ_succ]
    erw [Matrix.det_reindex_self]
    rw [Matrix.det_kronecker, Fintype.card_fin, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ ih) (pow_ne_zero _ hbase)

/-- **BPR Exercise 2.13.** `Mₛ` is invertible (over `ℚ`). -/
theorem signMatrix_isUnit (s : Nat) : IsUnit (signMatrixQ s) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (signMatrixQ_det_ne_zero s))

end Azurite.BPR
