import Azurite.BasuPollackRoy.Chapter8.Section8_3.Lemma_8_43
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_38

/-!
# BPR Corollary 8.44: the inverse of `B_{j,i}`

In the setting of Lemma 8.43 (`sResP_{i-1}(P,Q)` nonzero of degree `j`), the cofactor matrix
`B_{j,i}` has determinant `s_j t_{i-1} ≠ 0`, so `C(s_j t_{i-1})` is a unit in `K[X]` and
`B_{j,i}` is invertible with

  `B_{j,i}^{-1} = (1 / (s_j t_{i-1})) · [ sResV_{j-1}  -sResV_{i-1};
                                          -sResU_{j-1}   sResU_{i-1} ]`.

The matrix on the right is the adjugate of `B_{j,i}`; it has entries in `D[X]`, so
`s_j t_{i-1} · B_{j,i}^{-1} ∈ D[X]` (it equals that explicit polynomial matrix).
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- The adjugate of `B_{j,i}` is the explicit polynomial matrix
    `[ sResV_{j-1}, -sResV_{i-1}; -sResU_{j-1}, sResU_{i-1} ]` (the `2×2` adjugate of
    `[ sResU_{i-1}, sResV_{i-1}; sResU_{j-1}, sResV_{j-1} ]`). -/
theorem adjugate_cofactorMat (P Q : K[X]) (i j : ℕ) :
    Matrix.adjugate (cofactorMat P Q i j)
      = !![sResV P Q (j - 1), -sResV P Q (i - 1); -sResU P Q (j - 1), sResU P Q (i - 1)] := by
  rw [cofactorMat, Matrix.adjugate_fin_two_of]

/-- In the Lemma 8.43 setting, `s_j · t_{i-1} ≠ 0`. -/
theorem sBPR_mul_tBPR_ne_zero (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    sBPR P Q j * tBPR P Q (i - 1) ≠ 0 := by
  obtain ⟨hndj, hsj0⟩ := sResP_natDegree_realized P Q hP hQ hpq hq1 hne
  rw [hdeg] at hndj hsj0
  exact mul_ne_zero (sBPR_ne_of_nondef P Q hpq (by omega) hsj0 hndj)
    (tBPR_ne_of_ne P Q (by omega) hne)

/-- **BPR Corollary 8.44.**  If `sResP_{i-1}(P,Q)` is nonzero of degree `j` (with
    `1 ≤ j < i ≤ q+1`), then `B_{j,i}` is invertible with
    `B_{j,i}^{-1} = (1/(s_j t_{i-1})) · [ sResV_{j-1}, -sResV_{i-1}; -sResU_{j-1}, sResU_{i-1} ]`. -/
theorem cofactorMat_inv (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    (cofactorMat P Q i j)⁻¹
      = C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) •
          !![sResV P Q (j - 1), -sResV P Q (i - 1); -sResU P Q (j - 1), sResU P Q (i - 1)] := by
  have hc_ne := sBPR_mul_tBPR_ne_zero P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg
  have hdet := det_cofactorMat P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, ← adjugate_cofactorMat P Q i j, Matrix.mul_adjugate, hdet, smul_smul,
    ← Polynomial.C_mul, inv_mul_cancel₀ hc_ne, Polynomial.C_1, one_smul]

/-- **BPR Corollary 8.44, integrality part.**  `s_j t_{i-1} · B_{j,i}^{-1} ∈ D[X]`: it equals
    the explicit polynomial adjugate matrix. -/
theorem smul_cofactorMat_inv (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    C (sBPR P Q j * tBPR P Q (i - 1)) • (cofactorMat P Q i j)⁻¹
      = !![sResV P Q (j - 1), -sResV P Q (i - 1); -sResU P Q (j - 1), sResU P Q (i - 1)] := by
  have hc_ne := sBPR_mul_tBPR_ne_zero P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg
  rw [cofactorMat_inv P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg, smul_smul, ← Polynomial.C_mul,
    mul_inv_cancel₀ hc_ne, Polynomial.C_1, one_smul]

end Azurite.BPR.Chapter8
