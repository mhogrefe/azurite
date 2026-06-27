import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_42
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_35

/-!
# BPR Lemma 8.43: `det(B_{j,i}) = s_j · t_{i-1}`

In the setting of the Structure Theorem 8.34 (`sResP_{i-1}(P,Q)` nonzero of degree `j`, with
the cofactor indices `i-1, j-1 ≤ q`), the determinant of the cofactor matrix `B_{j,i}`
(Notation before equation (8.12)) is the constant `s_j · t_{i-1}`, where `s_j = sRes_j(P,Q)`
and `t_{i-1} = lcof(sResP_{i-1}(P,Q))`.

The proof eliminates `Q` from the system (8.12): multiplying the two cofactor relations
`sResP_{i-1} = sResU_{i-1}P + sResV_{i-1}Q`, `sResP_{j-1} = sResU_{j-1}P + sResV_{j-1}Q` by
`sResV_{j-1}`, `sResV_{i-1}` and subtracting gives
  `det(B_{j,i}) · P = sResV_{j-1}·sResP_{i-1} − sResV_{i-1}·sResP_{j-1}`.        (8.43)
The right-hand side has degree `p`: the term `sResV_{j-1}·sResP_{i-1}` has degree
`(p-j) + j = p` with leading coefficient `(a_p s_j)·t_{i-1}` (using `deg sResV_{j-1} = p-j` and
`lcof sResV_{j-1} = a_p s_j` from Proposition 8.42(c)), while the term `sResV_{i-1}·sResP_{j-1}`
has degree `≤ (p-i) + (j-1) < p`.  Hence `det(B_{j,i})` is constant; comparing leading
coefficients and cancelling `a_p ≠ 0` gives `det(B_{j,i}) = s_j t_{i-1}`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- **BPR Lemma 8.43.**  If `sResP_{i-1}(P,Q)` is nonzero of degree `j` (in the Structure
    Theorem setting, with `1 ≤ j < i ≤ q+1`), then `det(B_{j,i}) = s_j · t_{i-1}`, where
    `s_j = sRes_j(P,Q)` (`= sBPR`) and `t_{i-1} = lcof(sResP_{i-1}(P,Q))` (`= tBPR (i-1)`). -/
theorem det_cofactorMat (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    (cofactorMat P Q i j).det = C (sBPR P Q j * tBPR P Q (i - 1)) := by
  have hjq : j ≤ Q.natDegree := by omega
  -- The two cofactor relations of (8.12), and the elimination identity (8.43).
  have hcof_i : sResP P Q (i - 1) = sResU P Q (i - 1) * P + sResV P Q (i - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq (by omega)
  have hcof_j : sResP P Q (j - 1) = sResU P Q (j - 1) * P + sResV P Q (j - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq (by omega)
  have hdet : (cofactorMat P Q i j).det
      = sResU P Q (i - 1) * sResV P Q (j - 1) - sResV P Q (i - 1) * sResU P Q (j - 1) := by
    rw [cofactorMat, Matrix.det_fin_two_of]
  have hElim : (cofactorMat P Q i j).det * P
      = sResV P Q (j - 1) * sResP P Q (i - 1) - sResV P Q (i - 1) * sResP P Q (j - 1) := by
    rw [hdet, hcof_i, hcof_j]; ring
  -- Structure Theorem 8.34: the realized degree `j` is non-defective, so `sRes_j ≠ 0`.
  obtain ⟨hndj, hsj0⟩ := sResP_natDegree_realized P Q hP hQ hpq hq1 hne
  rw [hdeg] at hndj hsj0
  have hnd_j : IsNonDefective P Q j := by
    rw [IsNonDefective, Polynomial.degree_eq_natDegree hsj0, hndj]
  have hsRes_ne : Azurite.BPR.Chapter4.sRes P Q j ≠ 0 :=
    (isNonDefective_iff_sRes_ne_zero P Q hpq hjq).mp hnd_j
  -- Proposition 8.42(c): degree and leading coefficient of `sResV_{j-1}`.
  obtain ⟨hVjd, hVjl⟩ := sResV_sub_one_natDegree P Q hP hpq hj1 hjq hsRes_ne
  have hVj_ne : sResV P Q (j - 1) ≠ 0 := fun h =>
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hP) hsRes_ne) (by rw [← hVjl, h, leadingCoeff_zero])
  -- Degree bounds on the small factors.
  have hVid : (sResV P Q (i - 1)).natDegree ≤ P.natDegree - 1 - (i - 1) :=
    sResV_natDegree_le P Q hpq (by omega)
  have hPjd : (sResP P Q (j - 1)).natDegree ≤ j - 1 :=
    Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
  -- The leading term `sResV_{j-1}·sResP_{i-1}`: degree `p`, lcof `a_p·s_j·t_{i-1}`.
  have ht1d : (sResV P Q (j - 1) * sResP P Q (i - 1)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_mul hVj_ne hne, hVjd, hdeg]; omega
  have ht1l : (sResV P Q (j - 1) * sResP P Q (i - 1)).leadingCoeff
      = P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q j * (sResP P Q (i - 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, hVjl]
  -- The low term `sResV_{i-1}·sResP_{j-1}`: degree `< p`.
  have ht2d : (sResV P Q (i - 1) * sResP P Q (j - 1)).natDegree < P.natDegree := by
    rcases eq_or_ne (sResV P Q (i - 1)) 0 with h | h
    · rw [h, zero_mul, Polynomial.natDegree_zero]; omega
    · rcases eq_or_ne (sResP P Q (j - 1)) 0 with h' | h'
      · rw [h', mul_zero, Polynomial.natDegree_zero]; omega
      · rw [Polynomial.natDegree_mul h h']; omega
  -- Hence the RHS of (8.43) has degree `p` and leading coefficient `a_p·s_j·t_{i-1}`.
  have hRHSd : (sResV P Q (j - 1) * sResP P Q (i - 1)
      - sResV P Q (i - 1) * sResP P Q (j - 1)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [ht1d]; exact ht2d), ht1d]
  have hRHSl : (sResV P Q (j - 1) * sResP P Q (i - 1)
      - sResV P Q (i - 1) * sResP P Q (j - 1)).leadingCoeff
      = (sResV P Q (j - 1) * sResP P Q (i - 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff, hRHSd, Polynomial.coeff_sub,
      Polynomial.coeff_eq_zero_of_natDegree_lt ht2d, sub_zero, Polynomial.leadingCoeff, ht1d]
  -- `det(B) ≠ 0` (RHS is nonzero of degree `p`) and `det(B)` is constant (`natDegree 0`).
  have hRHS_ne : sResV P Q (j - 1) * sResP P Q (i - 1)
      - sResV P Q (i - 1) * sResP P Q (j - 1) ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hRHSd; omega
  have hdB_ne : (cofactorMat P Q i j).det ≠ 0 := fun h => by
    rw [h, zero_mul] at hElim; exact hRHS_ne hElim.symm
  have hdBnd : (cofactorMat P Q i j).det.natDegree = 0 := by
    have hmul : ((cofactorMat P Q i j).det * P).natDegree = P.natDegree := by
      rw [hElim]; exact hRHSd
    rw [Polynomial.natDegree_mul hdB_ne hP] at hmul; omega
  -- Compare leading coefficients of (8.43) and cancel `a_p`.
  have ha_ne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hlceq : (cofactorMat P Q i j).det.leadingCoeff * P.leadingCoeff
      = P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q j * (sResP P Q (i - 1)).leadingCoeff := by
    have h1 : ((cofactorMat P Q i j).det * P).leadingCoeff
        = (sResV P Q (j - 1) * sResP P Q (i - 1)
            - sResV P Q (i - 1) * sResP P Q (j - 1)).leadingCoeff := by rw [hElim]
    rw [Polynomial.leadingCoeff_mul] at h1
    rw [h1, hRHSl, ht1l]
  have hval : (cofactorMat P Q i j).det.leadingCoeff
      = Azurite.BPR.Chapter4.sRes P Q j * (sResP P Q (i - 1)).leadingCoeff :=
    mul_right_cancel₀ ha_ne (by rw [hlceq]; ring)
  -- `s_j t_{i-1} = sRes_j · lcof(sResP_{i-1})` (both `j, i-1 ≠ p`).
  have hc_eq : sBPR P Q j * tBPR P Q (i - 1)
      = Azurite.BPR.Chapter4.sRes P Q j * (sResP P Q (i - 1)).leadingCoeff := by
    rw [sBPR, if_neg (show j ≠ P.natDegree by omega),
      tBPR, if_neg (show i - 1 ≠ P.natDegree by omega)]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdBnd, hc_eq]
  congr 1
  rw [show (cofactorMat P Q i j).det.coeff 0 = (cofactorMat P Q i j).det.leadingCoeff from by
    rw [Polynomial.leadingCoeff, hdBnd]]
  exact hval

end Azurite.BPR.Chapter8
