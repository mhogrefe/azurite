import Azurite.BasuPollackRoy.Chapter8.Section8_3.TransitionMatrix

/-!
# BPR Lemma 8.45: `B_{k,j} = T_j B_{j,i}`

In the recurrence setting (`sResP_{i-1}(P,Q)` nonzero of degree `j`, `sResP_{j-1}(P,Q)` nonzero
of degree `k`, and the next subresultant `sResP_{k-1}(P,Q)` nonzero), the cofactor matrix of the
pair `(sResP_{j-1}, sResP_{k-1})` factors through the transition matrix:

  `B_{k,j} = T_j · B_{j,i}`.

Writing `T_j B_{j,i} = [[A,B],[C,D]]`, the top row is `[sResU_{j-1}, sResV_{j-1}]` directly
(`T_j`'s first row is `[0,1]`).  A degree calculation gives `deg C ≤ q-k`, `deg D ≤ p-k`, and
from (8.14) and (8.12) one reads `sResP_{k-1} = C P + D Q`.  The uniqueness of cofactors
(Proposition 8.42(b)) then forces `C = sResU_{k-1}`, `D = sResV_{k-1}`, i.e. the bottom row of
`B_{k,j}`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- **BPR Lemma 8.45.**  `B_{k,j} = T_j B_{j,i}` in the recurrence setting (with `sResP_{k-1}`
    also nonzero, the regime where the cofactor uniqueness of Proposition 8.42(b) applies). -/
theorem cofactorMat_transition (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1) {k : ℕ}
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hkk0 : sResP P Q (k - 1) ≠ 0)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    cofactorMat P Q j k = transMat P Q i j k * cofactorMat P Q i j := by
  have hjq : j ≤ Q.natDegree := by omega
  -- `k < j` since `k = deg sResP_{j-1} ≤ j-1`.
  have hkj : k < j := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  -- `c := s_j t_{i-1} ≠ 0` and `d := s_k t_{j-1} ≠ 0`.
  have hc_ne := sBPR_mul_tBPR_ne_zero P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg
  have hd_ne := sBPR_mul_tBPR_ne_zero P Q hP hQ hpq hq1 hk1 hkj (show j ≤ Q.natDegree + 1 by omega) hk0 hkdeg
  -- `deg(transC) = j - k` from the cleared-denominator recurrence.
  have hspec := transC_spec P Q hP hQ hpq hq1 hj1 hji hiq hk0 hkdeg hk1 hne hdeg
  have hTS : transC P Q i j k * sResP P Q (j - 1)
      = C (sBPR P Q j * tBPR P Q (i - 1)) * sResP P Q (k - 1)
        + C (sBPR P Q k * tBPR P Q (j - 1)) * sResP P Q (i - 1) := by
    rw [hspec]; ring
  have hbig : (C (sBPR P Q k * tBPR P Q (j - 1)) * sResP P Q (i - 1)).natDegree = j := by
    rw [Polynomial.natDegree_C_mul hd_ne, hdeg]
  have hsmall : (C (sBPR P Q j * tBPR P Q (i - 1)) * sResP P Q (k - 1)).natDegree < j := by
    refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C]
    have := Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (show k - 1 ≤ Q.natDegree by omega))
    omega
  have hTS_deg : (transC P Q i j k * sResP P Q (j - 1)).natDegree = j := by
    rw [hTS, Polynomial.natDegree_add_eq_right_of_natDegree_lt (by rw [hbig]; exact hsmall), hbig]
  have htransC_ne : transC P Q i j k ≠ 0 := by
    intro h; rw [h, zero_mul, Polynomial.natDegree_zero] at hTS_deg; omega
  have htransC_deg : (transC P Q i j k).natDegree = j - k := by
    rw [Polynomial.natDegree_mul htransC_ne hk0, hkdeg] at hTS_deg; omega
  -- `C P + D Q = sResP_{k-1}` from (8.13) and the cofactor relations (8.12).
  have hUV : (C (-(sBPR P Q k * tBPR P Q (j - 1)) / (sBPR P Q j * tBPR P Q (i - 1)))
        * sResU P Q (i - 1)
        + C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k * sResU P Q (j - 1)) * P
      + (C (-(sBPR P Q k * tBPR P Q (j - 1)) / (sBPR P Q j * tBPR P Q (i - 1)))
        * sResV P Q (i - 1)
        + C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k * sResV P Q (j - 1)) * Q
      = sResP P Q (k - 1) := by
    rw [sResP_transition P Q hP hQ hpq hq1 hj1 hji hiq hk0 hkdeg hk1 hne hdeg,
      sResP_eq_cofactor P Q hQ hpq (show i - 1 ≤ Q.natDegree by omega),
      sResP_eq_cofactor P Q hQ hpq (show j - 1 ≤ Q.natDegree by omega)]
    ring
  -- Degree bounds `deg C ≤ q-k`, `deg D ≤ p-k`.
  have hU : (C (-(sBPR P Q k * tBPR P Q (j - 1)) / (sBPR P Q j * tBPR P Q (i - 1)))
        * sResU P Q (i - 1)
      + C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k * sResU P Q (j - 1)).natDegree
      ≤ Q.natDegree - (k - 1) - 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C]
      have := sResU_natDegree_le P Q hpq (show i - 1 ≤ Q.natDegree by omega); omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have hsU := sResU_natDegree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega)
      have ht11 : (C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k).natDegree ≤ j - k := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C]; omega
      omega
  have hV : (C (-(sBPR P Q k * tBPR P Q (j - 1)) / (sBPR P Q j * tBPR P Q (i - 1)))
        * sResV P Q (i - 1)
      + C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k * sResV P Q (j - 1)).natDegree
      ≤ P.natDegree - (k - 1) - 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C]
      have := sResV_natDegree_le P Q hpq (show i - 1 ≤ Q.natDegree by omega); omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have hsV := sResV_natDegree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega)
      have ht11 : (C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k).natDegree ≤ j - k := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C]; omega
      omega
  -- Uniqueness (Proposition 8.42(b)) at index `k-1`.
  have hCD := cofactor_unique P Q hP hQ hpq (show k - 1 < Q.natDegree by omega) hkk0 hUV hU hV
  -- Assemble the matrix identity.
  simp only [cofactorMat, transMat, Matrix.mul_fin_two, zero_mul, one_mul, zero_add]
  rw [hCD.1, hCD.2]

end Azurite.BPR.Chapter8
