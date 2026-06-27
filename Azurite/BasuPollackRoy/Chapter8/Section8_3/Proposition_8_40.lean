import Azurite.BasuPollackRoy.Chapter8.Section8_3.TransitionMatrix

/-!
# BPR Proposition 8.40: `C_{k-1} ∈ D[X]`

Defining `C_{k-1}` as the Euclidean quotient of `s_k t_{j-1} sResP_{i-1}(P,Q)` by
`sResP_{j-1}(P,Q)` (this is `transC`, Notation before equation (8.13)), we show

  `C_{k-1} = sResU_{i-1} sResV_{k-1} − sResV_{i-1} sResU_{k-1}`,

an explicit combination of the cofactor determinants `sResU`, `sResV ∈ D[X]`; in particular
`C_{k-1} ∈ D[X]` (no division into the fraction field is needed).

The proof (BPR's, via Lemma 8.45 / Corollary 8.44) is captured here directly: writing
`X := sResU_{i-1} sResV_{k-1} − sResV_{i-1} sResU_{k-1}`, the determinant identities
`C(s_j t_{i-1}) = det B_{j,i}` and `C(s_k t_{j-1}) = det B_{k,j}` (Lemma 8.43) make
`X · sResP_{j-1} = s_j t_{i-1}·sResP_{k-1} + s_k t_{j-1}·sResP_{i-1}` a ring identity in the
cofactors; this is exactly the cleared-denominator recurrence satisfied by
`C_{k-1} · sResP_{j-1}`, so `C_{k-1} = X` after cancelling `sResP_{j-1} ≠ 0`.

(BPR's printed final formula carries a sign slip; the value matching their own intermediate
line — and the determinant computation — is the one above.)
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- **BPR Proposition 8.40.**  `C_{k-1} = sResU_{i-1} sResV_{k-1} − sResV_{i-1} sResU_{k-1}`,
    hence `C_{k-1} ∈ D[X]`. -/
theorem transC_eq_cofactors (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1) {k : ℕ}
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    transC P Q i j k
      = sResU P Q (i - 1) * sResV P Q (k - 1) - sResV P Q (i - 1) * sResU P Q (k - 1) := by
  have hjq : j ≤ Q.natDegree := by omega
  have hkj : k < j := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  -- `C(s_j t_{i-1}) = det B_{j,i}` and `C(s_k t_{j-1}) = det B_{k,j}` (Lemma 8.43).
  have hCc : C (sBPR P Q j * tBPR P Q (i - 1))
      = sResU P Q (i - 1) * sResV P Q (j - 1) - sResV P Q (i - 1) * sResU P Q (j - 1) := by
    rw [← det_cofactorMat P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg, cofactorMat,
      Matrix.det_fin_two_of]
  have hCd : C (sBPR P Q k * tBPR P Q (j - 1))
      = sResU P Q (j - 1) * sResV P Q (k - 1) - sResV P Q (j - 1) * sResU P Q (k - 1) := by
    rw [← det_cofactorMat P Q hP hQ hpq hq1 hk1 hkj (show j ≤ Q.natDegree + 1 by omega) hk0 hkdeg,
      cofactorMat, Matrix.det_fin_two_of]
  -- Cleared-denominator recurrence: `C_{k-1} sResP_{j-1} = C(c) sResP_{k-1} + C(d) sResP_{i-1}`.
  have hspec := transC_spec P Q hP hQ hpq hq1 hj1 hji hiq hk0 hkdeg hk1 hne hdeg
  have hTS : transC P Q i j k * sResP P Q (j - 1)
      = C (sBPR P Q j * tBPR P Q (i - 1)) * sResP P Q (k - 1)
        + C (sBPR P Q k * tBPR P Q (j - 1)) * sResP P Q (i - 1) := by
    rw [hspec]; ring
  -- The same identity holds with `transC` replaced by `X` (pure ring via the cofactor relations).
  have hi := sResP_eq_cofactor P Q hQ hpq (show i - 1 ≤ Q.natDegree by omega)
  have hj := sResP_eq_cofactor P Q hQ hpq (show j - 1 ≤ Q.natDegree by omega)
  have hk := sResP_eq_cofactor P Q hQ hpq (show k - 1 ≤ Q.natDegree by omega)
  have hX : (sResU P Q (i - 1) * sResV P Q (k - 1) - sResV P Q (i - 1) * sResU P Q (k - 1))
        * sResP P Q (j - 1)
      = C (sBPR P Q j * tBPR P Q (i - 1)) * sResP P Q (k - 1)
        + C (sBPR P Q k * tBPR P Q (j - 1)) * sResP P Q (i - 1) := by
    rw [hCc, hCd, hi, hj, hk]; ring
  exact mul_right_cancel₀ hk0 (hTS.trans hX.symm)

end Azurite.BPR.Chapter8
