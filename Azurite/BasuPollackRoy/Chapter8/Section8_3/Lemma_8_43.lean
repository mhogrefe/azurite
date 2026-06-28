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

/-- **Lemma 8.43 over an integral domain.**  The constant value of the cofactor determinant,
    stated with `Chapter4.sRes` and `leadingCoeff` (both `CommRing`-expressible) in place of the
    Field-only `sBPR`/`tBPR`: `det(B_{j,i}) = C(sRes_j · lcof(sResP_{i-1}))`.  The non-defectiveness
    `sRes_j ≠ 0` is taken as a hypothesis (the caller — here the `signedSubresultant` induction —
    has it directly), avoiding the Field-only `sResP_natDegree_realized`. -/
theorem det_cofactorMat_domain {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hpq : Q.natDegree < P.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1)
    (hQ : Q ≠ 0) (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j)
    (hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0) :
    (cofactorMat P Q i j).det
      = C (Azurite.BPR.Chapter4.sRes P Q j * (sResP P Q (i - 1)).leadingCoeff) := by
  have hjq : j ≤ Q.natDegree := by omega
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
  obtain ⟨hVjd, hVjl⟩ := sResV_sub_one_natDegree P Q hP hpq hj1 hjq hsRes
  have hVj_ne : sResV P Q (j - 1) ≠ 0 := fun h =>
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hP) hsRes) (by rw [← hVjl, h, leadingCoeff_zero])
  have hVid : (sResV P Q (i - 1)).natDegree ≤ P.natDegree - 1 - (i - 1) :=
    sResV_natDegree_le P Q hpq (by omega)
  have hPjd : (sResP P Q (j - 1)).natDegree ≤ j - 1 :=
    Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
  have ht1d : (sResV P Q (j - 1) * sResP P Q (i - 1)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_mul hVj_ne hne, hVjd, hdeg]; omega
  have ht1l : (sResV P Q (j - 1) * sResP P Q (i - 1)).leadingCoeff
      = P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q j * (sResP P Q (i - 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, hVjl]
  have ht2d : (sResV P Q (i - 1) * sResP P Q (j - 1)).natDegree < P.natDegree := by
    rcases eq_or_ne (sResV P Q (i - 1)) 0 with h | h
    · rw [h, zero_mul, Polynomial.natDegree_zero]; omega
    · rcases eq_or_ne (sResP P Q (j - 1)) 0 with h' | h'
      · rw [h', mul_zero, Polynomial.natDegree_zero]; omega
      · rw [Polynomial.natDegree_mul h h']; omega
  have hRHSd : (sResV P Q (j - 1) * sResP P Q (i - 1)
      - sResV P Q (i - 1) * sResP P Q (j - 1)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [ht1d]; exact ht2d), ht1d]
  have hRHSl : (sResV P Q (j - 1) * sResP P Q (i - 1)
      - sResV P Q (i - 1) * sResP P Q (j - 1)).leadingCoeff
      = (sResV P Q (j - 1) * sResP P Q (i - 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff, hRHSd, Polynomial.coeff_sub,
      Polynomial.coeff_eq_zero_of_natDegree_lt ht2d, sub_zero, Polynomial.leadingCoeff, ht1d]
  have hRHS_ne : sResV P Q (j - 1) * sResP P Q (i - 1)
      - sResV P Q (i - 1) * sResP P Q (j - 1) ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hRHSd; omega
  have hdB_ne : (cofactorMat P Q i j).det ≠ 0 := fun h => by
    rw [h, zero_mul] at hElim; exact hRHS_ne hElim.symm
  have hdBnd : (cofactorMat P Q i j).det.natDegree = 0 := by
    have hmul : ((cofactorMat P Q i j).det * P).natDegree = P.natDegree := by
      rw [hElim]; exact hRHSd
    rw [Polynomial.natDegree_mul hdB_ne hP] at hmul; omega
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
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdBnd]
  congr 1
  rw [show (cofactorMat P Q i j).det.coeff 0 = (cofactorMat P Q i j).det.leadingCoeff from by
    rw [Polynomial.leadingCoeff, hdBnd]]
  exact hval

/-- **Cleared-denominator recurrence in cofactor form (over a CommRing).**  The `hX` ring identity
    underlying `transC_eq_cofactors`, kept over a `CommRing` by writing the scalar coefficients as
    the cofactor determinants `det(B_{j,i})`, `det(B_{k,j})` (which `det_cofactorMat_domain`
    identifies with `C(sRes·lcof)`).  Pure Bézout algebra — no field, no `transC`. -/
theorem sResP_cofactor_recurrence {D : Type*} [CommRing D] (P Q : D[X]) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i j k : ℕ} (hi1 : i - 1 ≤ Q.natDegree)
    (hj1 : j - 1 ≤ Q.natDegree) (hk1 : k - 1 ≤ Q.natDegree) :
    (cofactorMat P Q j k).det * sResP P Q (i - 1)
      = (sResU P Q (i - 1) * sResV P Q (k - 1) - sResV P Q (i - 1) * sResU P Q (k - 1))
          * sResP P Q (j - 1)
        - (cofactorMat P Q i j).det * sResP P Q (k - 1) := by
  have hi := sResP_eq_cofactor P Q hQ hpq hi1
  have hj := sResP_eq_cofactor P Q hQ hpq hj1
  have hk := sResP_eq_cofactor P Q hQ hpq hk1
  rw [show (cofactorMat P Q j k).det
        = sResU P Q (j - 1) * sResV P Q (k - 1) - sResV P Q (j - 1) * sResU P Q (k - 1) from by
      rw [cofactorMat, Matrix.det_fin_two_of],
    show (cofactorMat P Q i j).det
        = sResU P Q (i - 1) * sResV P Q (j - 1) - sResV P Q (i - 1) * sResU P Q (j - 1) from by
      rw [cofactorMat, Matrix.det_fin_two_of],
    hi, hj, hk]
  ring

/-- **Boundary cofactor value.**  The constant cofactor `sResU_{q-1}(P,Q)` equals `-(s_q · lcof Q)`.
    Proof: compare the `X^p` coefficients of the Bézout relation
    `sResP_{q-1} = sResU_{q-1}·P + sResV_{q-1}·Q`.  Since `deg sResP_{q-1} < q < p`, the `X^p` terms
    of `sResU_{q-1}·P` (constant `× P`) and `sResV_{q-1}·Q` (degree `(p-q)+q = p`, leading coeff
    `a_p·s_q·b_q` via Prop 8.42(c)) cancel, giving `sResU_{q-1}·a_p + a_p·s_q·b_q = 0`, hence
    `sResU_{q-1} = -s_q·b_q` after cancelling `a_p ≠ 0`.  This is the boundary analogue of
    `det_cofactorMat_domain`, used where `i = p` (`i-1 > q`) so the matrix det formula does not apply. -/
theorem sResU_sub_one_eq {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    (hsRes : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0) :
    sResU P Q (Q.natDegree - 1)
      = - C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) := by
  obtain ⟨hVd, hVl⟩ := sResV_sub_one_natDegree P Q hP hpq hq1 le_rfl hsRes
  have hUdeg : (sResU P Q (Q.natDegree - 1)).natDegree = 0 := by
    have := sResU_natDegree_le P Q hpq (show Q.natDegree - 1 ≤ Q.natDegree from by omega)
    omega
  obtain ⟨c0, hc0⟩ := Polynomial.natDegree_eq_zero.mp hUdeg
  have hbez : sResP P Q (Q.natDegree - 1)
      = C c0 * P + sResV P Q (Q.natDegree - 1) * Q := by
    rw [hc0]; exact sResP_eq_cofactor P Q hQ hpq (by omega)
  have hVne : sResV P Q (Q.natDegree - 1) ≠ 0 := by
    intro h; rw [h, Polynomial.leadingCoeff_zero] at hVl
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) hsRes) hVl.symm
  have hVQd : (sResV P Q (Q.natDegree - 1) * Q).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_mul hVne hQ, hVd]; omega
  have hsPd : (sResP P Q (Q.natDegree - 1)).natDegree < P.natDegree := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show Q.natDegree - 1 ≤ Q.natDegree from by omega))
    omega
  have hVQcoeff : (sResV P Q (Q.natDegree - 1) * Q).coeff P.natDegree
      = (sResV P Q (Q.natDegree - 1)).leadingCoeff * Q.leadingCoeff := by
    rw [← Polynomial.leadingCoeff_mul]
    conv_rhs => rw [Polynomial.leadingCoeff, hVQd]
  have hcp : (0 : D)
      = c0 * P.leadingCoeff + P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q Q.natDegree
          * Q.leadingCoeff := by
    have h := congrArg (fun r : D[X] => r.coeff P.natDegree) hbez
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hsPd, hVQcoeff, hVl,
      show P.coeff P.natDegree = P.leadingCoeff from rfl] at h
    linear_combination h
  have hlcP : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hfac : P.leadingCoeff
      * (c0 + Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) = 0 := by
    linear_combination -hcp
  have hc0val : c0 = -(Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hfac).resolve_left hlcP)
  rw [← hc0, hc0val, Polynomial.C_neg]

/-- **Boundary recurrence at `i = p`.**  The integral Euclidean division of `C(d)·Q` by
    `sResP_{q-1}` (where `d = s_k · lcof(sResP_{q-1})`), valid for `i = p` (so `sResP_{i-1} = Q`),
    where the matrix cofactor `det(B_{p,q})` is unavailable.  Obtained by Cramer-eliminating `P` from
    the Bézout relations at `q-1` and `k-1` (both `≤ q`), with quotient `-sResU_{k-1}` and remainder
    `sResU_{q-1}·sResP_{k-1}` (degree `< k = deg sResP_{q-1}`); the coefficient of `Q` is identified
    via `det_cofactorMat_domain` at `(q,k)`. -/
theorem boundary_recurrence {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) {q k : ℕ} (hq : q = Q.natDegree)
    (hk1 : 1 ≤ k) (hkq : k < q) (hne : sResP P Q (q - 1) ≠ 0)
    (hdeg : (sResP P Q (q - 1)).natDegree = k)
    (hsResk : Azurite.BPR.Chapter4.sRes P Q k ≠ 0) :
    C (Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (q - 1)).leadingCoeff) * Q
      = (- sResU P Q (k - 1)) * sResP P Q (q - 1) + sResU P Q (q - 1) * sResP P Q (k - 1) := by
  have hbq : sResP P Q (q - 1) = sResU P Q (q - 1) * P + sResV P Q (q - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq (by omega)
  have hbk : sResP P Q (k - 1) = sResU P Q (k - 1) * P + sResV P Q (k - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq (by omega)
  have hdet : (cofactorMat P Q q k).det
      = C (Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (q - 1)).leadingCoeff) :=
    det_cofactorMat_domain P Q hP hpq hk1 hkq (by omega) hQ hne hdeg hsResk
  have hdet2 : (cofactorMat P Q q k).det
      = sResU P Q (q - 1) * sResV P Q (k - 1) - sResV P Q (q - 1) * sResU P Q (k - 1) := by
    rw [cofactorMat, Matrix.det_fin_two_of]
  have hcramer : sResU P Q (k - 1) * sResP P Q (q - 1) - sResU P Q (q - 1) * sResP P Q (k - 1)
      = (sResU P Q (k - 1) * sResV P Q (q - 1) - sResU P Q (q - 1) * sResV P Q (k - 1)) * Q := by
    rw [hbq, hbk]; ring
  have hcoef : sResU P Q (k - 1) * sResV P Q (q - 1) - sResU P Q (q - 1) * sResV P Q (k - 1)
      = - C (Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (q - 1)).leadingCoeff) := by
    rw [← hdet, hdet2]; ring
  have key : sResU P Q (k - 1) * sResP P Q (q - 1) - sResU P Q (q - 1) * sResP P Q (k - 1)
      = - C (Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (q - 1)).leadingCoeff) * Q := by
    rw [hcramer, hcoef]
  linear_combination key

end Azurite.BPR.Chapter8
