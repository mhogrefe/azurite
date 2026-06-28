import Azurite.BasuPollackRoy.Chapter8.Section8_3.Notation_8_41
import Azurite.BasuPollackRoy.Chapter8.Section8_3.SignedSubresultant
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_34
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Lemma_8_29

/-!
# BPR Proposition 8.42 (a): the cofactor (Bézout) identity

For `j ≤ q` (with `q < p`, `Q ≠ 0`), the `j`-th signed subresultant polynomial is the
`P`,`Q`-combination given by its cofactors:

  `sResP_j(P,Q) = sResU_j(P,Q) · P + sResV_j(P,Q) · Q`.

By Lemma 8.29, `sResP_j = det(SyHa_j(P,Q)^*)`, the determinant of the matrix whose last
column holds the family `X^{q-j-1}P, …, P, Q, …, X^{p-j-1}Q`.  That last column splits
entrywise as `uCol · P + wCol · Q`, where `uCol`/`wCol` are exactly the monomial last columns
of `M_j`/`N_j` (Notation 8.41); determinant column-linearity then yields the identity.
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {D : Type*} [CommRing D]

/-- **BPR Proposition 8.42 (a), cofactor identity.**  For `j ≤ q` (with `Q ≠ 0` and
    `q < p`), `sResP_j(P,Q) = sResU_j(P,Q) · P + sResV_j(P,Q) · Q`. -/
theorem sResP_eq_cofactor (P Q : D[X]) (_hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j : ℕ} (hjq : j ≤ Q.natDegree) :
    sResP P Q j = sResU P Q j * P + sResV P Q j * Q := by
  have hP : P ≠ 0 := by rintro rfl; simp at hpq
  set n := P.natDegree + Q.natDegree - j with hn_def
  have hm_pos : 0 < P.natDegree + Q.natDegree - 2 * j := by omega
  have hmn : P.natDegree + Q.natDegree - 2 * j ≤ n := by simp only [hn_def]; omega
  set last : Fin (P.natDegree + Q.natDegree - 2 * j) := ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩
    with hlast
  have hlastval : (last : ℕ) = P.natDegree + Q.natDegree - 2 * j - 1 := rfl
  set F : Fin (P.natDegree + Q.natDegree - 2 * j) → D[X] := fun r =>
    if (r : ℕ) < Q.natDegree - j then X ^ (Q.natDegree - j - 1 - (r : ℕ)) * P
    else X ^ ((r : ℕ) - (Q.natDegree - j)) * Q with hF
  set uCol : Fin (P.natDegree + Q.natDegree - 2 * j) → D[X] := fun r =>
    if (r : ℕ) < Q.natDegree - j then X ^ (Q.natDegree - 1 - j - (r : ℕ)) else 0 with hu
  set wCol : Fin (P.natDegree + Q.natDegree - 2 * j) → D[X] := fun r =>
    if (r : ℕ) < Q.natDegree - j then 0 else X ^ ((r : ℕ) - (Q.natDegree - j)) with hw
  have hFsplit : ∀ r, F r = uCol r * P + wCol r * Q := by
    intro r
    simp only [hF, hu, hw]
    by_cases hr : (r : ℕ) < Q.natDegree - j
    · rw [if_pos hr, if_pos hr, if_pos hr, zero_mul, add_zero,
        show Q.natDegree - 1 - j - (r : ℕ) = Q.natDegree - j - 1 - (r : ℕ) from by omega]
    · rw [if_neg hr, if_neg hr, if_neg hr, zero_mul, zero_add]
  have hFdeg : ∀ r, (F r).natDegree < n := by
    intro r
    have hr_lt : (r : ℕ) < P.natDegree + Q.natDegree - 2 * j := r.2
    simp only [hF]
    by_cases hr : (r : ℕ) < Q.natDegree - j
    · rw [if_pos hr]
      calc (X ^ (Q.natDegree - j - 1 - (r : ℕ)) * P).natDegree
          ≤ (X ^ (Q.natDegree - j - 1 - (r : ℕ))).natDegree + P.natDegree := Polynomial.natDegree_mul_le
        _ ≤ (Q.natDegree - j - 1 - (r : ℕ)) + P.natDegree := by
              gcongr; exact Polynomial.natDegree_X_pow_le _
        _ < n := by simp only [hn_def]; omega
    · rw [if_neg hr]
      calc (X ^ ((r : ℕ) - (Q.natDegree - j)) * Q).natDegree
          ≤ (X ^ ((r : ℕ) - (Q.natDegree - j))).natDegree + Q.natDegree := Polynomial.natDegree_mul_le
        _ ≤ ((r : ℕ) - (Q.natDegree - j)) + Q.natDegree := by
              gcongr; exact Polynomial.natDegree_X_pow_le _
        _ < n := by simp only [hn_def]; omega
  set FLT : Fin (P.natDegree + Q.natDegree - 2 * j) → degreeLT D n := fun r =>
    ⟨F r, Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hFdeg r))⟩ with hFLT
  have hFLTeq : (fun r => (FLT r : D[X])) = F := rfl
  have hsResP : sResP P Q j = (matStar n F).det := by
    rw [sResP, if_pos hjq, ← hFLTeq, pdetRing_eq_det_matStar hm_pos hmn FLT, hFLTeq]
  have hcol : matStar n F = (matStar n F).updateCol last (P • uCol + Q • wCol) := by
    refine Matrix.ext fun r c => ?_
    rw [Matrix.updateCol_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, matStar, if_neg (by rw [hlastval]; omega), hFsplit r]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · rw [if_neg hc]
  have hU : (matStar n F).updateCol last uCol = sResUMat P Q j := by
    refine Matrix.ext fun r c => ?_
    rw [Matrix.updateCol_apply, sResUMat, Matrix.of_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, if_neg (by rw [hlastval]; omega : ¬ (last : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j)]
    · have hcm : (c : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j := by
        rcases Nat.lt_or_ge ((c : ℕ) + 1) (P.natDegree + Q.natDegree - 2 * j) with h | h
        · exact h
        · exact absurd (Fin.ext (show (c : ℕ) = (last : ℕ) by rw [hlastval]; omega)) hc
      rw [if_neg hc, matStar, if_pos hcm, if_pos hcm]
      simp only [hF, Chapter4.SyHa, Matrix.of_apply, Fin.val_castLE, hn_def]
      split_ifs <;> rfl
  have hV : (matStar n F).updateCol last wCol = sResVMat P Q j := by
    refine Matrix.ext fun r c => ?_
    rw [Matrix.updateCol_apply, sResVMat, Matrix.of_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, if_neg (by rw [hlastval]; omega : ¬ (last : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j)]
    · have hcm : (c : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j := by
        rcases Nat.lt_or_ge ((c : ℕ) + 1) (P.natDegree + Q.natDegree - 2 * j) with h | h
        · exact h
        · exact absurd (Fin.ext (show (c : ℕ) = (last : ℕ) by rw [hlastval]; omega)) hc
      rw [if_neg hc, matStar, if_pos hcm, if_pos hcm]
      simp only [hF, Chapter4.SyHa, Matrix.of_apply, Fin.val_castLE, hn_def]
      split_ifs <;> rfl
  rw [hsResP, hcol, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
    Matrix.det_updateCol_smul, hU, hV]
  simp only [sResU, sResV]
  ring

/-- The determinant of a square polynomial matrix all of whose columns except `c₀` are
    constant (`natDegree 0`) and whose `c₀` column has `natDegree ≤ d` has `natDegree ≤ d`:
    in `det = Σ_σ ± ∏_i M (σ i) i`, exactly one factor (the `c₀` column) is non-constant. -/
theorem natDegree_det_le_col {N : ℕ} (M : Matrix (Fin N) (Fin N) D[X]) (c₀ : Fin N) (d : ℕ)
    (hconst : ∀ i c, c ≠ c₀ → (M i c).natDegree = 0)
    (hcol : ∀ i, (M i c₀).natDegree ≤ d) : M.det.natDegree ≤ d := by
  classical
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine le_trans (Polynomial.natDegree_smul_le _ _) (le_trans (Polynomial.natDegree_prod_le _ _) ?_)
  rw [← Finset.add_sum_erase Finset.univ (fun i => (M (σ i) i).natDegree) (Finset.mem_univ c₀),
    Finset.sum_eq_zero (fun i hi => hconst (σ i) i (Finset.ne_of_mem_erase hi)), add_zero]
  exact hcol (σ c₀)

/-- **BPR Proposition 8.42 (a), degree bound for `sResU`.** `deg(sResU_j(P,Q)) ≤ q - 1 - j`
    (so `deg(sResU_{j-1}) ≤ q - j`). -/
theorem sResU_natDegree_le (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hjq : j ≤ Q.natDegree) : (sResU P Q j).natDegree ≤ Q.natDegree - 1 - j := by
  rw [sResU]
  refine natDegree_det_le_col (sResUMat P Q j)
    ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩ (Q.natDegree - 1 - j) (fun i c hc => ?_)
    (fun i => ?_)
  · rw [sResUMat, Matrix.of_apply,
      if_pos (by
        have hcv : (c : ℕ) ≠ P.natDegree + Q.natDegree - 2 * j - 1 := fun h => hc (Fin.ext h)
        have := c.isLt; omega), Polynomial.natDegree_C]
  · rw [sResUMat, Matrix.of_apply,
      if_neg (show ¬ P.natDegree + Q.natDegree - 2 * j - 1 + 1 < P.natDegree + Q.natDegree - 2 * j by omega)]
    by_cases hi : (i : ℕ) < Q.natDegree - j
    · rw [if_pos hi]; exact le_trans (Polynomial.natDegree_X_pow_le _) (by omega)
    · rw [if_neg hi, Polynomial.natDegree_zero]; omega

/-- **BPR Proposition 8.42 (a), degree bound for `sResV`.** `deg(sResV_j(P,Q)) ≤ p - 1 - j`
    (so `deg(sResV_{j-1}) ≤ p - j`). -/
theorem sResV_natDegree_le (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hjq : j ≤ Q.natDegree) : (sResV P Q j).natDegree ≤ P.natDegree - 1 - j := by
  rw [sResV]
  refine natDegree_det_le_col (sResVMat P Q j)
    ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩ (P.natDegree - 1 - j) (fun i c hc => ?_)
    (fun i => ?_)
  · rw [sResVMat, Matrix.of_apply,
      if_pos (by
        have hcv : (c : ℕ) ≠ P.natDegree + Q.natDegree - 2 * j - 1 := fun h => hc (Fin.ext h)
        have := c.isLt; omega), Polynomial.natDegree_C]
  · rw [sResVMat, Matrix.of_apply,
      if_neg (show ¬ P.natDegree + Q.natDegree - 2 * j - 1 + 1 < P.natDegree + Q.natDegree - 2 * j by omega)]
    have hi_lt : (i : ℕ) < P.natDegree + Q.natDegree - 2 * j := i.2
    by_cases hi : (i : ℕ) < Q.natDegree - j
    · rw [if_pos hi, Polynomial.natDegree_zero]; omega
    · rw [if_neg hi]; exact le_trans (Polynomial.natDegree_X_pow_le _) (by omega)

/-- **BPR Proposition 8.42 (b), cofactor uniqueness.**  Over a field, if `sResP_j(P,Q) ≠ 0`
    and `U·P + V·Q = sResP_j(P,Q)` with `deg U ≤ q-j-1` and `deg V ≤ p-j-1`, then
    `U = sResU_j(P,Q)` and `V = sResV_j(P,Q)`. -/
theorem cofactor_unique {K : Type*} [Field K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j < Q.natDegree) (hsj : sResP P Q j ≠ 0)
    {U V : K[X]} (hUV : U * P + V * Q = sResP P Q j)
    (hU : U.natDegree ≤ Q.natDegree - j - 1) (_hV : V.natDegree ≤ P.natDegree - j - 1) :
    U = sResU P Q j ∧ V = sResV P Q j := by
  have hid := sResP_eq_cofactor P Q hQ hpq hjq.le
  have hUb := sResU_natDegree_le P Q hpq hjq.le
  -- `A := sResU_j - U`, `B := sResV_j - V`, with `A·P + B·Q = 0`
  have hAB0 : (sResU P Q j - U) * P + (sResV P Q j - V) * Q = 0 := by
    have h1 : (sResU P Q j - U) * P + (sResV P Q j - V) * Q
        = (sResU P Q j * P + sResV P Q j * Q) - (U * P + V * Q) := by ring
    rw [h1, ← hid, hUV, sub_self]
  have hAeq : sResU P Q j - U = 0 := by
    by_contra hA0
    have hB0 : sResV P Q j - V ≠ 0 := by
      intro hB0; rw [hB0, zero_mul, add_zero] at hAB0
      exact hA0 ((mul_eq_zero.mp hAB0).resolve_right hP)
    have hAP : (sResU P Q j - U) * P = -((sResV P Q j - V) * Q) := by linear_combination hAB0
    have hAP_ne : (sResU P Q j - U) * P ≠ 0 := mul_ne_zero hA0 hP
    -- `lcm P Q ∣ (sResU_j - U)·P` and the degree bound on the cofactor difference
    have hlcm_dvd : lcm P Q ∣ (sResU P Q j - U) * P :=
      lcm_dvd (dvd_mul_left P _) (by rw [hAP]; exact dvd_neg.mpr (dvd_mul_left Q _))
    have hAb : (sResU P Q j - U).natDegree ≤ Q.natDegree - 1 - j :=
      le_trans (Polynomial.natDegree_sub_le _ _) (max_le hUb (le_trans hU (by omega)))
    have hdegAP : ((sResU P Q j - U) * P).natDegree ≤ (Q.natDegree - 1 - j) + P.natDegree :=
      le_trans Polynomial.natDegree_mul_le (by gcongr)
    have hdeg_lcm := Polynomial.natDegree_le_of_dvd hlcm_dvd hAP_ne
    -- `deg gcd + deg lcm = p + q`
    have hgcd_ne : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
    have hlcm_ne : lcm P Q ≠ 0 := fun h =>
      mul_ne_zero hP hQ (zero_dvd_iff.mp (h ▸ lcm_dvd (dvd_mul_right P Q) (dvd_mul_left Q P)))
    have hgl : (gcd P Q).natDegree + (lcm P Q).natDegree = P.natDegree + Q.natDegree := by
      have h := Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated (gcd_mul_lcm P Q))
      rwa [Polynomial.natDegree_mul hgcd_ne hlcm_ne, Polynomial.natDegree_mul hP hQ] at h
    -- but `deg gcd ≤ deg sResP_j ≤ j`
    have hg_le : (gcd P Q).natDegree ≤ j :=
      le_trans (Polynomial.natDegree_le_of_dvd (gcd_dvd_sResP_all P Q hP hQ hpq j) hsj)
        (Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hjq.le))
    omega
  have hBeq : sResV P Q j - V = 0 := by
    rw [hAeq, zero_mul, zero_add] at hAB0
    exact (mul_eq_zero.mp hAB0).resolve_right hQ
  exact ⟨(sub_eq_zero.mp hAeq).symm, (sub_eq_zero.mp hBeq).symm⟩

/-- Expand the determinant of a polynomial matrix `M` whose first `N-1` columns are constants
    `C(A r c)` and whose last column is an arbitrary polynomial vector `V`:
    `det M = Σ_{r₀} V_{r₀} · C(det(A with last column = e_{r₀}))`. -/
theorem det_lastCol_expand {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) D)
    (V : Fin N → D[X]) (M : Matrix (Fin N) (Fin N) D[X])
    (hM : ∀ r c, M r c = if (c : ℕ) + 1 < N then C (A r c) else V r) :
    M.det = ∑ r₀ : Fin N, V r₀ * C ((A.updateCol ⟨N - 1, by omega⟩ (Pi.single r₀ 1)).det) := by
  set last : Fin N := ⟨N - 1, by omega⟩ with hlast
  have hlastval : (last : ℕ) = N - 1 := rfl
  have hMself : M = M.updateCol last V := by
    ext r c
    rw [Matrix.updateCol_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, hM, if_neg (show ¬ ((last : ℕ) + 1 < N) by rw [hlastval]; omega)]
    · rw [if_neg hc]
  have hcol : V = ∑ r₀ : Fin N, V r₀ • Pi.single r₀ (1 : D[X]) := by
    funext r; simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, Finset.sum_ite_eq]
  rw [hMself]
  conv_lhs => rw [hcol]
  rw [det_updateCol_finsetSum]
  refine Finset.sum_congr rfl (fun r₀ _ => ?_)
  rw [Matrix.det_updateCol_smul]
  have hmat : M.updateCol last (Pi.single r₀ (1 : D[X]))
      = (A.updateCol last (Pi.single r₀ 1)).map C := by
    ext r c
    rw [Matrix.updateCol_apply, Matrix.map_apply, Matrix.updateCol_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, if_pos rfl, Pi.single_apply, Pi.single_apply, apply_ite C, map_one, map_zero]
    · rw [if_neg hc, if_neg hc, hM,
        if_pos (show (c : ℕ) + 1 < N by
          have h1 := c.isLt
          have h2 : (c : ℕ) ≠ N - 1 := by rw [← hlastval]; exact Fin.val_ne_of_ne hc
          omega)]
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- **BPR Proposition 8.42 (c), coefficient as a cofactor minor.** The coefficient of
    `X^{p-j}` in `sResV_{j-1}(P,Q)` is the `(N-1, N-1)` cofactor of the Sylvester-Habicht
    determinant: the determinant of `SyHa_{j-1}`'s coefficient columns with the last column
    replaced by the standard basis vector `e_{N-1}`.  (BPR's Proposition 8.42(c) then
    identifies this minor with `a_p · sRes_j` by a block/`SyHaSquare_j` reduction.) -/
theorem sResV_sub_one_coeff_eq_minor (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree) :
    (sResV P Q (j - 1)).coeff (P.natDegree - j)
      = (Matrix.updateCol
          (fun (r c : Fin (P.natDegree + Q.natDegree - 2 * (j - 1))) =>
            Chapter4.SyHa P Q (j - 1) r (Fin.castLE (by omega) c))
          ⟨P.natDegree + Q.natDegree - 2 * (j - 1) - 1, by omega⟩
          (Pi.single ⟨P.natDegree + Q.natDegree - 2 * (j - 1) - 1, by omega⟩ 1)).det := by
  have hNpos : 0 < P.natDegree + Q.natDegree - 2 * (j - 1) := by omega
  set A : Matrix (Fin (P.natDegree + Q.natDegree - 2 * (j - 1)))
      (Fin (P.natDegree + Q.natDegree - 2 * (j - 1))) D :=
    fun r c => Chapter4.SyHa P Q (j - 1) r (Fin.castLE (by omega) c) with hA
  set wCol : Fin (P.natDegree + Q.natDegree - 2 * (j - 1)) → D[X] :=
    fun r => if (r : ℕ) < Q.natDegree - (j - 1) then 0
      else X ^ ((r : ℕ) - (Q.natDegree - (j - 1))) with hwCol
  set last : Fin (P.natDegree + Q.natDegree - 2 * (j - 1)) :=
    ⟨P.natDegree + Q.natDegree - 2 * (j - 1) - 1, by omega⟩ with hlast
  have hM : ∀ r c, sResVMat P Q (j - 1) r c
      = if (c : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * (j - 1) then C (A r c) else wCol r := by
    intro r c; rw [sResVMat, Matrix.of_apply]
  rw [sResV, det_lastCol_expand hNpos A wCol (sResVMat P Q (j - 1)) hM, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single last]
  · rw [Polynomial.coeff_mul_C,
      show wCol last = X ^ (P.natDegree - j) by
        simp only [hwCol]; rw [if_neg (by simp only [hlast]; omega)]; congr 1; simp only [hlast]; omega,
      Polynomial.coeff_X_pow, if_pos rfl, one_mul]
  · intro r₀ _ hr₀
    rw [Polynomial.coeff_mul_C, show (wCol r₀).coeff (P.natDegree - j) = 0 by
      simp only [hwCol]; split_ifs with hr
      · exact Polynomial.coeff_zero _
      · rw [Polynomial.coeff_X_pow, if_neg (by
          have h2 : (r₀ : ℕ) ≠ P.natDegree + Q.natDegree - 2 * (j - 1) - 1 :=
            fun h => hr₀ (Fin.ext (by simp only [hlast]; exact h))
          have := r₀.isLt; omega)], zero_mul]
  · intro h; exact absurd (Finset.mem_univ last) h

/-- The `(N-1,N-1)` cofactor minor of `SyHa_{j-1}` equals `a_p · sRes_j`: expand along the
    last column (a basis vector ⟹ the top-left block determinant), then along the first column
    (`a_p` times the standard basis ⟹ `a_p · det(SyHaSquare_j)`). -/
theorem sResV_minor_det_eq (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree) :
    (Matrix.updateCol
        (fun (r c : Fin (P.natDegree + Q.natDegree - 2 * (j - 1))) =>
          Chapter4.SyHa P Q (j - 1) r (Fin.castLE (by omega) c))
        ⟨P.natDegree + Q.natDegree - 2 * (j - 1) - 1, by omega⟩
        (Pi.single ⟨P.natDegree + Q.natDegree - 2 * (j - 1) - 1, by omega⟩ 1)).det
      = P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q j := by
  set m := P.natDegree + Q.natDegree - 2 * (j - 1) with hm_def
  have hm2 : 2 ≤ m := by simp only [hm_def]; omega
  set A : Matrix (Fin m) (Fin m) D :=
    fun r c => Chapter4.SyHa P Q (j - 1) r (Fin.castLE (by simp only [hm_def]; omega) c) with hA
  set last : Fin m := ⟨m - 1, by omega⟩ with hlast
  set N' : Matrix (Fin (m - 1)) (Fin (m - 1)) D :=
    fun i k => A ⟨(i : ℕ), by omega⟩ ⟨(k : ℕ), by omega⟩ with hN'
  -- Step 1: expand along the last column (= e_last) → top-left block N'
  have step1 : (A.updateCol last (Pi.single last 1)).det = N'.det := by
    set e1 : Fin (m - 1) ⊕ Fin 1 ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega)) with he1
    have he1l : ∀ i : Fin (m - 1), e1 (Sum.inl i) = ⟨(i : ℕ), by omega⟩ := fun i =>
      Fin.ext (by simp [he1, Equiv.trans_apply, finSumFinEquiv_apply_left])
    have he1r : ∀ i : Fin 1, e1 (Sum.inr i) = last := fun i =>
      Fin.ext (by simp [he1, hlast, Equiv.trans_apply, finSumFinEquiv_apply_right])
    have hne : ∀ i : Fin (m - 1), (⟨(i : ℕ), by omega⟩ : Fin m) ≠ last := fun i h =>
      absurd (Fin.ext_iff.mp h) (by simp only [hlast]; omega)
    set Mb := (A.updateCol last (Pi.single last 1)).submatrix e1 e1 with hMb
    have htb12 : Mb.toBlocks₁₂ = 0 := by
      ext i k
      simp only [hMb, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.zero_apply, Matrix.of_apply]
      rw [he1l, he1r, Matrix.updateCol_apply, if_pos rfl, Pi.single_apply, if_neg (hne i)]
    have htb11 : Mb.toBlocks₁₁ = N' := by
      ext i k
      simp only [hMb, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply]
      rw [he1l, he1l, Matrix.updateCol_apply, if_neg (hne k)]
    have htb22 : Mb.toBlocks₂₂.det = 1 := by
      rw [Matrix.det_fin_one]
      simp only [hMb, Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply]
      rw [he1r, Matrix.updateCol_apply, if_pos rfl, Pi.single_apply, if_pos rfl]
    rw [show (A.updateCol last (Pi.single last 1)).det = Mb.det from
        (Matrix.det_submatrix_equiv_self e1 _).symm]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mb]
    rw [htb12, Matrix.det_fromBlocks_zero₁₂, htb11, htb22, mul_one]
  rw [step1]
  -- Step 2: expand along the first column (= a_p · e_0) → a_p · det(SyHaSquare_j)
  set e2 : Fin 1 ⊕ Fin (m - 2) ≃ Fin (m - 1) := finSumFinEquiv.trans (finCongr (by omega)) with he2
  have he2l : ∀ i : Fin 1, e2 (Sum.inl i) = ⟨0, by omega⟩ := fun i =>
    Fin.ext (by simp [he2, Equiv.trans_apply, finSumFinEquiv_apply_left])
  have he2r : ∀ a : Fin (m - 2), e2 (Sum.inr a) = ⟨1 + (a : ℕ), by omega⟩ := fun a =>
    Fin.ext (by simp [he2, Equiv.trans_apply, finSumFinEquiv_apply_right])
  set Mb2 := N'.submatrix e2 e2 with hMb2
  have htb21 : Mb2.toBlocks₂₁ = 0 := by
    ext a k
    simp only [hMb2, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.zero_apply, hN', hA, he2r,
      he2l, Fin.castLE_mk, Chapter4.SyHa, Matrix.of_apply]
    split_ifs with hcond
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
      have h1 := Polynomial.natDegree_X_pow_le (R := D) (Q.natDegree - (j - 1) - 1 - (1 + (a : ℕ)))
      have h2 := a.isLt
      omega
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
      have h1 := Polynomial.natDegree_X_pow_le (R := D) (1 + (a : ℕ) - (Q.natDegree - (j - 1)))
      have h2 := a.isLt
      omega
  have htb11 : Mb2.toBlocks₁₁.det = P.leadingCoeff := by
    rw [Matrix.det_fin_one]
    simp only [hMb2, Matrix.toBlocks₁₁, Matrix.submatrix_apply, hN', hA, he2l, Fin.castLE_mk,
      Chapter4.SyHa, Matrix.of_apply]
    rw [if_pos (by omega), Polynomial.leadingCoeff,
      show Q.natDegree - (j - 1) - 1 - 0 = Q.natDegree - j from by omega,
      show P.natDegree + Q.natDegree - (j - 1) - 1 - 0 = P.natDegree + (Q.natDegree - j) from by omega,
      Polynomial.coeff_X_pow_mul]
  have hmcast : m - 2 = P.natDegree + Q.natDegree - 2 * j := by simp only [hm_def]; omega
  have htb22 : Mb2.toBlocks₂₂.det = Azurite.BPR.Chapter4.sRes P Q j := by
    rw [Chapter4.sRes, if_pos hjq,
      show Mb2.toBlocks₂₂ = (Chapter4.SyHaSquare P Q j).submatrix (finCongr hmcast) (finCongr hmcast) from ?_,
      Matrix.det_submatrix_equiv_self]
    ext a b
    simp only [hMb2, Matrix.toBlocks₂₂, Matrix.submatrix_apply, hN', hA, he2r,
      Chapter4.SyHaSquare, Chapter4.SyHa, Matrix.of_apply, Fin.val_castLE, finCongr_apply,
      Fin.val_cast, id_eq]
    split_ifs with h1 h2
    · rw [show Q.natDegree - (j - 1) - 1 - (1 + (a : ℕ)) = Q.natDegree - j - 1 - (a : ℕ) from by omega,
        show P.natDegree + Q.natDegree - (j - 1) - 1 - (1 + (b : ℕ))
          = P.natDegree + Q.natDegree - j - 1 - (b : ℕ) from by omega]
    · exfalso; omega
    · exfalso; omega
    · rw [show 1 + (a : ℕ) - (Q.natDegree - (j - 1)) = (a : ℕ) - (Q.natDegree - j) from by omega,
        show P.natDegree + Q.natDegree - (j - 1) - 1 - (1 + (b : ℕ))
          = P.natDegree + Q.natDegree - j - 1 - (b : ℕ) from by omega]
  rw [show N'.det = Mb2.det from (Matrix.det_submatrix_equiv_self e2 _).symm]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mb2]
  rw [htb21, Matrix.det_fromBlocks_zero₂₁, htb11, htb22]

/-- **BPR Proposition 8.42 (c), key coefficient identity.**  The coefficient of `X^{p-j}` in
    `sResV_{j-1}(P,Q)` is `a_p · sRes_j(P,Q)`. -/
theorem sResV_sub_one_coeff (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree) :
    (sResV P Q (j - 1)).coeff (P.natDegree - j)
      = P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q j :=
  (sResV_sub_one_coeff_eq_minor P Q hpq hj1 hjq).trans (sResV_minor_det_eq P Q hpq hj1 hjq)

/-- **BPR Proposition 8.42 (c), `sResV` part.**  Over a field, when `sResP_j(P,Q)` is
    non-defective (`sRes_j(P,Q) ≠ 0`), `deg(sResV_{j-1}(P,Q)) = p - j` and
    `lcof(sResV_{j-1}(P,Q)) = a_p · sRes_j(P,Q)`. -/
theorem sResV_sub_one_natDegree {K : Type*} [CommRing K] [IsDomain K] (P Q : K[X]) (hP : P ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree)
    (hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0) :
    (sResV P Q (j - 1)).natDegree = P.natDegree - j
    ∧ (sResV P Q (j - 1)).leadingCoeff = P.leadingCoeff * Azurite.BPR.Chapter4.sRes P Q j := by
  have hcoeff := sResV_sub_one_coeff P Q hpq hj1 hjq
  have hbound := sResV_natDegree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega)
  have hcne : (sResV P Q (j - 1)).coeff (P.natDegree - j) ≠ 0 := by
    rw [hcoeff]; exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) hsRes
  have hge := Polynomial.le_natDegree_of_ne_zero hcne
  have hnd : (sResV P Q (j - 1)).natDegree = P.natDegree - j := Nat.le_antisymm (by omega) hge
  exact ⟨hnd, by rw [Polynomial.leadingCoeff, hnd, hcoeff]⟩

/-- **BPR Proposition 8.42 (c), `sResU` part.**  Over a field, when `sResP_j(P,Q)` is
    non-defective (`sRes_j(P,Q) ≠ 0`), `deg(sResU_{j-1}(P,Q)) = q - j`.  (The top term of
    `sResV_{j-1}·Q` has degree `p+q-j`; since `sResP_{j-1}` has degree `≤ j-1`, the term
    `sResU_{j-1}·P` must match it, forcing `deg sResU_{j-1} = q-j`.) -/
theorem sResU_sub_one_natDegree {K : Type*} [Field K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree)
    (hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0) :
    (sResU P Q (j - 1)).natDegree = Q.natDegree - j := by
  have hid := sResP_eq_cofactor P Q hQ hpq (show j - 1 ≤ Q.natDegree by omega)
  have hvnd := (sResV_sub_one_natDegree P Q hP hpq hj1 hjq hsRes).1
  have hsResV_ne : sResV P Q (j - 1) ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hvnd; omega
  have hVQ_deg : (sResV P Q (j - 1) * Q).natDegree = P.natDegree + Q.natDegree - j := by
    rw [Polynomial.natDegree_mul hsResV_ne hQ, hvnd]; omega
  have hsResP_deg : (sResP P Q (j - 1)).natDegree ≤ j - 1 :=
    Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
  have hUP : sResU P Q (j - 1) * P = sResP P Q (j - 1) - sResV P Q (j - 1) * Q := by
    rw [hid]; ring
  have hUP_deg : (sResU P Q (j - 1) * P).natDegree = P.natDegree + Q.natDegree - j := by
    rw [hUP, Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by rw [hVQ_deg]; omega), hVQ_deg]
  have hUne : sResU P Q (j - 1) ≠ 0 := fun h => by
    rw [h, zero_mul, Polynomial.natDegree_zero] at hUP_deg; omega
  rw [Polynomial.natDegree_mul hUne hP] at hUP_deg
  omega

/-- **BPR matrix `B_{j,i}` (before equation (8.12)).**  For `sResP_{i-1}` nonzero of degree
    `j`, the `2 × 2` matrix of cofactors of the `(i-1)`-th and `(j-1)`-th relations of
    Proposition 8.42. -/
noncomputable def cofactorMat (P Q : D[X]) (i j : ℕ) : Matrix (Fin 2) (Fin 2) D[X] :=
  !![sResU P Q (i - 1), sResV P Q (i - 1);
     sResU P Q (j - 1), sResV P Q (j - 1)]

/-- **BPR equation (8.12).** `[sResP_{i-1}, sResP_{j-1}]ᵀ = B_{j,i} · [P, Q]ᵀ`: stacking the
    `(i-1)`-th and `(j-1)`-th cofactor relations of Proposition 8.42(a). -/
theorem cofactorMat_mulVec (P Q : D[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {i j : ℕ} (hiq : i - 1 ≤ Q.natDegree) (hjq : j - 1 ≤ Q.natDegree) :
    (cofactorMat P Q i j).mulVec ![P, Q] = ![sResP P Q (i - 1), sResP P Q (j - 1)] := by
  funext k
  fin_cases k
  · simp only [cofactorMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    exact (sResP_eq_cofactor P Q hQ hpq hiq).symm
  · simp only [cofactorMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    exact (sResP_eq_cofactor P Q hQ hpq hjq).symm

end Azurite.BPR.Chapter8
