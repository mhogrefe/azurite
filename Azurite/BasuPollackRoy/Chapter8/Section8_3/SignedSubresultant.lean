import Azurite.BasuPollackRoy.Chapter8.Section8_3.Lemma_8_31
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_27

/-!
# BPR §8.3.2.2, Notation 8.33: signed subresultant polynomials

For two non-zero polynomials `P, Q` of degrees `p, q` with `q < p` over an
integral domain `D`, and `0 ≤ j ≤ q`, the `j`-th **signed subresultant
polynomial** `sResP_j(P, Q)` is the polynomial determinant of the sequence

  `X^{q-j-1} P, …, P, Q, …, X^{p-j-1} Q`,

whose associated matrix is the Sylvester-Habicht matrix `SyHa_j(P, Q)`
(Notation 4.22). It has `p + q - 2j` rows and `p + q - j` columns, and
`deg(sResP_j(P, Q)) ≤ j`. The definitions are extended by convention for
`q < j ≤ p` by `sResP_p = P`, `sResP_{p-1} = Q`, and `sResP_j = 0` for
`q < j < p - 1` (and `sResP_{-1} = 0`).

Note this is the signed subresultant *polynomial* `sResP` of Chapter 8, distinct
from the signed subresultant *coefficient* `Azurite.BPR.Chapter4.sRes` of
Chapter 4 (which is the leading entry of the corresponding determinant).
-/

namespace Azurite.BPR.Chapter8

open Polynomial
open Azurite.BPR.Chapter4 (ε)

variable {D : Type*} [CommRing D]

/-- The polynomial determinant `pdet_{m,n}(𝒫)` has degree at most `n - m`, since
    it is a sum of `mᵢ · Xⁱ` over `i ≤ n - m`. -/
theorem pdetRing_degree_le {m n : ℕ} (P : Fin m → D[X]) :
    (pdetRing n P).degree ≤ (↑(n - m) : WithBot ℕ) := by
  rw [pdetRing]
  refine le_trans (Polynomial.degree_sum_le _ _) (Finset.sup_le (fun i _ => ?_))
  refine le_trans (Polynomial.degree_smul_le _ _) (le_trans (Polynomial.degree_X_pow_le _) ?_)
  exact_mod_cast Nat.lt_succ_iff.mp i.isLt

/-- Permuting the polynomial family by `σ` multiplies the polynomial determinant
    by `sign σ` (each minor is a determinant whose rows get permuted). -/
theorem pdetRing_comp_perm {m n : ℕ} (P : Fin m → D[X]) (σ : Equiv.Perm (Fin m)) :
    pdetRing n (P ∘ σ) = (Equiv.Perm.sign σ : ℤ) • pdetRing n P := by
  have hmr : ∀ i : ℕ, pdetMinorRing n (P ∘ σ) i
      = (Equiv.Perm.sign σ : ℤ) • pdetMinorRing n P i := by
    intro i
    rw [pdetMinorRing, pdetMinorRing,
      show pdetMinorMatRing n (P ∘ σ) i
        = (pdetMinorMatRing n P i).submatrix σ id from rfl,
      Matrix.det_permute, zsmul_eq_mul]
  rw [pdetRing, pdetRing]
  have hsum : (Equiv.Perm.sign σ : ℤ)
        • (∑ i : Fin (n - m + 1), pdetMinorRing n P (i : ℕ) • (X : D[X]) ^ (i : ℕ))
      = ∑ i : Fin (n - m + 1), (Equiv.Perm.sign σ : ℤ)
        • (pdetMinorRing n P (i : ℕ) • (X : D[X]) ^ (i : ℕ)) :=
    Finset.smul_sum
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hmr, smul_assoc])

/-- The polynomial determinant of a single polynomial `R` of degree `< n` is `R`
    (the `m = 1` case of `pdet`). -/
theorem pdetRing_single {n : ℕ} (hn : 0 < n) (R : D[X]) (hR : R.natDegree < n) :
    pdetRing n (fun _ : Fin 1 => R) = R := by
  have hmr : ∀ i : ℕ, pdetMinorRing n (fun _ : Fin 1 => R) i = R.coeff i := by
    intro i
    rw [pdetMinorRing, Matrix.det_fin_one]
    simp [pdetMinorMatRing, pdetColIdx]
  rw [pdetRing, Fin.sum_univ_eq_sum_range
    (fun k => pdetMinorRing n (fun _ : Fin 1 => R) k • X ^ k) (n - 1 + 1),
    show n - 1 + 1 = n by omega]
  conv_rhs => rw [as_sum_range' R n hR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hmr, smul_eq_C_mul, ← C_mul_X_pow_eq_monomial]

/-- The `m = 1` case of `pdet`, stated for a family on `Fin m` with `m = 1`
    (so it can absorb a `Fin (m - (m-1))` tail without transporting the type). -/
theorem pdetRing_single_of_eq {m n : ℕ} (hm : m = 1) (hn : 0 < n) (R : Fin m → D[X])
    (hR : (R ⟨0, by omega⟩).natDegree < n) : pdetRing n R = R ⟨0, by omega⟩ := by
  subst hm
  have hReq : R = fun _ : Fin 1 => R 0 := by funext x; rw [Subsingleton.elim x 0]
  rw [hReq]
  exact pdetRing_single hn (R 0) hR

/-- The polynomial determinant of the increasing shift family `Q, XQ, …, X^{m-1}Q`
    (degrees `q, q+1, …, q+m-1 = n-1`) is `ε_m · b_q^{m-1} · Q`. -/
theorem pdetRing_Q_shifts {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (Q : D[X]) (hQ0 : Q ≠ 0)
    (hq : Q.natDegree + m = n) :
    pdetRing n (fun r : Fin m => X ^ (r : ℕ) * Q)
      = (ε m : ℤ) • (C (Q.leadingCoeff ^ (m - 1)) * Q) := by
  haveI : Nontrivial D := Polynomial.nontrivial_iff.mp (nontrivial_of_ne Q 0 hQ0)
  -- reversing the family gives the decreasing shifts `X^{m-1}Q, …, Q`
  have hrev : (fun r : Fin m => X ^ (r : ℕ) * Q) ∘ ⇑(Fin.revPerm)
      = fun r : Fin m => X ^ (m - 1 - (r : ℕ)) * Q := by
    funext r
    have hval : (Fin.revPerm r : Fin m) = Fin.rev r := rfl
    simp only [Function.comp_apply, hval, Fin.val_rev]
    rw [show m - ((r : ℕ) + 1) = m - 1 - (r : ℕ) from by omega]
  -- the reversed (decreasing-degree) family collapses by triangular reduction
  have htri : pdetRing n (fun r : Fin m => X ^ (m - 1 - (r : ℕ)) * Q)
      = C (Q.leadingCoeff ^ (m - 1)) * Q := by
    have hd1 : ∀ r : Fin m, (r : ℕ) < m - 1 → ∀ j, n - 1 - (r : ℕ) < j →
        (X ^ (m - 1 - (r : ℕ)) * Q).coeff j = 0 := by
      intro r _ j hj
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_X_pow_mul _ hQ0]; omega
    have hd2 : ∀ r : Fin m, m - 1 ≤ (r : ℕ) → ∀ j, n - 1 - (m - 1) < j →
        (X ^ (m - 1 - (r : ℕ)) * Q).coeff j = 0 := by
      intro r hr j hj
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_X_pow_mul _ hQ0]; omega
    rw [pdetRing_triangular (by omega) hmn _ hd1 hd2]
    congr 1
    · congr 1
      trans (∏ _i : Fin (m - 1), Q.leadingCoeff)
      · apply Finset.prod_congr rfl
        intro i _
        have hi := i.isLt
        show (X ^ (m - 1 - (i : ℕ)) * Q).coeff (n - 1 - (i : ℕ)) = Q.leadingCoeff
        rw [show n - 1 - (i : ℕ) = Q.natDegree + (m - 1 - (i : ℕ)) from by omega,
          coeff_X_pow_mul, Polynomial.coeff_natDegree]
      · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [pdetRing_single_of_eq (by omega) (by omega) _ (by simp; omega)]
      simp
  -- assemble: pdet(fam) = ε_m • pdet(revfam) using ε_m² = 1
  have hperm := pdetRing_comp_perm (n := n) (fun r : Fin m => X ^ (r : ℕ) * Q) Fin.revPerm
  rw [hrev, Azurite.BPR.Chapter4.sign_revPerm, htri] at hperm
  rw [hperm, smul_smul, show (ε m : ℤ) * ε m = 1 from ?_, one_smul]
  rw [Azurite.BPR.Chapter4.ε, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- **BPR Notation 8.33.** The `j`-th signed subresultant *polynomial*
    `sResP_j(P, Q)`: for `j ≤ q`, the polynomial determinant of the sequence
    `X^{q-j-1} P, …, P, Q, …, X^{p-j-1} Q` (whose matrix is `SyHa_j(P, Q)`); and
    by convention `sResP_p = P`, `sResP_{p-1} = Q`, `sResP_j = 0` in the gap. -/
noncomputable def sResP (P Q : D[X]) (j : ℕ) : D[X] :=
  if j ≤ Q.natDegree then
    pdetRing (P.natDegree + Q.natDegree - j)
      (fun r : Fin (P.natDegree + Q.natDegree - 2 * j) =>
        if (r : ℕ) < Q.natDegree - j then X ^ (Q.natDegree - j - 1 - (r : ℕ)) * P
        else X ^ ((r : ℕ) - (Q.natDegree - j)) * Q)
  else if j = P.natDegree then P
  else if j = P.natDegree - 1 then Q
  else 0

/-- `deg(sResP_j(P, Q)) ≤ j` for `0 ≤ j ≤ q` (BPR's "Clearly …"). -/
theorem sResP_degree_le (P Q : D[X]) (hpq : Q.natDegree < P.natDegree)
    {j : ℕ} (hj : j ≤ Q.natDegree) :
    (sResP P Q j).degree ≤ (j : WithBot ℕ) := by
  rw [sResP, if_pos hj]
  refine le_trans (pdetRing_degree_le _) ?_
  exact_mod_cast
    (show P.natDegree + Q.natDegree - j - (P.natDegree + Q.natDegree - 2 * j) ≤ j by omega)

/-- Convention: `sResP_p(P, Q) = P`. -/
theorem sResP_eq_self (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) :
    sResP P Q P.natDegree = P := by
  rw [sResP, if_neg (by omega), if_pos rfl]

/-- Convention: `sResP_{p-1}(P, Q) = Q` (in the proper gap `q < p - 1`). -/
theorem sResP_eq_self_Q (P Q : D[X]) (hpq : Q.natDegree + 1 < P.natDegree) :
    sResP P Q (P.natDegree - 1) = Q := by
  rw [sResP, if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- Convention: `sResP_j(P, Q) = 0` for `q < j` with `j ∉ {p-1, p}` (the defective
    subresultants in the degree gap vanish). -/
theorem sResP_eq_zero (P Q : D[X]) {j : ℕ} (h1 : Q.natDegree < j)
    (h2 : j ≠ P.natDegree) (h3 : j ≠ P.natDegree - 1) :
    sResP P Q j = 0 := by
  rw [sResP, if_neg (by omega), if_neg h2, if_neg h3]

/-- The coefficient of `Xⁱ` in `pdet_{m,n}(𝒫)` is the minor `mᵢ`, for `i ≤ n - m`. -/
theorem pdetRing_coeff {m n : ℕ} (P : Fin m → D[X]) {i₀ : ℕ} (hi₀ : i₀ ≤ n - m) :
    (pdetRing n P).coeff i₀ = pdetMinorRing n P i₀ := by
  rw [pdetRing, Polynomial.finsetSum_coeff,
    Fin.sum_univ_eq_sum_range (fun k => (pdetMinorRing n P k • (X : D[X]) ^ k).coeff i₀) (n - m + 1),
    Finset.sum_eq_single i₀]
  · rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The signed subresultant coefficient is the coefficient of `Xʲ` in `sResP_j`.**
    `sRes_j(P, Q)` (Notation 4.22) equals the coefficient of `Xʲ` in
    `sResP_j(P, Q)`, for `j ≤ p`. -/
theorem coeff_sResP (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hj : j ≤ P.natDegree) :
    (sResP P Q j).coeff j = Azurite.BPR.Chapter4.sRes P Q j := by
  rcases le_or_gt j Q.natDegree with hjq | hjq
  · -- `j ≤ q`: both sides are the determinant of the (square) Sylvester-Habicht matrix.
    have hcol : ∀ c : Fin (P.natDegree + Q.natDegree - 2 * j),
        pdetColIdx (P.natDegree + Q.natDegree - j) j c
          = P.natDegree + Q.natDegree - j - 1 - (c : ℕ) := by
      intro c
      rw [pdetColIdx]
      split
      · rfl
      · have := c.isLt; omega
    rw [sResP, if_pos hjq, pdetRing_coeff _ (by omega), pdetMinorRing,
      Azurite.BPR.Chapter4.sRes, if_pos hjq]
    congr 1
    ext r c
    simp only [pdetMinorMatRing, Azurite.BPR.Chapter4.SyHaSquare, Matrix.submatrix_apply,
      Azurite.BPR.Chapter4.SyHa, Matrix.of_apply, id_eq, Fin.val_castLE, hcol]
    by_cases h : (r : ℕ) < Q.natDegree - j <;> simp [h]
  · -- `q < j ≤ p`: the convention cases.
    rw [Azurite.BPR.Chapter4.sRes, if_neg (by omega), if_pos hpq]
    rcases eq_or_ne j P.natDegree with hjp | hjp
    · subst hjp
      rw [if_pos rfl, sResP_eq_self P Q hpq, Polynomial.coeff_natDegree]
    · rw [if_neg hjp]
      rcases eq_or_ne j (P.natDegree - 1) with hjp1 | hjp1
      · rw [hjp1, sResP_eq_self_Q P Q (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      · rw [sResP_eq_zero P Q hjq hjp hjp1, Polynomial.coeff_zero]

/-- `sResP_j(P, Q)` is **non-defective** if `deg(sResP_j(P, Q)) = j`. -/
def IsNonDefective (P Q : D[X]) (j : ℕ) : Prop := (sResP P Q j).degree = (j : WithBot ℕ)

/-- `sResP_j(P, Q)` is **defective of degree `k`** if `deg(sResP_j(P, Q)) = k < j`. -/
def IsDefectiveOfDegree (P Q : D[X]) (j k : ℕ) : Prop :=
  (sResP P Q j).degree = (k : WithBot ℕ) ∧ k < j

/-- For `0 ≤ j ≤ q`, `sResP_j(P, Q)` is non-defective iff `sRes_j(P, Q) ≠ 0`. -/
theorem isNonDefective_iff_sRes_ne_zero (P Q : D[X]) (hpq : Q.natDegree < P.natDegree)
    {j : ℕ} (hj : j ≤ Q.natDegree) :
    IsNonDefective P Q j ↔ Azurite.BPR.Chapter4.sRes P Q j ≠ 0 := by
  rw [IsNonDefective, ← coeff_sResP P Q hpq (by omega)]
  constructor
  · intro h
    exact Polynomial.coeff_ne_zero_of_eq_degree h
  · intro h
    exact le_antisymm (sResP_degree_le P Q hpq hj) (Polynomial.le_degree_of_ne_zero h)

/-- **Theorem 8.34 (notation).** When `sResP_j(P, Q)` is non-defective (degree exactly
    `j`), its leading coefficient `t_j` equals the signed subresultant coefficient
    `s_j = sRes_j(P, Q)`. -/
theorem leadingCoeff_sResP_eq_sRes (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hj : j ≤ Q.natDegree) (hnd : IsNonDefective P Q j) :
    (sResP P Q j).leadingCoeff = Azurite.BPR.Chapter4.sRes P Q j := by
  rw [Polynomial.leadingCoeff, natDegree_eq_of_degree_eq_some hnd, coeff_sResP P Q hpq (by omega)]

/-- **BPR Notation 8.33 (closing note).** `sResP_q(P, Q) = ε_{p-q} · b_q^{p-q-1} · Q`. -/
theorem sResP_eq_of_natDegree (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) (hQ0 : Q ≠ 0) :
    sResP P Q Q.natDegree
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (C (Q.leadingCoeff ^ (P.natDegree - Q.natDegree - 1)) * Q) := by
  rw [sResP, if_pos (le_refl _)]
  have hfun : (fun r : Fin (P.natDegree + Q.natDegree - 2 * Q.natDegree) =>
        if (r : ℕ) < Q.natDegree - Q.natDegree then
          X ^ (Q.natDegree - Q.natDegree - 1 - (r : ℕ)) * P
        else X ^ ((r : ℕ) - (Q.natDegree - Q.natDegree)) * Q)
      = fun r : Fin (P.natDegree + Q.natDegree - 2 * Q.natDegree) => X ^ (r : ℕ) * Q := by
    funext r; simp
  rw [hfun, pdetRing_Q_shifts (by omega) (by omega) Q hQ0 (by omega),
    show P.natDegree + Q.natDegree - 2 * Q.natDegree = P.natDegree - Q.natDegree from by omega]

/-- **The signed subresultant coefficient `s_q = sRes_q(P, Q) = ε_{p-q} · b_q^{p-q}`**:
    the coefficient of `X^q` in the closing-note value of `sResP_q(P, Q)`. -/
theorem sRes_natDegree (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) (hQ0 : Q ≠ 0) :
    Azurite.BPR.Chapter4.sRes P Q Q.natDegree
      = (ε (P.natDegree - Q.natDegree) : ℤ) • Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
  rw [← coeff_sResP P Q hpq (le_of_lt hpq), sResP_eq_of_natDegree P Q hpq hQ0]
  rw [zsmul_eq_mul, zsmul_eq_mul, ← C_eq_intCast, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_natDegree, mul_assoc, ← pow_succ,
    show P.natDegree - Q.natDegree - 1 + 1 = P.natDegree - Q.natDegree from by omega]

end Azurite.BPR.Chapter8
