import Azurite.BasuPollackRoy.Chapter4.Section4_1.Subdiscriminant
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_9
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_8
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_22

/-!
# BPR Proposition 4.28: `a_p · sDisc_{p-k}(P) = sRes_{p-k}(P, P')`

For `P : K[X]` of positive degree and `0 < k ≤ p := P.natDegree`,

  `a_p · sDisc_{p-k}(P) = sRes_{p-k}(P, P')` (BPR equation (4.4)).

## Proof structure

BPR factors `SyHa_{p-k, p-k}(P, P')` as `D_k · D_k'` where `D_k` has
identity rows on top and Newton-sum rows below (so
`det D_k = det(newtMat P k)`), and `D_k'` is upper-triangular with
`a_p` on the diagonal (so `det D_k' = a_p^{2k-1}`). The matrix
identity uses BPR's relations (4.1), i.e. the Newton recurrence
`j · a_j = ∑_{m ≥ j} a_m · N_{m-j}` from Proposition 4.8.

Combined with Proposition 4.9
(`sDisc_{p-k}(P) = a_p^{2k-2} · det(newtMat P k)`):

  `sRes_{p-k}(P, P') = det D_k · det D_k' = a_p^{2k-1} · det(newtMat)`
                    `= a_p · sDisc_{p-k}(P)`.

The `(2k-1) × (2k-1)` dimension of `SyHa_{p-k, p-k}(P, P')` is encoded
in Lean as `Fin (p + q - 2j)` with `q = p - 1` and `j = p - k`, which
is propositionally (but not definitionally) `Fin (2k-1)`. We reindex
via `finCongr` to align the types.
-/

namespace Azurite.BPR.Chapter4

open Polynomial Matrix

variable {K : Type*} [Field K] [CharZero K]
variable {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-! ### The matrices `D_k` and `D_k'` -/

/-- `D_k'` is the `(2k-1) × (2k-1)` upper-triangular matrix from BPR's
    proof of Proposition 4.28: entry `(i, j)` with `i ≤ j ≤ i + p`
    equals `(algebraMap K C) (P.coeff (p + i - j))`, and `0` outside
    that range (in particular `0` below the diagonal). The upper bound
    `j ≤ i + p` enforces BPR's `a_l = 0` convention for `l < 0`. -/
private noncomputable def DkPrime (P : K[X]) (k : ℕ) :
    Matrix (Fin (2 * k - 1)) (Fin (2 * k - 1)) C :=
  Matrix.of fun i j =>
    if i.val ≤ j.val ∧ j.val ≤ i.val + P.natDegree then
      algebraMap K C (P.coeff (P.natDegree + i.val - j.val))
    else 0

/-- `D_k` is the `(2k-1) × (2k-1)` matrix from BPR's proof of
    Proposition 4.28: identity rows for `0 ≤ i ≤ k-2`, Newton-sum rows
    for `k-1 ≤ i ≤ 2k-2`. -/
private noncomputable def Dk (P : K[X]) (k : ℕ) :
    Matrix (Fin (2 * k - 1)) (Fin (2 * k - 1)) C :=
  Matrix.of fun i l =>
    if i.val < k - 1 then
      if l.val = i.val then 1 else 0
    else
      if 2 * k - 2 - i.val ≤ l.val then
        newtonSum P (l.val - (2 * k - 2 - i.val))
      else 0

/-! ### `det(D_k') = a_p^{2k-1}` -/

omit [CharZero K] [IsAlgClosed C] in
private lemma DkPrime_blockTriangular (P : K[X]) (k : ℕ) :
    (DkPrime (C := C) P k).BlockTriangular id := by
  intro i j h_ji
  unfold DkPrime
  rw [Matrix.of_apply, if_neg]
  intro h
  exact absurd h.1 (not_le_of_gt h_ji)

omit [CharZero K] [IsAlgClosed C] in
private lemma DkPrime_diag (P : K[X]) (k : ℕ) (i : Fin (2 * k - 1)) :
    (DkPrime (C := C) P k) i i = algebraMap K C P.leadingCoeff := by
  unfold DkPrime
  rw [Matrix.of_apply, if_pos ⟨le_rfl, Nat.le_add_right _ _⟩, Nat.add_sub_cancel]
  rfl

omit [CharZero K] [IsAlgClosed C] in
private theorem DkPrime_det (P : K[X]) (k : ℕ) :
    (DkPrime (C := C) P k).det =
      algebraMap K C P.leadingCoeff ^ (2 * k - 1) := by
  rw [Matrix.det_of_upperTriangular (DkPrime_blockTriangular P k)]
  simp_rw [DkPrime_diag]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### `det(D_k) = det(newtMat P k)` -/

private noncomputable def splitFin (k : ℕ) (h : 1 ≤ k) :
    Fin (k - 1) ⊕ Fin k ≃ Fin (2 * k - 1) :=
  finSumFinEquiv.trans (finCongr (show k - 1 + k = 2 * k - 1 from by omega))

omit [CharZero K] in
private lemma splitFin_symm_apply (k : ℕ) (h : 1 ≤ k) (m : Fin (2 * k - 1)) :
    (splitFin k h).symm m =
      if h_m : m.val < k - 1 then Sum.inl ⟨m.val, h_m⟩
      else Sum.inr ⟨m.val - (k - 1), by have := m.isLt; omega⟩ := by
  unfold splitFin
  simp only [Equiv.symm_trans_apply, finCongr_symm]
  by_cases h_m : m.val < k - 1
  · rw [dif_pos h_m]
    have h_cast :
        (finCongr (show 2 * k - 1 = k - 1 + k from by omega)) m =
          Fin.castAdd k ⟨m.val, h_m⟩ := by
      apply Fin.ext; simp [finCongr_apply, Fin.castAdd, Fin.castLE]
    rw [h_cast, finSumFinEquiv_symm_apply_castAdd]
  · rw [dif_neg h_m]
    have h_ge : k - 1 ≤ m.val := Nat.le_of_not_lt h_m
    have h_lt : m.val - (k - 1) < k := by have := m.isLt; omega
    have h_cast :
        (finCongr (show 2 * k - 1 = k - 1 + k from by omega)) m =
          Fin.natAdd (k - 1) ⟨m.val - (k - 1), h_lt⟩ := by
      apply Fin.ext
      simp [finCongr_apply, Fin.natAdd]
      omega
    rw [h_cast, finSumFinEquiv_symm_apply_natAdd]

omit [CharZero K] [IsAlgClosed C] in
/-- `D_k` factors through `splitFin` as block matrix `[[I, 0], [A, newtMat]]`. -/
private theorem Dk_eq_fromBlocks (P : K[X]) (k : ℕ) (h : 1 ≤ k) :
    Dk (C := C) P k =
      (Matrix.fromBlocks
        (1 : Matrix (Fin (k - 1)) (Fin (k - 1)) C)
        (0 : Matrix (Fin (k - 1)) (Fin k) C)
        (Matrix.of fun (i : Fin k) (l : Fin (k - 1)) =>
          if 2 * k - 2 - (i.val + (k - 1)) ≤ l.val then
            newtonSum P (l.val - (2 * k - 2 - (i.val + (k - 1))))
          else 0)
        (newtMat P k : Matrix (Fin k) (Fin k) C)).submatrix
          (splitFin k h).symm (splitFin k h).symm := by
  ext i l
  rw [Matrix.submatrix_apply]
  rw [splitFin_symm_apply, splitFin_symm_apply]
  unfold Dk
  rw [Matrix.of_apply]
  by_cases h_i : i.val < k - 1
  · rw [dif_pos h_i, if_pos h_i]
    by_cases h_l : l.val < k - 1
    · rw [dif_pos h_l, Matrix.fromBlocks_apply₁₁]
      show (if l.val = i.val then (1 : C) else 0) =
        (1 : Matrix (Fin (k - 1)) (Fin (k - 1)) C) ⟨i.val, h_i⟩ ⟨l.val, h_l⟩
      rw [Matrix.one_apply]
      by_cases h_eq : i.val = l.val
      · rw [if_pos h_eq.symm]
        rw [if_pos]
        exact Fin.ext h_eq
      · rw [if_neg fun h => h_eq h.symm]
        rw [if_neg]
        intro h
        exact h_eq (Fin.mk.inj_iff.mp h)
    · rw [dif_neg h_l, Matrix.fromBlocks_apply₁₂]
      show (if l.val = i.val then (1 : C) else 0) = (0 : Matrix _ _ _) _ _
      rw [Matrix.zero_apply]
      rw [if_neg (by omega)]
  · rw [dif_neg h_i, if_neg h_i]
    have h_i_ge : k - 1 ≤ i.val := Nat.le_of_not_lt h_i
    by_cases h_l : l.val < k - 1
    · rw [dif_pos h_l, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
      have h_simp : (i.val - (k - 1)) + (k - 1) = i.val := by omega
      rw [h_simp]
    · rw [dif_neg h_l, Matrix.fromBlocks_apply₂₂]
      have h_l_ge : k - 1 ≤ l.val := Nat.le_of_not_lt h_l
      have h_ile : 2 * k - 2 - i.val ≤ l.val := by
        have := i.isLt; have := l.isLt; omega
      rw [if_pos h_ile]
      unfold newtMat
      rw [Matrix.of_apply]
      congr 1
      show l.val - (2 * k - 2 - i.val) = (i.val - (k - 1)) + (l.val - (k - 1))
      omega

omit [CharZero K] [IsAlgClosed C] in
private theorem Dk_det (P : K[X]) (k : ℕ) (h : 1 ≤ k) :
    (Dk (C := C) P k).det = (newtMat P k).det := by
  rw [Dk_eq_fromBlocks P k h]
  rw [Matrix.det_submatrix_equiv_self]
  rw [Matrix.det_fromBlocks_zero₁₂]
  rw [Matrix.det_one, one_mul]

/-! ### The product `D_k · D_k'` matches `SyHaSquare(P, P', p-k)` -/

/-- The reindex equiv used to align `SyHaSquare`'s natural dimension
    `Fin (p + q - 2 (p - k))` with the cleaner `Fin (2 k - 1)`. -/
private noncomputable def syHaReindex (P : K[X]) (k : ℕ)
    (h_size : 2 * k - 1 =
      P.natDegree + P.derivative.natDegree - 2 * (P.natDegree - k)) :
    Fin (2 * k - 1) ≃
      Fin (P.natDegree + P.derivative.natDegree - 2 * (P.natDegree - k)) :=
  finCongr h_size

omit [CharZero K] [IsAlgClosed C] in
/-- The `(i, l)` entry of the lifted Sylvester-Habicht submatrix, after
    reindexing along `syHaReindex`, written out in a clean shifted form. -/
private lemma SyHaSquare_map_reindex_apply (P : K[X])
    (hk_pos : 0 < k) (hk_le : k ≤ P.natDegree)
    (h_p_deriv : P.derivative.natDegree = P.natDegree - 1)
    (h_size : 2 * k - 1 =
      P.natDegree + P.derivative.natDegree - 2 * (P.natDegree - k))
    (i l : Fin (2 * k - 1)) :
    ((SyHaSquare P P.derivative (P.natDegree - k)).map
        (algebraMap K C)).submatrix
          (syHaReindex P k h_size) (syHaReindex P k h_size) i l =
      algebraMap K C (if i.val < k - 1 then
        (X ^ (k - 1 - 1 - i.val) * P).coeff (P.natDegree + k - 2 - l.val)
      else
        (X ^ (i.val - (k - 1)) * P.derivative).coeff
          (P.natDegree + k - 2 - l.val)) := by
  rw [Matrix.submatrix_apply, Matrix.map_apply]
  unfold SyHaSquare
  rw [Matrix.submatrix_apply]
  unfold SyHa
  rw [Matrix.of_apply]
  -- syHaReindex preserves .val.
  have h_si : (syHaReindex P k h_size i).val = i.val := by
    unfold syHaReindex; simp [finCongr_apply]
  have h_sl_val : (syHaReindex P k h_size l).val = l.val := by
    unfold syHaReindex; simp [finCongr_apply]
  have h_castLE_val :
      (Fin.castLE (show P.natDegree + P.derivative.natDegree -
        2 * (P.natDegree - k) ≤ P.natDegree +
        P.derivative.natDegree - (P.natDegree - k) from by omega)
        (syHaReindex P k h_size l)).val = l.val := h_sl_val
  simp only [id_eq]
  rw [h_si, h_castLE_val]
  rw [show P.derivative.natDegree - (P.natDegree - k) = k - 1 from by
        rw [h_p_deriv]; omega]
  rw [show P.natDegree + P.derivative.natDegree - (P.natDegree - k) - 1 =
        P.natDegree + k - 2 from by rw [h_p_deriv]; omega]

omit [CharZero K] [IsAlgClosed C] in
/-- For `i.val ≥ k - 1`, the P'-row coefficient simplifies to
    `j · P.coeff j` where `j := p + 2k - 2 - i.val - l.val` (Nat).
    Out-of-range cases give `0 · a_0 = 0` automatically. -/
private lemma SyHa_P_prime_row_coeff_eq_j_aj (P : K[X]) (k : ℕ)
    (hk_pos : 0 < k) (hk_le : k ≤ P.natDegree)
    (i l : Fin (2 * k - 1)) (h_i : k - 1 ≤ i.val) :
    (X ^ (i.val - (k - 1)) * P.derivative).coeff
        (P.natDegree + k - 2 - l.val) =
      ((P.natDegree + 2 * k - 2 - i.val - l.val : ℕ) : K) *
        P.coeff (P.natDegree + 2 * k - 2 - i.val - l.val) := by
  rw [show (X : K[X]) ^ (i.val - (k - 1)) * P.derivative =
      P.derivative * X ^ (i.val - (k - 1)) from by ring]
  rw [Polynomial.coeff_mul_X_pow']
  have hi_lt := i.isLt
  have hl_lt := l.isLt
  by_cases h_shift : i.val - (k - 1) ≤ P.natDegree + k - 2 - l.val
  · rw [if_pos h_shift, Polynomial.coeff_derivative]
    have h_pos : P.natDegree + k - 2 - l.val - (i.val - (k - 1)) + 1 =
        P.natDegree + 2 * k - 2 - i.val - l.val := by omega
    have h_cast : ((P.natDegree + k - 2 - l.val - (i.val - (k - 1)) : ℕ) : K) + 1 =
        ((P.natDegree + 2 * k - 2 - i.val - l.val : ℕ) : K) := by
      rw [show ((P.natDegree + k - 2 - l.val - (i.val - (k - 1)) : ℕ) : K) + 1 =
          (((P.natDegree + k - 2 - l.val - (i.val - (k - 1)) + 1 : ℕ) : K)) from by
          push_cast; ring]
      congr 1
    -- LHS: P.coeff (a + 1) * (↑a + 1) where a = p+k-2-l-(i-(k-1))
    -- We have a + 1 = p+2k-2-i-l in Nat, and ↑a + 1 = ↑(p+2k-2-i-l) in K.
    rw [h_pos, h_cast, mul_comm]
  · rw [if_neg h_shift]
    push Not at h_shift
    have h_j_zero : P.natDegree + 2 * k - 2 - i.val - l.val = 0 := by omega
    rw [h_j_zero, Nat.cast_zero, zero_mul]

omit [CharZero K] [IsAlgClosed C] in
/-- For `i.val < k - 1`, the P-row of `SyHa` matches the
    `D_k'` upper-triangular pattern. -/
private lemma SyHa_P_row_eq_coeff (P : K[X]) (k : ℕ) (hk_pos : 0 < k)
    (hk_le : k ≤ P.natDegree)
    (i l : Fin (2 * k - 1)) (h_i : i.val < k - 1) :
    (X ^ (k - 1 - 1 - i.val) * P).coeff (P.natDegree + k - 2 - l.val) =
      if i.val ≤ l.val ∧ l.val ≤ i.val + P.natDegree then
        P.coeff (P.natDegree + i.val - l.val) else 0 := by
  rw [show (X : K[X]) ^ (k - 1 - 1 - i.val) * P = P * X ^ (k - 1 - 1 - i.val)
      from by ring]
  rw [Polynomial.coeff_mul_X_pow']
  have hi_lt := i.isLt
  have hl_lt := l.isLt
  by_cases h_il : i.val ≤ l.val ∧ l.val ≤ i.val + P.natDegree
  · obtain ⟨h_il_le, h_il_bd⟩ := h_il
    have h_shift_le : k - 1 - 1 - i.val ≤ P.natDegree + k - 2 - l.val := by
      have : k - 2 - i.val ≤ P.natDegree + k - 2 - l.val := by omega
      have : k - 1 - 1 = k - 2 := by omega
      omega
    rw [if_pos h_shift_le]
    rw [if_pos ⟨h_il_le, h_il_bd⟩]
    congr 1; omega
  · rw [if_neg h_il]
    rw [not_and_or] at h_il
    rcases h_il with h_not_le | h_not_bd
    · push Not at h_not_le
      by_cases h_shift : k - 1 - 1 - i.val ≤ P.natDegree + k - 2 - l.val
      · rw [if_pos h_shift]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hp_ge_k : P.natDegree ≥ k := hk_le
        have h_simp : k - 1 - 1 = k - 2 := by omega
        omega
      · rw [if_neg h_shift]
    · push Not at h_not_bd
      have h_simp : k - 1 - 1 - i.val = k - 2 - i.val := by omega
      rw [h_simp]
      have h_shift_gt : ¬ k - 2 - i.val ≤ P.natDegree + k - 2 - l.val := by
        have hp_ge_k : P.natDegree ≥ k := hk_le
        omega
      rw [if_neg h_shift_gt]

omit [CharZero K] in
/-- **Key entry-wise identity.** With `D_k`, `D_k'` defined over the
    aligned dimension `Fin (2k-1)`, their product matches the lifted
    Sylvester-Habicht submatrix `SyHa_{p-k,p-k}(P, P').map (algebraMap K C)`. -/
private theorem Dk_mul_DkPrime_eq_SyHaSquare_map (P : K[X])
    (hP : 0 < P.natDegree) (k : ℕ) (hk_pos : 0 < k)
    (hk_le : k ≤ P.natDegree)
    (h_p_deriv : P.derivative.natDegree = P.natDegree - 1)
    (h_size : 2 * k - 1 =
      P.natDegree + P.derivative.natDegree - 2 * (P.natDegree - k)) :
    Dk (C := C) P k * DkPrime (C := C) P k =
      ((SyHaSquare P P.derivative (P.natDegree - k)).map
        (algebraMap K C)).submatrix
          (syHaReindex P k h_size) (syHaReindex P k h_size) := by
  ext i l
  rw [Matrix.mul_apply]
  rw [SyHaSquare_map_reindex_apply P hk_pos hk_le h_p_deriv h_size]
  by_cases h_i : i.val < k - 1
  · -- P-row case: D_k row i is the identity row at column i, so the
    -- sum collapses to DkPrime i l.
    rw [if_pos h_i]
    rw [SyHa_P_row_eq_coeff P k hk_pos hk_le i l h_i]
    have h_collapse :
        ∑ m : Fin (2 * k - 1), (Dk P k i m) * (DkPrime (C := C) P k m l) =
          DkPrime P k i l := by
      rw [Finset.sum_eq_single i]
      · unfold Dk
        rw [Matrix.of_apply, if_pos h_i, if_pos rfl, one_mul]
      · intro m _ h_ne
        unfold Dk
        rw [Matrix.of_apply, if_pos h_i]
        rw [if_neg (fun h => h_ne (Fin.ext h))]
        rw [zero_mul]
      · intro h_no; exact absurd (Finset.mem_univ i) h_no
    rw [h_collapse]
    unfold DkPrime
    rw [Matrix.of_apply]
    by_cases h_il : i.val ≤ l.val ∧ l.val ≤ i.val + P.natDegree
    · rw [if_pos h_il, if_pos h_il]
    · rw [if_neg h_il, if_neg h_il, RingHom.map_zero]
  · -- P'-row case: use Prop 4.8 Newton recurrence at
    -- j := P.natDegree + 2k - 2 - i.val - l.val.
    rw [if_neg h_i]
    push Not at h_i
    rw [SyHa_P_prime_row_coeff_eq_j_aj P k hk_pos hk_le i l h_i]
    rw [(algebraMap K C).map_mul]
    rw [show ((algebraMap K C) ((P.natDegree + 2 * k - 2 - i.val - l.val : ℕ) : K)) =
        ((P.natDegree + 2 * k - 2 - i.val - l.val : ℕ) : C) from by
      push_cast; rfl]
    -- Reduce the product inner term to a clean form.
    have h_inner : ∀ m : Fin (2 * k - 1),
        Dk (C := C) P k i m * DkPrime P k m l =
          if 2 * k - 2 - i.val ≤ m.val ∧ m.val ≤ l.val ∧
              l.val ≤ m.val + P.natDegree then
            newtonSum P (m.val - (2 * k - 2 - i.val)) *
              algebraMap K C (P.coeff (P.natDegree + m.val - l.val))
          else 0 := by
      intro m
      unfold Dk DkPrime
      rw [Matrix.of_apply, Matrix.of_apply]
      rw [if_neg (not_lt_of_ge h_i)]
      by_cases h_c1 : 2 * k - 2 - i.val ≤ m.val
      · rw [if_pos h_c1]
        by_cases h_c2 : m.val ≤ l.val ∧ l.val ≤ m.val + P.natDegree
        · rw [if_pos h_c2]
          rw [if_pos ⟨h_c1, h_c2.1, h_c2.2⟩]
        · rw [if_neg h_c2, mul_zero]
          rw [if_neg]
          intro h
          exact h_c2 ⟨h.2.1, h.2.2⟩
      · rw [if_neg h_c1, zero_mul]
        rw [if_neg]
        intro h; exact h_c1 h.1
    rw [Finset.sum_congr rfl (fun m _ => h_inner m)]
    -- Convert the Fin sum to a Finset.range sum.
    rw [Fin.sum_univ_eq_sum_range
      (fun mv => if 2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree then
        newtonSum P (mv - (2 * k - 2 - i.val)) *
          algebraMap K C (P.coeff (P.natDegree + mv - l.val))
      else 0) (2 * k - 1)]
    -- Apply the case split on whether j is positive or 0.
    by_cases hj_pos : l.val + i.val ≤ P.natDegree + 2 * k - 2
    · -- Case A: l + i ≤ p + 2k - 2 (no Nat clipping for j).
      -- Two sub-cases: A1 (j ≤ p, apply Prop 4.8) and A2 (j > p, both 0).
      set j : ℕ := P.natDegree + 2 * k - 2 - i.val - l.val with hj_def
      -- Bijection: m_p = P.natDegree + mv - l.val on the valid range.
      -- Valid range = [2k-2-i.val, l.val] (when 2k-2-i.val ≤ l.val).
      have h_sum_eq :
          ∑ mv ∈ Finset.range (2 * k - 1),
            (if 2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree then
              newtonSum P (mv - (2 * k - 2 - i.val)) *
                algebraMap K C (P.coeff (P.natDegree + mv - l.val))
            else 0) =
          ∑ m_p ∈ Finset.Ico j (P.natDegree + 1),
            algebraMap K C (P.coeff m_p) * newtonSum P (m_p - j) := by
        rw [show (∑ mv ∈ Finset.range (2 * k - 1),
            (if 2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree then
              newtonSum P (mv - (2 * k - 2 - i.val)) *
                algebraMap K C (P.coeff (P.natDegree + mv - l.val))
            else 0)) =
            ∑ mv ∈ (Finset.range (2 * k - 1)).filter (fun mv =>
                2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree),
              newtonSum P (mv - (2 * k - 2 - i.val)) *
                algebraMap K C (P.coeff (P.natDegree + mv - l.val)) from
          (Finset.sum_filter _ _).symm]
        apply Finset.sum_nbij'
          (i := fun mv => P.natDegree + mv - l.val)
          (j := fun m_p => m_p + l.val - P.natDegree)
        · intro mv hmv
          rw [Finset.mem_filter, Finset.mem_range] at hmv
          rw [Finset.mem_Ico]
          obtain ⟨_, h_lo, h_hi, h_l_bd⟩ := hmv
          refine ⟨?_, ?_⟩
          · rw [hj_def]; omega
          · omega
        · intro m_p hm_p
          rw [Finset.mem_Ico] at hm_p
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · rw [hj_def] at hm_p; omega
          · omega
          · omega
        · intro mv hmv
          rw [Finset.mem_filter, Finset.mem_range] at hmv
          obtain ⟨_, _, h_hi, h_l_bd⟩ := hmv
          omega
        · intro m_p hm_p
          rw [Finset.mem_Ico] at hm_p
          rw [hj_def] at hm_p
          omega
        · intro mv hmv
          rw [Finset.mem_filter, Finset.mem_range] at hmv
          obtain ⟨_, h_lo, h_hi, h_l_bd⟩ := hmv
          show newtonSum P (mv - (2 * k - 2 - i.val)) *
              algebraMap K C (P.coeff (P.natDegree + mv - l.val)) =
            algebraMap K C (P.coeff (P.natDegree + mv - l.val)) *
              newtonSum P ((P.natDegree + mv - l.val) - j)
          rw [mul_comm]
          congr 2
          rw [hj_def]; omega
      rw [h_sum_eq]
      by_cases hj_le_p : j ≤ P.natDegree
      · rw [← proposition_4_8 (C := C) P j hj_le_p]
      · push Not at hj_le_p
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj_le_p,
            RingHom.map_zero, mul_zero]
        rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    · -- Case B: l.val + i.val > p + 2k - 2, so j (Nat) = 0.
      push Not at hj_pos
      have hj_zero : P.natDegree + 2 * k - 2 - i.val - l.val = 0 := by omega
      rw [hj_zero, Nat.cast_zero, zero_mul]
      -- Use newtonSum_orthogonality with
      -- q := (l.val + i.val + 2) - (P.natDegree + 2*k) > 0.
      -- Single Nat-sub to avoid clipping ambiguity.
      set q : ℕ := l.val + i.val + 2 - (P.natDegree + 2 * k) with hq_def
      have hq_pos : 0 < q := by rw [hq_def]; omega
      have h_sum_eq :
          ∑ mv ∈ Finset.range (2 * k - 1),
            (if 2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree then
              newtonSum P (mv - (2 * k - 2 - i.val)) *
                algebraMap K C (P.coeff (P.natDegree + mv - l.val))
            else 0) =
          ∑ n ∈ Finset.range (P.natDegree + 1),
            algebraMap K C (P.coeff n) * newtonSum P (n + q) := by
        rw [show (∑ mv ∈ Finset.range (2 * k - 1),
            (if 2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree then
              newtonSum P (mv - (2 * k - 2 - i.val)) *
                algebraMap K C (P.coeff (P.natDegree + mv - l.val))
            else 0)) =
            ∑ mv ∈ (Finset.range (2 * k - 1)).filter (fun mv =>
                2 * k - 2 - i.val ≤ mv ∧ mv ≤ l.val ∧ l.val ≤ mv + P.natDegree),
              newtonSum P (mv - (2 * k - 2 - i.val)) *
                algebraMap K C (P.coeff (P.natDegree + mv - l.val)) from
          (Finset.sum_filter _ _).symm]
        apply Finset.sum_nbij'
          (i := fun mv => P.natDegree + mv - l.val)
          (j := fun n => n + l.val - P.natDegree)
        · intro mv hmv
          rw [Finset.mem_filter, Finset.mem_range] at hmv
          rw [Finset.mem_range]
          have := i.isLt
          have := l.isLt
          obtain ⟨_, _, h_hi, h_l_bd⟩ := hmv
          omega
        · intro n hn
          rw [Finset.mem_range] at hn
          rw [Finset.mem_filter, Finset.mem_range]
          have := i.isLt; have := l.isLt
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · omega
          · omega
          · omega
        · intro mv hmv
          rw [Finset.mem_filter, Finset.mem_range] at hmv
          obtain ⟨_, _, h_hi, h_l_bd⟩ := hmv
          omega
        · intro n hn
          rw [Finset.mem_range] at hn
          omega
        · intro mv hmv
          rw [Finset.mem_filter, Finset.mem_range] at hmv
          obtain ⟨_, h_lo, h_hi, h_l_bd⟩ := hmv
          show newtonSum P (mv - (2 * k - 2 - i.val)) *
              algebraMap K C (P.coeff (P.natDegree + mv - l.val)) =
            algebraMap K C (P.coeff (P.natDegree + mv - l.val)) *
              newtonSum P ((P.natDegree + mv - l.val) + q)
          rw [mul_comm]
          congr 2
          rw [hq_def]
          have h_i_lt := i.isLt
          have h_l_lt := l.isLt
          omega
      rw [h_sum_eq]
      exact newtonSum_orthogonality (C := C) P q

/-! ### Main theorem -/

omit [CharZero K] [IsAlgClosed C] in
private lemma algebraMap_sRes_eq_det_map (P : K[X])
    (hp_deriv : P.derivative.natDegree = P.natDegree - 1)
    (k : ℕ) (hk_pos : 0 < k) (hk_le : k ≤ P.natDegree) :
    (algebraMap K C) (sRes P P.derivative (P.natDegree - k)) =
      ((SyHaSquare P P.derivative (P.natDegree - k)).map
        (algebraMap K C)).det := by
  unfold sRes
  have h_le : P.natDegree - k ≤ P.derivative.natDegree := by rw [hp_deriv]; omega
  rw [if_pos h_le]
  exact (algebraMap K C).map_det _

/-- **BPR Proposition 4.28.** For `P : K[X]` with positive `natDegree`
    and `0 < k ≤ P.natDegree`,

      `a_p · sDisc_{p-k}(P) = sRes_{p-k}(P, P')`. -/
theorem proposition_4_28 (P : K[X]) (hP : 0 < P.natDegree) (k : ℕ)
    (hk_pos : 0 < k) (hk_le : k ≤ P.natDegree) :
    (algebraMap K C) P.leadingCoeff *
        sDisc P (P.natDegree - k) =
      (algebraMap K C) (sRes P P.derivative (P.natDegree - k)) := by
  -- (P.aroots C).card = P.natDegree.
  have hP_ne : P ≠ 0 := fun h => by rw [h] at hP; simp at hP
  have h_aroots_card : (P.aroots C).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hP_ne).isUnit
  -- Derivative degree.
  have hp_deriv : P.derivative.natDegree = P.natDegree - 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_derivative hP.ne')
  -- Dimension equation.
  have h_size : 2 * k - 1 =
      P.natDegree + P.derivative.natDegree - 2 * (P.natDegree - k) := by
    rw [hp_deriv]; omega
  -- Apply Prop 4.9: sDisc P (p-k) = a_p^{2k-2} · det(newtMat P k).
  have h_prop49 := proposition_4_9 (C := C) P k (by rw [h_aroots_card]; exact hk_le)
  rw [h_aroots_card] at h_prop49
  -- sRes side via lifted SyHaSquare det.
  rw [algebraMap_sRes_eq_det_map P hp_deriv k hk_pos hk_le]
  -- Replace SyHa.map with its reindexed form to use Dk * DkPrime.
  rw [← Matrix.det_submatrix_equiv_self (syHaReindex P k h_size)
        ((SyHaSquare P P.derivative (P.natDegree - k)).map (algebraMap K C))]
  rw [← Dk_mul_DkPrime_eq_SyHaSquare_map P hP k hk_pos hk_le hp_deriv h_size]
  rw [Matrix.det_mul, Dk_det P k hk_pos, DkPrime_det]
  rw [h_prop49]
  rw [show (2 * k - 1) = 1 + (2 * k - 2) from by omega, pow_add, pow_one]
  ring

end Azurite.BPR.Chapter4
