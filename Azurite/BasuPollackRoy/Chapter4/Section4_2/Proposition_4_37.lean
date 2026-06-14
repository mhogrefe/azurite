import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_22
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_27

/-!
# BPR Proposition 4.37: subresultants under a Euclidean step (in progress)

For `P` of degree `p`, `Q` of degree `q < p`, and `R = Rem(P, Q) = P % Q` of
degree `r`, BPR Proposition 4.37 relates the subresultant coefficients of
`(P, Q)` to those of `(Q, −R)`:

* `sRes_j(P, Q) = ε_{p-q} · b_q^{p-r} · sRes_j(Q, −R)` for `j ≤ r`;
* `sRes_j(P, Q) = sRes_j(Q, −R) = 0` for `r < j < q − 1`
  (the strict interior; at the convention boundary `j = q − 1`,
  `sRes_{q-1}(Q, −R) = leadingCoeff(−R) = −b_r` by Notation 4.22, so the
  vanishing claim is stated on `r < j < q − 1`).

The proof manipulates the Sylvester-Habicht determinant `det(SyHaSquare(P,Q,j))`
(`= sRes_j`): the `P`-rows `X^k P` are replaced by `X^k R` (a determinant-
preserving row operation, since `R = P − (P/Q)·Q`; `MpMatrix_det_eq_sRes`), the
rows are reversed (factor `ε_{p+q-2j}`) and the `R`-rows are negated (factor
`(-1)^{q-j}`), with combined sign `(-1)^{q-j} ε_{p+q-2j} = ε_{p-q}`
(`eps_qj`/`DjMatrix_det_eq_eps_mul`). The resulting determinant `D_j` is then
block-triangular with a `b_q^{p-r}` corner over `SyHaSquare(Q,−R,j)`
(`DjMatrix_det_eq`). Assembling these with `ε² = 1` gives `proposition_4_37_part1`,
and the null-row vanishing `DjMatrix_det_eq_zero` gives `proposition_4_37_part2`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

/-! ### The combined sign `(-1)^{q-j} ε_{p+q-2j} = ε_{p-q}` -/

/-- **The sign-normalization identity** behind Proposition 4.37: reversing the
`p + q - 2j` rows (signature `ε_{p+q-2j}`) and negating the `q - j` `R`-rows
(factor `(-1)^{q-j}`) combine to `ε_{p-q}`. This is `ε_sub_two_mul`
(Notation 4.27) with `i = p + q - 2j`, since `(p+q-2j) - 2(q-j) = p - q`. -/
theorem eps_qj (p q j : ℕ) (hqp : q ≤ p) (hjq : j ≤ q) :
    (-1 : ℤ) ^ (q - j) * ε (p + q - 2 * j) = ε (p - q) := by
  have h := ε_sub_two_mul (p + q - 2 * j) (q - j) (by omega)
  rw [show p + q - 2 * j - 2 * (q - j) = p - q by omega] at h
  exact h.symm

variable {K : Type*} [Field K]

/-- **The determinant `D_j` of Proposition 4.37.** The `(p+q-2j) × (p+q-2j)`
matrix whose rows are the coefficients (in the descending power basis, first
`p+q-2j` columns) of

  `X^{p-j-1} Q, …, X Q, Q, −R, −X R, …, −X^{q-j-1} R`,

with `p = P.natDegree`, `q = Q.natDegree` and `R = P % Q`. The first `p - j`
rows are `Q`-shifts (decreasing exponent), the last `q - j` rows are `−R`-shifts
(increasing exponent). BPR's proof shows `sRes_j(P,Q) = ε_{p-q} · det(D_j)`. -/
noncomputable def DjMatrix (P Q : K[X]) (j : ℕ) :
    Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
           (Fin (P.natDegree + Q.natDegree - 2 * j)) K :=
  Matrix.of fun i k =>
    if i.val < P.natDegree - j then
      (X ^ (P.natDegree - j - 1 - i.val) * Q).coeff
        (P.natDegree + Q.natDegree - j - 1 - k.val)
    else
      (-(X ^ (i.val - (P.natDegree - j)) * (P % Q))).coeff
        (P.natDegree + Q.natDegree - j - 1 - k.val)

/-- **Null-row vanishing (the mechanism behind Part 2).** When `r < j < q`, the
first `−R` row of `D_j` (row index `p - j`, which carries `−X^0 R = −R` of degree
`r`) is identically zero: every column exponent is `≥ j > r`. Hence
`det(D_j) = 0`. -/
theorem DjMatrix_det_eq_zero (P Q : K[X]) (j : ℕ)
    (hqp : Q.natDegree < P.natDegree) (hjq : j < Q.natDegree)
    (hr : (P % Q).natDegree < j) :
    (DjMatrix P Q j).det = 0 := by
  have hrow : P.natDegree - j < P.natDegree + Q.natDegree - 2 * j := by omega
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨P.natDegree - j, hrow⟩ (fun k => ?_)
  have hk : k.val < P.natDegree + Q.natDegree - 2 * j := k.isLt
  simp only [DjMatrix, Matrix.of_apply, lt_irrefl, if_false, Nat.sub_self, pow_zero,
    one_mul, Polynomial.coeff_neg, neg_eq_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ### L2: the block-triangular reduction `det(D_j) = b_q^{p-r} · sRes_j(Q, −R)` -/

/-- `natDegree (X^n * S) = n + S.natDegree` for `S ≠ 0`. -/
private theorem natDegree_X_pow_mul' (n : ℕ) {S : K[X]} (hS : S ≠ 0) :
    (X ^ n * S).natDegree = n + S.natDegree := by
  rw [Polynomial.natDegree_mul (pow_ne_zero n Polynomial.X_ne_zero) hS,
    Polynomial.natDegree_X_pow]

/-- **BPR Proposition 4.37, the determinant `D_j`.** For `j ≤ r` (with
`r = (P % Q).natDegree`, `q < p`, `Q ≠ 0`), the determinant of `D_j` factors as a
block-triangular product: a `b_q`-upper-triangular `(p-r)` corner times the
Sylvester-Habicht determinant of `(Q, −R)`. -/
theorem DjMatrix_det_eq (P Q : K[X]) (j : ℕ)
    (hQ : Q ≠ 0) (hjr : j ≤ (P % Q).natDegree)
    (hrq : (P % Q).natDegree < Q.natDegree) (hqp : Q.natDegree < P.natDegree) :
    (DjMatrix P Q j).det =
      Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) * sRes Q (-(P % Q)) j := by
  classical
  have hrneg : (-(P % Q)).natDegree = (P % Q).natDegree := Polynomial.natDegree_neg _
  have hmn : (P.natDegree - (P % Q).natDegree) +
      (Q.natDegree + (-(P % Q)).natDegree - 2 * j) = P.natDegree + Q.natDegree - 2 * j := by
    rw [hrneg]; omega
  set m := P.natDegree - (P % Q).natDegree with hm
  set n := Q.natDegree + (-(P % Q)).natDegree - 2 * j with hndef
  -- the reindexing equiv `Fin m ⊕ Fin n ≃ Fin (p + q - 2j)`
  set e : Fin m ⊕ Fin n ≃ Fin (P.natDegree + Q.natDegree - 2 * j) :=
    finSumFinEquiv.trans (finCongr hmn) with he_def
  have he_inl : ∀ i : Fin m, (e (Sum.inl i)).val = i.val := by
    intro i; rw [he_def]; simp [finSumFinEquiv_apply_left]
  have he_inr : ∀ i : Fin n, (e (Sum.inr i)).val = m + i.val := by
    intro i; rw [he_def]; simp [finSumFinEquiv_apply_right]
  -- the three nontrivial blocks
  set A : Matrix (Fin m) (Fin m) K := Matrix.of fun i k =>
    (X ^ (P.natDegree - j - 1 - i.val) * Q).coeff (P.natDegree + Q.natDegree - j - 1 - k.val)
    with hA
  set B : Matrix (Fin m) (Fin n) K := Matrix.of fun i k =>
    (X ^ (P.natDegree - j - 1 - i.val) * Q).coeff
      (P.natDegree + Q.natDegree - j - 1 - (m + k.val)) with hB
  set D : Matrix (Fin n) (Fin n) K := SyHaSquare Q (-(P % Q)) j with hD
  -- block decomposition: bottom-left vanishes
  have hblock : (DjMatrix P Q j).submatrix e e = Matrix.fromBlocks A B 0 D := by
    ext a b
    rcases a with i | i <;> rcases b with k | k
    · -- (inl, inl): the `b_q`-triangular corner `A`
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, DjMatrix, Matrix.of_apply,
        he_inl, hA]
      rw [if_pos (by have := i.isLt; omega)]
    · -- (inl, inr): the corner-coupling block `B`
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, DjMatrix, Matrix.of_apply,
        he_inl, he_inr, hB]
      rw [if_pos (by have := i.isLt; omega)]
    · -- (inr, inl): the vanishing block
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        DjMatrix, Matrix.of_apply, he_inr, he_inl]
      have hki : k.val < m := k.isLt
      have hin : i.val < n := i.isLt
      split
      · -- upper `Q`-shift row: degree `< q + r - j ≤` column exponent
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [natDegree_X_pow_mul' _ hQ]; omega
      · -- lower `−R`-shift row
        rw [Polynomial.coeff_neg, neg_eq_zero]
        rcases eq_or_ne (P % Q) 0 with h0 | h0
        · simp [h0]
        · apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [natDegree_X_pow_mul' _ h0]; omega
    · -- (inr, inr): the `SyHaSquare(Q, −R, j)` block
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, hD, DjMatrix, SyHaSquare,
        SyHa, Matrix.of_apply, he_inr, id_eq, Fin.val_castLE]
      have hin := i.isLt; have hkn := k.isLt
      by_cases hc : i.val < (-(P % Q)).natDegree - j
      · rw [if_pos (show m + i.val < P.natDegree - j by omega), if_pos hc,
          show P.natDegree - j - 1 - (m + i.val) = (-(P % Q)).natDegree - j - 1 - i.val by
            rw [hrneg]; omega,
          show P.natDegree + Q.natDegree - j - 1 - (m + k.val)
            = Q.natDegree + (-(P % Q)).natDegree - j - 1 - k.val by rw [hrneg]; omega]
      · rw [if_neg (show ¬ m + i.val < P.natDegree - j by omega), if_neg hc, mul_neg,
          show m + i.val - (P.natDegree - j) = i.val - ((-(P % Q)).natDegree - j) by
            rw [hrneg]; omega,
          show P.natDegree + Q.natDegree - j - 1 - (m + k.val)
            = Q.natDegree + (-(P % Q)).natDegree - j - 1 - k.val by rw [hrneg]; omega]
  -- assemble the determinant
  rw [← Matrix.det_submatrix_equiv_self e (DjMatrix P Q j), hblock,
    Matrix.det_fromBlocks_zero₂₁]
  -- `A` is upper-triangular with diagonal `b_q`, so `det A = b_q^m`
  have hAdet : A.det = Q.leadingCoeff ^ m := by
    rw [Matrix.det_of_upperTriangular (M := A) (fun i k hki => ?_)]
    · rw [Finset.prod_congr rfl (g := fun _ => Q.leadingCoeff) (fun i _ => ?_),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · -- diagonal entry `A i i = b_q`
        show (X ^ (P.natDegree - j - 1 - i.val) * Q).coeff
            (P.natDegree + Q.natDegree - j - 1 - i.val) = Q.leadingCoeff
        rw [show P.natDegree + Q.natDegree - j - 1 - i.val
            = Q.natDegree + (P.natDegree - j - 1 - i.val) by have := i.isLt; omega,
          Polynomial.coeff_X_pow_mul]
        rfl
    · -- below-diagonal entries vanish
      show (X ^ (P.natDegree - j - 1 - i.val) * Q).coeff
          (P.natDegree + Q.natDegree - j - 1 - k.val) = 0
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [natDegree_X_pow_mul' _ hQ]
      have := i.isLt; have := k.isLt; have : k.val < i.val := hki
      omega
  -- `D = SyHaSquare(Q, −R, j)` and `sRes_j(Q,−R)` is its determinant for `j ≤ r`
  have hsRes : sRes Q (-(P % Q)) j = D.det := by
    rw [hD, sRes, if_pos (by rw [hrneg]; exact hjr)]
  rw [hAdet, hsRes]

/-! ### L1b: reversal and negation — `det(D_j) = ε_{p-q} · det(M')` -/

/-- The intermediate matrix `M'`: the Sylvester-Habicht square of `(P, Q)` with
the `P`-rows replaced by `R = P % Q`-rows (rows `X^{q-j-1}R, …, R, Q, …, X^{p-j-1}Q`,
first `p+q-2j` columns). Reversing its rows and negating the `R`-block yields
`D_j`. -/
noncomputable def MpMatrix (P Q : K[X]) (j : ℕ) :
    Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
           (Fin (P.natDegree + Q.natDegree - 2 * j)) K :=
  Matrix.of fun i k =>
    if i.val < Q.natDegree - j then
      (X ^ (Q.natDegree - j - 1 - i.val) * (P % Q)).coeff
        (P.natDegree + Q.natDegree - j - 1 - k.val)
    else
      (X ^ (i.val - (Q.natDegree - j)) * Q).coeff
        (P.natDegree + Q.natDegree - j - 1 - k.val)

/-- `∏_{i < N} (if i < m then 1 else -1) = (-1)^{N-m}`. -/
private theorem prod_ite_one_neg_one (m N : ℕ) :
    ∏ i : Fin N, (if i.val < m then (1 : K) else -1) = (-1) ^ (N - m) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.val_last]
    have hcong : (∏ x : Fin n, if (x.castSucc).val < m then (1 : K) else -1)
        = (-1) ^ (n - m) := by
      rw [← ih]; exact Finset.prod_congr rfl (fun x _ => by rw [Fin.val_castSucc])
    rw [hcong]
    by_cases h : n < m
    · rw [if_pos h, mul_one]; congr 1; omega
    · rw [if_neg h, show n + 1 - m = (n - m) + 1 by omega, pow_succ]

/-- **BPR Proposition 4.37, the reversal–negation step.** `det(D_j) = ε_{p-q} · det(M')`:
reversing the `p+q-2j` rows (signature `ε_{p+q-2j}`) and negating the `q-j` `R`-rows
(factor `(-1)^{q-j}`) combine to `ε_{p-q}` (`eps_qj`). -/
theorem DjMatrix_det_eq_eps_mul (P Q : K[X]) (j : ℕ)
    (hjq : j ≤ Q.natDegree) (hqp : Q.natDegree < P.natDegree) :
    (DjMatrix P Q j).det =
      ((ε (P.natDegree - Q.natDegree) : ℤ) : K) * (MpMatrix P Q j).det := by
  -- `D_j = diagonal s · (M' permuted by reversal)`
  have hDj : DjMatrix P Q j =
      Matrix.diagonal (fun i : Fin (P.natDegree + Q.natDegree - 2 * j) =>
        if i.val < P.natDegree - j then (1 : K) else -1) *
        (MpMatrix P Q j).submatrix Fin.revPerm id := by
    ext i k
    rw [Matrix.diagonal_mul, Matrix.submatrix_apply, id_eq]
    have hrev : (Fin.revPerm i).val = P.natDegree + Q.natDegree - 2 * j - 1 - i.val := by
      rw [show (Fin.revPerm i) = Fin.rev i from rfl, Fin.val_rev]; omega
    have hi := i.isLt
    by_cases hc : i.val < P.natDegree - j
    · rw [if_pos hc]
      simp only [DjMatrix, MpMatrix, Matrix.of_apply, hrev]
      rw [if_pos hc, if_neg (show ¬ P.natDegree + Q.natDegree - 2 * j - 1 - i.val
        < Q.natDegree - j by omega), one_mul,
        show P.natDegree + Q.natDegree - 2 * j - 1 - i.val - (Q.natDegree - j)
          = P.natDegree - j - 1 - i.val by omega]
    · rw [if_neg hc]
      simp only [DjMatrix, MpMatrix, Matrix.of_apply, hrev]
      rw [if_neg hc, if_pos (show P.natDegree + Q.natDegree - 2 * j - 1 - i.val
        < Q.natDegree - j by omega), neg_one_mul, Polynomial.coeff_neg,
        show Q.natDegree - j - 1 - (P.natDegree + Q.natDegree - 2 * j - 1 - i.val)
          = i.val - (P.natDegree - j) by omega]
  rw [hDj, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, prod_ite_one_neg_one]
  -- `(-1)^{q-j} · (ε_{p+q-2j} · det M') = ε_{p-q} · det M'`
  have hsign : (↑(Equiv.Perm.sign
      (Fin.revPerm : Equiv.Perm (Fin (P.natDegree + Q.natDegree - 2 * j)))) : K)
      = ((ε (P.natDegree + Q.natDegree - 2 * j) : ℤ) : K) := by
    rw [← sign_revPerm]
  have he := eps_qj P.natDegree Q.natDegree j (le_of_lt hqp) hjq
  have hfac : ((-1 : K)) ^ (Q.natDegree - j) *
      ((ε (P.natDegree + Q.natDegree - 2 * j) : ℤ) : K)
      = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) := by
    rw [← he]; push_cast; ring
  rw [show P.natDegree + Q.natDegree - 2 * j - (P.natDegree - j) = Q.natDegree - j by omega,
    hsign, ← mul_assoc, hfac]

/-! ### L1a: the `P → R` row operation — `det(M') = sRes_j(P,Q)` -/

/-- `(G·S).coeff E = ∑_{ℓ < M} G.coeff ℓ · (X^ℓ·S).coeff E` when `deg G < M`: writing
`G` as `∑ C(G.coeff ℓ)·X^ℓ` over `range M` and distributing. -/
private theorem coeff_mul_eq_sum_shift (G S : K[X]) (E M : ℕ) (hG : G.natDegree < M) :
    (G * S).coeff E = ∑ ℓ ∈ Finset.range M, G.coeff ℓ * (X ^ ℓ * S).coeff E := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' G hG, Finset.sum_mul,
    Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl (fun ℓ _ => by rw [mul_assoc, Polynomial.coeff_C_mul])

/-- Reindex a `Fin N`-sum whose summand is supported on `a ≤ l` to a `range b`-sum,
where `a + b = N`. -/
private theorem sum_fin_ite_shift {N a b : ℕ} (hab : a + b = N) (g : ℕ → K) :
    ∑ l : Fin N, (if a ≤ l.val then g (l.val - a) else 0) = ∑ ℓ ∈ Finset.range b, g ℓ := by
  rw [Fin.sum_univ_eq_sum_range (fun l => if a ≤ l then g (l - a) else 0) N, ← Finset.sum_filter,
    show (Finset.range N).filter (fun l => a ≤ l) = Finset.Ico a N from by
      ext l; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, show N - a = b by omega]
  exact Finset.sum_congr rfl (fun ℓ _ => by rw [Nat.add_sub_cancel_left])

/-- **BPR Proposition 4.37, the row operation.** `det(M') = sRes_j(P, Q)`: replacing
the `P`-rows of the Sylvester-Habicht matrix by `R = P % Q`-rows (`M' = E · SyHaSquare`
with `E` unitriangular, `det E = 1`) preserves the determinant, since
`R = P − (P / Q)·Q`. -/
theorem MpMatrix_det_eq_sRes (P Q : K[X]) (j : ℕ)
    (hQ : Q ≠ 0) (hjq : j ≤ Q.natDegree) (hqp : Q.natDegree < P.natDegree) :
    (MpMatrix P Q j).det = sRes P Q j := by
  classical
  have hPne : P ≠ 0 := by rintro rfl; simp at hqp
  -- the quotient has degree `p − q`
  have hqp_deg : Q.degree ≤ P.degree := by
    rw [Polynomial.degree_eq_natDegree hQ, Polynomial.degree_eq_natDegree hPne]
    exact_mod_cast hqp.le
  have hadd := degree_add_div hQ hqp_deg
  have hdivne : P / Q ≠ 0 := by
    rintro h0
    rw [h0, Polynomial.degree_zero, Polynomial.degree_eq_natDegree hPne] at hadd
    simp at hadd
  have hnd : (P / Q).natDegree = P.natDegree - Q.natDegree := by
    have h1 : (Q.natDegree : WithBot ℕ) + ((P / Q).natDegree : ℕ) = (P.natDegree : ℕ) := by
      rw [← Polynomial.degree_eq_natDegree hQ, ← Polynomial.degree_eq_natDegree hdivne,
        ← Polynomial.degree_eq_natDegree hPne]; exact hadd
    have h2 : Q.natDegree + (P / Q).natDegree = P.natDegree := by exact_mod_cast h1
    omega
  -- key polynomial identity `R = P − (P / Q)·Q`
  have hmod : P % Q = P - (P / Q) * Q := by
    have := EuclideanDomain.div_add_mod P Q
    linear_combination this - mul_comm Q (P / Q)
  -- the unitriangular transition matrix `E`
  set E : Matrix (Fin (P.natDegree + Q.natDegree - 2 * j))
      (Fin (P.natDegree + Q.natDegree - 2 * j)) K := Matrix.of fun i l =>
    (if l = i then 1 else 0) -
    (if i.val < Q.natDegree - j ∧ Q.natDegree - j ≤ l.val then
      (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff (l.val - (Q.natDegree - j)) else 0)
    with hE
  have hsRes : sRes P Q j = (SyHaSquare P Q j).det := by rw [sRes, if_pos hjq]
  -- `M' = E · SyHaSquare`
  have hME : MpMatrix P Q j = E * SyHaSquare P Q j := by
    ext i k
    rw [Matrix.mul_apply]
    simp only [hE, Matrix.of_apply, sub_mul]
    rw [Finset.sum_sub_distrib]
    -- first sum picks out row `i`
    have hfirst : (∑ l, (if l = i then (1 : K) else 0) * (SyHaSquare P Q j) l k)
        = (SyHaSquare P Q j) i k := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hfirst]
    -- unfold the `SyHaSquare` entries
    have hSyEntry : ∀ l : Fin (P.natDegree + Q.natDegree - 2 * j),
        (SyHaSquare P Q j) l k =
          if l.val < Q.natDegree - j then
            (X ^ (Q.natDegree - j - 1 - l.val) * P).coeff
              (P.natDegree + Q.natDegree - j - 1 - k.val)
          else
            (X ^ (l.val - (Q.natDegree - j)) * Q).coeff
              (P.natDegree + Q.natDegree - j - 1 - k.val) := by
      intro l
      simp only [SyHaSquare, SyHa, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.val_castLE]
    by_cases hi : i.val < Q.natDegree - j
    · -- `P`-row: subtract the `Q`-combination
      rw [hSyEntry i, if_pos hi]
      have hsecond : (∑ l, (if i.val < Q.natDegree - j ∧ Q.natDegree - j ≤ l.val then
            (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff (l.val - (Q.natDegree - j))
            else 0) * (SyHaSquare P Q j) l k)
          = (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q) * Q).coeff
              (P.natDegree + Q.natDegree - j - 1 - k.val) := by
        have hstep : (∑ l, (if i.val < Q.natDegree - j ∧ Q.natDegree - j ≤ l.val then
              (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff (l.val - (Q.natDegree - j))
              else 0) * (SyHaSquare P Q j) l k)
            = ∑ l : Fin (P.natDegree + Q.natDegree - 2 * j), if Q.natDegree - j ≤ l.val then
                (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff (l.val - (Q.natDegree - j)) *
                (X ^ (l.val - (Q.natDegree - j)) * Q).coeff
                  (P.natDegree + Q.natDegree - j - 1 - k.val) else 0 := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          by_cases hl : Q.natDegree - j ≤ l.val
          · rw [if_pos ⟨hi, hl⟩, if_pos hl, hSyEntry l, if_neg (by omega)]
          · rw [if_neg (fun h => hl h.2), if_neg hl, zero_mul]
        rw [hstep]
        trans (∑ ℓ ∈ Finset.range (P.natDegree - j),
            (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff ℓ *
            (X ^ ℓ * Q).coeff (P.natDegree + Q.natDegree - j - 1 - k.val))
        · exact sum_fin_ite_shift (N := P.natDegree + Q.natDegree - 2 * j)
            (a := Q.natDegree - j) (b := P.natDegree - j) (by omega)
            (fun ℓ => (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff ℓ *
              (X ^ ℓ * Q).coeff (P.natDegree + Q.natDegree - j - 1 - k.val))
        · refine (coeff_mul_eq_sum_shift _ Q _ (P.natDegree - j) ?_).symm
          rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hdivne,
            Polynomial.natDegree_X_pow, hnd]
          omega
      rw [hsecond, ← Polynomial.coeff_sub, mul_assoc, ← mul_sub, ← hmod]
      simp only [MpMatrix, Matrix.of_apply, hi, if_true]
    · -- `Q`-row: unchanged
      rw [hSyEntry i, if_neg hi]
      have hsecond : (∑ l, (if i.val < Q.natDegree - j ∧ Q.natDegree - j ≤ l.val then
            (X ^ (Q.natDegree - j - 1 - i.val) * (P / Q)).coeff (l.val - (Q.natDegree - j))
            else 0) * (SyHaSquare P Q j) l k) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        rw [if_neg (fun h => hi h.1), zero_mul]
      rw [hsecond, sub_zero]
      simp only [MpMatrix, Matrix.of_apply, hi, if_false]
  -- conclude
  rw [hME, Matrix.det_mul, hsRes]
  have hEdet : E.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := E) (fun i l hil => ?_)]
    · refine (Finset.prod_congr rfl (fun i _ => ?_)).trans (Finset.prod_const_one)
      show (if i = i then (1 : K) else 0) -
        (if i.val < Q.natDegree - j ∧ Q.natDegree - j ≤ i.val then _ else 0) = 1
      rw [if_pos rfl, if_neg (by rintro ⟨h1, h2⟩; omega), sub_zero]
    · show (if l = i then (1 : K) else 0) -
        (if i.val < Q.natDegree - j ∧ Q.natDegree - j ≤ l.val then _ else 0) = 0
      have hlt : l.val < i.val := hil
      rw [if_neg (fun h => by rw [h] at hlt; omega), if_neg (by rintro ⟨h1, h2⟩; omega), sub_zero]
  rw [hEdet, one_mul]

/-! ### Assembly: BPR Proposition 4.37 -/

/-- `ε_n · ε_n = 1` (it is `±1`). -/
theorem ε_mul_self (n : ℕ) : ε n * ε n = 1 := by
  unfold ε; rw [← pow_add, ← two_mul]; exact Even.neg_one_pow (even_two_mul _)

/-- **BPR Proposition 4.37 (main relation).** For `j ≤ r = deg(P % Q)`,
`sRes_j(P, Q) = ε_{p-q} · b_q^{p-r} · sRes_j(Q, −R)`. Combines the determinant
chain `L1a` (`det M' = sRes`), `L1b` (`det D_j = ε_{p-q}·det M'`), and `L2`
(`det D_j = b_q^{p-r}·sRes_j(Q,−R)`), using `ε_{p-q}² = 1`. -/
theorem proposition_4_37_part1 (P Q : K[X]) (j : ℕ) (hQ : Q ≠ 0)
    (hjr : j ≤ (P % Q).natDegree) (hrq : (P % Q).natDegree < Q.natDegree)
    (hqp : Q.natDegree < P.natDegree) :
    sRes P Q j = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
      Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) * sRes Q (-(P % Q)) j := by
  have hjq : j ≤ Q.natDegree := le_trans hjr hrq.le
  have hL1b := DjMatrix_det_eq_eps_mul P Q j hjq hqp
  rw [MpMatrix_det_eq_sRes P Q j hQ hjq hqp] at hL1b
  have hL2 := DjMatrix_det_eq P Q j hQ hjr hrq hqp
  rw [hL1b] at hL2
  have hε2 : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
      ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ε_mul_self, Int.cast_one]
  rw [← one_mul (sRes P Q j), ← hε2, mul_assoc, hL2]; ring

/-- **BPR Proposition 4.37 (vanishing).** On `r < j < q`, both `sRes_j(P, Q)` and
`sRes_j(Q, −R)` vanish (with the corrected `sRes` convention of Notation 4.22, in
which the defective subresultants in a degree gap are `0`). -/
theorem proposition_4_37_part2 (P Q : K[X]) (j : ℕ) (hQ : Q ≠ 0)
    (hr : (P % Q).natDegree < j) (hjq : j < Q.natDegree)
    (hqp : Q.natDegree < P.natDegree) :
    sRes P Q j = 0 ∧ sRes Q (-(P % Q)) j = 0 := by
  refine ⟨?_, ?_⟩
  · have hL1b := DjMatrix_det_eq_eps_mul P Q j (le_of_lt hjq) hqp
    rw [MpMatrix_det_eq_sRes P Q j hQ (le_of_lt hjq) hqp,
      DjMatrix_det_eq_zero P Q j hqp hjq hr] at hL1b
    have hε2 : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
        ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, ε_mul_self, Int.cast_one]
    have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := fun h => by
      rw [h, mul_zero] at hε2; exact one_ne_zero hε2.symm
    exact (mul_eq_zero.mp hL1b.symm).resolve_left hεne
  · rw [sRes, if_neg (show ¬ j ≤ (-(P % Q)).natDegree by
        rw [Polynomial.natDegree_neg]; omega),
      if_pos (show (-(P % Q)).natDegree < Q.natDegree by rw [Polynomial.natDegree_neg]; omega),
      if_neg (show j ≠ Q.natDegree by omega)]

end Azurite.BPR.Chapter4
