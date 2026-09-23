import Azurite.BasuPollackRoy.Chapter4.Section4_2.ResEqResultant
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_22
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# BPR Notation 4.27: reversing-rows signature `ε`

BPR's `ε_i = (-1)^{i(i-1)/2}` is the signature of the permutation
reversing `i` consecutive rows in a matrix. The two-line consequence
of the BPR definitions is

  `sRes_0(P, Q) = ε_{deg P} · Res(P, Q)`,

stemming from the fact that the `j = 0` Sylvester-Habicht matrix
`SyHa(P, Q, 0)` is the BPR Sylvester matrix `Syl(P, Q)` with its
`p`-row Q-block reversed (BPR's `SyHa` has Q-rows ascending in the
power of `X`, ours and BPR's `Syl` have them descending).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### `ε`: the row-reversal signature -/

/-- `ε_i = (-1)^{i(i-1)/2}`, the signature of reversing `i` rows. -/
def ε (i : ℕ) : ℤ := (-1) ^ (i * (i - 1) / 2)

@[simp] theorem ε_zero : ε 0 = 1 := rfl
@[simp] theorem ε_one : ε 1 = 1 := rfl

/-! ### The mod-4 pattern (BPR equation 4.2) -/

theorem ε_four_mul (i : ℕ) : ε (4 * i) = 1 := by
  unfold ε
  have h : 4 * i * (4 * i - 1) / 2 = 2 * (i * (4 * i - 1)) := by
    have : 4 * i * (4 * i - 1) = 2 * (2 * (i * (4 * i - 1))) := by ring
    omega
  rw [h, pow_mul]
  norm_num

theorem ε_four_mul_sub_one (i : ℕ) (hi : 1 ≤ i) : ε (4 * i - 1) = -1 := by
  unfold ε
  have h_n : 4 * i - 1 - 1 = 4 * i - 2 := by omega
  rw [h_n]
  have h : (4 * i - 1) * (4 * i - 2) / 2 = (4 * i - 1) * (2 * i - 1) := by
    have h_eq : (4 * i - 1) * (4 * i - 2) = 2 * ((4 * i - 1) * (2 * i - 1)) := by
      have h1 : 4 * i - 2 = 2 * (2 * i - 1) := by omega
      rw [h1]; ring
    omega
  rw [h]
  exact Odd.neg_one_pow (Odd.mul ⟨2 * i - 1, by omega⟩ ⟨i - 1, by omega⟩)

theorem ε_four_mul_sub_two (i : ℕ) (hi : 1 ≤ i) : ε (4 * i - 2) = -1 := by
  unfold ε
  have h_n : 4 * i - 2 - 1 = 4 * i - 3 := by omega
  rw [h_n]
  have h : (4 * i - 2) * (4 * i - 3) / 2 = (2 * i - 1) * (4 * i - 3) := by
    have h_eq : (4 * i - 2) * (4 * i - 3) = 2 * ((2 * i - 1) * (4 * i - 3)) := by
      have h1 : 4 * i - 2 = 2 * (2 * i - 1) := by omega
      rw [h1]; ring
    omega
  rw [h]
  exact Odd.neg_one_pow (Odd.mul ⟨i - 1, by omega⟩ ⟨2 * i - 2, by omega⟩)

theorem ε_four_mul_sub_three (i : ℕ) (hi : 1 ≤ i) : ε (4 * i - 3) = 1 := by
  unfold ε
  have h_n : 4 * i - 3 - 1 = 4 * i - 4 := by omega
  rw [h_n]
  have h : (4 * i - 3) * (4 * i - 4) / 2 = 2 * ((4 * i - 3) * (i - 1)) := by
    have h_eq : (4 * i - 3) * (4 * i - 4) = 2 * (2 * ((4 * i - 3) * (i - 1))) := by
      have h1 : 4 * i - 4 = 4 * (i - 1) := by omega
      rw [h1]; ring
    omega
  rw [h, pow_mul]
  norm_num

/-! ### Two-step recurrence and the `ε_{i - 2 j}` identity -/

/-- Reversing two more rows multiplies the signature by `-1`. -/
theorem ε_add_two (n : ℕ) : ε (n + 2) = -ε n := by
  unfold ε
  have h_step : (n + 2) * (n + 2 - 1) = n * (n - 1) + 2 * (2 * n + 1) := by
    cases n with
    | zero => decide
    | succ m =>
      have h1 : m + 1 + 2 - 1 = m + 2 := by omega
      have h2 : m + 1 - 1 = m := by omega
      show (m + 1 + 2) * (m + 1 + 2 - 1) = (m + 1) * (m + 1 - 1) + 2 * (2 * (m + 1) + 1)
      rw [h1, h2]; ring
  have h : (n + 2) * (n + 2 - 1) / 2 = n * (n - 1) / 2 + (2 * n + 1) := by
    rw [h_step, Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 2)]
  rw [h, pow_add]
  have h_pow : (-1 : ℤ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [h_pow]; ring

/-- **BPR's `ε_{i - 2 j} = (-1)^j ε_i` identity.** -/
theorem ε_sub_two_mul (i j : ℕ) (h : 2 * j ≤ i) :
    ε (i - 2 * j) = (-1) ^ j * ε i := by
  induction j with
  | zero => simp
  | succ k ih =>
    have h_k : 2 * k ≤ i := by omega
    have h_eq : i - 2 * (k + 1) + 2 = i - 2 * k := by omega
    have step : ε (i - 2 * k) = -ε (i - 2 * (k + 1)) := by
      rw [← h_eq, ε_add_two]
    have ih' := ih h_k
    rw [step] at ih'
    have h_lin : ε (i - 2 * (k + 1)) = -((-1) ^ k * ε i) := by linarith
    rw [h_lin, pow_succ]; ring

/-! ### Signature of `Fin.revPerm` -/

/-- Each pair `i < j` in `Fin n` contributes `-1` to the `prod_prod_Ioi`
    formula for `Equiv.Perm.sign Fin.revPerm`, because `Fin.rev` is
    antitone. -/
private lemma revPerm_term_eq_neg_one (n : ℕ) (i j : Fin n)
    (hij : j ∈ Finset.Ioi i) :
    (if (Fin.revPerm : Equiv.Perm (Fin n)) i < Fin.revPerm j
        then (1 : ℤˣ) else -1) = (-1 : ℤˣ) := by
  have hi_lt_j : i < j := Finset.mem_Ioi.mp hij
  have h_rev_gt : Fin.revPerm j < Fin.revPerm i := by
    simp only [Fin.revPerm_apply, Fin.rev_lt_rev]
    exact hi_lt_j
  rw [ite_eq_right (not_lt_of_gt h_rev_gt)]

/-- The signature of `Fin.revPerm` on `Fin n` is `ε_n = (-1)^{n(n-1)/2}`. -/
theorem sign_revPerm (n : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) : ℤ) = ε n := by
  unfold ε
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have h_inner : ∀ i : Fin n,
      ∏ j ∈ Finset.Ioi i,
        (if (Fin.revPerm : Equiv.Perm (Fin n)) i < Fin.revPerm j
          then (1 : ℤˣ) else -1) =
        (-1 : ℤˣ) ^ (n - 1 - i.val) := by
    intro i
    rw [Finset.prod_congr rfl fun j hj => revPerm_term_eq_neg_one n i j hj]
    rw [Finset.prod_const, Fin.card_Ioi]
  rw [Finset.prod_congr rfl fun i _ => h_inner i]
  push_cast
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n]
  have h_reflect : ∑ k ∈ Finset.range n, (n - 1 - k) = ∑ k ∈ Finset.range n, k :=
    Finset.sum_range_reflect (fun k => k) n
  rw [h_reflect, Finset.sum_range_id]

/-! ### `blockReversePerm`: identity on first `q`, reversal on last `p` -/

/-- The permutation of `Fin (p + q)` that is the identity on the first
    `q` indices and reverses the last `p`. Encodes BPR's "reverse the
    Q-block of the Sylvester matrix" operation.

    Defined as the conjugate of `Equiv.sumCongr (refl) Fin.revPerm`
    through `finSumFinEquiv`, which makes the signature computation
    `ε_p` immediate. -/
noncomputable def blockReversePerm (p q : ℕ) : Equiv.Perm (Fin (p + q)) :=
  let e : Fin (p + q) ≃ Fin q ⊕ Fin p :=
    (finCongr (Nat.add_comm p q)).trans finSumFinEquiv.symm
  e.symm.permCongr (Equiv.sumCongr (Equiv.refl (Fin q)) Fin.revPerm)

/-- Action of `blockReversePerm` on indices: identity on `[0, q)`,
    `i ↦ p + 2q - 1 - i` on `[q, p+q)`. -/
theorem blockReversePerm_apply_val (p q : ℕ) (i : Fin (p + q)) :
    (blockReversePerm p q i).val =
      if i.val < q then i.val else p + 2 * q - 1 - i.val := by
  unfold blockReversePerm
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.trans_apply]
  by_cases h : i.val < q
  · rw [ite_eq_left h]
    have h_cast : finCongr (Nat.add_comm p q) i = Fin.castAdd p ⟨i.val, h⟩ := by
      apply Fin.ext; simp [finCongr_apply, Fin.castAdd, Fin.castLE]
    rw [h_cast, finSumFinEquiv_symm_apply_castAdd]
    simp [Equiv.sumCongr_apply, finCongr_symm,
      finSumFinEquiv_apply_left, Fin.castAdd, Fin.castLE]
  · rw [ite_eq_right h]
    have h_ge : q ≤ i.val := Nat.le_of_not_lt h
    have h_lt_p : i.val - q < p := by have := i.isLt; omega
    have h_cast : finCongr (Nat.add_comm p q) i =
        Fin.natAdd q ⟨i.val - q, h_lt_p⟩ := by
      apply Fin.ext
      simp [finCongr_apply, Fin.natAdd]
      omega
    rw [h_cast, finSumFinEquiv_symm_apply_natAdd]
    simp [Equiv.sumCongr_apply, finCongr_symm,
      finSumFinEquiv_apply_right, Fin.natAdd, Fin.revPerm_apply, Fin.rev]
    omega

/-- The signature of `blockReversePerm` is `ε_p`. -/
theorem sign_blockReversePerm (p q : ℕ) :
    ((Equiv.Perm.sign (blockReversePerm p q)) : ℤ) = ε p := by
  unfold blockReversePerm
  rw [Equiv.Perm.sign_permCongr]
  rw [Equiv.Perm.sign_sumCongr]
  simp only [Equiv.Perm.sign_refl, one_mul]
  exact sign_revPerm p

/-! ### Main result: `sRes_0(P, Q) = ε_p · Res(P, Q)` -/

/-- The `j = 0` Sylvester-Habicht matrix `SyHa(P, Q, 0)` is the
    Sylvester matrix `Syl(P, Q)` with its Q-block (last `p` rows)
    reversed. -/
theorem SyHa_zero_eq_Syl_submatrix (P Q : D[X]) :
    SyHa P Q 0 = (Syl P Q).submatrix
      (blockReversePerm P.natDegree Q.natDegree) id := by
  ext i j
  unfold SyHa Syl
  rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply]
  show (if i.val < Q.natDegree - 0 then
          (X ^ (Q.natDegree - 0 - 1 - i.val) * P).coeff
            (P.natDegree + Q.natDegree - 0 - 1 - j.val)
        else
          (X ^ (i.val - (Q.natDegree - 0)) * Q).coeff
            (P.natDegree + Q.natDegree - 0 - 1 - j.val)) = _
  simp only [Nat.sub_zero]
  by_cases h : i.val < Q.natDegree
  · rw [ite_eq_left h]
    have h_perm : (blockReversePerm P.natDegree Q.natDegree i).val = i.val := by
      rw [blockReversePerm_apply_val, ite_eq_left h]
    show _ = Syl P Q (blockReversePerm P.natDegree Q.natDegree i) j
    unfold Syl
    rw [Matrix.of_apply, ite_eq_left]
    · congr 1
      rw [h_perm]
    · rw [h_perm]; exact h
  · rw [ite_eq_right h]
    push Not at h
    have h_perm : (blockReversePerm P.natDegree Q.natDegree i).val =
        P.natDegree + 2 * Q.natDegree - 1 - i.val := by
      rw [blockReversePerm_apply_val, ite_eq_right (not_lt_of_ge h)]
    have h_perm_ge : ¬ (blockReversePerm P.natDegree Q.natDegree i).val < Q.natDegree := by
      rw [h_perm]; have := i.isLt; omega
    show _ = Syl P Q (blockReversePerm P.natDegree Q.natDegree i) j
    unfold Syl
    rw [Matrix.of_apply, ite_eq_right h_perm_ge]
    rw [h_perm]
    have h_exp_eq : P.natDegree + Q.natDegree - 1 -
        (P.natDegree + 2 * Q.natDegree - 1 - i.val) = i.val - Q.natDegree := by
      have := i.isLt; omega
    rw [h_exp_eq]

/-- **Notation 4.27 (consequence).** `sRes_0(P, Q) = ε_{deg P} · Res(P, Q)`,
    because `SyHa(P, Q, 0)` is `Syl(P, Q)` with the Q-block of `p` rows
    reversed, and reversing `p` rows multiplies the determinant by
    `ε_p`. -/
theorem sRes_zero_eq_eps_mul_Res (P Q : D[X]) :
    sRes P Q 0 = ε P.natDegree * Res P Q := by
  -- For `j = 0`, `sRes_0 = det(SyHaSquare P Q 0)` and the `castLE` is
  -- the identity, so `SyHaSquare = SyHa`.
  have h_sRes : sRes P Q 0 = (SyHa P Q 0).det := by
    unfold sRes
    rw [ite_eq_left (Nat.zero_le _)]
    unfold SyHaSquare
    show (Matrix.submatrix (SyHa P Q 0) id (Fin.castLE _)).det = _
    congr 1
  rw [h_sRes, SyHa_zero_eq_Syl_submatrix, Matrix.det_permute]
  unfold Res
  congr 1
  have h := sign_blockReversePerm P.natDegree Q.natDegree
  rw [show (ε P.natDegree : D) = ((ε P.natDegree : ℤ) : D) from rfl, ← h]

end Azurite.BPR.Chapter4
