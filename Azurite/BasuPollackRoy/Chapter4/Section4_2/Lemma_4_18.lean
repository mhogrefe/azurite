import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_13
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# BPR Lemma 4.18 (Res part): resultant under a Euclidean step

For polynomials `P, Q` of degrees `p, q` with `P = C·Q + R` and
`deg R ≤ r < q`, BPR Lemma 4.18 asserts

  `Res(P, Q) = (-1)^{p·q} · b_q^{p-r} · Res(Q, R)`,

where `b_q = Q.coeff q` is the leading coefficient of `Q`.

## Strategy

Our `Syl P p Q q` (BPR-faithful, rows = polynomial shifts in descending
power basis) is related to Mathlib's `Polynomial.sylvester P Q p q`
(columns = polynomial shifts in ascending power basis, with the
`Q`-shifts forming the first `p` columns and `P`-shifts the last `q`)
via transposition and reindexing both axes by `Fin.rev`. Because
`det` is invariant under transposition and under reindexing by the same
equivalence, our `Res` equals Mathlib's `Polynomial.resultant` (under
the natural hypotheses `P.natDegree ≤ p`, `Q.natDegree ≤ q`).

We use this bridge plus three Mathlib facts —
`Polynomial.resultant_add_mul_left` (kills the `C·Q` term),
`Polynomial.resultant_comm` (gives the `(-1)^{p·q}` factor), and
`Polynomial.resultant_add_right_deg` (gives the `b_q^{p-r}` factor) —
to conclude.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### Bridge: `Syl = (Polynomial.sylvester)ᵀ.submatrix Fin.rev Fin.rev` -/

/-- Each entry of our `Syl` matches the corresponding (transposed,
    reversed) entry of `Polynomial.sylvester`, provided `P.natDegree ≤ p`
    and `Q.natDegree ≤ q`. -/
private theorem Syl_eq_sylvester_T_submatrix_rev (P Q : D[X]) (p q : ℕ)
    (hP : P.natDegree ≤ p) (hQ : Q.natDegree ≤ q) :
    Syl P p Q q =
      ((Polynomial.sylvester P Q p q).transpose).submatrix Fin.rev Fin.rev := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.transpose_apply]
  unfold Syl
  rw [Matrix.of_apply]
  unfold Polynomial.sylvester
  rw [Matrix.of_apply]
  have hij : i.val < p + q := i.isLt
  have hjj : j.val < p + q := j.isLt
  have h_revi_val : (Fin.rev i).val = p + q - 1 - i.val := by
    rw [Fin.val_rev]; omega
  have h_revj_val : (Fin.rev j).val = p + q - 1 - j.val := by
    rw [Fin.val_rev]; omega
  by_cases hi : i.val < q
  · -- P-row branch. `(Fin.rev i).val ≥ p`, so addCases right.
    rw [if_pos hi, Polynomial.coeff_X_pow_mul']
    have h_natAdd : Fin.rev i = Fin.natAdd p ⟨q - 1 - i.val, by omega⟩ := by
      apply Fin.ext
      rw [h_revi_val]
      show p + q - 1 - i.val = p + (q - 1 - i.val)
      omega
    conv_rhs => rw [h_natAdd]
    rw [Fin.addCases_right]
    simp only [Set.mem_Icc, h_revj_val]
    split_ifs with h1 h2 h2
    · -- Both conditions true. Compute the coefficient indices.
      rfl
    · -- LHS true, RHS false. RHS = 0, so need LHS coeff = 0.
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      push Not at h2
      -- h1: q - 1 - i.val ≤ p + q - 1 - j.val.
      -- h2: ¬(q - 1 - i.val ≤ p + q - 1 - j.val ∧ p + q - 1 - j.val ≤ q - 1 - i.val + p).
      -- Combined with h1: ¬ p + q - 1 - j.val ≤ q - 1 - i.val + p.
      -- Hence p + q - 1 - j.val > q - 1 - i.val + p, i.e., -j.val > -i.val, i.e., j.val < i.val.
      -- Then p + q - 1 - j.val - (q - 1 - i.val) > p. So P.natDegree ≤ p < this. ✓
      have := h2 h1
      omega
    · -- LHS false, RHS true. RHS coeff value = 0, so need 0 = 0.
      -- LHS condition false means ¬ q - 1 - i.val ≤ p + q - 1 - j.val.
      -- RHS conditions both hold; in particular the first means q - 1 - i.val ≤ p+q-1-j.val.
      -- Contradiction.
      exfalso
      omega
    · rfl
  · -- Q-row branch. `(Fin.rev i).val < p`, so addCases left.
    push Not at hi
    rw [if_neg (not_lt.mpr hi), Polynomial.coeff_X_pow_mul']
    have h_revi_lt : p + q - 1 - i.val < p := by omega
    have h_castAdd : Fin.rev i = Fin.castAdd q ⟨p + q - 1 - i.val, h_revi_lt⟩ := by
      apply Fin.ext
      rw [h_revi_val]
      rfl
    conv_rhs => rw [h_castAdd]
    rw [Fin.addCases_left]
    simp only [Set.mem_Icc, h_revj_val]
    split_ifs with h1 h2 h2
    · -- Both conditions true.
      rfl
    · -- LHS true, RHS false.
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      push Not at h2
      have := h2 h1
      omega
    · -- LHS false, RHS true. Contradiction.
      exfalso
      omega
    · rfl

/-- **Bridge.** Our `Res` agrees with Mathlib's `Polynomial.resultant`
    when `P.natDegree ≤ p` and `Q.natDegree ≤ q`. -/
theorem Res_eq_resultant (P Q : D[X]) (p q : ℕ)
    (hP : P.natDegree ≤ p) (hQ : Q.natDegree ≤ q) :
    Res P p Q q = Polynomial.resultant P Q p q := by
  unfold Res Polynomial.resultant
  rw [Syl_eq_sylvester_T_submatrix_rev P Q p q hP hQ]
  rw [show ((Polynomial.sylvester P Q p q).transpose).submatrix
        (Fin.rev : Fin (p + q) → _) (Fin.rev : Fin (p + q) → _)
      = ((Polynomial.sylvester P Q p q).transpose).submatrix
          (Fin.revPerm : Equiv.Perm (Fin (p + q)))
          (Fin.revPerm : Equiv.Perm (Fin (p + q)))
      from rfl]
  rw [Matrix.det_submatrix_equiv_self Fin.revPerm]
  exact Matrix.det_transpose _

/-! ### Lemma 4.18 (Res part) -/

/-- **BPR Lemma 4.18 (Res part).** For `P = C·Q + R` of formal degrees
    `p, q, r` with `r ≤ p`, `R.natDegree ≤ r`, `Q.natDegree ≤ q`,
    `P.natDegree ≤ p`, and `C.natDegree + q ≤ p`,

      `Res(P, Q) = (-1)^{p·q} · b_q^{p-r} · Res(Q, R)`. -/
theorem Lemma_4_18_Res (P Q C R : D[X]) (p q r : ℕ)
    (h_P : P.natDegree ≤ p) (h_Q : Q.natDegree ≤ q)
    (h_R : R.natDegree ≤ r) (h_r_le_p : r ≤ p)
    (h_C : C.natDegree + q ≤ p)
    (h_decomp : P = C * Q + R) :
    Res P p Q q =
      (-1) ^ (p * q) * Q.coeff q ^ (p - r) * Res Q q R r := by
  rw [Res_eq_resultant P Q p q h_P h_Q, Res_eq_resultant Q R q r h_Q h_R]
  rw [h_decomp, show C * Q + R = R + Q * C from by ring]
  rw [Polynomial.resultant_add_mul_left R Q C p q h_C h_Q]
  rw [Polynomial.resultant_comm R Q p q]
  rw [show (p : ℕ) = r + (p - r) from by omega]
  rw [Polynomial.resultant_add_right_deg Q R q r (p - r) h_R]
  rw [show r + (p - r) - r = p - r from by omega]
  ring

/-! ### BPR notation Θ and Lemma 4.18 (Θ part) -/

section Theta

variable {K : Type*} [Field K]

/-- BPR's Θ symbol (asymmetric form): `Θ(P, Q) := a_p^q · ∏_i Q(x_i)`,
    the product taken over the multiset of roots `x_i` of `P`. For
    polynomials that split over `K`, this matches BPR's symmetric formula
    `Θ(P, Q) = a_p^q b_q^p ∏(x_i - y_j)`, since
    `Q.eval x = b_q · ∏_j (x - y_j)`. -/
noncomputable def Θ (P Q : K[X]) (q : ℕ) : K :=
  P.leadingCoeff ^ q * (P.roots.map Q.eval).prod

/-- When `P` splits and `Q.natDegree ≤ q`, the BPR symbol `Θ(P, Q)`
    coincides with Mathlib's resultant `resultant P Q P.natDegree q`. -/
theorem Θ_eq_resultant (P Q : K[X]) (q : ℕ) (hP : P.Splits)
    (hQ : Q.natDegree ≤ q) :
    Θ P Q q = Polynomial.resultant P Q P.natDegree q := by
  unfold Θ
  exact (Polynomial.resultant_eq_prod_eval P Q q hQ hP).symm

/-- **BPR Lemma 4.18 (Θ part).** Under the same algebraic hypotheses as
    the Res part plus the splitting hypotheses on `P` and `Q` (needed
    for the BPR roots-based definition of `Θ` to capture all `p` roots
    of `P` and all `q` roots of `Q`),

      `Θ(P, Q) = (-1)^{p·q} · b_q^{p-r} · Θ(Q, R)`. -/
theorem Lemma_4_18_Theta (P Q C R : K[X]) (p q r : ℕ)
    (h_P : P.natDegree = p) (h_Q : Q.natDegree = q)
    (h_R : R.natDegree ≤ r) (h_r_le_p : r ≤ p)
    (h_C : C.natDegree + q ≤ p)
    (h_P_splits : P.Splits) (h_Q_splits : Q.Splits)
    (h_decomp : P = C * Q + R) :
    Θ P Q q = (-1) ^ (p * q) * Q.leadingCoeff ^ (p - r) * Θ Q R r := by
  rw [Θ_eq_resultant P Q q h_P_splits (h_Q ▸ le_refl q),
      Θ_eq_resultant Q R r h_Q_splits h_R]
  rw [h_P, h_Q]
  rw [h_decomp, show C * Q + R = R + Q * C from by ring]
  rw [Polynomial.resultant_add_mul_left R Q C p q h_C (h_Q ▸ le_refl q)]
  rw [Polynomial.resultant_comm R Q p q]
  rw [show (p : ℕ) = r + (p - r) from by omega]
  rw [Polynomial.resultant_add_right_deg Q R q r (p - r) h_R]
  rw [show r + (p - r) - r = p - r from by omega]
  -- Note: `Q.coeff q = Q.leadingCoeff` since `Q.natDegree = q`.
  rw [show Q.coeff q = Q.leadingCoeff from by rw [← h_Q]; rfl]
  ring

end Theta

end Azurite.BPR.Chapter4
