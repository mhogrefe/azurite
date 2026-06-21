import Azurite.BasuPollackRoy.Chapter4.Section4_2.Remark_4_23
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# BPR Lemma 4.24: vanishing subresultant criterion

For non-zero polynomials `P, Q : D[X]` over a domain `D` of degrees
`p := P.natDegree`, `q := Q.natDegree`, and an index `j` in BPR's range
(`0 ≤ j ≤ q` if `p > q`, `0 ≤ j ≤ p - 1` if `p = q`),

  `sRes_j(P, Q) = 0 ↔ ∃ non-zero U, V : D[X] with
    deg U < q - j, deg V < p - j, and deg(U·P + V·Q) < j.`

(Reading `deg` as `Polynomial.degree`, so a zero polynomial has
`degree = ⊥ < ↑j` for any `j` — matching BPR's convention `deg 0 = -∞`.)

The proof mirrors Lemma 4.15. We use the `SyHa.mulMap` /
`SyHa.transpose_mulVec_apply` machinery from Remark 4.23 to translate
the matrix kernel condition into a polynomial-coefficient condition,
then decompose `SyHa.mulMap` as `encodeU·P + encodeV·Q` via the
auxiliary encodings of the coordinate vector, and finally upgrade
`uv ≠ 0` to `U ≠ 0 ∧ V ≠ 0` via domain cancellation.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### Encoding a coordinate vector as a polynomial pair -/

/-- The "P-side" encoding: the first `q - j` entries of a coordinate
    vector `uv : Fin (p + q - 2 j) → D` give a polynomial of
    `natDegree < q - j`. Hypothesis `hj_p : j ≤ p` (plus
    `hj_q : j ≤ q`) ensures the index lift
    `Fin (q - j) ↪ Fin (p + q - 2 j)` is well-defined. -/
noncomputable def SyHa.encodeU (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) : D[X] :=
  ∑ k : Fin (q - j),
    C (uv ⟨k.val, by have := k.isLt; omega⟩) * X ^ (q - j - 1 - k.val)

/-- The "Q-side" encoding. Hypotheses ensure the index lift
    `(q - j) + ℓ.val ∈ Fin (p + q - 2 j)` is well-defined. Note that
    the powers ascend (`X^0, X^1, …`) to match `SyHa`'s row convention
    (Q-block uses `X^0 Q, X·Q, …`). -/
noncomputable def SyHa.encodeV (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) : D[X] :=
  ∑ ℓ : Fin (p - j),
    C (uv ⟨(q - j) + ℓ.val, by have := ℓ.isLt; omega⟩) * X ^ ℓ.val

/-! ### Coefficient extraction -/

theorem SyHa.encodeU_coeff (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) (m : ℕ) (hm : m < q - j) :
    (SyHa.encodeU p q j hj_q hj_p uv).coeff m =
      uv ⟨q - j - 1 - m, by omega⟩ := by
  unfold SyHa.encodeU
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨q - j - 1 - m, by omega⟩ : Fin (q - j))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_eq : q - j - 1 - (⟨q - j - 1 - m, by omega⟩ : Fin (q - j)).val = m := by
      show q - j - 1 - (q - j - 1 - m) = m
      omega
    rw [if_pos h_eq.symm, mul_one]
  · intro k _ h_ne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_neq : q - j - 1 - k.val ≠ m := by
      intro h_eq
      apply h_ne
      apply Fin.ext
      show k.val = q - j - 1 - m
      have := k.isLt
      omega
    rw [if_neg (Ne.symm h_neq), mul_zero]
  · intro h_not_mem
    exact absurd (Finset.mem_univ _) h_not_mem

theorem SyHa.encodeV_coeff (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) (m : ℕ) (hm : m < p - j) :
    (SyHa.encodeV p q j hj_q hj_p uv).coeff m =
      uv ⟨(q - j) + m, by omega⟩ := by
  unfold SyHa.encodeV
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨m, by omega⟩ : Fin (p - j))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [if_pos rfl, mul_one]
  · intro ℓ _ h_ne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_neq : ℓ.val ≠ m := by
      intro h_eq
      apply h_ne
      apply Fin.ext h_eq
    rw [if_neg (Ne.symm h_neq), mul_zero]
  · intro h_not_mem
    exact absurd (Finset.mem_univ _) h_not_mem

theorem SyHa.encodeU_coeff_of_ge (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) (m : ℕ) (hm : q - j ≤ m) :
    (SyHa.encodeU p q j hj_q hj_p uv).coeff m = 0 := by
  unfold SyHa.encodeU
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have h_neq : q - j - 1 - k.val ≠ m := by
    have := k.isLt
    omega
  rw [if_neg (Ne.symm h_neq), mul_zero]

theorem SyHa.encodeV_coeff_of_ge (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) (m : ℕ) (hm : p - j ≤ m) :
    (SyHa.encodeV p q j hj_q hj_p uv).coeff m = 0 := by
  unfold SyHa.encodeV
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ℓ _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have h_neq : ℓ.val ≠ m := by
    have := ℓ.isLt
    omega
  rw [if_neg (Ne.symm h_neq), mul_zero]

/-! ### `Fin (p + q - 2 j)` sum split at `q - j` -/

omit [CommRing D] in
private lemma Fin_sum_split_at_SyHa {M : Type*} [AddCommMonoid M] (p q j : ℕ)
    (hj_q : j ≤ q) (hj_p : j ≤ p)
    (f : Fin (p + q - 2 * j) → M) :
    ∑ i : Fin (p + q - 2 * j), f i =
      (∑ k : Fin (q - j), f ⟨k.val, by have := k.isLt; omega⟩) +
      (∑ ℓ : Fin (p - j), f ⟨(q - j) + ℓ.val, by have := ℓ.isLt; omega⟩) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (p + q - 2 * j)))
      (·.val < q - j) f]
  congr 1
  · apply Finset.sum_bij
      (fun (i : Fin (p + q - 2 * j)) (h : i ∈ _) =>
        (⟨i.val, by
          rw [Finset.mem_filter] at h
          exact h.2⟩ : Fin (q - j)))
    · intros; exact Finset.mem_univ _
    · intro i₁ _ i₂ _ h_eq
      simp only [Fin.mk.injEq] at h_eq
      exact Fin.ext h_eq
    · intro k _
      refine ⟨⟨k.val, by have := k.isLt; omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, k.isLt⟩
      · exact Fin.ext rfl
    · intro i hi
      apply congrArg
      apply Fin.ext
      rfl
  · apply Finset.sum_bij
      (fun (i : Fin (p + q - 2 * j)) (h : i ∈ _) =>
        (⟨i.val - (q - j), by
          rw [Finset.mem_filter] at h
          have := i.isLt
          push Not at h
          omega⟩ : Fin (p - j)))
    · intros; exact Finset.mem_univ _
    · intro i₁ h₁ i₂ h₂ h_eq
      simp only [Fin.mk.injEq] at h_eq
      rw [Finset.mem_filter] at h₁ h₂
      push Not at h₁ h₂
      apply Fin.ext
      omega
    · intro ℓ _
      refine ⟨⟨(q - j) + ℓ.val, by have := ℓ.isLt; omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show ¬ (q - j) + ℓ.val < q - j
        omega
      · apply Fin.ext
        show (q - j) + ℓ.val - (q - j) = ℓ.val
        omega
    · intro i hi
      apply congrArg
      apply Fin.ext
      rw [Finset.mem_filter] at hi
      push Not at hi
      show i.val = (q - j) + (i.val - (q - j))
      omega

/-! ### `mulMap` decomposes as `encodeU * P + encodeV * Q` -/

theorem SyHa.mulMap_eq_pair (P Q : D[X]) (j : ℕ)
    (hj_q : j ≤ Q.natDegree) (hj_p : j ≤ P.natDegree)
    (uv : Fin (P.natDegree + Q.natDegree - 2 * j) → D) :
    SyHa.mulMap P Q j uv =
      SyHa.encodeU P.natDegree Q.natDegree j hj_q hj_p uv * P +
      SyHa.encodeV P.natDegree Q.natDegree j hj_q hj_p uv * Q := by
  apply Polynomial.ext
  intro n
  unfold SyHa.mulMap
  rw [Polynomial.finsetSum_coeff]
  rw [Polynomial.coeff_add]
  have h_eU : (SyHa.encodeU P.natDegree Q.natDegree j hj_q hj_p uv * P).coeff n =
      ∑ k : Fin (Q.natDegree - j),
        uv ⟨k.val, by have := k.isLt; omega⟩ *
        (X ^ (Q.natDegree - j - 1 - k.val) * P).coeff n := by
    unfold SyHa.encodeU
    rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc, Polynomial.coeff_C_mul]
  have h_eV : (SyHa.encodeV P.natDegree Q.natDegree j hj_q hj_p uv * Q).coeff n =
      ∑ ℓ : Fin (P.natDegree - j),
        uv ⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩ *
        (X ^ ℓ.val * Q).coeff n := by
    unfold SyHa.encodeV
    rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [mul_assoc, Polynomial.coeff_C_mul]
  rw [h_eU, h_eV]
  rw [Fin_sum_split_at_SyHa P.natDegree Q.natDegree j hj_q hj_p]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    have h_lt :
        (⟨k.val, by have := k.isLt; omega⟩ :
          Fin (P.natDegree + Q.natDegree - 2 * j)).val < Q.natDegree - j :=
      k.isLt
    show (C (uv ⟨k.val, by have := k.isLt; omega⟩) *
        if (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree - 2 * j)).val < Q.natDegree - j then
          X ^ (Q.natDegree - j - 1 -
            (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree - 2 * j)).val) * P
        else
          X ^ ((⟨k.val, by have := k.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree - 2 * j)).val -
            (Q.natDegree - j)) * Q).coeff n =
      _
    rw [if_pos h_lt]
    rw [Polynomial.coeff_C_mul]
  · apply Finset.sum_congr rfl
    intro ℓ _
    have h_not_lt :
        ¬ (⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩ :
            Fin (P.natDegree + Q.natDegree - 2 * j)).val < Q.natDegree - j := by
      show ¬ (Q.natDegree - j) + ℓ.val < Q.natDegree - j
      omega
    show (C (uv ⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩) *
        if (⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree - 2 * j)).val < Q.natDegree - j then
          X ^ (Q.natDegree - j - 1 -
            (⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree - 2 * j)).val) * P
        else
          X ^ ((⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree - 2 * j)).val -
            (Q.natDegree - j)) * Q).coeff n =
      _
    rw [if_neg h_not_lt]
    rw [Polynomial.coeff_C_mul]
    have h_idx :
        (⟨(Q.natDegree - j) + ℓ.val, by have := ℓ.isLt; omega⟩ :
          Fin (P.natDegree + Q.natDegree - 2 * j)).val -
        (Q.natDegree - j) = ℓ.val := by
      show (Q.natDegree - j) + ℓ.val - (Q.natDegree - j) = ℓ.val
      omega
    rw [h_idx]

/-! ### Degree bounds -/

variable [Nontrivial D]

omit [Nontrivial D] in
theorem SyHa.encodeU_natDegree_lt (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) (hqj : 0 < q - j) :
    (SyHa.encodeU p q j hj_q hj_p uv).natDegree < q - j := by
  apply Nat.lt_of_lt_of_le _ (le_refl (q - j))
  by_contra h_ge
  push Not at h_ge
  have h_coeff : (SyHa.encodeU p q j hj_q hj_p uv).coeff
      (SyHa.encodeU p q j hj_q hj_p uv).natDegree = 0 :=
    SyHa.encodeU_coeff_of_ge p q j hj_q hj_p uv _ h_ge
  by_cases h_zero : SyHa.encodeU p q j hj_q hj_p uv = 0
  · rw [h_zero, Polynomial.natDegree_zero] at h_ge
    omega
  · exact Polynomial.leadingCoeff_ne_zero.mpr h_zero h_coeff

omit [Nontrivial D] in
theorem SyHa.encodeV_natDegree_lt (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) (hpj : 0 < p - j) :
    (SyHa.encodeV p q j hj_q hj_p uv).natDegree < p - j := by
  apply Nat.lt_of_lt_of_le _ (le_refl (p - j))
  by_contra h_ge
  push Not at h_ge
  have h_coeff : (SyHa.encodeV p q j hj_q hj_p uv).coeff
      (SyHa.encodeV p q j hj_q hj_p uv).natDegree = 0 :=
    SyHa.encodeV_coeff_of_ge p q j hj_q hj_p uv _ h_ge
  by_cases h_zero : SyHa.encodeV p q j hj_q hj_p uv = 0
  · rw [h_zero, Polynomial.natDegree_zero] at h_ge
    omega
  · exact Polynomial.leadingCoeff_ne_zero.mpr h_zero h_coeff

omit [Nontrivial D] in
theorem SyHa.mulMap_natDegree_lt (P Q : D[X]) (j : ℕ)
    (hj_q : j ≤ Q.natDegree) (hj_p : j ≤ P.natDegree)
    (uv : Fin (P.natDegree + Q.natDegree - 2 * j) → D)
    (hpq : 0 < P.natDegree + Q.natDegree - 2 * j) :
    (SyHa.mulMap P Q j uv).natDegree <
      P.natDegree + Q.natDegree - j := by
  rw [SyHa.mulMap_eq_pair P Q j hj_q hj_p]
  refine Nat.lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
  refine max_lt ?_ ?_
  · rcases Nat.eq_zero_or_pos (Q.natDegree - j) with hqj | hqj
    · have h_eu_zero :
          SyHa.encodeU P.natDegree Q.natDegree j hj_q hj_p uv = 0 := by
        unfold SyHa.encodeU
        apply Finset.sum_eq_zero
        intro k _
        exfalso
        have := k.isLt
        omega
      rw [h_eu_zero, zero_mul, Polynomial.natDegree_zero]
      omega
    · refine Nat.lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
      have := SyHa.encodeU_natDegree_lt P.natDegree Q.natDegree j hj_q hj_p uv hqj
      omega
  · rcases Nat.eq_zero_or_pos (P.natDegree - j) with hpj | hpj
    · have h_ev_zero :
          SyHa.encodeV P.natDegree Q.natDegree j hj_q hj_p uv = 0 := by
        unfold SyHa.encodeV
        apply Finset.sum_eq_zero
        intro ℓ _
        exfalso
        have := ℓ.isLt
        omega
      rw [h_ev_zero, zero_mul, Polynomial.natDegree_zero]
      omega
    · refine Nat.lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
      have := SyHa.encodeV_natDegree_lt P.natDegree Q.natDegree j hj_q hj_p uv hpj
      omega

/-! ### `uv = 0` iff both encodings vanish -/

omit [Nontrivial D] in
theorem SyHa.encode_eq_zero_iff (p q j : ℕ) (hj_q : j ≤ q) (hj_p : j ≤ p)
    (uv : Fin (p + q - 2 * j) → D) :
    (SyHa.encodeU p q j hj_q hj_p uv = 0 ∧
      SyHa.encodeV p q j hj_q hj_p uv = 0) ↔ uv = 0 := by
  constructor
  · rintro ⟨hU, hV⟩
    funext i
    show uv i = (0 : Fin (p + q - 2 * j) → D) i
    by_cases h : i.val < q - j
    · have h_uv_eq :
          uv i = (SyHa.encodeU p q j hj_q hj_p uv).coeff (q - j - 1 - i.val) := by
        rw [SyHa.encodeU_coeff p q j hj_q hj_p uv (q - j - 1 - i.val)
              (by have := i.isLt; omega)]
        congr 1
        apply Fin.ext
        show i.val = q - j - 1 - (q - j - 1 - i.val)
        omega
      rw [h_uv_eq, hU, Polynomial.coeff_zero]
      rfl
    · push Not at h
      have h_uv_eq :
          uv i = (SyHa.encodeV p q j hj_q hj_p uv).coeff (i.val - (q - j)) := by
        rw [SyHa.encodeV_coeff p q j hj_q hj_p uv (i.val - (q - j))
              (by have := i.isLt; omega)]
        congr 1
        apply Fin.ext
        show i.val = (q - j) + (i.val - (q - j))
        have := i.isLt; omega
      rw [h_uv_eq, hV, Polynomial.coeff_zero]
      rfl
  · intro h
    refine ⟨?_, ?_⟩
    · rw [show uv = 0 from h]
      unfold SyHa.encodeU; simp
    · rw [show uv = 0 from h]
      unfold SyHa.encodeV; simp

/-! ### Lemma 4.24 -/

variable [IsDomain D] [DecidableEq D]

omit [Nontrivial D] in
/-- **BPR Lemma 4.24.** Over a domain `D`, the `j`-th signed
    subresultant coefficient `sRes_j(P, Q)` of non-zero `P, Q : D[X]`
    vanishes if and only if there exist non-zero polynomials
    `U, V : D[X]` with `deg U < Q.natDegree - j`,
    `deg V < P.natDegree - j`, and `deg(U·P + V·Q) < j`
    (using `Polynomial.degree`, so a zero polynomial satisfies the
    last condition vacuously — matching BPR's `deg 0 = -∞`).

    BPR's range is `0 ≤ j ≤ Q.natDegree` if `P.natDegree > Q.natDegree`,
    or `0 ≤ j ≤ P.natDegree - 1` if `P.natDegree = Q.natDegree`. The
    hypotheses `j ≤ Q.natDegree` and `j < P.natDegree` cover both. -/
theorem Lemma_4_24 (P Q : D[X]) (j : ℕ)
    (hj_q : j ≤ Q.natDegree) (hj_p : j < P.natDegree)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    sRes P Q j = 0 ↔
      ∃ U V : D[X], U ≠ 0 ∧ V ≠ 0 ∧
        U.degree < ↑(Q.natDegree - j) ∧
        V.degree < ↑(P.natDegree - j) ∧
        (U * P + V * Q).degree < ↑j := by
  classical
  set p := P.natDegree with hp_def
  set q := Q.natDegree with hq_def
  -- Unfold sRes for the `j ≤ q` branch.
  have h_sRes : sRes P Q j = (SyHaSquare P Q j).det := by
    unfold sRes
    rw [if_pos hj_q]
  rw [h_sRes]
  have hjp_le : j ≤ p := Nat.le_of_lt hj_p
  have hpq_pos : 0 < p + q - 2 * j := by omega
  -- Apply Matrix.exists_mulVec_eq_zero_iff to the transposed submatrix.
  rw [show (SyHaSquare P Q j).det = (SyHaSquare P Q j).transpose.det from by
    rw [Matrix.det_transpose]]
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  -- Translate the kernel condition into a polynomial-coefficient condition.
  have h_kernel_iff : ∀ uv : Fin (p + q - 2 * j) → D,
      (SyHaSquare P Q j).transpose.mulVec uv = 0 ↔
        ∀ i : Fin (p + q - 2 * j),
          (SyHa.mulMap P Q j uv).coeff (p + q - j - 1 - i.val) = 0 := by
    intro uv
    constructor
    · intro h i
      have h_castLE : (SyHaSquare P Q j).transpose.mulVec uv i =
          (SyHa P Q j).transpose.mulVec uv (Fin.castLE (by omega) i) := by
        unfold SyHaSquare
        simp [Matrix.transpose, Matrix.submatrix, Matrix.mulVec, Matrix.of_apply,
              dotProduct, Fin.castLE]
      have hi := congrFun h i
      rw [h_castLE, SyHa.transpose_mulVec_apply] at hi
      show (SyHa.mulMap P Q j uv).coeff (p + q - j - 1 - i.val) = 0
      exact hi
    · intro h
      funext i
      have h_castLE : (SyHaSquare P Q j).transpose.mulVec uv i =
          (SyHa P Q j).transpose.mulVec uv (Fin.castLE (by omega) i) := by
        unfold SyHaSquare
        simp [Matrix.transpose, Matrix.submatrix, Matrix.mulVec, Matrix.of_apply,
              dotProduct, Fin.castLE]
      rw [h_castLE, SyHa.transpose_mulVec_apply]
      have hi := h i
      show (SyHa.mulMap P Q j uv).coeff
          (p + q - j - 1 - (Fin.castLE _ i).val) = (0 : Fin (p + q - 2 * j) → D) i
      have h_eq : (Fin.castLE
            (show p + q - 2 * j ≤ p + q - j from by omega) i).val = i.val := rfl
      rw [h_eq, hi]; rfl
  -- The kernel condition is equivalent to `(mulMap).degree < ↑j`
  -- (combining the kernel coefficient annihilation with the degree
  -- bound `mulMap.natDegree < p + q - j`).
  have h_kernel_degree : ∀ uv : Fin (p + q - 2 * j) → D,
      (∀ i : Fin (p + q - 2 * j),
        (SyHa.mulMap P Q j uv).coeff (p + q - j - 1 - i.val) = 0) ↔
        (SyHa.mulMap P Q j uv).degree < ↑j := by
    intro uv
    constructor
    · intro h_kernel
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      by_cases hm_hi : m < p + q - j
      · -- m ∈ [j, p+q-j): set i.val := p+q-j-1-m, then m = p+q-j-1-i.val.
        have h_i_bound : p + q - j - 1 - m < p + q - 2 * j := by
          have hm_ge : (↑j : ℕ) ≤ m := by exact_mod_cast hm
          omega
        have h_idx_eq : p + q - j - 1 - (⟨p + q - j - 1 - m, h_i_bound⟩ :
            Fin (p + q - 2 * j)).val = m := by
          have hm_ge : (↑j : ℕ) ≤ m := by exact_mod_cast hm
          show p + q - j - 1 - (p + q - j - 1 - m) = m
          omega
        have := h_kernel ⟨p + q - j - 1 - m, h_i_bound⟩
        rwa [h_idx_eq] at this
      · push Not at hm_hi
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h_deg : (SyHa.mulMap P Q j uv).natDegree < p + q - j :=
          SyHa.mulMap_natDegree_lt P Q j hj_q hjp_le uv hpq_pos
        omega
    · intro h_deg i
      have hm_ge : j ≤ p + q - j - 1 - i.val := by
        have hi := i.isLt
        omega
      by_cases h0 : SyHa.mulMap P Q j uv = 0
      · rw [h0, Polynomial.coeff_zero]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.degree_eq_natDegree h0] at h_deg
        have : (SyHa.mulMap P Q j uv).natDegree < j := by exact_mod_cast h_deg
        omega
  -- Combine the two equivalences and prove the main biconditional.
  constructor
  · -- Forward direction.
    rintro ⟨uv, h_ne, h_mul⟩
    rw [h_kernel_iff, h_kernel_degree] at h_mul
    rw [SyHa.mulMap_eq_pair P Q j hj_q hjp_le] at h_mul
    set U := SyHa.encodeU p q j hj_q hjp_le uv with hU_def
    set V := SyHa.encodeV p q j hj_q hjp_le uv with hV_def
    have h_U_nonzero : U ≠ 0 := by
      intro hU
      rw [hU, zero_mul, zero_add] at h_mul
      have hV_zero : V = 0 := by
        rcases eq_or_ne V 0 with h | h
        · exact h
        · exfalso
          rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree h,
              Polynomial.degree_eq_natDegree hQ] at h_mul
          have hcast : ((V.natDegree + Q.natDegree : ℕ) : WithBot ℕ) =
              (V.natDegree : WithBot ℕ) + (Q.natDegree : WithBot ℕ) := by push_cast; rfl
          rw [← hcast] at h_mul
          have h_lt : V.natDegree + Q.natDegree < j := by exact_mod_cast h_mul
          omega
      exact h_ne ((SyHa.encode_eq_zero_iff p q j hj_q hjp_le uv).mp ⟨hU, hV_zero⟩)
    have h_V_nonzero : V ≠ 0 := by
      intro hV
      rw [hV, zero_mul, add_zero] at h_mul
      have hU_zero : U = 0 := by
        rcases eq_or_ne U 0 with h | h
        · exact h
        · exfalso
          rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree h,
              Polynomial.degree_eq_natDegree hP] at h_mul
          have hcast : ((U.natDegree + P.natDegree : ℕ) : WithBot ℕ) =
              (U.natDegree : WithBot ℕ) + (P.natDegree : WithBot ℕ) := by push_cast; rfl
          rw [← hcast] at h_mul
          have : U.natDegree + P.natDegree < j := by exact_mod_cast h_mul
          omega
      exact h_ne ((SyHa.encode_eq_zero_iff p q j hj_q hjp_le uv).mp ⟨hU_zero, hV⟩)
    refine ⟨U, V, h_U_nonzero, h_V_nonzero, ?_, ?_, h_mul⟩
    · rcases Nat.eq_zero_or_pos (q - j) with hqj | hqj
      · exfalso
        apply h_U_nonzero
        rw [hU_def]
        unfold SyHa.encodeU
        apply Finset.sum_eq_zero
        intro k _
        exfalso
        have := k.isLt
        omega
      · rw [Polynomial.degree_eq_natDegree h_U_nonzero]
        exact_mod_cast SyHa.encodeU_natDegree_lt p q j hj_q hjp_le uv hqj
    · rcases Nat.eq_zero_or_pos (p - j) with hpj | hpj
      · exfalso
        apply h_V_nonzero
        rw [hV_def]
        unfold SyHa.encodeV
        apply Finset.sum_eq_zero
        intro ℓ _
        exfalso
        have := ℓ.isLt
        omega
      · rw [Polynomial.degree_eq_natDegree h_V_nonzero]
        exact_mod_cast SyHa.encodeV_natDegree_lt p q j hj_q hjp_le uv hpj
  · -- Reverse direction.
    rintro ⟨U, V, hU, hV, hUq, hVp, h_lt⟩
    -- Build uv from U, V coefficients.
    let uv : Fin (p + q - 2 * j) → D := fun i =>
      if h : i.val < q - j then U.coeff (q - j - 1 - i.val)
      else V.coeff (i.val - (q - j))
    refine ⟨uv, ?_, ?_⟩
    · -- uv ≠ 0: if uv = 0 then U = 0 (contradiction since U ≠ 0).
      intro h_uv_zero
      apply hU
      apply Polynomial.ext
      intro m
      rw [Polynomial.coeff_zero]
      by_cases hmqj : m < q - j
      · have h_idx : (⟨q - j - 1 - m, by omega⟩ :
            Fin (p + q - 2 * j)).val < q - j := by
          show q - j - 1 - m < q - j; omega
        have h := congrFun h_uv_zero ⟨q - j - 1 - m, by omega⟩
        show U.coeff m = 0
        have h_uv_val : uv ⟨q - j - 1 - m, by omega⟩ = U.coeff m := by
          show (if h : _ < q - j then _ else _) = _
          rw [dif_pos h_idx]
          congr 1
          show q - j - 1 - (q - j - 1 - m) = m; omega
        rw [← h_uv_val, h]
        rfl
      · push Not at hmqj
        have h_U_natDeg : U.natDegree < q - j := by
          rw [Polynomial.degree_eq_natDegree hU] at hUq
          exact_mod_cast hUq
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · -- Show SyHaSquare^T.mulVec uv = 0.
      rw [h_kernel_iff, h_kernel_degree]
      have h_eU : SyHa.encodeU p q j hj_q hjp_le uv = U := by
        apply Polynomial.ext
        intro m
        by_cases hmqj : m < q - j
        · rw [SyHa.encodeU_coeff p q j hj_q hjp_le uv m hmqj]
          have h_idx : (⟨q - j - 1 - m, by omega⟩ :
              Fin (p + q - 2 * j)).val < q - j := by
            show q - j - 1 - m < q - j; omega
          show (if h : _ < q - j then _ else _) = U.coeff m
          rw [dif_pos h_idx]
          congr 1
          show q - j - 1 - (q - j - 1 - m) = m; omega
        · rw [SyHa.encodeU_coeff_of_ge p q j hj_q hjp_le uv m (by omega)]
          have h_U_natDeg : U.natDegree < q - j := by
            rw [Polynomial.degree_eq_natDegree hU] at hUq
            exact_mod_cast hUq
          rw [show U.coeff m = 0 from
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      have h_eV : SyHa.encodeV p q j hj_q hjp_le uv = V := by
        apply Polynomial.ext
        intro m
        by_cases hmpj : m < p - j
        · rw [SyHa.encodeV_coeff p q j hj_q hjp_le uv m hmpj]
          have h_idx : ¬ (⟨(q - j) + m, by omega⟩ :
              Fin (p + q - 2 * j)).val < q - j := by
            show ¬ (q - j) + m < q - j; omega
          show (if h : _ < q - j then _ else _) = V.coeff m
          rw [dif_neg h_idx]
          congr 1
          show ((q - j) + m) - (q - j) = m; omega
        · rw [SyHa.encodeV_coeff_of_ge p q j hj_q hjp_le uv m (by omega)]
          have h_V_natDeg : V.natDegree < p - j := by
            rw [Polynomial.degree_eq_natDegree hV] at hVp
            exact_mod_cast hVp
          rw [show V.coeff m = 0 from
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      rw [SyHa.mulMap_eq_pair P Q j hj_q hjp_le, h_eU, h_eV]
      exact h_lt

end Azurite.BPR.Chapter4
