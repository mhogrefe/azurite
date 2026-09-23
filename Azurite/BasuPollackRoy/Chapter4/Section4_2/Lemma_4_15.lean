import Azurite.BasuPollackRoy.Chapter4.Section4_2.Remark_4_14
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# BPR Lemma 4.15: vanishing resultant criterion

For non-zero polynomials `P, Q : D[X]` over a domain `D` (of degrees
`p := P.natDegree`, `q := Q.natDegree`), the resultant `Res(P, Q)`
vanishes iff there exist non-zero polynomials `U, V : D[X]` with
`natDegree U < q`, `natDegree V < p`, and `U · P + V · Q = 0`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### Encoding a coordinate vector as a polynomial pair -/

/-- Encode the first `q` entries of a coordinate vector
    `uv : Fin (p + q) → D` as a polynomial `U` of `natDegree < q`. -/
noncomputable def Syl.encodeU (p q : ℕ) (uv : Fin (p + q) → D) : D[X] :=
  ∑ k : Fin q, C (uv ⟨k.val, by have := k.isLt; omega⟩) * X ^ (q - 1 - k.val)

/-- Encode the last `p` entries of a coordinate vector
    `uv : Fin (p + q) → D` as a polynomial `V` of `natDegree < p`. -/
noncomputable def Syl.encodeV (p q : ℕ) (uv : Fin (p + q) → D) : D[X] :=
  ∑ ℓ : Fin p, C (uv ⟨q + ℓ.val, by have := ℓ.isLt; omega⟩) *
    X ^ (p - 1 - ℓ.val)

/-! ### Coefficient extraction -/

theorem Syl.encodeU_coeff (p q : ℕ) (uv : Fin (p + q) → D) (m : ℕ) (hm : m < q) :
    (Syl.encodeU p q uv).coeff m = uv ⟨q - 1 - m, by omega⟩ := by
  unfold Syl.encodeU
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨q - 1 - m, by omega⟩ : Fin q)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_eq : q - 1 - (⟨q - 1 - m, by omega⟩ : Fin q).val = m := by
      show q - 1 - (q - 1 - m) = m
      omega
    rw [ite_eq_left h_eq.symm, mul_one]
  · intro k _ h_ne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_neq : q - 1 - k.val ≠ m := by
      intro h_eq
      apply h_ne
      apply Fin.ext
      show k.val = q - 1 - m
      have := k.isLt
      omega
    rw [ite_eq_right (Ne.symm h_neq), mul_zero]
  · intro h_not_mem
    exact absurd (Finset.mem_univ _) h_not_mem

theorem Syl.encodeV_coeff (p q : ℕ) (uv : Fin (p + q) → D) (m : ℕ) (hm : m < p) :
    (Syl.encodeV p q uv).coeff m = uv ⟨q + (p - 1 - m), by omega⟩ := by
  unfold Syl.encodeV
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨p - 1 - m, by omega⟩ : Fin p)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_eq : p - 1 - (⟨p - 1 - m, by omega⟩ : Fin p).val = m := by
      show p - 1 - (p - 1 - m) = m
      omega
    rw [ite_eq_left h_eq.symm, mul_one]
  · intro ℓ _ h_ne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_neq : p - 1 - ℓ.val ≠ m := by
      intro h_eq
      apply h_ne
      apply Fin.ext
      show ℓ.val = p - 1 - m
      have := ℓ.isLt
      omega
    rw [ite_eq_right (Ne.symm h_neq), mul_zero]
  · intro h_not_mem
    exact absurd (Finset.mem_univ _) h_not_mem

theorem Syl.encodeU_coeff_of_ge (p q : ℕ) (uv : Fin (p + q) → D) (m : ℕ)
    (hm : q ≤ m) : (Syl.encodeU p q uv).coeff m = 0 := by
  unfold Syl.encodeU
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have h_neq : q - 1 - k.val ≠ m := by
    have := k.isLt
    omega
  rw [ite_eq_right (Ne.symm h_neq), mul_zero]

theorem Syl.encodeV_coeff_of_ge (p q : ℕ) (uv : Fin (p + q) → D) (m : ℕ)
    (hm : p ≤ m) : (Syl.encodeV p q uv).coeff m = 0 := by
  unfold Syl.encodeV
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ℓ _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have h_neq : p - 1 - ℓ.val ≠ m := by
    have := ℓ.isLt
    omega
  rw [ite_eq_right (Ne.symm h_neq), mul_zero]

/-! ### `Fin (p + q)` sum split at coordinate `q` -/

omit [CommRing D] in
private lemma Fin_sum_split_at {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p + q) → M) :
    ∑ j : Fin (p + q), f j =
      (∑ k : Fin q, f ⟨k.val, by have := k.isLt; omega⟩) +
      (∑ ℓ : Fin p, f ⟨q + ℓ.val, by have := ℓ.isLt; omega⟩) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (p + q)))
      (·.val < q) f]
  congr 1
  · apply Finset.sum_bij
      (fun (j : Fin (p + q)) (h : j ∈ _) =>
        (⟨j.val, by
          rw [Finset.mem_filter] at h
          exact h.2⟩ : Fin q))
    · intros; exact Finset.mem_univ _
    · intro j₁ _ j₂ _ h_eq
      simp only [Fin.mk.injEq] at h_eq
      exact Fin.ext h_eq
    · intro k _
      refine ⟨⟨k.val, by have := k.isLt; omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, k.isLt⟩
      · exact Fin.ext rfl
    · intro j hj
      apply congrArg
      apply Fin.ext
      rfl
  · apply Finset.sum_bij
      (fun (j : Fin (p + q)) (h : j ∈ _) =>
        (⟨j.val - q, by
          rw [Finset.mem_filter] at h
          have := j.isLt
          push Not at h
          omega⟩ : Fin p))
    · intros; exact Finset.mem_univ _
    · intro j₁ h₁ j₂ h₂ h_eq
      simp only [Fin.mk.injEq] at h_eq
      rw [Finset.mem_filter] at h₁ h₂
      push Not at h₁ h₂
      apply Fin.ext
      omega
    · intro ℓ _
      refine ⟨⟨q + ℓ.val, by have := ℓ.isLt; omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show ¬ q + ℓ.val < q
        omega
      · apply Fin.ext
        show q + ℓ.val - q = ℓ.val
        omega
    · intro j hj
      apply congrArg
      apply Fin.ext
      rw [Finset.mem_filter] at hj
      push Not at hj
      show j.val = q + (j.val - q)
      omega

/-! ### `mulMap` decomposes as `encodeU * P + encodeV * Q` -/

theorem Syl.mulMap_eq_pair (P Q : D[X])
    (uv : Fin (P.natDegree + Q.natDegree) → D) :
    Syl.mulMap P Q uv =
      Syl.encodeU P.natDegree Q.natDegree uv * P +
      Syl.encodeV P.natDegree Q.natDegree uv * Q := by
  apply Polynomial.ext
  intro n
  unfold Syl.mulMap
  rw [Polynomial.finsetSum_coeff]
  rw [Polynomial.coeff_add]
  have h_eU : (Syl.encodeU P.natDegree Q.natDegree uv * P).coeff n =
      ∑ k : Fin Q.natDegree,
        uv ⟨k.val, by have := k.isLt; omega⟩ *
        (X ^ (Q.natDegree - 1 - k.val) * P).coeff n := by
    unfold Syl.encodeU
    rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc, Polynomial.coeff_C_mul]
  have h_eV : (Syl.encodeV P.natDegree Q.natDegree uv * Q).coeff n =
      ∑ ℓ : Fin P.natDegree,
        uv ⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩ *
        (X ^ (P.natDegree - 1 - ℓ.val) * Q).coeff n := by
    unfold Syl.encodeV
    rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [mul_assoc, Polynomial.coeff_C_mul]
  rw [h_eU, h_eV]
  rw [Fin_sum_split_at P.natDegree Q.natDegree]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    have h_lt :
        (⟨k.val, by have := k.isLt; omega⟩ : Fin (P.natDegree + Q.natDegree)).val
        < Q.natDegree := k.isLt
    show (C (uv ⟨k.val, by have := k.isLt; omega⟩) *
        if (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree)).val < Q.natDegree then
          X ^ (Q.natDegree - 1 -
            (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree)).val) * P
        else
          X ^ (P.natDegree + Q.natDegree - 1 -
            (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree)).val) * Q).coeff n =
      _
    rw [ite_eq_left h_lt]
    rw [Polynomial.coeff_C_mul]
  · apply Finset.sum_congr rfl
    intro ℓ _
    have h_not_lt : ¬ (⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩ :
                       Fin (P.natDegree + Q.natDegree)).val < Q.natDegree := by
      show ¬ Q.natDegree + ℓ.val < Q.natDegree
      omega
    show (C (uv ⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩) *
        if (⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree)).val < Q.natDegree then
          X ^ (Q.natDegree - 1 -
            (⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree)).val) * P
        else
          X ^ (P.natDegree + Q.natDegree - 1 -
            (⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (P.natDegree + Q.natDegree)).val) * Q).coeff n =
      _
    rw [ite_eq_right h_not_lt]
    rw [Polynomial.coeff_C_mul]
    have h_idx : P.natDegree + Q.natDegree - 1 -
        (⟨Q.natDegree + ℓ.val, by have := ℓ.isLt; omega⟩ :
          Fin (P.natDegree + Q.natDegree)).val =
        P.natDegree - 1 - ℓ.val := by
      show P.natDegree + Q.natDegree - 1 - (Q.natDegree + ℓ.val) =
        P.natDegree - 1 - ℓ.val
      have := ℓ.isLt; omega
    rw [h_idx]

/-! ### Degree bounds -/

variable [Nontrivial D]

omit [Nontrivial D] in
theorem Syl.encodeU_natDegree_lt (p q : ℕ) (uv : Fin (p + q) → D) (hq : 0 < q) :
    (Syl.encodeU p q uv).natDegree < q := by
  apply Nat.lt_of_lt_of_le _ (le_refl q)
  by_contra h_ge
  push Not at h_ge
  have h_le_max : q ≤ (Syl.encodeU p q uv).natDegree := h_ge
  have h_coeff : (Syl.encodeU p q uv).coeff (Syl.encodeU p q uv).natDegree = 0 :=
    Syl.encodeU_coeff_of_ge p q uv _ h_le_max
  by_cases h_zero : Syl.encodeU p q uv = 0
  · rw [h_zero, Polynomial.natDegree_zero] at h_le_max
    omega
  · exact Polynomial.leadingCoeff_ne_zero.mpr h_zero h_coeff

omit [Nontrivial D] in
theorem Syl.encodeV_natDegree_lt (p q : ℕ) (uv : Fin (p + q) → D) (hp : 0 < p) :
    (Syl.encodeV p q uv).natDegree < p := by
  apply Nat.lt_of_lt_of_le _ (le_refl p)
  by_contra h_ge
  push Not at h_ge
  have h_le_max : p ≤ (Syl.encodeV p q uv).natDegree := h_ge
  have h_coeff : (Syl.encodeV p q uv).coeff (Syl.encodeV p q uv).natDegree = 0 :=
    Syl.encodeV_coeff_of_ge p q uv _ h_le_max
  by_cases h_zero : Syl.encodeV p q uv = 0
  · rw [h_zero, Polynomial.natDegree_zero] at h_le_max
    omega
  · exact Polynomial.leadingCoeff_ne_zero.mpr h_zero h_coeff

omit [Nontrivial D] in
theorem Syl.mulMap_natDegree_lt (P Q : D[X])
    (uv : Fin (P.natDegree + Q.natDegree) → D)
    (hpq : 0 < P.natDegree + Q.natDegree) :
    (Syl.mulMap P Q uv).natDegree < P.natDegree + Q.natDegree := by
  rw [Syl.mulMap_eq_pair]
  refine Nat.lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
  refine max_lt ?_ ?_
  · rcases Nat.eq_zero_or_pos Q.natDegree with hq | hq
    · have h_eu_zero : Syl.encodeU P.natDegree Q.natDegree uv = 0 := by
        unfold Syl.encodeU
        apply Finset.sum_eq_zero
        intro k _
        exfalso
        have := k.isLt
        omega
      rw [h_eu_zero, zero_mul, Polynomial.natDegree_zero]
      omega
    · refine Nat.lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
      have := Syl.encodeU_natDegree_lt P.natDegree Q.natDegree uv hq
      omega
  · rcases Nat.eq_zero_or_pos P.natDegree with hp | hp
    · have h_ev_zero : Syl.encodeV P.natDegree Q.natDegree uv = 0 := by
        unfold Syl.encodeV
        apply Finset.sum_eq_zero
        intro ℓ _
        exfalso
        have := ℓ.isLt
        omega
      rw [h_ev_zero, zero_mul, Polynomial.natDegree_zero]
      omega
    · refine Nat.lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
      have := Syl.encodeV_natDegree_lt P.natDegree Q.natDegree uv hp
      omega

/-! ### `uv = 0` iff both encodings vanish -/

omit [Nontrivial D] in
theorem Syl.encode_eq_zero_iff (p q : ℕ) (uv : Fin (p + q) → D) :
    (Syl.encodeU p q uv = 0 ∧ Syl.encodeV p q uv = 0) ↔ uv = 0 := by
  constructor
  · rintro ⟨hU, hV⟩
    funext j
    show uv j = (0 : Fin (p + q) → D) j
    by_cases h : j.val < q
    · have h_uv_eq : uv j = (Syl.encodeU p q uv).coeff (q - 1 - j.val) := by
        rw [Syl.encodeU_coeff p q uv (q - 1 - j.val) (by have := j.isLt; omega)]
        congr 1
        apply Fin.ext
        show j.val = q - 1 - (q - 1 - j.val)
        omega
      rw [h_uv_eq, hU, Polynomial.coeff_zero]
      rfl
    · push Not at h
      have h_uv_eq : uv j = (Syl.encodeV p q uv).coeff (p - 1 - (j.val - q)) := by
        rw [Syl.encodeV_coeff p q uv (p - 1 - (j.val - q))
              (by have := j.isLt; omega)]
        congr 1
        apply Fin.ext
        show j.val = q + (p - 1 - (p - 1 - (j.val - q)))
        have := j.isLt; omega
      rw [h_uv_eq, hV, Polynomial.coeff_zero]
      rfl
  · intro h
    refine ⟨?_, ?_⟩
    · rw [show uv = 0 from h]
      unfold Syl.encodeU; simp
    · rw [show uv = 0 from h]
      unfold Syl.encodeV; simp

/-! ### Lemma 4.15 -/

variable [IsDomain D] [DecidableEq D]

omit [Nontrivial D] in
/-- **BPR Lemma 4.15.** Over a domain `D`, the resultant `Res(P, Q)` of
    non-zero `P, Q : D[X]` (at their actual degrees) vanishes if and
    only if there exist non-zero polynomials `U, V : D[X]` with
    `U.natDegree < Q.natDegree`, `V.natDegree < P.natDegree`, and
    `U · P + V · Q = 0`.

    The proof chains: `Matrix.exists_mulVec_eq_zero_iff` (det = 0 ↔ ∃
    null vector) + Remark 4.14 (`Syl.transpose_mulVec_apply`,
    identifying matrix-vector multiplication with coefficient
    extraction from `Syl.mulMap`) + the structural decomposition
    `Syl.mulMap_eq_pair` (`mulMap = encodeU·P + encodeV·Q`) + domain
    cancellation. -/
theorem Res_eq_zero_iff (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Res P Q = 0 ↔
      ∃ U V : D[X], U ≠ 0 ∧ V ≠ 0 ∧
        U.natDegree < Q.natDegree ∧ V.natDegree < P.natDegree ∧
        U * P + V * Q = 0 := by
  classical
  set p := P.natDegree with hp_def
  set q := Q.natDegree with hq_def
  by_cases hpq_pos : 0 < p + q
  swap
  · push Not at hpq_pos
    have hpq0 : p + q = 0 := Nat.le_zero.mp hpq_pos
    have hq0 : q = 0 := by omega
    constructor
    · intro h_zero
      exfalso
      have h_size_zero : (Syl P Q).det = 1 := by
        rw [show (Syl P Q : Matrix (Fin (p + q)) (Fin (p + q)) D) = 1 from
            Matrix.ext (fun i _ => by have := i.isLt; omega)]
        exact Matrix.det_one
      unfold Res at h_zero
      rw [h_size_zero] at h_zero
      exact one_ne_zero h_zero
    · rintro ⟨U, V, _, _, hUq, _, _⟩
      rw [hq0] at hUq
      exact absurd hUq (Nat.not_lt_zero _)
  rw [show Res P Q = (Syl P Q).transpose.det from by
    unfold Res; rw [Matrix.det_transpose]]
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨uv, h_ne, h_mul⟩
    have h_mulMap_zero : Syl.mulMap P Q uv = 0 := by
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_zero]
      by_cases hk : k < p + q
      · have h_hi : p + q - 1 - k < p + q := by omega
        have h_eq_k : p + q - 1 - (p + q - 1 - k) = k := by omega
        have h := congrFun h_mul ⟨p + q - 1 - k, h_hi⟩
        rw [Syl.transpose_mulVec_apply] at h
        rw [show (⟨p + q - 1 - k, h_hi⟩ : Fin (p + q)).val = p + q - 1 - k from rfl,
            h_eq_k] at h
        exact h
      · have hd : (Syl.mulMap P Q uv).natDegree < p + q :=
          Syl.mulMap_natDegree_lt P Q uv hpq_pos
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Syl.mulMap_eq_pair] at h_mulMap_zero
    set U := Syl.encodeU p q uv with hU_def
    set V := Syl.encodeV p q uv with hV_def
    have h_U_nonzero : U ≠ 0 := by
      intro hU
      rw [hU, zero_mul, zero_add] at h_mulMap_zero
      have hV_zero : V = 0 := (mul_eq_zero.mp h_mulMap_zero).resolve_right hQ
      exact h_ne ((Syl.encode_eq_zero_iff p q uv).mp ⟨hU, hV_zero⟩)
    have h_V_nonzero : V ≠ 0 := by
      intro hV
      rw [hV, zero_mul, add_zero] at h_mulMap_zero
      have hU_zero : U = 0 := (mul_eq_zero.mp h_mulMap_zero).resolve_right hP
      exact h_ne ((Syl.encode_eq_zero_iff p q uv).mp ⟨hU_zero, hV⟩)
    refine ⟨U, V, h_U_nonzero, h_V_nonzero, ?_, ?_, h_mulMap_zero⟩
    · rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · exfalso
        apply h_U_nonzero
        rw [hU_def]
        unfold Syl.encodeU
        apply Finset.sum_eq_zero
        intro k _
        exfalso
        have := k.isLt
        omega
      · exact Syl.encodeU_natDegree_lt p q uv hq0
    · rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · exfalso
        apply h_V_nonzero
        rw [hV_def]
        unfold Syl.encodeV
        apply Finset.sum_eq_zero
        intro ℓ _
        exfalso
        have := ℓ.isLt
        omega
      · exact Syl.encodeV_natDegree_lt p q uv hp0
  · rintro ⟨U, V, hU, hV, hUq, hVp, h_rel⟩
    let uv : Fin (p + q) → D := fun j =>
      if h : j.val < q then U.coeff (q - 1 - j.val)
      else V.coeff (p - 1 - (j.val - q))
    refine ⟨uv, ?_, ?_⟩
    · intro h_uv_zero
      apply hU
      apply Polynomial.ext
      intro m
      rw [Polynomial.coeff_zero]
      by_cases hmq : m < q
      · have h_idx : (⟨q - 1 - m, by omega⟩ : Fin (p + q)).val < q := by
          show q - 1 - m < q; omega
        have h := congrFun h_uv_zero ⟨q - 1 - m, by omega⟩
        show U.coeff m = 0
        have h_uv_val : uv ⟨q - 1 - m, by omega⟩ = U.coeff m := by
          show (if h : _ < q then _ else _) = _
          rw [dite_eq_left h_idx]
          congr 1
          show q - 1 - (q - 1 - m) = m; omega
        rw [← h_uv_val, h]
        rfl
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · funext i
      rw [Syl.transpose_mulVec_apply]
      have h_eU : Syl.encodeU p q uv = U := by
        apply Polynomial.ext
        intro m
        by_cases hmq : m < q
        · rw [Syl.encodeU_coeff p q uv m hmq]
          have h_idx : (⟨q - 1 - m, by omega⟩ : Fin (p + q)).val < q := by
            show q - 1 - m < q; omega
          show (if h : _ < q then _ else _) = U.coeff m
          rw [dite_eq_left h_idx]
          congr 1
          show q - 1 - (q - 1 - m) = m; omega
        · rw [Syl.encodeU_coeff_of_ge p q uv m (by omega)]
          rw [show U.coeff m = 0 from
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      have h_eV : Syl.encodeV p q uv = V := by
        apply Polynomial.ext
        intro m
        by_cases hmp : m < p
        · rw [Syl.encodeV_coeff p q uv m hmp]
          have h_idx : ¬ (⟨q + (p - 1 - m), by omega⟩ : Fin (p + q)).val < q := by
            show ¬ q + (p - 1 - m) < q; omega
          show (if h : _ < q then _ else _) = V.coeff m
          rw [dite_eq_right h_idx]
          congr 1
          show p - 1 - ((q + (p - 1 - m)) - q) = m; omega
        · rw [Syl.encodeV_coeff_of_ge p q uv m (by omega)]
          rw [show V.coeff m = 0 from
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      rw [Syl.mulMap_eq_pair, h_eU, h_eV, h_rel, Polynomial.coeff_zero]
      rfl

end Azurite.BPR.Chapter4
