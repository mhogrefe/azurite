import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_41
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_43

/-!
# BPR Proposition 2.44: Sign variations of `A · (X − x)` for normal `A`, `x > 0`

**Proposition 2.44 (BPR).** If `A` is a normal polynomial and `x > 0`, then
`Var(A · (X − x)) = 1`.

**Proof strategy.**

Let `p = natDegree A` and write `b_k = (A · (X − x)).coeff k`. Using
`Polynomial.coeff_mul_X_sub_C`:
- `b_0 = −x · a_0 ≤ 0` (always, since `a_0 ≥ 0` and `x > 0`);
- `b_k = a_{k−1} − x · a_k` for `1 ≤ k ≤ p + 1` (with the convention
  `a_{−1} = 0` and `a_{p+1} = 0`);
- `b_{p+1} = a_p > 0`.

The key *monotonicity* claim is that for `1 ≤ k ≤ p`, `b_k ≤ 0 → b_{k−1} ≤ 0`.
This walks down through the coefficient sequence and follows from log-concavity
in the "both adjacent positive" case and from the `no_gap` condition in the
"adjacent zero" case.

Combining with the strict bookends (some strictly negative `b_{k*}` always
exists, and `b_{p+1} > 0`), the coefficient list splits as a (nonempty) prefix
of values `≤ 0` followed by a (nonempty) suffix of values `> 0`, which has
exactly one sign variation.
-/

namespace Azurite.BPR.Proposition2_44

open Polynomial Azurite.BPR

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Helper: `varNonzero (neg ++ pos) = 1` for strictly-signed nonempty lists -/

/-- For a nonempty list `neg` of strictly negative values and a nonempty list
    `pos` of strictly positive values, `varNonzero (neg ++ pos) = 1`. -/
private lemma varNonzero_append_neg_pos :
    ∀ {neg pos : List R}, neg ≠ [] → pos ≠ [] →
      (∀ x ∈ neg, x < 0) → (∀ x ∈ pos, 0 < x) →
      varNonzero (neg ++ pos) = 1
  | [], _, hne, _, _, _ => absurd rfl hne
  | [_], [], _, hpe, _, _ => absurd rfl hpe
  | [a], b :: prest, _, _, hneg, hpos => by
      have ha : a < 0 := hneg a List.mem_cons_self
      have hb : 0 < b := hpos b List.mem_cons_self
      rw [List.singleton_append, varNonzero_cons_cons]
      have hab : a * b < 0 := mul_neg_of_neg_of_pos ha hb
      rw [if_pos hab]
      have htail : varNonzero (b :: prest) = 0 :=
        varNonzero_eq_zero_of_forall_nonneg
          (fun x hx => (hpos x hx).le)
      rw [htail]
  | a :: c :: nrest, pos, _, hpos_ne, hneg, hpos => by
      simp only [List.cons_append, varNonzero_cons_cons]
      have ha : a < 0 := hneg a List.mem_cons_self
      have hc : c < 0 :=
        hneg c (List.mem_cons_of_mem _ List.mem_cons_self)
      have hac : ¬ a * c < 0 :=
        not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos ha.le hc.le)
      rw [if_neg hac, zero_add]
      exact varNonzero_append_neg_pos (neg := c :: nrest) (pos := pos)
        (by simp) hpos_ne
        (fun x hx => hneg x (List.mem_cons_of_mem _ hx))
        hpos

/-- If a list `l` splits at index `k` so that the first segment consists of
    non-positive values (with at least one strictly negative) and the second
    of non-negative values (with at least one strictly positive), then
    `Var l = 1`. -/
private lemma Var_eq_one_of_take_drop_split (l : List R) (k : ℕ)
    (h_take : ∀ x ∈ l.take k, x ≤ 0)
    (h_drop : ∀ x ∈ l.drop k, 0 ≤ x)
    (h_take_neg : ∃ x ∈ l.take k, x < 0)
    (h_drop_pos : ∃ x ∈ l.drop k, 0 < x) :
    Var l = 1 := by
  have hfilter : l.filter (· ≠ 0) =
      (l.take k).filter (· ≠ 0) ++ (l.drop k).filter (· ≠ 0) := by
    conv_lhs => rw [← List.take_append_drop k l]
    rw [List.filter_append]
  unfold Var
  rw [hfilter]
  set nl := (l.take k).filter (· ≠ 0) with hnl_def
  set pl := (l.drop k).filter (· ≠ 0) with hpl_def
  have hnl_ne : nl ≠ [] := by
    intro hempty
    obtain ⟨y, hymem, hyneg⟩ := h_take_neg
    have : y ∈ nl := by
      rw [hnl_def, List.mem_filter]
      exact ⟨hymem, by simpa using hyneg.ne⟩
    rw [hempty] at this
    exact (List.not_mem_nil this)
  have hpl_ne : pl ≠ [] := by
    intro hempty
    obtain ⟨y, hymem, hypos⟩ := h_drop_pos
    have : y ∈ pl := by
      rw [hpl_def, List.mem_filter]
      exact ⟨hymem, by simpa using hypos.ne'⟩
    rw [hempty] at this
    exact (List.not_mem_nil this)
  have hnl_neg : ∀ y ∈ nl, y < 0 := by
    intro y hy
    rw [hnl_def, List.mem_filter] at hy
    obtain ⟨hyl, hynz⟩ := hy
    have hnz : y ≠ 0 := by simpa using hynz
    exact lt_of_le_of_ne (h_take y hyl) hnz
  have hpl_pos : ∀ y ∈ pl, 0 < y := by
    intro y hy
    rw [hpl_def, List.mem_filter] at hy
    obtain ⟨hyl, hynz⟩ := hy
    have hnz : y ≠ 0 := by simpa using hynz
    exact lt_of_le_of_ne (h_drop y hyl) (Ne.symm hnz)
  exact varNonzero_append_neg_pos hnl_ne hpl_ne hnl_neg hpl_pos

/-! ### Coefficient analysis of `A · (X − C x)` -/

section MulXSubC

variable {A : R[X]} {x : R}

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `(A · (X − C x)).coeff 0 = −x · A.coeff 0`. -/
private lemma coeff_zero_eq : (A * (X - C x)).coeff 0 = -x * A.coeff 0 := by
  simp [Polynomial.mul_coeff_zero, Polynomial.coeff_X, Polynomial.coeff_C, mul_comm]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `(A · (X − C x)).coeff (k + 1) = A.coeff k − x · A.coeff (k + 1)`. -/
private lemma coeff_succ_eq (k : ℕ) :
    (A * (X - C x)).coeff (k + 1) = A.coeff k - x * A.coeff (k + 1) := by
  rw [Polynomial.coeff_mul_X_sub_C]; ring

end MulXSubC

section MulXSubCNormal

variable {A : R[X]} (hA : IsNormal A) {x : R} (hx : 0 < x)

omit [IsStrictOrderedRing R] in
include hA in
private lemma A_ne_zero : A ≠ 0 := by
  intro h
  have := hA.leading_pos
  simp [h] at this

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `(A · (X − C x)).coeff (natDegree A + 1) = A.leadingCoeff`. -/
private lemma coeff_top_eq :
    (A * (X - C x)).coeff (A.natDegree + 1) = A.coeff A.natDegree := by
  rw [coeff_succ_eq]
  have h1 : A.coeff (A.natDegree + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h1, mul_zero, sub_zero]

omit [IsStrictOrderedRing R] in
include hA in
/-- `(A · (X − C x)).coeff (natDegree A + 1) > 0`. -/
private lemma coeff_top_pos : 0 < (A * (X - C x)).coeff (A.natDegree + 1) := by
  rw [coeff_top_eq]
  exact hA.leading_pos

include hA hx in
/-- `(A · (X − C x)).coeff 0 ≤ 0`. -/
private lemma coeff_zero_nonpos : (A * (X - C x)).coeff 0 ≤ 0 := by
  rw [coeff_zero_eq]
  have hxn : -x ≤ 0 := neg_nonpos_of_nonneg hx.le
  exact mul_nonpos_of_nonpos_of_nonneg hxn (hA.coeff_nonneg 0)

include hA in
/-- **Monotonicity.** For `0 ≤ m` with `m + 1 ≤ natDegree A`, if
    `(A · (X − C x)).coeff (m + 2) ≤ 0` then
    `(A · (X − C x)).coeff (m + 1) ≤ 0`. -/
private lemma coeff_nonpos_step (m : ℕ) (hm : m + 1 ≤ A.natDegree)
    (hk : (A * (X - C x)).coeff (m + 2) ≤ 0) :
    (A * (X - C x)).coeff (m + 1) ≤ 0 := by
  rw [show m + 2 = (m + 1) + 1 from rfl, coeff_succ_eq] at hk
  rw [coeff_succ_eq]
  have h_m1 : A.coeff (m + 1) ≤ x * A.coeff (m + 2) := by linarith
  have hA_m_nn : 0 ≤ A.coeff m := hA.coeff_nonneg _
  have hA_m1_nn : 0 ≤ A.coeff (m + 1) := hA.coeff_nonneg _
  have hA_m2_nn : 0 ≤ A.coeff (m + 2) := hA.coeff_nonneg _
  by_cases h_m2 : A.coeff (m + 2) = 0
  · -- Case A.coeff (m+2) = 0. Then A.coeff (m+1) = 0 from h_m1.
    have h_m1z : A.coeff (m + 1) = 0 := by
      rw [h_m2, mul_zero] at h_m1
      exact le_antisymm h_m1 hA_m1_nn
    by_cases h_m_zero : A.coeff m = 0
    · rw [h_m_zero, h_m1z, mul_zero, sub_zero]
    · -- A.coeff m > 0, derive contradiction using structure of A.
      exfalso
      have h_m_pos : 0 < A.coeff m :=
        lt_of_le_of_ne hA_m_nn (Ne.symm h_m_zero)
      rcases Nat.lt_or_ge (m + 2) (A.natDegree + 1) with hlt | hge
      · -- m + 2 ≤ natDegree: use isNormal_pos_between
        have h_le : m + 2 ≤ A.natDegree := by omega
        have h_pos_m2 : 0 < A.coeff (m + 2) :=
          isNormal_pos_between hA (by omega : m ≤ m + 2) h_le h_m_pos hA.leading_pos
        rw [h_m2] at h_pos_m2
        exact lt_irrefl _ h_pos_m2
      · -- m + 2 ≥ natDegree + 1, i.e., m + 1 = natDegree. Then A.coeff (m+1) = leading > 0.
        have heq : m + 1 = A.natDegree := by omega
        have h_pos_m1 : 0 < A.coeff (m + 1) := heq ▸ hA.leading_pos
        rw [h_m1z] at h_pos_m1
        exact lt_irrefl _ h_pos_m1
  · -- A.coeff (m+2) > 0.
    have h_m2_pos : 0 < A.coeff (m + 2) :=
      lt_of_le_of_ne hA_m2_nn (Ne.symm h_m2)
    by_cases h_m1_zero : A.coeff (m + 1) = 0
    · -- A.coeff (m+1) = 0, A.coeff (m+2) > 0. Log-concavity → A.coeff m = 0.
      have hlc := hA.log_concave m
      rw [h_m1_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hlc
      have h_m_zero : A.coeff m = 0 := by
        have h_prod_nn : 0 ≤ A.coeff m * A.coeff (m + 2) :=
          mul_nonneg hA_m_nn hA_m2_nn
        have h_prod_eq : A.coeff m * A.coeff (m + 2) = 0 :=
          le_antisymm hlc h_prod_nn
        exact (mul_eq_zero.mp h_prod_eq).resolve_right h_m2
      rw [h_m_zero, h_m1_zero, mul_zero, sub_zero]
    · -- A.coeff (m+1) > 0, A.coeff (m+2) > 0. Log-concavity chain.
      have h_m1_pos : 0 < A.coeff (m + 1) :=
        lt_of_le_of_ne hA_m1_nn (Ne.symm h_m1_zero)
      have hlc := hA.log_concave m
      -- hlc : A.coeff m * A.coeff (m+2) ≤ A.coeff (m+1)^2
      have key : A.coeff m * A.coeff (m + 2) ≤ x * A.coeff (m + 1) * A.coeff (m + 2) := by
        calc A.coeff m * A.coeff (m + 2)
            ≤ A.coeff (m + 1) ^ 2 := hlc
          _ = A.coeff (m + 1) * A.coeff (m + 1) := by ring
          _ ≤ A.coeff (m + 1) * (x * A.coeff (m + 2)) :=
              mul_le_mul_of_nonneg_left h_m1 hA_m1_nn
          _ = x * A.coeff (m + 1) * A.coeff (m + 2) := by ring
      have h_ineq : A.coeff m ≤ x * A.coeff (m + 1) :=
        le_of_mul_le_mul_right key h_m2_pos
      linarith

end MulXSubCNormal

/-! ### Descent and existence of split -/

section Main

variable {A : R[X]} (hA : IsNormal A) {x : R} (hx : 0 < x)

include hA in
private lemma natDegree_mul_X_sub_C_eq :
    (A * (X - C x)).natDegree = A.natDegree + 1 := by
  rw [Polynomial.natDegree_mul (A_ne_zero hA) (X_sub_C_ne_zero x),
      Polynomial.natDegree_X_sub_C]

include hA hx in
/-- The descent lemma: if `coeff k ≤ 0` for some `k ≤ p`, then `coeff j ≤ 0`
    for all `j ≤ k`. -/
private lemma coeff_nonpos_of_le : ∀ (k : ℕ), k ≤ A.natDegree →
    (A * (X - C x)).coeff k ≤ 0 →
    ∀ j ≤ k, (A * (X - C x)).coeff j ≤ 0 := by
  intro k
  induction k with
  | zero =>
    intro _ h j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    rw [hj0]
    exact h
  | succ k ih =>
    intro hk h j hj
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · have hk_prev : k ≤ A.natDegree := by omega
      have h_prev : (A * (X - C x)).coeff k ≤ 0 := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          exact coeff_zero_nonpos hA hx
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          exact coeff_nonpos_step hA m (by omega) h
      exact ih hk_prev h_prev j (by omega)
    · have : j = k + 1 := by omega
      subst this
      exact h

include hA hx in
/-- There is a strictly negative coefficient of `A · (X − C x)` at some index
    in `[0, natDegree A]`. -/
private lemma exists_coeff_neg :
    ∃ m ≤ A.natDegree, (A * (X - C x)).coeff m < 0 := by
  classical
  -- Let m = smallest k with A.coeff k > 0.
  have hS_nonempty : ∃ k, 0 < A.coeff k := ⟨A.natDegree, hA.leading_pos⟩
  set m := Nat.find hS_nonempty with hm_def
  have hm_mem : 0 < A.coeff m := Nat.find_spec hS_nonempty
  have hm_min : ∀ k < m, ¬ (0 < A.coeff k) := fun k hk =>
    Nat.find_min hS_nonempty hk
  have hm_le : m ≤ A.natDegree := Nat.find_min' hS_nonempty hA.leading_pos
  refine ⟨m, hm_le, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- m = 0: A.coeff 0 > 0. coeff 0 = -x * A.coeff 0 < 0.
    rw [hm0, coeff_zero_eq]
    have h0_pos : 0 < A.coeff 0 := hm0 ▸ hm_mem
    have : 0 < x * A.coeff 0 := mul_pos hx h0_pos
    linarith
  · -- m ≥ 1: introduce m' = m - 1. A.coeff (m'+1) > 0 and A.coeff m' = 0.
    set m' := m - 1 with hm'_def
    have heq : m = m' + 1 := by omega
    rw [heq]
    have h_pos : 0 < A.coeff (m' + 1) := heq ▸ hm_mem
    have h_m'_zero : A.coeff m' = 0 := by
      have h_lt : m' < m := by omega
      have h_nlt : ¬ 0 < A.coeff m' := hm_min m' h_lt
      exact le_antisymm (not_lt.mp h_nlt) (hA.coeff_nonneg _)
    rw [coeff_succ_eq, h_m'_zero, zero_sub]
    have : 0 < x * A.coeff (m' + 1) := mul_pos hx h_pos
    linarith

include hA hx in
/-- Existence of a split index `K ≤ natDegree A`: all `j ≤ K` have
    `coeff j ≤ 0`, all `K < j ≤ natDegree A + 1` have `coeff j > 0`, and
    some `m ≤ K` has `coeff m < 0`. -/
private lemma exists_split :
    ∃ K, K ≤ A.natDegree ∧
      (∀ j ≤ K, (A * (X - C x)).coeff j ≤ 0) ∧
      (∀ j, K < j → j ≤ A.natDegree + 1 → 0 < (A * (X - C x)).coeff j) ∧
      ∃ m ≤ K, (A * (X - C x)).coeff m < 0 := by
  classical
  -- Define P k: "for all j in (k, natDegree+1], coeff j > 0".
  -- Let K = smallest such k. Then K satisfies P K and (K = 0 or K-1 doesn't).
  set P : ℕ → Prop := fun k => ∀ j, k < j → j ≤ A.natDegree + 1 →
    0 < (A * (X - C x)).coeff j with hP_def
  have hPexist : ∃ k, P k := by
    refine ⟨A.natDegree + 1, ?_⟩
    intro j hj1 hj2
    omega
  set K := Nat.find hPexist with hK_def
  have hKP : P K := Nat.find_spec hPexist
  have hK_min : ∀ k, k < K → ¬ P k := fun k hk => Nat.find_min hPexist hk
  -- K ≤ natDegree A.
  have hKle_p1 : K ≤ A.natDegree + 1 :=
    Nat.find_min' hPexist (by intro j hj1 hj2; omega)
  have hPp : P A.natDegree := by
    intro j hj1 hj2
    have : j = A.natDegree + 1 := by omega
    rw [this]
    exact coeff_top_pos hA
  have hK_le : K ≤ A.natDegree := by
    by_contra h
    push Not at h
    have hKeq : K = A.natDegree + 1 := by omega
    have : A.natDegree < K := by omega
    exact hK_min _ this hPp
  -- coeff K ≤ 0.
  have hK_nonpos : (A * (X - C x)).coeff K ≤ 0 := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · rw [hK0]; exact coeff_zero_nonpos hA hx
    · have hKm1 : ¬ P (K - 1) := hK_min (K - 1) (by omega)
      simp only [hP_def, not_forall, not_lt] at hKm1
      obtain ⟨j, hj1, hj2, hj3⟩ := hKm1
      -- K - 1 < j ≤ natDegree + 1, coeff j ≤ 0.
      have hjK : j ≤ K := by
        by_contra h
        push Not at h
        exact absurd (hKP j h hj2) (not_lt.mpr hj3)
      have : j = K := by omega
      rw [← this]
      exact hj3
  -- All j ≤ K have coeff j ≤ 0.
  have h_take : ∀ j ≤ K, (A * (X - C x)).coeff j ≤ 0 :=
    coeff_nonpos_of_le hA hx K hK_le hK_nonpos
  -- Strict negative witness.
  obtain ⟨m, hm_le, hm_neg⟩ := exists_coeff_neg hA hx
  have hm_K : m ≤ K := by
    by_contra h
    push Not at h
    exact absurd (hKP m h (by omega)) (not_lt.mpr hm_neg.le)
  exact ⟨K, hK_le, h_take, hKP, m, hm_K, hm_neg⟩

end Main

/-! ### Main theorem -/

/-- **BPR Proposition 2.44.** If `A` is a normal polynomial and `x > 0`, then
    `Var(A · (X − C x)) = 1`. -/
theorem varPoly_mul_X_sub_C_of_isNormal
    {A : R[X]} (hA : IsNormal A) {x : R} (hx : 0 < x) :
    varPoly (A * (X - C x)) = 1 := by
  classical
  unfold varPoly
  rw [natDegree_mul_X_sub_C_eq hA]
  obtain ⟨K, hK_le, h_take, h_drop, m, hm_K, hm_neg⟩ := exists_split hA hx
  set l := (List.range (A.natDegree + 1 + 1)).map (A * (X - C x)).coeff with hl_def
  have hK1_bound : K + 1 ≤ A.natDegree + 1 + 1 := by omega
  -- Characterize `l.take (K + 1)`:  elements are `(A * (X - C x)).coeff i` for `i < K + 1`.
  have h_take_range : (List.range (A.natDegree + 1 + 1)).take (K + 1) = List.range (K + 1) := by
    apply List.ext_getElem
    · simp; omega
    · intros; simp
  apply Var_eq_one_of_take_drop_split l (K + 1)
  · -- All values in l.take (K + 1) are ≤ 0.
    intro y hy
    rw [hl_def, ← List.map_take, h_take_range, List.mem_map] at hy
    obtain ⟨i, hi_mem, rfl⟩ := hy
    rw [List.mem_range] at hi_mem
    exact h_take i (by omega)
  · -- All values in l.drop (K + 1) are ≥ 0.
    intro y hy
    rw [hl_def, ← List.map_drop, List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [List.mem_iff_getElem] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    rw [List.length_drop, List.length_range] at hi
    rw [List.getElem_drop, List.getElem_range]
    exact (h_drop (K + 1 + i) (by omega) (by omega)).le
  · -- Strictly negative witness.
    refine ⟨(A * (X - C x)).coeff m, ?_, hm_neg⟩
    rw [hl_def, ← List.map_take, h_take_range, List.mem_map]
    exact ⟨m, by rw [List.mem_range]; omega, rfl⟩
  · -- Strictly positive witness: coeff (natDegree + 1).
    refine ⟨(A * (X - C x)).coeff (A.natDegree + 1), ?_, coeff_top_pos hA⟩
    rw [hl_def, ← List.map_drop, List.mem_map]
    refine ⟨A.natDegree + 1, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨A.natDegree - K, ?_, ?_⟩
    · rw [List.length_drop, List.length_range]; omega
    · rw [List.getElem_drop, List.getElem_range]
      show (K + 1 + (A.natDegree - K) : ℕ) = A.natDegree + 1
      omega

end Azurite.BPR.Proposition2_44
