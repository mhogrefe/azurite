import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_27
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# BPR Proposition 2.28 & Definition 2.29: Thom Encoding

**Proposition 2.28 (BPR).** Let `P ∈ R[X]` be non-zero of degree `p`, and let
`x, x' ∈ R` with sign conditions `σ, σ'` on `Der(P)`.

1. If `σ = σ'` (on `{0, …, p}`) and `σ(P) = 0`, then `x = x'`.
2. If `σ ≠ σ'`, one can determine whether `x < x'` or `x > x'` from the sign
   conditions and the index of their first disagreement (scanning from the
   highest derivative down).

**Definition 2.29 (BPR).** A sign condition `σ` on `Der(P)` is a *Thom encoding*
of `x ∈ R` if `σ(P) = 0` and `Reali(σ) = {x}`.
-/

namespace Azurite.BPR.Proposition2_28

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_21 Azurite.BPR.Proposition2_22 Azurite.BPR.Corollary2_23 Azurite.BPR.Corollary2_24 Azurite.BPR.Proposition2_27

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Helper: open intervals are infinite -/

private lemma isOpenInterval_infinite (S : Set R) (hS : IsOpenInterval S) :
    S.Infinite := by
  obtain ⟨⟨x, hxS⟩, hconn, hlt, _⟩ := hS
  obtain ⟨y, hyS, hyx⟩ := hlt x hxS
  exact (Set.Icc_infinite hyx).mono (hconn.out hyS hxS)

/-! ### Part 1: Root injectivity -/

/-- **BPR Proposition 2.28, Part 1 (Root injectivity).** If `x` and `x'` both
    realize the same sign condition `σ` on `Der(P)` and `σ(P) = 0`,
    then `x = x'`. -/
theorem proposition_2_28_part1 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) (n : ℕ) (σ : ℕ → SignType) (hn : P.natDegree ≤ n)
    (hσ0 : σ 0 = 0) (x x' : R)
    (hx : x ∈ derReali P n σ) (hx' : x' ∈ derReali P n σ) : x = x' := by
  rcases proposition_2_27 hIVP P n σ hn with hempty | ⟨a, hsing⟩ | hopen
  · simp [hempty] at hx
  · simp only [hsing, Set.mem_singleton_iff] at hx hx'; exact hx.trans hx'.symm
  · exfalso
    have hroots : derReali P n σ ⊆ {y | P.IsRoot y} := by
      intro y hy
      have h := hy 0 (Nat.zero_le n)
      rw [Function.iterate_zero_apply, hσ0] at h
      exact sign_eq_zero_iff.mp h
    exact isOpenInterval_infinite _ hopen ((finite_setOfPred_isRoot hP).subset hroots)

/-! ### Helper: sign ordering reflects value ordering -/

private lemma lt_of_sign_lt {a b : R}
    (h : SignType.sign a < SignType.sign b) : a < b := by
  simp only [sign_apply] at h
  split_ifs at h with h1 h2 h3 h4 <;> simp_all <;> linarith

/-! ### Helper: polynomial constant when derivative is zero -/

private lemma eval_eq_of_derivative_eq_zero (hIVP : HasIntermediateValueProperty R)
    {Q : R[X]} (hder : derivative Q = 0) (y y' : R) :
    Q.eval y = Q.eval y' := by
  rcases lt_trichotomy y y' with h | rfl | h
  · obtain ⟨c, _, hMVT⟩ := corollary_2_23 hIVP Q h
    rw [hder, eval_zero, mul_zero] at hMVT; linarith
  · rfl
  · obtain ⟨c, _, hMVT⟩ := corollary_2_23 hIVP Q h
    rw [hder, eval_zero, mul_zero] at hMVT; linarith

/-! ### Helper: derivative iteration -/

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma derivative_iterate_eq (P : R[X]) (j : ℕ) :
    derivative ((⇑derivative)^[j] P) = (⇑derivative)^[j + 1] P :=
  (Function.iterate_succ_apply' (⇑derivative) j P).symm

/-! ### Part 2: Comparison criterion -/

/-- **BPR Proposition 2.28, Part 2 (Thom encoding comparison).** Let `j` be the
    largest index where the sign conditions `σ` and `σ'` differ. Then
    `σ(j+1) = σ'(j+1) ≠ 0`, and the comparison of `x` vs `x'` is determined
    by `σ(j+1)` and the ordering of `σ(j)` vs `σ'(j)`. -/
theorem proposition_2_28_part2 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (_hP : P ≠ 0) (n : ℕ) (σ σ' : ℕ → SignType) (hn : P.natDegree ≤ n)
    (x x' : R)
    (hx : x ∈ derReali P n σ) (hx' : x' ∈ derReali P n σ')
    (j : ℕ) (hj_le : j ≤ n)
    (hj_diff : σ j ≠ σ' j)
    (hj_agree : ∀ i, j < i → i ≤ n → σ i = σ' i) :
    j < n ∧
    σ (j + 1) = σ' (j + 1) ∧
    σ (j + 1) ≠ 0 ∧
    (σ (j + 1) = 1 → (x' < x ↔ σ' j < σ j)) ∧
    (σ (j + 1) = -1 → (x' < x ↔ σ j < σ' j)) := by
  -- Step 1: j < n
  have hjn : j < n := by
    rcases lt_or_eq_of_le hj_le with h | heq
    · exact h
    · exfalso; subst heq
      have hndeg : ((⇑derivative)^[j] P).natDegree ≤ 0 := by
        have := natDegree_iterate_derivative P j; omega
      have hconst := eq_C_of_natDegree_le_zero hndeg
      have h1 := hx j (le_refl j)
      have h2 := hx' j (le_refl j)
      rw [hconst] at h1 h2; simp only [eval_C] at h1 h2
      exact hj_diff (h1.symm.trans h2)
  -- Common setup
  set Q := (⇑derivative)^[j + 1] P with hQ_def
  set τ : ℕ → SignType := fun i => σ (i + (j + 1)) with hτ_def
  set m := n - (j + 1) with hm_def
  have hQdeg : Q.natDegree ≤ m := by
    simp only [hQ_def, hm_def]
    have := natDegree_iterate_derivative P (j + 1); omega
  -- Membership in derReali Q m τ
  have hx_mem : x ∈ derReali Q m τ := by
    intro i hi
    simp only [hQ_def, hτ_def, ← Function.iterate_add_apply]
    exact hx (i + (j + 1)) (by omega)
  have hx'_mem : x' ∈ derReali Q m τ := by
    intro i hi
    simp only [hQ_def, hτ_def, ← Function.iterate_add_apply]
    rw [show σ (i + (j + 1)) = σ' (i + (j + 1)) from hj_agree _ (by omega) (by omega)]
    exact hx' (i + (j + 1)) (by omega)
  -- Helper: x ≠ x'
  have hxne : x ≠ x' := by
    intro heq; subst heq
    exact hj_diff ((hx j (by omega)).symm.trans (hx' j (by omega)))
  -- Helper: sign of derivative^[j] P
  have hσj : SignType.sign (((⇑derivative)^[j] P).eval x) = σ j := hx j (by omega)
  have hσ'j : SignType.sign (((⇑derivative)^[j] P).eval x') = σ' j := hx' j (by omega)
  refine ⟨hjn, ?_, ?_, ?_, ?_⟩
  -- Step 2: σ(j+1) = σ'(j+1)
  · exact hj_agree (j + 1) (by omega) (by omega)
  -- Step 3: σ(j+1) ≠ 0
  · intro hσ_zero
    by_cases hQ0 : Q = 0
    · -- Q = 0 → derivative^[j] P is constant
      have hder : derivative ((⇑derivative)^[j] P) = 0 := by
        rw [derivative_iterate_eq]; exact hQ0
      have hconst := eval_eq_of_derivative_eq_zero hIVP hder x x'
      rw [hconst] at hσj
      exact hj_diff (hσj.symm.trans hσ'j)
    · -- Q ≠ 0 → by Part 1, x = x'
      have hτ0 : τ 0 = 0 := by simp [hτ_def, hσ_zero]
      have := proposition_2_28_part1 hIVP Q hQ0 m τ hQdeg hτ0 x x' hx_mem hx'_mem
      exact hxne this
  -- Step 4: Comparison when σ(j+1) = 1
  · intro hσ_pos
    rcases proposition_2_27 hIVP Q m τ hQdeg with hempty | ⟨a, hsing⟩ | hopen
    · simp [hempty] at hx_mem
    · simp only [hsing, Set.mem_singleton_iff] at hx_mem hx'_mem
      exact absurd (hx_mem.trans hx'_mem.symm) hxne
    · -- P^(j+1) > 0 on S, so P^(j) is strictly increasing
      have hP'_pos : ∀ z ∈ derReali Q m τ,
          0 < (derivative ((⇑derivative)^[j] P)).eval z := by
        intro z hz
        rw [derivative_iterate_eq]
        have h := hz 0 (Nat.zero_le _)
        simp only [hτ_def, Nat.zero_add, Function.iterate_zero_apply] at h
        rw [hσ_pos] at h
        exact sign_eq_one_iff.mp h
      have hmono := strictMonoOn_of_deriv_pos hIVP hopen hP'_pos
      constructor
      · intro hlt
        have hval := hmono hx'_mem hx_mem hlt
        have hle : σ' j ≤ σ j := by
          rw [← hσ'j, ← hσj]; exact SignType.sign.monotone hval.le
        exact lt_of_le_of_ne hle hj_diff.symm
      · intro hslt
        have hsign_lt : SignType.sign (((⇑derivative)^[j] P).eval x') <
            SignType.sign (((⇑derivative)^[j] P).eval x) := by rw [hσ'j, hσj]; exact hslt
        have hval_lt := lt_of_sign_lt hsign_lt
        rcases lt_trichotomy x' x with h | heq | h
        · exact h
        · exact absurd heq hxne.symm
        · exact absurd (hmono hx_mem hx'_mem h) (not_lt.mpr hval_lt.le)
  -- Step 5: Comparison when σ(j+1) = -1
  · intro hσ_neg
    rcases proposition_2_27 hIVP Q m τ hQdeg with hempty | ⟨a, hsing⟩ | hopen
    · simp [hempty] at hx_mem
    · simp only [hsing, Set.mem_singleton_iff] at hx_mem hx'_mem
      exact absurd (hx_mem.trans hx'_mem.symm) hxne
    · -- P^(j+1) < 0 on S, so P^(j) is strictly decreasing
      have hP'_neg : ∀ z ∈ derReali Q m τ,
          (derivative ((⇑derivative)^[j] P)).eval z < 0 := by
        intro z hz
        rw [derivative_iterate_eq]
        have h := hz 0 (Nat.zero_le _)
        simp only [hτ_def, Nat.zero_add, Function.iterate_zero_apply] at h
        rw [hσ_neg] at h
        exact sign_eq_neg_one_iff.mp h
      have hanti := strictAntiOn_of_deriv_neg hIVP hopen hP'_neg
      constructor
      · intro hlt
        have hval := hanti hx'_mem hx_mem hlt
        have hle : σ j ≤ σ' j := by
          rw [← hσj, ← hσ'j]; exact SignType.sign.monotone hval.le
        exact lt_of_le_of_ne hle hj_diff
      · intro hslt
        have hsign_lt : SignType.sign (((⇑derivative)^[j] P).eval x) <
            SignType.sign (((⇑derivative)^[j] P).eval x') := by rw [hσj, hσ'j]; exact hslt
        have hval_lt := lt_of_sign_lt hsign_lt
        rcases lt_trichotomy x' x with h | heq | h
        · exact h
        · exact absurd heq hxne.symm
        · exact absurd (hanti hx_mem hx'_mem h) (not_lt.mpr hval_lt.le)

/-! Note: BPR Definition 2.29 (`IsThomEncoding`, `isThomEncoding_of_mem`) is
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_29`. -/

/-! ### Real closed corollaries -/

theorem proposition_2_28_part1_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (hP : P ≠ 0) (n : ℕ) (σ : ℕ → SignType) (hn : P.natDegree ≤ n)
    (hσ0 : σ 0 = 0) (x x' : R)
    (hx : letI : LinearOrder R := IsRealClosed.toLinearOrder; x ∈ derReali P n σ)
    (hx' : letI : LinearOrder R := IsRealClosed.toLinearOrder; x' ∈ derReali P n σ) :
    x = x' := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  exact proposition_2_28_part1 Theorem2_11.theorem_2_11_b_c P hP n σ hn hσ0 x x' hx hx'

theorem proposition_2_28_part2_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (hP : P ≠ 0) (n : ℕ) (σ σ' : ℕ → SignType) (hn : P.natDegree ≤ n)
    (x x' : R)
    (hx : letI : LinearOrder R := IsRealClosed.toLinearOrder; x ∈ derReali P n σ)
    (hx' : letI : LinearOrder R := IsRealClosed.toLinearOrder; x' ∈ derReali P n σ')
    (j : ℕ) (hj_le : j ≤ n)
    (hj_diff : σ j ≠ σ' j)
    (hj_agree : ∀ i, j < i → i ≤ n → σ i = σ' i) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    j < n ∧
    σ (j + 1) = σ' (j + 1) ∧
    σ (j + 1) ≠ 0 ∧
    (σ (j + 1) = 1 → (x' < x ↔ σ' j < σ j)) ∧
    (σ (j + 1) = -1 → (x' < x ↔ σ j < σ' j)) := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  exact proposition_2_28_part2 Theorem2_11.theorem_2_11_b_c P hP n σ σ' hn x x' hx hx'
    j hj_le hj_diff hj_agree

/-! Note: BPR Example 2.30 (`example_2_30`, the roots of `X² − 2` are
distinguished by the sign of the derivative — the canonical Thom-encoding
example) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Example_2_30`. -/

end Azurite.BPR.Proposition2_28
