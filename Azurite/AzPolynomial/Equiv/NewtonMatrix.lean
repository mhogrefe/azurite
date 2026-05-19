import Azurite.AzPolynomial.NewtonMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Correctness of `newtonSumsMonicIter` and `newtMatMonic`

The iterative `newtonSumsMonicIter P n` produces the same array as the
spec function `newtonSumsMonic P n`, namely `[N_0, …, N_{n-1}]` where
`N_i = newtonSumMonic P i`. As a consequence, the computable Hankel
matrix `newtMatMonic P k` has entry `(i, j) = newtonSumMonic P (i + j)`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R]

/-- `newtonSumStep P prev` matches `newtonSumMonic P prev.size` provided
    `prev` agrees with `newtonSumMonic` on every index it stores. -/
theorem newtonSumStep_eq (P : AzPolynomial R) (prev : Array R)
    (h_prev : ∀ i, i < prev.size → prev.getD i 0 = P.newtonSumMonic i) :
    newtonSumStep P prev = P.newtonSumMonic prev.size := by
  cases h_size : prev.size with
  | zero =>
    show newtonSumStep P prev = _
    unfold newtonSumStep
    rw [h_size]
    simp [newtonSumMonic]
  | succ n =>
    show newtonSumStep P prev = _
    unfold newtonSumStep
    rw [h_size]
    simp only [Nat.succ_ne_zero, if_neg, not_false_eq_true]
    simp only [newtonSumMonic]
    congr 1
    apply Finset.sum_congr rfl
    intro k h_k
    have h_idx : n + 1 - 1 - k = n - k := by omega
    rw [h_idx]
    congr 1
    have h_lt : n - k < prev.size := by
      rw [h_size]
      have := Finset.mem_range.mp h_k
      omega
    exact h_prev (n - k) h_lt

/-- **Size invariant:** `newtonSumsMonicIter P n` has exactly `n` entries. -/
@[simp]
theorem newtonSumsMonicIter_size (P : AzPolynomial R) (n : ℕ) :
    (P.newtonSumsMonicIter n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (Array.push _ _).size = n + 1
    rw [Array.size_push, ih]

/-- **Correctness of `newtonSumsMonicIter` (entry version).** The `i`-th
    entry of the precomputed array equals the spec value. -/
theorem newtonSumsMonicIter_getElem (P : AzPolynomial R) (n : ℕ) :
    ∀ (i : ℕ) (h : i < (P.newtonSumsMonicIter n).size),
      (P.newtonSumsMonicIter n)[i] = P.newtonSumMonic i := by
  induction n with
  | zero =>
    intro i h
    rw [P.newtonSumsMonicIter_size] at h
    exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro i h
    have h' : i < n + 1 := by
      rw [P.newtonSumsMonicIter_size] at h; exact h
    show ((P.newtonSumsMonicIter n).push
      (newtonSumStep P (P.newtonSumsMonicIter n)))[i] = _
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h') with h_lt | h_eq
    · have h_iter : i < (P.newtonSumsMonicIter n).size := by
        rw [P.newtonSumsMonicIter_size]; exact h_lt
      rw [Array.getElem_push, dif_pos h_iter]
      exact ih i h_iter
    · -- i = n
      have h_iter_size : (P.newtonSumsMonicIter n).size = n :=
        P.newtonSumsMonicIter_size n
      have h_not_lt : ¬ i < (P.newtonSumsMonicIter n).size := by
        rw [h_iter_size]; omega
      rw [Array.getElem_push, dif_neg h_not_lt]
      have h_size_eq_i : (P.newtonSumsMonicIter n).size = i := by
        rw [h_iter_size]; exact h_eq.symm
      rw [← h_size_eq_i]
      apply newtonSumStep_eq
      intro j h_j
      rw [(Array.getElem_eq_getD 0 (xs := P.newtonSumsMonicIter n) (i := j)).symm]
      exact ih j h_j

/-- **Correctness of `newtonSumsMonicIter` (getD form).** -/
theorem newtonSumsMonicIter_getD (P : AzPolynomial R) (n i : ℕ) (h : i < n) :
    (P.newtonSumsMonicIter n).getD i 0 = P.newtonSumMonic i := by
  have h_size : i < (P.newtonSumsMonicIter n).size := by
    rw [P.newtonSumsMonicIter_size]; exact h
  rw [(Array.getElem_eq_getD 0 (xs := P.newtonSumsMonicIter n) (i := i)).symm]
  exact P.newtonSumsMonicIter_getElem n i h_size

/-- **Equivalence:** the iterative and spec `newtonSumsMonic` agree as
    arrays. -/
theorem newtonSumsMonicIter_eq_newtonSumsMonic
    (P : AzPolynomial R) (n : ℕ) :
    P.newtonSumsMonicIter n = P.newtonSumsMonic n := by
  apply Array.ext
  · rw [P.newtonSumsMonicIter_size]
    unfold newtonSumsMonic
    simp
  · intro i h_iter h_spec
    have h_lt : i < n := by
      rw [P.newtonSumsMonicIter_size] at h_iter; exact h_iter
    rw [P.newtonSumsMonicIter_getElem n i h_iter]
    unfold newtonSumsMonic
    simp

/-! ### Correctness of the Newton matrix -/

/-- **Correctness of `newtMatMonic`.** Each entry `(i, j)` of the
    `k × k` Hankel matrix is the Newton sum `N_{i + j}`. -/
theorem newtMatMonic_toFn (P : AzPolynomial R) (k : ℕ) (i j : Fin k) :
    (P.newtMatMonic k).toFn i j = P.newtonSumMonic (i.val + j.val) := by
  unfold newtMatMonic
  rw [AzMatrix.toFn_ofFn]
  apply P.newtonSumsMonicIter_getD
  have h_i : i.val < k := i.isLt
  have h_j : j.val < k := j.isLt
  -- For k = 0 this case is vacuous; for k ≥ 1 we have i + j ≤ 2k − 2 < 2k − 1.
  have h_k_pos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) h_i
  omega

/-- **Get version.** Convenient direct form using `AzMatrix.get`. -/
theorem newtMatMonic_get (P : AzPolynomial R) (k : ℕ) (i j : Fin k) :
    (P.newtMatMonic k).get i j = P.newtonSumMonic (i.val + j.val) :=
  P.newtMatMonic_toFn k i j

end Azurite.AzPolynomial
