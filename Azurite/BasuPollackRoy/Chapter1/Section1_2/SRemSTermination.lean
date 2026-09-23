import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11

/-!
# Termination of the signed remainder sequence

The signed remainder sequence of two polynomials $(P, Q)$ over a field
$K$ — with $P \ne 0$ — eventually reaches $0$. We define
$\lcode{sremTermIndex}\,P\,Q$ to be the largest index $k$ such that
$\lcode{SRemS}\,P\,Q\;k \ne 0$ (so $\lcode{SRemS}\,P\,Q\;(k+1) = 0$).
This is the index at which Proposition 1.8 evaluates the GCD.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
/-- Every signed remainder sequence terminates. -/
lemma SRemS_terminates (P Q : K[X]) (hP : P ≠ 0) :
    ∃ k : ℕ, SRemS P Q (k + 1) = 0 ∧ SRemS P Q k ≠ 0 := by
  by_contra h
  push Not at h
  by_cases hQ : Q = 0
  · have h0 := h 0 (by simp [SRemS_snd, hQ])
    exact absurd h0 (by simp [SRemS_fst, hP])
  · have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS_snd, hQ]
    have h_all : ∀ k, SRemS P Q (k + 1) ≠ 0 := by
      intro k; induction k with
      | zero => exact h1
      | succ n ih =>
        intro heq
        exact absurd (h (n + 1) heq) ih
    have h_dec : ∀ k, (SRemS P Q (k + 2)).natDegree < (SRemS P Q (k + 1)).natDegree := by
      intro k
      exact Polynomial.natDegree_lt_natDegree (h_all (k + 1)) (degree_SRemS_lt P Q k (h_all k))
    have h_le : ∀ k, (SRemS P Q (k + 1)).natDegree + k ≤ (SRemS P Q 1).natDegree := by
      intro k; induction k with
      | zero => exact Nat.le_refl _
      | succ n ih =>
        have hstep : (SRemS P Q (n + 1 + 1)).natDegree < (SRemS P Q (n + 1)).natDegree := h_dec n
        omega
    have h_out := h_le ((SRemS P Q 1).natDegree + 1)
    omega

open Classical in
/-- The termination index k where SRemS(k+1) = 0 -/
noncomputable def sremTermIndex (P Q : K[X]) : ℕ :=
  if hP : P = 0 then 0 else Classical.choose (SRemS_terminates P Q hP)

open Classical in
lemma SRemS_sremTermIndex_succ_eq_zero (P Q : K[X]) (hP : P ≠ 0) :
    SRemS P Q (sremTermIndex P Q + 1) = 0 := by
  rw [sremTermIndex, dite_eq_right hP]
  exact (Classical.choose_spec (SRemS_terminates P Q hP)).1

open Classical in
lemma SRemS_sremTermIndex_ne_zero (P Q : K[X]) (hP : P ≠ 0) :
    SRemS P Q (sremTermIndex P Q) ≠ 0 := by
  rw [sremTermIndex, dite_eq_right hP]
  exact (Classical.choose_spec (SRemS_terminates P Q hP)).2

open Classical in
lemma SRemS_ne_zero_of_le_sremTermIndex (P Q : K[X]) (hP : P ≠ 0) (i : ℕ) (hi : i ≤ sremTermIndex P Q) :
    SRemS P Q i ≠ 0 := by
  cases i with
  | zero => simp [SRemS_fst, hP]
  | succ p =>
    exact SRemS_ne_zero_of_le P Q _ _ (SRemS_sremTermIndex_succ_eq_zero P Q hP) (SRemS_sremTermIndex_ne_zero P Q hP) (by omega) hi

end Azurite.BPR
