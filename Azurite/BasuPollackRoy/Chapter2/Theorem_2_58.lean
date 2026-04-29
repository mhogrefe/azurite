import Azurite.BasuPollackRoy.Chapter2.Lemma_2_59
import Azurite.BasuPollackRoy.Chapter2.Lemma_2_60

/-!
# BPR Theorem 2.58

Let `P ≠ 0` and `Q` be polynomials over a real closed field `R`, and let
`a, b ∈ R ∪ {±∞}` with `a < b`. If `a` and `b` are not roots of any
polynomial in the signed remainder sequence of `P, Q`, then

`Var(SRemS(P, Q); a, b) = Ind(Q/P; a, b)`.

The proof is by induction on the length `n` of the signed remainder
sequence:

* base case `Q = 0`: both sides are zero.
* inductive case `Q ≠ 0`: combine Lemma 2.59 (for `Var`) with Lemma 2.60
  (for `Ind`), then apply the IH to the tail `(Q, -R)` where `R = P % Q`.

For the formalization we add the hypothesis `ExtendedPoint.Lt a b` (i.e.
`a < b` in extended order) — matching BPR's "for `a < b`" assumption.
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- `varNonzero` of a list of length at most 1 vanishes. -/
private lemma varNonzero_eq_zero_of_length_le_one
    {L : List R} (h : L.length ≤ 1) : varNonzero L = 0 := by
  match L, h with
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => simp at h

omit [IsStrictOrderedRing R] in
/-- `Var` of a singleton list vanishes (no adjacent pairs to check). -/
private lemma Var_singleton (a : R) : Var [a] = 0 := by
  classical
  unfold Var
  by_cases h : a = 0
  · simp [h]
  · simp [h]

omit [IsStrictOrderedRing R] in
/-- `varAt` of a list `[P, 0, 0, …, 0]` (one polynomial followed by zeros)
    is zero. -/
private lemma varAt_singleton_with_trailing_zeros (P : R[X]) (n : ℕ)
    (x : ExtendedPoint R) :
    varAt (P :: List.replicate n (0 : R[X])) x = 0 := by
  classical
  unfold varAt
  set L := (P :: List.replicate n (0 : R[X])).map (ExtendedPoint.evalPoly · x)
  -- Show L = [evalPoly P x] ++ replicate n 0
  have hL : L = ExtendedPoint.evalPoly P x ::
      List.replicate n (0 : R) := by
    show (P :: List.replicate n (0 : R[X])).map (ExtendedPoint.evalPoly · x) = _
    rw [List.map_cons]
    congr 1
    rw [List.map_replicate]
    cases x <;> simp [ExtendedPoint.evalPoly]
  rw [hL]
  unfold Var
  simp only [List.filter_cons, List.filter_replicate]
  -- Now the filtered list equals either [] or [evalPoly P x]; varNonzero is 0 either way.
  by_cases hP : ExtendedPoint.evalPoly P x = 0
  · simp [hP]
  · simp [hP]

/-- `JumpsFromNegInfToPosInf` requires `Q ≠ 0`: a zero numerator can't
    have positive sign on any interval. -/
private lemma not_jumpsFromNegInfToPosInf_zero (P : R[X]) (x : R) :
    ¬ JumpsFromNegInfToPosInf 0 P x := by
  intro ⟨_, _, hsign⟩
  obtain ⟨b, hxb, h_sign⟩ := hsign
  obtain ⟨t, hxt, htb⟩ := exists_between hxb
  have h_eval : SignType.sign (((0 : R[X]) * P).eval t) = 1 :=
    h_sign t ⟨hxt, htb⟩
  simp at h_eval

/-- `JumpsFromPosInfToNegInf` requires `Q ≠ 0`. -/
private lemma not_jumpsFromPosInfToNegInf_zero (P : R[X]) (x : R) :
    ¬ JumpsFromPosInfToNegInf 0 P x := by
  intro ⟨_, _, hsign⟩
  obtain ⟨b, hxb, h_sign⟩ := hsign
  obtain ⟨t, hxt, htb⟩ := exists_between hxb
  have h_eval : SignType.sign (((0 : R[X]) * P).eval t) = -1 :=
    h_sign t ⟨hxt, htb⟩
  simp at h_eval

/-- `cauchyIndexOn 0 P a b = 0`: a zero numerator produces no jumps. -/
theorem cauchyIndexOn_zero_left (P : R[X]) (a b : ExtendedPoint R) :
    cauchyIndexOn 0 P a b = 0 := by
  classical
  unfold cauchyIndexOn
  simp only
  have h1 : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromNegInfToPosInf 0 P x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x _ ⟨_, hjump⟩
    exact not_jumpsFromNegInfToPosInf_zero P x hjump
  have h2 : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromPosInfToNegInf 0 P x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x _ ⟨_, hjump⟩
    exact not_jumpsFromPosInfToNegInf_zero P x hjump
  rw [h1, h2]
  simp

omit [IsStrictOrderedRing R] in
/-- **Helper: σ-correction equality.** For `t : ExtendedPoint R` with
    `evalPoly P t * evalPoly Q t ≠ 0`,
    `2 * (if PQ(t) < 0 then 1 else 0) = 1 - sigmaPQ P Q t`. -/
private lemma two_mul_indicator_eq
    (P Q : R[X]) (t : ExtendedPoint R)
    (ht : ExtendedPoint.evalPoly P t * ExtendedPoint.evalPoly Q t ≠ 0) :
    2 * (if ExtendedPoint.evalPoly P t * ExtendedPoint.evalPoly Q t < 0
          then (1 : ℤ) else 0) =
      1 - sigmaPQ P Q t := by
  unfold sigmaPQ
  set s := ExtendedPoint.evalPoly P t * ExtendedPoint.evalPoly Q t
  rcases lt_trichotomy s 0 with h | h | h
  · simp [h, sign_eq_neg_one_iff.mpr h]
  · exact absurd h ht
  · simp [not_lt_of_gt h, sign_eq_one_iff.mpr h]

/-- **BPR Theorem 2.58 (truncated form).** Under `a < b` and the
    assumption that `a, b` are not roots of any nonzero polynomial in
    the SRemS sequence (encoded as: each `SRemS P Q i` is either zero or
    has nonzero evaluation at `a` and `b`), for any `n` past the end of
    the sequence (i.e. `SRemS P Q n = 0`),

    `Var(SRemSList P Q n; a, b) = Ind(Q/P; a, b)`. -/
theorem theorem_2_58
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (h_a : ∀ i : ℕ, SRemS P Q i = 0 ∨
        ExtendedPoint.evalPoly (SRemS P Q i) a ≠ 0)
    (h_b : ∀ i : ℕ, SRemS P Q i = 0 ∨
        ExtendedPoint.evalPoly (SRemS P Q i) b ≠ 0)
    (n : ℕ) (hn : SRemS P Q n = 0) :
    ((varAt (SRemSList P Q n) a : ℤ) - (varAt (SRemSList P Q n) b : ℤ)) =
      cauchyIndexOn Q P a b := by
  classical
  induction n using Nat.strong_induction_on generalizing P Q with
  | _ n ih =>
    match n, hn with
    | 0, hn0 =>
      have : P = 0 := hn0
      exact absurd this hP
    | 1, hn1 =>
      have hQ : Q = 0 := hn1
      subst hQ
      have h_LHS : ∀ y : ExtendedPoint R,
          varAt (SRemSList P (0 : R[X]) 1) y = 0 := by
        intro y
        show varAt [P] y = 0
        unfold varAt
        rw [List.map_singleton]
        exact Var_singleton _
      rw [h_LHS a, h_LHS b]
      simp [cauchyIndexOn_zero_left]
    | n + 2, hn2 =>
      by_cases hQ : Q = 0
      · subst hQ
        have h_list : SRemSList P (0 : R[X]) (n + 2) =
            P :: List.replicate (n + 1) (0 : R[X]) := by
          unfold SRemSList
          rw [List.range_succ_eq_map]
          simp only [List.map_cons]
          show SRemS P 0 0 :: _ = P :: _
          rw [show SRemS P (0 : R[X]) 0 = P from rfl]
          congr 1
          rw [List.map_map]
          apply (List.eq_replicate_iff).mpr
          refine ⟨by simp, ?_⟩
          intro x hx
          simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨i, _, rfl⟩ := hx
          show SRemS P 0 (i + 1) = 0
          exact SRemS_zero_right P (i + 1) (by omega)
        rw [h_list, varAt_singleton_with_trailing_zeros,
            varAt_singleton_with_trailing_zeros]
        simp [cauchyIndexOn_zero_left]
      · -- Q ≠ 0 case: use Lemma 2.59 + Lemma 2.60 + IH on (Q, -R).
        have hP_a : ExtendedPoint.evalPoly P a ≠ 0 := by
          rcases h_a 0 with hzero | hne
          · exact absurd (show P = 0 from hzero) hP
          · exact hne
        have hQ_a : ExtendedPoint.evalPoly Q a ≠ 0 := by
          rcases h_a 1 with hzero | hne
          · exact absurd (show Q = 0 from hzero) hQ
          · exact hne
        have hP_b : ExtendedPoint.evalPoly P b ≠ 0 := by
          rcases h_b 0 with hzero | hne
          · exact absurd (show P = 0 from hzero) hP
          · exact hne
        have hQ_b : ExtendedPoint.evalPoly Q b ≠ 0 := by
          rcases h_b 1 with hzero | hne
          · exact absurd (show Q = 0 from hzero) hQ
          · exact hne
        have h59 := lemma_2_59 P Q hQ n a b hP_a hQ_a hP_b hQ_b
        have h_tail_zero : SRemS Q (-(P % Q)) (n + 1) = 0 := by
          rw [← SRemS_succ P Q hQ]
          exact hn2
        have h_a_tail : ∀ i : ℕ,
            SRemS Q (-(P % Q)) i = 0 ∨
              ExtendedPoint.evalPoly (SRemS Q (-(P % Q)) i) a ≠ 0 := by
          intro i
          rw [← SRemS_succ P Q hQ]
          exact h_a (i + 1)
        have h_b_tail : ∀ i : ℕ,
            SRemS Q (-(P % Q)) i = 0 ∨
              ExtendedPoint.evalPoly (SRemS Q (-(P % Q)) i) b ≠ 0 := by
          intro i
          rw [← SRemS_succ P Q hQ]
          exact h_b (i + 1)
        have h_ih := ih (n + 1) (by omega) Q (-(P % Q)) hQ
          h_a_tail h_b_tail h_tail_zero
        have h_aPQ : ExtendedPoint.evalPoly P a *
            ExtendedPoint.evalPoly Q a ≠ 0 := mul_ne_zero hP_a hQ_a
        have h_bPQ : ExtendedPoint.evalPoly P b *
            ExtendedPoint.evalPoly Q b ≠ 0 := mul_ne_zero hP_b hQ_b
        have h60 := lemma_2_60 hIVP P Q hP hQ a b hab h_aPQ h_bPQ
        have h_sigma_a := two_mul_indicator_eq P Q a h_aPQ
        have h_sigma_b := two_mul_indicator_eq P Q b h_bPQ
        rw [h59, h_ih]
        linarith [h60, h_sigma_a, h_sigma_b]

end Azurite.BPR
