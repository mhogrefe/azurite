import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_59
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_60

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

/-- **BPR Theorem 2.58, strong-hypothesis version.** Under `a < b` and
    the assumption that `a, b` are not roots of any nonzero polynomial
    in the SRemS sequence — encoded as `SRemS P Q i = 0 ∨ evalPoly
    (SRemS P Q i) {a,b} ≠ 0` — for any `n` past the end of the sequence
    (`SRemS P Q n = 0`),

    `Var(SRemSList P Q n; a, b) = Ind(Q/P; a, b)`.

    This is the version directly proved by induction on `n` using
    Lemmas 2.59 and 2.60. The BPR-faithful `theorem_2_58` (only
    `evalPoly P a, b ≠ 0`) below reduces to this via a perturbation
    argument. -/
theorem theorem_2_58_no_SRemS_root_at_endpoints
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

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **SRemS cascade lemma 1.** If `SRemS_{j+1}` is a nonzero polynomial
    that vanishes at `a`, and `SRemS_j` also vanishes at `a`, then
    `P` vanishes at `a`. (Cascade backwards via the Euclidean
    recurrence `SRemS_{j+2} = -(SRemS_j % SRemS_{j+1})` and
    `eval_mod_at_root`.) -/
lemma SRemS_eval_cascade (P Q : R[X]) (a : R) (j : ℕ)
    (h_succ_ne : SRemS P Q (j + 1) ≠ 0)
    (h_succ_zero : (SRemS P Q (j + 1)).eval a = 0)
    (h_curr_zero : (SRemS P Q j).eval a = 0) : P.eval a = 0 := by
  classical
  induction j with
  | zero => exact h_curr_zero
  | succ k ih =>
    -- Hypotheses: SRemS_{k+2} ≠ 0 poly, SRemS_{k+2}(a) = 0, SRemS_{k+1}(a) = 0.
    have h_kp1_ne : SRemS P Q (k + 1) ≠ 0 := by
      intro h_zero
      exact h_succ_ne (SRemS_zero_ge P Q k h_zero (k + 2) (by omega))
    -- Recurrence at index `k`.
    have h_step : SRemS P Q (k + 2) = -(SRemS P Q k % SRemS P Q (k + 1)) := by
      simp [SRemS, h_kp1_ne]
    -- Eval at `a` using `(SRemS_{k+1}).eval a = 0`.
    have h_mod_eval : (SRemS P Q k % SRemS P Q (k + 1)).eval a =
        (SRemS P Q k).eval a :=
      eval_mod_at_root (SRemS P Q k) (SRemS P Q (k + 1)) a h_curr_zero
    have h_succ_eval : (SRemS P Q (k + 2)).eval a = -(SRemS P Q k).eval a := by
      rw [h_step, Polynomial.eval_neg, h_mod_eval]
    have h_succ_zero' : (SRemS P Q (k + 2)).eval a = 0 := h_succ_zero
    have h_k_zero : (SRemS P Q k).eval a = 0 := by
      have h : -(SRemS P Q k).eval a = 0 := by
        rw [← h_succ_eval]; exact h_succ_zero'
      exact neg_eq_zero.mp h
    exact ih h_kp1_ne h_curr_zero h_k_zero

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **SRemS cascade lemma 2.** If `SRemS_j` is a nonzero polynomial
    vanishing at `a`, but `SRemS_{j+1}` is the zero polynomial (i.e.
    the SRemS sequence has just terminated), then `P` vanishes at `a`.

    Proof: `SRemS_{j+1} = 0` polynomial means `SRemS_j` divides
    `SRemS_{j-1}` (via the Euclidean recurrence). So `SRemS_{j-1}(a)`
    is a multiple of `SRemS_j(a) = 0`, hence vanishes too. Apply
    cascade 1. -/
lemma SRemS_eval_cascade_terminal (P Q : R[X]) (a : R) (j : ℕ)
    (h_curr_ne : SRemS P Q j ≠ 0)
    (h_succ_zero_poly : SRemS P Q (j + 1) = 0)
    (h_curr_eval_zero : (SRemS P Q j).eval a = 0) : P.eval a = 0 := by
  classical
  -- For j = 0: SRemS_0 = P, so P.eval a = 0 directly.
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    exact h_curr_eval_zero
  · -- j ≥ 1. Use the recurrence to show SRemS_{j-1}(a) = 0, then cascade 1.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
    -- j = k + 1, so SRemS_{j+1} = SRemS_{k+2}.
    -- SRemS_{k+2} = -(SRemS_k % SRemS_{k+1}) when SRemS_{k+1} ≠ 0.
    -- h_succ_zero_poly: SRemS_{k+2} = 0 polynomial.
    -- h_curr_ne: SRemS_{k+1} ≠ 0 polynomial.
    have h_step : SRemS P Q (k + 2) = -(SRemS P Q k % SRemS P Q (k + 1)) := by
      simp [SRemS, h_curr_ne]
    have h_mod_zero : SRemS P Q k % SRemS P Q (k + 1) = 0 := by
      have := h_step.symm.trans h_succ_zero_poly
      rwa [neg_eq_zero] at this
    -- So SRemS_{k+1} divides SRemS_k.
    have h_dvd : SRemS P Q (k + 1) ∣ SRemS P Q k := by
      have h_div_add := EuclideanDomain.div_add_mod (SRemS P Q k) (SRemS P Q (k + 1))
      rw [h_mod_zero, add_zero] at h_div_add
      exact ⟨_, h_div_add.symm⟩
    -- Hence SRemS_k.eval a is a multiple of SRemS_{k+1}.eval a = 0.
    have h_k_eval_zero : (SRemS P Q k).eval a = 0 := by
      obtain ⟨q, hq⟩ := h_dvd
      rw [hq, Polynomial.eval_mul, h_curr_eval_zero, zero_mul]
    -- Apply cascade 1 with index k.
    exact SRemS_eval_cascade P Q a k h_curr_ne h_curr_eval_zero h_k_eval_zero

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Opposite-sign lemma.** Under `P(a) ≠ 0`, at any `j ≥ 1` where
    `SRemS_j` is a nonzero polynomial vanishing at `a`:

    * `SRemS_{j-1}` is a nonzero polynomial with `SRemS_{j-1}.eval a ≠ 0`;
    * `SRemS_{j+1}` is a nonzero polynomial with `SRemS_{j+1}.eval a ≠ 0`;
    * `SRemS_{j+1}.eval a = -(SRemS_{j-1}.eval a)`. -/
lemma SRemS_eval_opposite_sign_at_zero (P Q : R[X]) (a : R) (j : ℕ)
    (hP_eval : P.eval a ≠ 0)
    (h_curr_ne : SRemS P Q (j + 1) ≠ 0)
    (h_curr_eval_zero : (SRemS P Q (j + 1)).eval a = 0) :
    SRemS P Q j ≠ 0 ∧ (SRemS P Q j).eval a ≠ 0 ∧
      SRemS P Q (j + 2) ≠ 0 ∧ (SRemS P Q (j + 2)).eval a ≠ 0 ∧
      (SRemS P Q (j + 2)).eval a = -(SRemS P Q j).eval a := by
  classical
  -- SRemS_j ≠ 0 polynomial: if SRemS_j = 0 then SRemS_{j+1} = 0, contradicting h_curr_ne.
  have h_prev_ne : SRemS P Q j ≠ 0 := by
    intro h_zero
    apply h_curr_ne
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      -- SRemS P Q 0 = P; if P = 0, contradicts hP_eval.
      simp [SRemS] at h_zero
      exact absurd (by rw [h_zero, Polynomial.eval_zero] : P.eval a = 0) hP_eval
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
      -- j = k + 1, SRemS_{k+1} = 0, so SRemS_{k+2} = 0.
      simp [SRemS, h_zero]
  -- SRemS_{j+2} ≠ 0 polynomial: by cascade_terminal contrapositive.
  have h_succ_ne : SRemS P Q (j + 2) ≠ 0 := by
    intro h_zero
    -- If SRemS_{j+2} = 0, by cascade_terminal applied at index j+1, P.eval a = 0.
    exact hP_eval (SRemS_eval_cascade_terminal P Q a (j + 1) h_curr_ne h_zero h_curr_eval_zero)
  -- Recurrence: SRemS_{j+2} = -(SRemS_j % SRemS_{j+1}).
  have h_step : SRemS P Q (j + 2) = -(SRemS P Q j % SRemS P Q (j + 1)) := by
    simp [SRemS, h_curr_ne]
  -- Eval at a using SRemS_{j+1}(a) = 0:
  have h_mod_eval : (SRemS P Q j % SRemS P Q (j + 1)).eval a =
      (SRemS P Q j).eval a :=
    eval_mod_at_root (SRemS P Q j) (SRemS P Q (j + 1)) a h_curr_eval_zero
  have h_succ_eval : (SRemS P Q (j + 2)).eval a = -(SRemS P Q j).eval a := by
    rw [h_step, Polynomial.eval_neg, h_mod_eval]
  -- SRemS_j.eval a ≠ 0: by cascade 1 contrapositive.
  have h_prev_eval_ne : (SRemS P Q j).eval a ≠ 0 := by
    intro h_zero
    exact hP_eval (SRemS_eval_cascade P Q a j h_curr_ne h_curr_eval_zero h_zero)
  -- SRemS_{j+2}.eval a ≠ 0 follows from `h_succ_eval`: equals -prev_eval ≠ 0.
  have h_succ_eval_ne : (SRemS P Q (j + 2)).eval a ≠ 0 := by
    rw [h_succ_eval]
    exact neg_ne_zero.mpr h_prev_eval_ne
  exact ⟨h_prev_ne, h_prev_eval_ne, h_succ_ne, h_succ_eval_ne, h_succ_eval⟩

omit [IsStrictOrderedRing R] in
open Classical in
/-- **CauchyIndexOn invariance under interval narrowing.** If
    `(a', b') ⊆ (a, b)` and the open intervals contain the same
    `P`-roots, `cauchyIndexOn Q P a b = cauchyIndexOn Q P a' b'`. The
    `same-roots` property holds whenever `(a, a'] ∪ [b', b)` is free
    of `P`-roots. -/
lemma cauchyIndexOn_eq_of_same_P_roots
    (Q P : R[X]) (a b a' b' : ExtendedPoint R)
    (h_same : ∀ x ∈ P.roots,
        x ∈ ExtendedPoint.openInterval a b ↔
          x ∈ ExtendedPoint.openInterval a' b') :
    cauchyIndexOn Q P a b = cauchyIndexOn Q P a' b' := by
  show
    ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      (P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromPosInfToNegInf Q P x)).card =
    ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a' b' ∧
          JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      (P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a' b' ∧
          JumpsFromPosInfToNegInf Q P x)).card
  have h_pos : P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromNegInfToPosInf Q P x) =
      P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a' b' ∧
          JumpsFromNegInfToPosInf Q P x) := by
    apply Finset.filter_congr
    intro x hx
    have hx_root : x ∈ P.roots := Multiset.mem_toFinset.mp hx
    rw [h_same x hx_root]
  have h_neg : P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromPosInfToNegInf Q P x) =
      P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a' b' ∧
          JumpsFromPosInfToNegInf Q P x) := by
    apply Finset.filter_congr
    intro x hx
    have hx_root : x ∈ P.roots := Multiset.mem_toFinset.mp hx
    rw [h_same x hx_root]
  rw [h_pos, h_neg]

open Classical in
/-- **Existence of root-free perturbation on the right.** For any
    `a < α` in `R` and any finite set of nonzero polynomials, there
    exists `a' ∈ (a, α)` with no root of any polynomial in the set
    lying in the half-open interval `(a, a']`.

    Used for the WLOG perturbation step in `theorem_2_58`. -/
lemma exists_lt_not_root_in_Ioo
    (a α : R) (hαlt : a < α) (S : Finset R[X])
    (hS : ∀ p ∈ S, p ≠ 0) :
    ∃ a' : R, a < a' ∧ a' < α ∧
      ∀ p ∈ S, ∀ x : R, a < x → x ≤ a' → p.eval x ≠ 0 := by
  set badSet : Finset R :=
    S.biUnion (fun p => p.roots.toFinset) with h_badSet
  set badInOpen : Finset R := badSet.filter (fun x => a < x ∧ x < α)
  by_cases hEmpty : badInOpen = ∅
  · -- No bad points in (a, α). Pick a' anywhere in (a, α).
    obtain ⟨a', ha_lt, ha_lt_α⟩ := exists_between hαlt
    refine ⟨a', ha_lt, ha_lt_α, ?_⟩
    intro p hpS x hx_gt hx_le h_root
    have hp_ne : p ≠ 0 := hS p hpS
    have h_x_in_p : x ∈ p.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
      exact h_root
    have h_x_in_bad : x ∈ badSet :=
      Finset.mem_biUnion.mpr ⟨p, hpS, h_x_in_p⟩
    have h_x_in_open : x ∈ badInOpen :=
      Finset.mem_filter.mpr
        ⟨h_x_in_bad, hx_gt, lt_of_le_of_lt hx_le ha_lt_α⟩
    rw [hEmpty] at h_x_in_open
    exact absurd h_x_in_open (Finset.notMem_empty _)
  · -- Pick a' below the min of badInOpen.
    have hNe : badInOpen.Nonempty := Finset.nonempty_of_ne_empty hEmpty
    set m : R := badInOpen.min' hNe with h_m_def
    have hm_in : m ∈ badInOpen := Finset.min'_mem _ _
    have hm_lt_α : m < α := (Finset.mem_filter.mp hm_in).2.2
    have ha_lt_m : a < m := (Finset.mem_filter.mp hm_in).2.1
    obtain ⟨a', ha_lt, ha_lt_m'⟩ := exists_between ha_lt_m
    refine ⟨a', ha_lt, lt_trans ha_lt_m' hm_lt_α, ?_⟩
    intro p hpS x hx_gt hx_le h_root
    have hp_ne : p ≠ 0 := hS p hpS
    have h_x_in_p : x ∈ p.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
      exact h_root
    have h_x_in_bad : x ∈ badSet :=
      Finset.mem_biUnion.mpr ⟨p, hpS, h_x_in_p⟩
    have hx_lt_α : x < α := lt_of_le_of_lt hx_le (lt_trans ha_lt_m' hm_lt_α)
    have h_x_in_open : x ∈ badInOpen :=
      Finset.mem_filter.mpr ⟨h_x_in_bad, hx_gt, hx_lt_α⟩
    have h_m_le_x : m ≤ x := Finset.min'_le _ x h_x_in_open
    linarith

open Classical in
/-- **Existence of root-free perturbation on the left.** Symmetric
    counterpart of `exists_lt_not_root_in_Ioo`, used for the right
    endpoint `b`. -/
lemma exists_gt_not_root_in_Ioo
    (β b : R) (hβlt : β < b) (S : Finset R[X])
    (hS : ∀ p ∈ S, p ≠ 0) :
    ∃ b' : R, β < b' ∧ b' < b ∧
      ∀ p ∈ S, ∀ x : R, b' ≤ x → x < b → p.eval x ≠ 0 := by
  set badSet : Finset R :=
    S.biUnion (fun p => p.roots.toFinset) with h_badSet
  set badInOpen : Finset R := badSet.filter (fun x => β < x ∧ x < b)
  by_cases hEmpty : badInOpen = ∅
  · obtain ⟨b', hβ_lt, hb_lt⟩ := exists_between hβlt
    refine ⟨b', hβ_lt, hb_lt, ?_⟩
    intro p hpS x hx_ge hx_lt h_root
    have hp_ne : p ≠ 0 := hS p hpS
    have h_x_in_p : x ∈ p.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
      exact h_root
    have h_x_in_bad : x ∈ badSet :=
      Finset.mem_biUnion.mpr ⟨p, hpS, h_x_in_p⟩
    have hβ_lt_x : β < x := lt_of_lt_of_le hβ_lt hx_ge
    have h_x_in_open : x ∈ badInOpen :=
      Finset.mem_filter.mpr ⟨h_x_in_bad, hβ_lt_x, hx_lt⟩
    rw [hEmpty] at h_x_in_open
    exact absurd h_x_in_open (Finset.notMem_empty _)
  · have hNe : badInOpen.Nonempty := Finset.nonempty_of_ne_empty hEmpty
    set M : R := badInOpen.max' hNe with h_M_def
    have hM_in : M ∈ badInOpen := Finset.max'_mem _ _
    have hM_lt_b : M < b := (Finset.mem_filter.mp hM_in).2.2
    have hβ_lt_M : β < M := (Finset.mem_filter.mp hM_in).2.1
    obtain ⟨b', hM_lt_b', hb'_lt⟩ := exists_between hM_lt_b
    refine ⟨b', lt_trans hβ_lt_M hM_lt_b', hb'_lt, ?_⟩
    intro p hpS x hx_ge hx_lt h_root
    have hp_ne : p ≠ 0 := hS p hpS
    have h_x_in_p : x ∈ p.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
      exact h_root
    have h_x_in_bad : x ∈ badSet :=
      Finset.mem_biUnion.mpr ⟨p, hpS, h_x_in_p⟩
    have hβ_lt_x : β < x :=
      lt_of_lt_of_le (lt_trans hβ_lt_M hM_lt_b') hx_ge
    have h_x_in_open : x ∈ badInOpen :=
      Finset.mem_filter.mpr ⟨h_x_in_bad, hβ_lt_x, hx_lt⟩
    have h_x_le_M : x ≤ M := Finset.le_max' _ x h_x_in_open
    linarith

/-- **Sign preservation under IVP.** If `F.eval a ≠ 0`, `F.eval b ≠ 0`,
    `a < b`, and `F` has no roots in the open interval `(a, b)`, then
    `F.eval a` and `F.eval b` have the same sign.

    Direct from the intermediate value property: opposite signs would
    yield a root by `hIVP`. -/
lemma sign_eval_eq_of_no_root_Ioo
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (F : R[X]) {a b : R} (hab : a < b)
    (hFa : F.eval a ≠ 0) (hFb : F.eval b ≠ 0)
    (h_no_roots : ∀ x : R, a < x → x < b → F.eval x ≠ 0) :
    SignType.sign (F.eval a) = SignType.sign (F.eval b) := by
  by_contra h_neq
  -- Trichotomy: signs differ, so the product is negative.
  have h_prod_neg : F.eval a * F.eval b < 0 := by
    rcases lt_trichotomy (F.eval a) 0 with ha_lt | ha_eq | ha_gt
    · rcases lt_trichotomy (F.eval b) 0 with hb_lt | hb_eq | hb_gt
      · exfalso; apply h_neq
        rw [sign_eq_neg_one_iff.mpr ha_lt, sign_eq_neg_one_iff.mpr hb_lt]
      · exact absurd hb_eq hFb
      · exact mul_neg_of_neg_of_pos ha_lt hb_gt
    · exact absurd ha_eq hFa
    · rcases lt_trichotomy (F.eval b) 0 with hb_lt | hb_eq | hb_gt
      · exact mul_neg_of_pos_of_neg ha_gt hb_lt
      · exact absurd hb_eq hFb
      · exfalso; apply h_neq
        rw [sign_eq_one_iff.mpr ha_gt, sign_eq_one_iff.mpr hb_gt]
  obtain ⟨x, hx_gt, hx_lt, hFx⟩ := hIVP F a b hab h_prod_neg
  exact h_no_roots x hx_gt hx_lt hFx

/-- **Local Var invariance under nonzero insertion between opposite
    signs.** If `a, b` have opposite signs and `c` is nonzero, then
    inserting `c` between `a` and `b` preserves the sign-variation
    count: `varNonzero (a :: c :: b :: rest) = varNonzero (a :: b :: rest)`.

    This is the key local-cascade invariance that makes
    `varAt(SRemS) a = varAt(SRemS) a'` under the perturbation. -/
lemma varNonzero_insert_between_opposite
    (a c b : R) (rest : List R) (hc : c ≠ 0) (h_opp : a * b < 0) :
    varNonzero (a :: c :: b :: rest) = varNonzero (a :: b :: rest) := by
  show (if a * c < 0 then 1 else 0) + varNonzero (c :: b :: rest) =
    (if a * b < 0 then 1 else 0) + varNonzero (b :: rest)
  show (if a * c < 0 then 1 else 0) +
      ((if c * b < 0 then 1 else 0) + varNonzero (b :: rest)) =
    (if a * b < 0 then 1 else 0) + varNonzero (b :: rest)
  rw [if_pos h_opp]
  ring_nf
  -- Goal: (if a*c < 0 then 1 else 0) + (if c*b < 0 then 1 else 0) = 1
  -- (modulo placement of varNonzero (b :: rest) which cancels via add_comm).
  have h_sum : (if a * c < 0 then (1 : ℕ) else 0) +
        (if c * b < 0 then 1 else 0) = 1 := by
    -- a*b < 0 (h_opp) means a, b have opposite signs.
    -- Exactly one of a*c, c*b is negative (since c is nonzero).
    rcases lt_trichotomy (a * c) 0 with hac_lt | hac_eq | hac_gt
    · -- a*c < 0. Show c*b ≥ 0.
      rw [if_pos hac_lt]
      -- a*c < 0 means a, c have opposite signs.
      -- a*b < 0 means a, b have opposite signs.
      -- So c, b have the same sign (both opposite of a).
      -- Hence c*b > 0 (both nonzero).
      have h_cb : ¬ (c * b < 0) := by
        intro h_cb_lt
        -- Multiply: (a*c)*(c*b) > 0 (both negative).
        have : a * c * (c * b) > 0 := mul_pos_of_neg_of_neg hac_lt h_cb_lt
        -- LHS = a * b * c^2.
        have h_eq : a * c * (c * b) = a * b * (c * c) := by ring
        rw [h_eq] at this
        have h_csq_pos : 0 < c * c := mul_self_pos.mpr hc
        have h_ab_pos : 0 < a * b := by
          rcases mul_pos_iff.mp this with ⟨_, _⟩ | ⟨h_ab_neg, _⟩
          · assumption
          · linarith [h_csq_pos]
        linarith
      rw [if_neg h_cb]
    · -- a*c = 0. Since c ≠ 0, a = 0. But then a*b = 0, contradicting h_opp < 0.
      have h_a_zero : a = 0 := by
        rcases mul_eq_zero.mp hac_eq with ha | hc'
        · exact ha
        · exact absurd hc' hc
      exfalso
      rw [h_a_zero, zero_mul] at h_opp
      exact lt_irrefl 0 h_opp
    · -- a*c > 0. Show c*b < 0.
      rw [if_neg (not_lt.mpr (le_of_lt hac_gt))]
      have h_cb_neg : c * b < 0 := by
        -- a, c same sign; a, b opposite; so c, b opposite. Hence c*b < 0.
        by_contra h_not_neg
        push Not at h_not_neg
        -- h_not_neg : 0 ≤ c * b. Combined with hac_gt: a*c > 0.
        -- Multiply: (a*c)*(c*b) ≥ 0.
        have h_prod : 0 ≤ a * c * (c * b) := mul_nonneg (le_of_lt hac_gt) h_not_neg
        -- LHS = a * b * c^2.
        have h_eq : a * c * (c * b) = a * b * (c * c) := by ring
        rw [h_eq] at h_prod
        have h_csq_pos : 0 < c * c := mul_self_pos.mpr hc
        -- h_prod : 0 ≤ a * b * (c * c). a*b < 0, c*c > 0. So a*b*(c*c) < 0. Contradiction.
        have h_ab_csq_neg : a * b * (c * c) < 0 := mul_neg_of_neg_of_pos h_opp h_csq_pos
        linarith
      rw [if_pos h_cb_neg]
  linarith [h_sum]

omit [IsStrictOrderedRing R] in
/-- **VarNonzero is preserved by appending a nonzero head when the
    next element has the same sign.** -/
lemma varNonzero_cons_same_sign
    (a b : R) (rest : List R) (h_same : 0 < a * b) :
    varNonzero (a :: b :: rest) = varNonzero (b :: rest) := by
  show (if a * b < 0 then 1 else 0) + varNonzero (b :: rest) =
    varNonzero (b :: rest)
  rw [if_neg (not_lt.mpr (le_of_lt h_same))]
  simp

/-- **VarNonzero insertion at any position.** Inserting a nonzero
    value between two adjacent opposite-signed values, anywhere in a
    list, preserves `varNonzero`. Proof by induction on the prefix
    before the insertion point. -/
lemma varNonzero_eq_after_insertion
    (pre : List R) (a c b : R) (rest : List R)
    (hc : c ≠ 0) (h_opp : a * b < 0) :
    varNonzero (pre ++ a :: c :: b :: rest) =
      varNonzero (pre ++ a :: b :: rest) := by
  induction pre with
  | nil =>
    show varNonzero (a :: c :: b :: rest) = varNonzero (a :: b :: rest)
    exact varNonzero_insert_between_opposite a c b rest hc h_opp
  | cons x xs ih =>
    -- Goal: varNonzero (x :: xs ++ a :: c :: b :: rest) =
    --       varNonzero (x :: xs ++ a :: b :: rest)
    -- Pull off the head x and recurse on xs ++ ...
    rw [show (x :: xs) ++ a :: c :: b :: rest =
      x :: (xs ++ a :: c :: b :: rest) from rfl]
    rw [show (x :: xs) ++ a :: b :: rest =
      x :: (xs ++ a :: b :: rest) from rfl]
    -- Now consider the second element of each list.
    cases h_xs : xs with
    | nil =>
      simp only [List.nil_append]
      show (if x * a < 0 then 1 else 0) + varNonzero (a :: c :: b :: rest) =
        (if x * a < 0 then 1 else 0) + varNonzero (a :: b :: rest)
      congr 1
      exact varNonzero_insert_between_opposite a c b rest hc h_opp
    | cons x' xs' =>
      simp only [List.cons_append]
      show (if x * x' < 0 then 1 else 0) +
          varNonzero (x' :: (xs' ++ a :: c :: b :: rest)) =
        (if x * x' < 0 then 1 else 0) +
          varNonzero (x' :: (xs' ++ a :: b :: rest))
      congr 1
      have : (x' :: xs') ++ a :: c :: b :: rest =
          x' :: (xs' ++ a :: c :: b :: rest) := rfl
      rw [← this]
      have : (x' :: xs') ++ a :: b :: rest =
          x' :: (xs' ++ a :: b :: rest) := rfl
      rw [← this]
      rw [← h_xs]
      exact ih

/-- **Var-level cascade replacement.** If `a, b` are nonzero with
    opposite signs and `c` is nonzero, then `Var` (which filters zeros)
    is the same whether we have a `0` or `c` between them.

    `Var (pre ++ a :: 0 :: b :: rest) = Var (pre ++ a :: c :: b :: rest)`. -/
lemma Var_eq_replace_zero_with_nonzero
    (pre : List R) (a b : R) (rest : List R)
    (ha : a ≠ 0) (hb : b ≠ 0) (c : R) (hc : c ≠ 0) (h_opp : a * b < 0) :
    Var (pre ++ a :: (0 : R) :: b :: rest) =
      Var (pre ++ a :: c :: b :: rest) := by
  unfold Var
  have h_filter_zero :
      (pre ++ a :: (0 : R) :: b :: rest).filter (· ≠ 0) =
      (pre.filter (· ≠ 0)) ++ a :: b :: (rest.filter (· ≠ 0)) := by
    rw [List.filter_append]
    congr 1
    simp [ha, hb]
  have h_filter_c :
      (pre ++ a :: c :: b :: rest).filter (· ≠ 0) =
      (pre.filter (· ≠ 0)) ++ a :: c :: b :: (rest.filter (· ≠ 0)) := by
    rw [List.filter_append]
    congr 1
    simp [ha, hb, hc]
  rw [h_filter_zero, h_filter_c]
  exact (varNonzero_eq_after_insertion (pre.filter (· ≠ 0)) a c b
    (rest.filter (· ≠ 0)) hc h_opp).symm

/-- **Cascade triple lemma.** For a triple `[p, q, r] ++ L` where
    `p, r` are nonzero with opposite signs and `q` is anything (zero or
    nonzero), `Var (p :: q :: r :: L) = 1 + Var (r :: L)`.

    Used to peel off cascade triples in the `varAt` perturbation
    induction: at a cascade-zero point `a` with `q = Q.eval a = 0` and
    `r = -(P%Q).eval a = -p`, the contribution `[p, 0, -p]` filters to
    `[p, -p]` (1 sign change). At the perturbed point `a'` (q nonzero
    of either sign), the triple `[p, q, -p']` (with `p'` close to `p`)
    contributes exactly one sign change, regardless of `q`'s sign,
    since `[p, q]` and `[q, -p']` indicators sum to `1`. -/
private lemma Var_cons_three_cascade
    (p q r : R) (L : List R) (hp : p ≠ 0) (hr : r ≠ 0) (hpr : p * r < 0) :
    Var (p :: q :: r :: L) = 1 + Var (r :: L) := by
  classical
  rw [Var, Var]
  have h_filter2 : ((r :: L).filter (· ≠ 0) : List R) =
      r :: (L.filter (· ≠ 0)) :=
    List.filter_cons_of_pos (by simpa)
  rw [h_filter2]
  by_cases hq : q = 0
  · subst hq
    have h_filter1 : ((p :: (0 : R) :: r :: L).filter (· ≠ 0) : List R) =
        p :: r :: (L.filter (· ≠ 0)) := by
      simp [hp, hr]
    rw [h_filter1, varNonzero_cons_cons, if_pos hpr]
  · have h_filter1 : ((p :: q :: r :: L).filter (· ≠ 0) : List R) =
        p :: q :: r :: (L.filter (· ≠ 0)) := by
      simp [hp, hq, hr]
    rw [h_filter1]
    rw [varNonzero_insert_between_opposite p q r
      (L.filter (· ≠ 0)) hq hpr]
    rw [varNonzero_cons_cons, if_pos hpr]

/-- **`varAt` cascade triple lemma.** Polynomial form of
    `Var_cons_three_cascade`. For polynomials `P, Q, S` and an extended
    point `t` with `P` and `S` nonzero-evaluating at `t` of opposite
    signs, `varAt (P :: Q :: S :: L) t = 1 + varAt (S :: L) t`. -/
private lemma varAt_cons_three_cascade
    (P₁ P₂ P₃ : R[X]) (L : List R[X]) (t : ExtendedPoint R)
    (hP₁ : ExtendedPoint.evalPoly P₁ t ≠ 0)
    (hP₃ : ExtendedPoint.evalPoly P₃ t ≠ 0)
    (h_opp : ExtendedPoint.evalPoly P₁ t * ExtendedPoint.evalPoly P₃ t < 0) :
    varAt (P₁ :: P₂ :: P₃ :: L) t = 1 + varAt (P₃ :: L) t := by
  unfold varAt
  simp only [List.map_cons]
  exact Var_cons_three_cascade _ _ _ _ hP₁ hP₃ h_opp

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **`evalPoly` at `posInf` is nonzero for nonzero polynomials.** -/
private lemma evalPoly_posInf_ne_zero_of_ne_zero (P : R[X]) (hP : P ≠ 0) :
    ExtendedPoint.evalPoly P ExtendedPoint.posInf ≠ 0 := by
  show P.leadingCoeff ≠ 0
  exact mt Polynomial.leadingCoeff_eq_zero.mp hP

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **`evalPoly` at `negInf` is nonzero for nonzero polynomials.** -/
private lemma evalPoly_negInf_ne_zero_of_ne_zero (P : R[X]) (hP : P ≠ 0) :
    ExtendedPoint.evalPoly P ExtendedPoint.negInf ≠ 0 := by
  show (-1 : R) ^ P.natDegree * P.leadingCoeff ≠ 0
  apply mul_ne_zero
  · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · exact mt Polynomial.leadingCoeff_eq_zero.mp hP

/-- **`varAt` invariance under finite-endpoint right-perturbation.**
    Given `a < a'` such that for every nonzero `SRemS_i` (`i ∈ ℕ`)
    there is no root in the half-open interval `(a, a']`, and `n` past
    the end of the SRemS sequence, the `varAt` count is invariant
    under replacing the finite endpoint `a` with `a'`.

    The proof is by strong induction on `n`, mirroring the inductive
    structure of `theorem_2_58_no_SRemS_root_at_endpoints` but with
    cascade-zero handling at non-perturbed endpoints. The two sub-cases
    in the inductive step are:

    * `Q.eval a ≠ 0` (standard): use `varAt_cons_cons_of_ne_zero` at
      both `a` and `a'`, applying sign preservation for the indicator
      term and the IH for the tail.
    * `Q.eval a = 0` (cascade): peel off `[P, Q, -(P%Q)]` via the
      cascade-triple lemma `Var_cons_three_cascade` at both `a` and
      `a'`, with `-(P%Q).eval a = -P.eval a` (by `eval_mod_at_root`)
      providing the opposite-sign neighbor. -/
private lemma varAt_finite_perturb_eq
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (a a' : R) (haa' : a < a')
    (h_aP : P.eval a ≠ 0)
    (h_no_root_Ioc : ∀ i : ℕ, SRemS P Q i = 0 ∨
        ∀ x : R, a < x → x ≤ a' → (SRemS P Q i).eval x ≠ 0)
    (n : ℕ) (hn : SRemS P Q n = 0) :
    varAt (SRemSList P Q n) (.finite a) =
      varAt (SRemSList P Q n) (.finite a') := by
  classical
  induction n using Nat.strong_induction_on generalizing P Q with
  | _ n ih =>
    match n, hn with
    | 0, _ => rfl
    | 1, hn1 =>
      have hQ : Q = 0 := hn1
      subst hQ
      show Var [P.eval a] = Var [P.eval a']
      rw [Var_singleton, Var_singleton]
    | k + 2, hn2 =>
      by_cases hQ : Q = 0
      · subst hQ
        -- SRemSList P 0 (k+2) = P :: List.replicate (k+1) 0
        have h_list : SRemSList P (0 : R[X]) (k + 2) =
            P :: List.replicate (k + 1) (0 : R[X]) := by
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
      · -- Q ≠ 0.
        -- Extract evaluations: P(a) ≠ 0 (given), P(a') ≠ 0 (no root in (a, a']).
        have hP_a' : P.eval a' ≠ 0 := by
          rcases h_no_root_Ioc 0 with h_zero | h_no_root
          · -- SRemS P Q 0 = P. If 0, contradicts h_aP via eval at a.
            have hP : P = 0 := h_zero
            subst hP
            exact absurd (Polynomial.eval_zero) h_aP
          · exact h_no_root a' haa' le_rfl
        have hQ_a' : Q.eval a' ≠ 0 := by
          rcases h_no_root_Ioc 1 with h_zero | h_no_root
          · -- SRemS P Q 1 = Q. If 0, contradicts hQ.
            exact absurd (show Q = 0 from h_zero) hQ
          · exact h_no_root a' haa' le_rfl
        -- Tail hypothesis for IH:
        have h_no_root_Ioc_tail :
            ∀ i : ℕ, SRemS Q (-(P % Q)) i = 0 ∨
              ∀ x : R, a < x → x ≤ a' →
                (SRemS Q (-(P % Q)) i).eval x ≠ 0 := by
          intro i
          rw [← SRemS_succ P Q hQ]
          exact h_no_root_Ioc (i + 1)
        have h_tail_zero : SRemS Q (-(P % Q)) (k + 1) = 0 := by
          rw [← SRemS_succ P Q hQ]
          exact hn2
        by_cases hQa : Q.eval a = 0
        · -- Cascade case. First show -(P % Q) ≠ 0 (else P(a) = 0).
          have h_S2_step : SRemS P Q 2 = -(P % Q) := by simp [SRemS, hQ]
          have hPQ_ne : -(P % Q) ≠ 0 := by
            intro hPQ
            have h_S2_zero : SRemS P Q 2 = 0 := h_S2_step.trans hPQ
            exact h_aP (SRemS_eval_cascade_terminal P Q a 1 hQ h_S2_zero hQa)
          -- Need k ≥ 1 (else SRemS_2 = 0 from hn, but hPQ_ne contradicts).
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            -- hn2 : SRemS P Q 2 = 0. But h_S2_step gives = -(P%Q), contradicting hPQ_ne.
            have : (-(P % Q) : R[X]) = 0 := h_S2_step.symm.trans hn2
            exact absurd this hPQ_ne
          · -- k ≥ 1. Apply cascade triple lemma at a and a'.
            obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.pos_iff_ne_zero.mp hkpos)
            -- Decompose SRemSList using SRemSList_succ twice.
            have h_decomp : SRemSList P Q (k' + 1 + 2) =
                P :: Q :: SRemSList (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) := by
              rw [show k' + 1 + 2 = (k' + 2) + 1 from rfl, SRemSList_succ P Q hQ]
              rw [show k' + 2 = (k' + 1) + 1 from rfl,
                  SRemSList_succ Q (-(P % Q)) hPQ_ne]
            -- Decompose the inner list further.
            have h_decomp_inner : SRemSList (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) =
                (-(P % Q)) ::
                  (List.range k').map (fun i =>
                    SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (i + 1)) := by
              exact SRemSList_head_decomp (-(P % Q)) (-(Q % (-(P % Q)))) k'
            -- Eval setup: -(P%Q).eval a = -P.eval a.
            have h_PmodQ_eval_a : (-(P % Q)).eval a = -P.eval a := by
              rw [Polynomial.eval_neg, eval_mod_at_root P Q a hQa]
            -- IH application setup: shift indices by 2.
            have h_no_root_Ioc_new :
                ∀ i : ℕ, SRemS (-(P % Q)) (-(Q % (-(P % Q)))) i = 0 ∨
                  ∀ x : R, a < x → x ≤ a' →
                    (SRemS (-(P % Q)) (-(Q % (-(P % Q)))) i).eval x ≠ 0 := by
              intro i
              rw [← SRemS_succ Q (-(P % Q)) hPQ_ne]
              rw [← SRemS_succ P Q hQ]
              exact h_no_root_Ioc (i + 2)
            have h_tail_zero_new :
                SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) = 0 := by
              rw [← SRemS_succ Q (-(P % Q)) hPQ_ne]
              rw [← SRemS_succ P Q hQ]
              exact hn2
            have h_aP_new : (-(P % Q)).eval a ≠ 0 := by
              rw [h_PmodQ_eval_a]
              exact neg_ne_zero.mpr h_aP
            -- IH gives the equality on the inner SRemSList.
            have h_ih_inner :=
              ih (k' + 1) (by omega) (-(P % Q)) (-(Q % (-(P % Q))))
                h_aP_new h_no_root_Ioc_new h_tail_zero_new
            -- Now compute both sides via cascade triple lemma.
            -- LHS at a: P :: Q :: -(P%Q) :: tail; with Q.eval a = 0, P*r < 0 holds.
            -- RHS at a': P :: Q :: -(P%Q) :: tail; with Q.eval a' ≠ 0, P*r < 0 still holds (signs preserved).
            -- First, set up signs at a'.
            have h_PmodQ_a'_ne : (-(P % Q)).eval a' ≠ 0 := by
              rcases h_no_root_Ioc_new 0 with h_zero | h_no_root
              · -- SRemS_new 0 = -(P%Q). If 0, contradicts hPQ_ne.
                exact absurd (h_zero : -(P % Q) = 0) hPQ_ne
              · exact h_no_root a' haa' le_rfl
            have hP_pmodQ_opp_at_a : P.eval a * (-(P % Q)).eval a < 0 := by
              rw [h_PmodQ_eval_a]
              -- P.eval a * -P.eval a = -(P.eval a)^2 < 0.
              have h_sq_pos : 0 < P.eval a * P.eval a :=
                mul_self_pos.mpr h_aP
              have h_eq : P.eval a * -P.eval a = -(P.eval a * P.eval a) := by ring
              rw [h_eq]; linarith
            -- Sign preservation for P and -(P%Q) gives same opposite-sign relation at a'.
            have h_no_root_P : ∀ x : R, a < x → x < a' → P.eval x ≠ 0 := by
              intro x hax hxa'
              rcases h_no_root_Ioc 0 with h_zero | h_no_root
              · exact absurd (h_zero : P = 0)
                  (fun h => h_aP (by subst h; exact Polynomial.eval_zero))
              · exact h_no_root x hax (le_of_lt hxa')
            have h_no_root_PmodQ :
                ∀ x : R, a < x → x < a' → (-(P % Q)).eval x ≠ 0 := by
              intro x hax hxa'
              rcases h_no_root_Ioc_new 0 with h_zero | h_no_root
              · exact absurd (h_zero : -(P % Q) = 0) hPQ_ne
              · exact h_no_root x hax (le_of_lt hxa')
            have h_sign_P : SignType.sign (P.eval a) = SignType.sign (P.eval a') :=
              sign_eval_eq_of_no_root_Ioo hIVP P haa' h_aP hP_a' h_no_root_P
            have h_sign_PmodQ : SignType.sign ((-(P % Q)).eval a) =
                SignType.sign ((-(P % Q)).eval a') :=
              sign_eval_eq_of_no_root_Ioo hIVP (-(P % Q)) haa'
                h_aP_new h_PmodQ_a'_ne h_no_root_PmodQ
            have hP_pmodQ_opp_at_a' : P.eval a' * (-(P % Q)).eval a' < 0 := by
              -- sign at a' equals sign at a, which is < 0.
              have h_signs_eq : SignType.sign (P.eval a * (-(P % Q)).eval a) =
                  SignType.sign (P.eval a' * (-(P % Q)).eval a') := by
                rw [sign_mul, sign_mul, h_sign_P, h_sign_PmodQ]
              rw [← sign_eq_neg_one_iff] at hP_pmodQ_opp_at_a ⊢
              rw [← h_signs_eq]; exact hP_pmodQ_opp_at_a
            -- Decompose, then apply varAt_cons_three_cascade at both points.
            have h_full_decomp : SRemSList P Q (k' + 1 + 2) =
                P :: Q :: (-(P % Q)) ::
                  ((List.range k').map (fun i =>
                    SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (i + 1))) := by
              rw [h_decomp, h_decomp_inner]
            rw [h_full_decomp]
            -- Apply cascade triple lemma at .finite a (Q.eval a = 0 case).
            have h_PmodQ_a_ne : ExtendedPoint.evalPoly (-(P % Q))
                (ExtendedPoint.finite a) ≠ 0 := by
              show (-(P % Q)).eval a ≠ 0
              exact h_aP_new
            have h_PmodQ_a'_ne_ext :
                ExtendedPoint.evalPoly (-(P % Q)) (ExtendedPoint.finite a') ≠ 0 := by
              show (-(P % Q)).eval a' ≠ 0
              exact h_PmodQ_a'_ne
            have h_aP_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a) ≠ 0 :=
              h_aP
            have hP_a'_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a') ≠ 0 :=
              hP_a'
            have h_opp_a_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a) *
                ExtendedPoint.evalPoly (-(P % Q)) (ExtendedPoint.finite a) < 0 :=
              hP_pmodQ_opp_at_a
            have h_opp_a'_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a') *
                ExtendedPoint.evalPoly (-(P % Q)) (ExtendedPoint.finite a') < 0 :=
              hP_pmodQ_opp_at_a'
            rw [varAt_cons_three_cascade P Q (-(P % Q)) _ _ h_aP_ext
              h_PmodQ_a_ne h_opp_a_ext]
            rw [varAt_cons_three_cascade P Q (-(P % Q)) _ _ hP_a'_ext
              h_PmodQ_a'_ne_ext h_opp_a'_ext]
            congr 1
            -- Goal: varAt (-(P%Q) :: tail) at a = varAt (...) at a'.
            -- This is the IH inner equality after rewriting with h_decomp_inner.
            rw [show (-(P % Q)) :: ((List.range k').map fun i =>
                SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (i + 1)) =
                SRemSList (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) from
              h_decomp_inner.symm]
            exact h_ih_inner
        · -- Standard case: Q(a) ≠ 0, Q(a') ≠ 0.
          -- Apply lemma_2_59_pointwise at (.finite a) and (.finite a').
          have h_step_a : varAt (SRemSList P Q (k + 2)) (.finite a) =
              varAt (SRemSList Q (-(P % Q)) (k + 1)) (.finite a) +
                (if P.eval a * Q.eval a < 0 then 1 else 0) := by
            have := lemma_2_59_pointwise P Q hQ k (.finite a) h_aP hQa
            convert this using 1
          have h_step_a' : varAt (SRemSList P Q (k + 2)) (.finite a') =
              varAt (SRemSList Q (-(P % Q)) (k + 1)) (.finite a') +
                (if P.eval a' * Q.eval a' < 0 then 1 else 0) := by
            have := lemma_2_59_pointwise P Q hQ k (.finite a') hP_a' hQ_a'
            convert this using 1
          rw [h_step_a, h_step_a']
          -- Sign preservation: P(a)Q(a) and P(a')Q(a') have same sign.
          have h_sign_PQ : (if P.eval a * Q.eval a < 0 then (1 : ℕ) else 0) =
              (if P.eval a' * Q.eval a' < 0 then 1 else 0) := by
            have h_no_root_P : ∀ x : R, a < x → x < a' → P.eval x ≠ 0 := by
              intro x hax hxa'
              rcases h_no_root_Ioc 0 with h_zero | h_no_root
              · exact absurd (h_zero : P = 0) (fun h => by subst h; exact h_aP Polynomial.eval_zero)
              · exact h_no_root x hax (le_of_lt hxa')
            have h_no_root_Q : ∀ x : R, a < x → x < a' → Q.eval x ≠ 0 := by
              intro x hax hxa'
              rcases h_no_root_Ioc 1 with h_zero | h_no_root
              · exact absurd (h_zero : Q = 0) hQ
              · exact h_no_root x hax (le_of_lt hxa')
            have h_sign_P : SignType.sign (P.eval a) = SignType.sign (P.eval a') :=
              sign_eval_eq_of_no_root_Ioo hIVP P haa' h_aP hP_a' h_no_root_P
            have h_sign_Q : SignType.sign (Q.eval a) = SignType.sign (Q.eval a') :=
              sign_eval_eq_of_no_root_Ioo hIVP Q haa' hQa hQ_a' h_no_root_Q
            -- sign(PQ) = sign P * sign Q. Combine.
            have h_signPQa : SignType.sign (P.eval a * Q.eval a) =
                SignType.sign (P.eval a' * Q.eval a') := by
              rw [sign_mul, sign_mul, h_sign_P, h_sign_Q]
            -- (PQ < 0) ↔ sign(PQ) = -1. Use sign equality.
            have h_iff : (P.eval a * Q.eval a < 0) ↔ (P.eval a' * Q.eval a' < 0) := by
              rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h_signPQa]
            split_ifs with h1 h2 h3
            · rfl
            · exact absurd (h_iff.mp h1) h2
            · exact absurd (h_iff.mpr h3) h1
            · rfl
          rw [h_sign_PQ]
          -- Apply IH to (Q, -(P%Q)) at index k+1.
          have h_ih := ih (k + 1) (by omega) Q (-(P % Q))
            hQa h_no_root_Ioc_tail h_tail_zero
          rw [h_ih]

/-- **`varAt` invariance under finite-endpoint left-perturbation.**
    Symmetric counterpart of `varAt_finite_perturb_eq`: when the
    perturbation `a'` is to the left of the original endpoint `a`
    (`a' < a`), with no SRemS roots in the half-open interval `[a', a)`
    and `P.eval a ≠ 0`, the `varAt` count is preserved. -/
private lemma varAt_finite_perturb_eq_left
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (a' a : R) (haa' : a' < a)
    (h_aP : P.eval a ≠ 0)
    (h_no_root_Ico : ∀ i : ℕ, SRemS P Q i = 0 ∨
        ∀ x : R, a' ≤ x → x < a → (SRemS P Q i).eval x ≠ 0)
    (n : ℕ) (hn : SRemS P Q n = 0) :
    varAt (SRemSList P Q n) (.finite a) =
      varAt (SRemSList P Q n) (.finite a') := by
  classical
  induction n using Nat.strong_induction_on generalizing P Q with
  | _ n ih =>
    match n, hn with
    | 0, _ => rfl
    | 1, hn1 =>
      have hQ : Q = 0 := hn1
      subst hQ
      show Var [P.eval a] = Var [P.eval a']
      rw [Var_singleton, Var_singleton]
    | k + 2, hn2 =>
      by_cases hQ : Q = 0
      · subst hQ
        have h_list : SRemSList P (0 : R[X]) (k + 2) =
            P :: List.replicate (k + 1) (0 : R[X]) := by
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
      · have hP_a' : P.eval a' ≠ 0 := by
          rcases h_no_root_Ico 0 with h_zero | h_no_root
          · have hP : P = 0 := h_zero
            subst hP
            exact absurd (Polynomial.eval_zero) h_aP
          · exact h_no_root a' le_rfl haa'
        have hQ_a' : Q.eval a' ≠ 0 := by
          rcases h_no_root_Ico 1 with h_zero | h_no_root
          · exact absurd (show Q = 0 from h_zero) hQ
          · exact h_no_root a' le_rfl haa'
        have h_no_root_Ico_tail :
            ∀ i : ℕ, SRemS Q (-(P % Q)) i = 0 ∨
              ∀ x : R, a' ≤ x → x < a →
                (SRemS Q (-(P % Q)) i).eval x ≠ 0 := by
          intro i
          rw [← SRemS_succ P Q hQ]
          exact h_no_root_Ico (i + 1)
        have h_tail_zero : SRemS Q (-(P % Q)) (k + 1) = 0 := by
          rw [← SRemS_succ P Q hQ]
          exact hn2
        by_cases hQa : Q.eval a = 0
        · have h_S2_step : SRemS P Q 2 = -(P % Q) := by simp [SRemS, hQ]
          have hPQ_ne : -(P % Q) ≠ 0 := by
            intro hPQ
            have h_S2_zero : SRemS P Q 2 = 0 := h_S2_step.trans hPQ
            exact h_aP (SRemS_eval_cascade_terminal P Q a 1 hQ h_S2_zero hQa)
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            have : (-(P % Q) : R[X]) = 0 := h_S2_step.symm.trans hn2
            exact absurd this hPQ_ne
          · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.pos_iff_ne_zero.mp hkpos)
            have h_decomp : SRemSList P Q (k' + 1 + 2) =
                P :: Q :: SRemSList (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) := by
              rw [show k' + 1 + 2 = (k' + 2) + 1 from rfl, SRemSList_succ P Q hQ]
              rw [show k' + 2 = (k' + 1) + 1 from rfl,
                  SRemSList_succ Q (-(P % Q)) hPQ_ne]
            have h_decomp_inner : SRemSList (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) =
                (-(P % Q)) ::
                  (List.range k').map (fun i =>
                    SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (i + 1)) := by
              exact SRemSList_head_decomp (-(P % Q)) (-(Q % (-(P % Q)))) k'
            have h_PmodQ_eval_a : (-(P % Q)).eval a = -P.eval a := by
              rw [Polynomial.eval_neg, eval_mod_at_root P Q a hQa]
            have h_no_root_Ico_new :
                ∀ i : ℕ, SRemS (-(P % Q)) (-(Q % (-(P % Q)))) i = 0 ∨
                  ∀ x : R, a' ≤ x → x < a →
                    (SRemS (-(P % Q)) (-(Q % (-(P % Q)))) i).eval x ≠ 0 := by
              intro i
              rw [← SRemS_succ Q (-(P % Q)) hPQ_ne]
              rw [← SRemS_succ P Q hQ]
              exact h_no_root_Ico (i + 2)
            have h_tail_zero_new :
                SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) = 0 := by
              rw [← SRemS_succ Q (-(P % Q)) hPQ_ne]
              rw [← SRemS_succ P Q hQ]
              exact hn2
            have h_aP_new : (-(P % Q)).eval a ≠ 0 := by
              rw [h_PmodQ_eval_a]
              exact neg_ne_zero.mpr h_aP
            have h_ih_inner :=
              ih (k' + 1) (by omega) (-(P % Q)) (-(Q % (-(P % Q))))
                h_aP_new h_no_root_Ico_new h_tail_zero_new
            have h_PmodQ_a'_ne : (-(P % Q)).eval a' ≠ 0 := by
              rcases h_no_root_Ico_new 0 with h_zero | h_no_root
              · exact absurd (h_zero : -(P % Q) = 0) hPQ_ne
              · exact h_no_root a' le_rfl haa'
            have hP_pmodQ_opp_at_a : P.eval a * (-(P % Q)).eval a < 0 := by
              rw [h_PmodQ_eval_a]
              have h_sq_pos : 0 < P.eval a * P.eval a :=
                mul_self_pos.mpr h_aP
              have h_eq : P.eval a * -P.eval a = -(P.eval a * P.eval a) := by ring
              rw [h_eq]; linarith
            have h_no_root_P : ∀ x : R, a' < x → x < a → P.eval x ≠ 0 := by
              intro x ha'x hxa
              rcases h_no_root_Ico 0 with h_zero | h_no_root
              · exact absurd (h_zero : P = 0)
                  (fun h => h_aP (by subst h; exact Polynomial.eval_zero))
              · exact h_no_root x (le_of_lt ha'x) hxa
            have h_no_root_PmodQ :
                ∀ x : R, a' < x → x < a → (-(P % Q)).eval x ≠ 0 := by
              intro x ha'x hxa
              rcases h_no_root_Ico_new 0 with h_zero | h_no_root
              · exact absurd (h_zero : -(P % Q) = 0) hPQ_ne
              · exact h_no_root x (le_of_lt ha'x) hxa
            -- Sign preservation: signs at a and a' agree (over open interval (a', a)).
            have h_sign_P : SignType.sign (P.eval a') = SignType.sign (P.eval a) :=
              sign_eval_eq_of_no_root_Ioo hIVP P haa' hP_a' h_aP h_no_root_P
            have h_sign_PmodQ : SignType.sign ((-(P % Q)).eval a') =
                SignType.sign ((-(P % Q)).eval a) :=
              sign_eval_eq_of_no_root_Ioo hIVP (-(P % Q)) haa'
                h_PmodQ_a'_ne h_aP_new h_no_root_PmodQ
            have hP_pmodQ_opp_at_a' : P.eval a' * (-(P % Q)).eval a' < 0 := by
              have h_signs_eq : SignType.sign (P.eval a' * (-(P % Q)).eval a') =
                  SignType.sign (P.eval a * (-(P % Q)).eval a) := by
                rw [sign_mul, sign_mul, h_sign_P, h_sign_PmodQ]
              rw [← sign_eq_neg_one_iff] at hP_pmodQ_opp_at_a ⊢
              rw [h_signs_eq]; exact hP_pmodQ_opp_at_a
            have h_full_decomp : SRemSList P Q (k' + 1 + 2) =
                P :: Q :: (-(P % Q)) ::
                  ((List.range k').map (fun i =>
                    SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (i + 1))) := by
              rw [h_decomp, h_decomp_inner]
            rw [h_full_decomp]
            have h_PmodQ_a_ne_ext : ExtendedPoint.evalPoly (-(P % Q))
                (ExtendedPoint.finite a) ≠ 0 := h_aP_new
            have h_PmodQ_a'_ne_ext :
                ExtendedPoint.evalPoly (-(P % Q)) (ExtendedPoint.finite a') ≠ 0 :=
              h_PmodQ_a'_ne
            have h_aP_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a) ≠ 0 :=
              h_aP
            have hP_a'_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a') ≠ 0 :=
              hP_a'
            have h_opp_a_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a) *
                ExtendedPoint.evalPoly (-(P % Q)) (ExtendedPoint.finite a) < 0 :=
              hP_pmodQ_opp_at_a
            have h_opp_a'_ext : ExtendedPoint.evalPoly P (ExtendedPoint.finite a') *
                ExtendedPoint.evalPoly (-(P % Q)) (ExtendedPoint.finite a') < 0 :=
              hP_pmodQ_opp_at_a'
            rw [varAt_cons_three_cascade P Q (-(P % Q)) _ _ h_aP_ext
              h_PmodQ_a_ne_ext h_opp_a_ext]
            rw [varAt_cons_three_cascade P Q (-(P % Q)) _ _ hP_a'_ext
              h_PmodQ_a'_ne_ext h_opp_a'_ext]
            congr 1
            rw [show (-(P % Q)) :: ((List.range k').map fun i =>
                SRemS (-(P % Q)) (-(Q % (-(P % Q)))) (i + 1)) =
                SRemSList (-(P % Q)) (-(Q % (-(P % Q)))) (k' + 1) from
              h_decomp_inner.symm]
            exact h_ih_inner
        · have h_step_a : varAt (SRemSList P Q (k + 2)) (.finite a) =
              varAt (SRemSList Q (-(P % Q)) (k + 1)) (.finite a) +
                (if P.eval a * Q.eval a < 0 then 1 else 0) := by
            have := lemma_2_59_pointwise P Q hQ k (.finite a) h_aP hQa
            convert this using 1
          have h_step_a' : varAt (SRemSList P Q (k + 2)) (.finite a') =
              varAt (SRemSList Q (-(P % Q)) (k + 1)) (.finite a') +
                (if P.eval a' * Q.eval a' < 0 then 1 else 0) := by
            have := lemma_2_59_pointwise P Q hQ k (.finite a') hP_a' hQ_a'
            convert this using 1
          rw [h_step_a, h_step_a']
          have h_sign_PQ : (if P.eval a * Q.eval a < 0 then (1 : ℕ) else 0) =
              (if P.eval a' * Q.eval a' < 0 then 1 else 0) := by
            have h_no_root_P : ∀ x : R, a' < x → x < a → P.eval x ≠ 0 := by
              intro x ha'x hxa
              rcases h_no_root_Ico 0 with h_zero | h_no_root
              · exact absurd (h_zero : P = 0) (fun h => by subst h; exact h_aP Polynomial.eval_zero)
              · exact h_no_root x (le_of_lt ha'x) hxa
            have h_no_root_Q : ∀ x : R, a' < x → x < a → Q.eval x ≠ 0 := by
              intro x ha'x hxa
              rcases h_no_root_Ico 1 with h_zero | h_no_root
              · exact absurd (h_zero : Q = 0) hQ
              · exact h_no_root x (le_of_lt ha'x) hxa
            have h_sign_P : SignType.sign (P.eval a') = SignType.sign (P.eval a) :=
              sign_eval_eq_of_no_root_Ioo hIVP P haa' hP_a' h_aP h_no_root_P
            have h_sign_Q : SignType.sign (Q.eval a') = SignType.sign (Q.eval a) :=
              sign_eval_eq_of_no_root_Ioo hIVP Q haa' hQ_a' hQa h_no_root_Q
            have h_signPQa : SignType.sign (P.eval a * Q.eval a) =
                SignType.sign (P.eval a' * Q.eval a') := by
              rw [sign_mul, sign_mul, ← h_sign_P, ← h_sign_Q]
            have h_iff : (P.eval a * Q.eval a < 0) ↔ (P.eval a' * Q.eval a' < 0) := by
              rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h_signPQa]
            split_ifs with h1 h2 h3
            · rfl
            · exact absurd (h_iff.mp h1) h2
            · exact absurd (h_iff.mpr h3) h1
            · rfl
          rw [h_sign_PQ]
          have h_ih := ih (k + 1) (by omega) Q (-(P % Q))
            hQa h_no_root_Ico_tail h_tail_zero
          rw [h_ih]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Helper: SRemS sequence stabilizes past `n` once `SRemS P Q n = 0`.** -/
private lemma SRemS_zero_of_ge (P Q : R[X]) (hP : P ≠ 0) (n : ℕ)
    (hn : SRemS P Q n = 0) : ∀ m ≥ n, SRemS P Q m = 0 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : P = 0 := hn
    exact absurd this hP
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    intro m hm
    exact SRemS_zero_ge P Q k hn m hm

omit [IsStrictOrderedRing R] in
/-- **Helper: from `S`-avoidance to the `∀ i`-disjunctive condition.** -/
private lemma strong_hyp_of_S_avoidance
    (P Q : R[X]) (hP : P ≠ 0) (n : ℕ) (hn : SRemS P Q n = 0)
    (pt : R)
    (h_avoid : ∀ p ∈ ((Finset.range n).image (SRemS P Q)).filter (· ≠ 0),
        p.eval pt ≠ 0) :
    ∀ i : ℕ, SRemS P Q i = 0 ∨ (SRemS P Q i).eval pt ≠ 0 := by
  intro i
  by_cases hi : n ≤ i
  · left; exact SRemS_zero_of_ge P Q hP n hn i hi
  · push Not at hi
    by_cases hSi : SRemS P Q i = 0
    · left; exact hSi
    · right
      apply h_avoid
      apply Finset.mem_filter.mpr
      refine ⟨?_, hSi⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

omit [IsStrictOrderedRing R] in
/-- **Helper: lift `S`-avoidance to the extended `evalPoly` form.** -/
private lemma strong_hyp_of_S_avoidance_ext
    (P Q : R[X]) (hP : P ≠ 0) (n : ℕ) (hn : SRemS P Q n = 0)
    (pt : R)
    (h_avoid : ∀ p ∈ ((Finset.range n).image (SRemS P Q)).filter (· ≠ 0),
        p.eval pt ≠ 0) :
    ∀ i : ℕ, SRemS P Q i = 0 ∨
      ExtendedPoint.evalPoly (SRemS P Q i) (.finite pt) ≠ 0 :=
  strong_hyp_of_S_avoidance P Q hP n hn pt h_avoid

omit [IsStrictOrderedRing R] in
/-- **Helper: at `.posInf`/`.negInf`, every nonzero polynomial evaluates
    nonzero, hence the strong hypothesis is automatic. -/
private lemma strong_hyp_at_infinity
    (P Q : R[X]) (b : ExtendedPoint R)
    (hb_inf : b = .posInf ∨ b = .negInf) :
    ∀ i : ℕ, SRemS P Q i = 0 ∨
      ExtendedPoint.evalPoly (SRemS P Q i) b ≠ 0 := by
  intro i
  by_cases hSi : SRemS P Q i = 0
  · left; exact hSi
  · right
    rcases hb_inf with h | h
    · subst h; exact evalPoly_posInf_ne_zero_of_ne_zero _ hSi
    · subst h; exact evalPoly_negInf_ne_zero_of_ne_zero _ hSi

/-- **WLOG perturbation lemma for theorem_2_58.** Given the BPR-faithful
    hypotheses (`P ≠ 0`, `a < b`, `P` not vanishing at `a, b`), there
    exist perturbed endpoints `a', b'` with the strong "no SRemS root
    at endpoints" property AND with `varAt`/`cauchyIndexOn` matching
    those at the original `(a, b)`. -/
lemma theorem_2_58_perturbation_exists
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly P a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly P b ≠ 0)
    (n : ℕ) (hn : SRemS P Q n = 0) :
    ∃ a' b' : ExtendedPoint R,
      ExtendedPoint.Lt a' b' ∧
      (∀ i : ℕ, SRemS P Q i = 0 ∨
        ExtendedPoint.evalPoly (SRemS P Q i) a' ≠ 0) ∧
      (∀ i : ℕ, SRemS P Q i = 0 ∨
        ExtendedPoint.evalPoly (SRemS P Q i) b' ≠ 0) ∧
      varAt (SRemSList P Q n) a = varAt (SRemSList P Q n) a' ∧
      varAt (SRemSList P Q n) b = varAt (SRemSList P Q n) b' ∧
      cauchyIndexOn Q P a b = cauchyIndexOn Q P a' b' := by
  classical
  -- Set of nonzero SRemS polynomials within [0, n).
  set S : Finset R[X] :=
    ((Finset.range n).image (SRemS P Q)).filter (· ≠ 0) with hS_def
  have hS_ne : ∀ p ∈ S, p ≠ 0 := fun p hp => (Finset.mem_filter.mp hp).2
  -- Case split on `(a, b)`.
  cases a with
  | posInf => exact absurd hab (by cases b <;> simp [ExtendedPoint.Lt])
  | negInf =>
    cases b with
    | negInf => exact absurd hab (by simp [ExtendedPoint.Lt])
    | posInf =>
      -- Case (1): no perturbation.
      refine ⟨.negInf, .posInf, hab, ?_, ?_, rfl, rfl, rfl⟩
      · exact strong_hyp_at_infinity P Q .negInf (Or.inr rfl)
      · exact strong_hyp_at_infinity P Q .posInf (Or.inl rfl)
    | finite b_val =>
      -- Case (2): perturb b only.
      have h_β_lt : b_val - 1 < b_val := by linarith
      obtain ⟨b'_val, h_β_lt_b', h_b'_lt_b, h_avoid_b⟩ :=
        exists_gt_not_root_in_Ioo (b_val - 1) b_val h_β_lt S hS_ne
      refine ⟨.negInf, .finite b'_val, (by trivial : ExtendedPoint.Lt
        (R := R) .negInf (.finite b'_val)), ?_, ?_, rfl, ?_, ?_⟩
      · exact strong_hyp_at_infinity P Q .negInf (Or.inr rfl)
      · exact strong_hyp_of_S_avoidance_ext P Q hP n hn b'_val
          (fun p hp => h_avoid_b p hp b'_val le_rfl h_b'_lt_b)
      · -- varAt at .finite b = varAt at .finite b'_val (right perturbation).
        have h_no_root_Ico : ∀ i : ℕ, SRemS P Q i = 0 ∨
            ∀ x : R, b'_val ≤ x → x < b_val → (SRemS P Q i).eval x ≠ 0 := by
          intro i
          by_cases hi : n ≤ i
          · left; exact SRemS_zero_of_ge P Q hP n hn i hi
          · push Not at hi
            by_cases hSi : SRemS P Q i = 0
            · left; exact hSi
            · right
              intro x hx_ge hx_lt
              apply h_avoid_b (SRemS P Q i)
              · apply Finset.mem_filter.mpr
                refine ⟨?_, hSi⟩
                exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
              · exact hx_ge
              · exact hx_lt
        exact varAt_finite_perturb_eq_left hIVP P Q b'_val b_val h_b'_lt_b
          h_bP h_no_root_Ico n hn
      · -- cauchyIndexOn invariance.
        apply cauchyIndexOn_eq_of_same_P_roots
        intro x hx
        have hP_root : P.eval x = 0 := (Polynomial.mem_roots hP).mp hx
        constructor
        · intro hx_in
          show x ∈ Set.Iio b'_val
          show x < b'_val
          -- x ∈ openInterval .negInf (.finite b_val) = Set.Iio b_val.
          have hx_lt_b : x < b_val := hx_in
          -- If x ∈ [b'_val, b_val), then P has a root in [b'_val, b_val), contradicting h_avoid_b for P.
          by_contra h_not_lt
          push Not at h_not_lt
          -- h_not_lt : b'_val ≤ x. Combined with hx_lt_b: b'_val ≤ x < b_val.
          -- P ∈ S (since SRemS P Q 0 = P is nonzero and 0 < n; we need n ≥ 1).
          -- Actually we need n ≥ 1 for P ∈ image.
          -- If n = 0: SRemS P Q 0 = P = 0 contradicts hP.
          rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
          · subst hn_zero
            exact absurd (hn : P = 0) hP
          · have hP_in_S : P ∈ S := by
              apply Finset.mem_filter.mpr
              refine ⟨?_, hP⟩
              exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn_pos, rfl⟩
            exact h_avoid_b P hP_in_S x h_not_lt hx_lt_b hP_root
        · intro hx_in
          show x ∈ Set.Iio b_val
          show x < b_val
          have hx_lt_b' : x < b'_val := hx_in
          linarith
  | finite a_val =>
    cases b with
    | negInf => exact absurd hab (by simp [ExtendedPoint.Lt])
    | posInf =>
      -- Case (3): perturb a only.
      have h_α_gt : a_val < a_val + 1 := by linarith
      obtain ⟨a'_val, h_a_lt_a', h_a'_lt_α, h_avoid_a⟩ :=
        exists_lt_not_root_in_Ioo a_val (a_val + 1) h_α_gt S hS_ne
      refine ⟨.finite a'_val, .posInf, (by trivial : ExtendedPoint.Lt
        (R := R) (.finite a'_val) .posInf), ?_, ?_, ?_, rfl, ?_⟩
      · exact strong_hyp_of_S_avoidance_ext P Q hP n hn a'_val
          (fun p hp => h_avoid_a p hp a'_val h_a_lt_a' le_rfl)
      · exact strong_hyp_at_infinity P Q .posInf (Or.inl rfl)
      · -- varAt invariance.
        have h_no_root_Ioc : ∀ i : ℕ, SRemS P Q i = 0 ∨
            ∀ x : R, a_val < x → x ≤ a'_val → (SRemS P Q i).eval x ≠ 0 := by
          intro i
          by_cases hi : n ≤ i
          · left; exact SRemS_zero_of_ge P Q hP n hn i hi
          · push Not at hi
            by_cases hSi : SRemS P Q i = 0
            · left; exact hSi
            · right
              intro x hx_gt hx_le
              apply h_avoid_a (SRemS P Q i)
              · apply Finset.mem_filter.mpr
                refine ⟨?_, hSi⟩
                exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
              · exact hx_gt
              · exact hx_le
        exact varAt_finite_perturb_eq hIVP P Q a_val a'_val h_a_lt_a'
          h_aP h_no_root_Ioc n hn
      · -- cauchyIndexOn invariance.
        apply cauchyIndexOn_eq_of_same_P_roots
        intro x hx
        have hP_root : P.eval x = 0 := (Polynomial.mem_roots hP).mp hx
        constructor
        · intro hx_in
          show x ∈ Set.Ioi a'_val
          show a'_val < x
          have hx_gt_a : a_val < x := hx_in
          by_contra h_not_gt
          push Not at h_not_gt
          rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
          · subst hn_zero
            exact absurd (hn : P = 0) hP
          · have hP_in_S : P ∈ S := by
              apply Finset.mem_filter.mpr
              refine ⟨?_, hP⟩
              exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn_pos, rfl⟩
            exact h_avoid_a P hP_in_S x hx_gt_a h_not_gt hP_root
        · intro hx_in
          show x ∈ Set.Ioi a_val
          show a_val < x
          have ha'_lt_x : a'_val < x := hx_in
          linarith
    | finite b_val =>
      -- Case (4): perturb both.
      have h_a_lt_b : a_val < b_val := hab
      obtain ⟨a'_val, h_a_lt_a', h_a'_lt_b, h_avoid_a⟩ :=
        exists_lt_not_root_in_Ioo a_val b_val h_a_lt_b S hS_ne
      obtain ⟨b'_val, h_a'_lt_b', h_b'_lt_b, h_avoid_b⟩ :=
        exists_gt_not_root_in_Ioo a'_val b_val h_a'_lt_b S hS_ne
      have h_a'_lt_b' : a'_val < b'_val := h_a'_lt_b'
      refine ⟨.finite a'_val, .finite b'_val, h_a'_lt_b', ?_, ?_, ?_, ?_, ?_⟩
      · exact strong_hyp_of_S_avoidance_ext P Q hP n hn a'_val
          (fun p hp => h_avoid_a p hp a'_val h_a_lt_a' le_rfl)
      · exact strong_hyp_of_S_avoidance_ext P Q hP n hn b'_val
          (fun p hp => h_avoid_b p hp b'_val le_rfl h_b'_lt_b)
      · -- varAt at .finite a = varAt at .finite a'_val.
        have h_no_root_Ioc : ∀ i : ℕ, SRemS P Q i = 0 ∨
            ∀ x : R, a_val < x → x ≤ a'_val → (SRemS P Q i).eval x ≠ 0 := by
          intro i
          by_cases hi : n ≤ i
          · left; exact SRemS_zero_of_ge P Q hP n hn i hi
          · push Not at hi
            by_cases hSi : SRemS P Q i = 0
            · left; exact hSi
            · right
              intro x hx_gt hx_le
              apply h_avoid_a (SRemS P Q i)
              · apply Finset.mem_filter.mpr
                refine ⟨?_, hSi⟩
                exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
              · exact hx_gt
              · exact hx_le
        exact varAt_finite_perturb_eq hIVP P Q a_val a'_val h_a_lt_a'
          h_aP h_no_root_Ioc n hn
      · -- varAt at .finite b = varAt at .finite b'_val.
        have h_no_root_Ico : ∀ i : ℕ, SRemS P Q i = 0 ∨
            ∀ x : R, b'_val ≤ x → x < b_val → (SRemS P Q i).eval x ≠ 0 := by
          intro i
          by_cases hi : n ≤ i
          · left; exact SRemS_zero_of_ge P Q hP n hn i hi
          · push Not at hi
            by_cases hSi : SRemS P Q i = 0
            · left; exact hSi
            · right
              intro x hx_ge hx_lt
              apply h_avoid_b (SRemS P Q i)
              · apply Finset.mem_filter.mpr
                refine ⟨?_, hSi⟩
                exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
              · exact hx_ge
              · exact hx_lt
        exact varAt_finite_perturb_eq_left hIVP P Q b'_val b_val h_b'_lt_b
          h_bP h_no_root_Ico n hn
      · -- cauchyIndexOn invariance.
        apply cauchyIndexOn_eq_of_same_P_roots
        intro x hx
        have hP_root : P.eval x = 0 := (Polynomial.mem_roots hP).mp hx
        rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
        · subst hn_zero
          exact absurd (hn : P = 0) hP
        · have hP_in_S : P ∈ S := by
            apply Finset.mem_filter.mpr
            refine ⟨?_, hP⟩
            exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn_pos, rfl⟩
          constructor
          · intro hx_in
            show x ∈ Set.Ioo a'_val b'_val
            obtain ⟨hx_gt_a, hx_lt_b⟩ := hx_in
            refine ⟨?_, ?_⟩
            · -- a'_val < x: avoid (a_val, a'_val] root.
              by_contra h_not_gt
              push Not at h_not_gt
              exact h_avoid_a P hP_in_S x hx_gt_a h_not_gt hP_root
            · -- x < b'_val: avoid [b'_val, b_val) root.
              by_contra h_not_lt
              push Not at h_not_lt
              exact h_avoid_b P hP_in_S x h_not_lt hx_lt_b hP_root
          · intro hx_in
            show x ∈ Set.Ioo a_val b_val
            obtain ⟨hx_gt_a', hx_lt_b'⟩ := hx_in
            refine ⟨?_, ?_⟩
            · linarith
            · linarith

/-- **BPR Theorem 2.58.** Let `P ≠ 0`, `Q ∈ R[X]` over a real closed
    field `R`, and let `a < b` in `R ∪ {±∞}` with `a, b` not roots of
    `P`. For any `n` past the end of the SRemS sequence,

    `Var(SRemSList P Q n; a, b) = Ind(Q/P; a, b)`.

    This is the BPR-faithful statement: the only hypotheses on the
    endpoints are that `P` does not vanish there. The proof reduces to
    `theorem_2_58_no_SRemS_root_at_endpoints` via the WLOG perturbation
    argument (BPR p.62): pick `a < a' < b' < b` so that `(a, a']` and
    `[b', b)` contain no root of any nonzero polynomial in the SRemS
    sequence. Then

    * `Ind(Q/P; a, b) = Ind(Q/P; a', b')` since the same `P`-roots lie
      in both open intervals;
    * `Var(SRemS; a) = Var(SRemS; a')` is invariant by the local triple
      analysis: at any `j ≥ 1` with `(SRemS_j)(a) = 0` and
      `SRemS_j ≠ 0` polynomial, the cascade lemmas
      `SRemS_eval_cascade` + `SRemS_eval_cascade_terminal` (proved
      above) plus `SRemS_eval_opposite_sign_at_zero` give
      `SRemS_{j-1}(a) = -(SRemS_{j+1}(a))` with both nonzero, so the
      filtered local Var contribution `(s, -s) ↦ 1` matches the
      perturbed `(s, ±, -s) ↦ 1` (always 1, regardless of the sign
      `±` taken by `SRemS_j(a')`).

    The existence + invariance portion of the WLOG argument is in
    `theorem_2_58_perturbation_exists`, which itself relies on the
    cascade and Var-invariance lemmas plus density and finiteness of
    root sets. -/
theorem theorem_2_58
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly P a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly P b ≠ 0)
    (n : ℕ) (hn : SRemS P Q n = 0) :
    ((varAt (SRemSList P Q n) a : ℤ) - (varAt (SRemSList P Q n) b : ℤ)) =
      cauchyIndexOn Q P a b := by
  obtain ⟨a', b', hab', hStrong_a, hStrong_b, hVar_a, hVar_b, hCauchy⟩ :=
    theorem_2_58_perturbation_exists hIVP P Q hP a b hab h_aP h_bP n hn
  rw [hVar_a, hVar_b, hCauchy]
  exact theorem_2_58_no_SRemS_root_at_endpoints hIVP P Q hP a' b' hab'
    hStrong_a hStrong_b n hn

end Azurite.BPR
