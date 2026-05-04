import Azurite.BasuPollackRoy.Chapter1.Section1_2.Coprime
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Corollary1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Divisor
import Azurite.BasuPollackRoy.Chapter1.Section1_2.EuclideanDivision
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14Corollaries
import Azurite.BasuPollackRoy.Chapter1.Section1_2.PolynomialBasics
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_9
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_12
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Remark1_4
import Azurite.BasuPollackRoy.Chapter1.Section1_2.RootCharacterizations
import Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination
import Azurite.BasuPollackRoy.Chapter2.Section2_2

/-!
# BPR Lemma 2.59

Let `P ≠ 0` and `Q` be polynomials over an ordered field `R`, with
`R' = Rem(P, Q) = P % Q`. The signed remainder sequence of `P, Q` and the
signed remainder sequence of `Q, −R'` are related by an SRemS step:

  `SRemS(P, Q) i+1 = SRemS(Q, −R') i`  for all `i ≥ 0`,

i.e. `SRemS(Q, −R')` is the tail of `SRemS(P, Q)`. Letting
`σ(x) = sign(P(x)·Q(x))`, BPR Lemma 2.59 says: if `a, b ∈ R ∪ {±∞}` are
not roots of `P` (and not roots of `Q`):

* `Var(SRemS(P,Q); a, b) = Var(SRemS(Q,−R'); a, b)`  when `σ(a)·σ(b) = 1`;
* `Var(SRemS(P,Q); a, b) = Var(SRemS(Q,−R'); a, b) + σ(b)`  when `σ(a)·σ(b) = −1`.

The proof follows from the pointwise identity at any `x` with
`P(x)·Q(x) ≠ 0`:

* `Var(SRemS(P,Q); x) = Var(SRemS(Q,−R'); x) + 1`  if `P(x)·Q(x) < 0`,
* `Var(SRemS(P,Q); x) = Var(SRemS(Q,−R'); x)`      if `P(x)·Q(x) > 0`.

Subtracting the values at `b` from those at `a` gives the lemma.
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The first `n` terms of `SRemS P Q` packaged as a list. -/
noncomputable def SRemSList (P Q : K[X]) (n : ℕ) : List K[X] :=
  (List.range n).map (SRemS P Q)

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] lemma SRemSList_zero (P Q : K[X]) : SRemSList P Q 0 = [] := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] lemma SRemSList_one (P Q : K[X]) : SRemSList P Q 1 = [P] := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `Q % (-R) = Q % R` for polynomials over a field. -/
private lemma mod_neg (Q R : K[X]) : Q % (-R) = Q % R := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [Polynomial.mod_def, Polynomial.mod_def]; simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Local helper: explicit form of `SRemS` at index `n + 2` when the
    `(n+1)`-th term is nonzero. -/
private lemma SRemS_step_ne (P Q : K[X]) (n : ℕ)
    (h : SRemS P Q (n + 1) ≠ 0) :
    SRemS P Q (n + 2) = -(SRemS P Q n % SRemS P Q (n + 1)) := by
  classical
  simp [SRemS, h]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Local helper: explicit form of `SRemS` at index `n + 2` when the
    `(n+1)`-th term is zero. -/
private lemma SRemS_step_zero (P Q : K[X]) (n : ℕ)
    (h : SRemS P Q (n + 1) = 0) :
    SRemS P Q (n + 2) = 0 := by
  classical
  simp [SRemS, h]

omit [IsStrictOrderedRing K] in
/-- **Tail identity for the signed remainder sequence.** With `R' = P % Q`,
    `SRemS(Q, -R') i = SRemS(P, Q) (i+1)` for all `i ≥ 0`, assuming `Q ≠ 0`.

    The hypothesis `Q ≠ 0` is needed: when `Q = 0`, `SRemS(P, Q) 2 = 0`
    while `SRemS(Q, -P) 1 = -P` may be nonzero, so the identity fails. -/
lemma SRemS_succ (P Q : K[X]) (hQ : Q ≠ 0) (i : ℕ) :
    SRemS P Q (i + 1) = SRemS Q (-(P % Q)) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases i with _ | _ | j
    · rfl
    · show SRemS P Q 2 = -(P % Q)
      exact SRemS_step_ne P Q 0 hQ
    · have ih1 := ih (j + 1) (by omega)
      have ih2 := ih j (by omega)
      show SRemS P Q (j + 1 + 2) = SRemS Q (-(P % Q)) (j + 2)
      by_cases hQne : SRemS P Q (j + 1 + 1) = 0
      · -- Both sides are zero.
        have h_lhs : SRemS P Q (j + 1 + 2) = 0 := SRemS_step_zero P Q (j + 1) hQne
        have hQne' : SRemS Q (-(P % Q)) (j + 1) = 0 := by rw [← ih1]; exact hQne
        have h_rhs : SRemS Q (-(P % Q)) (j + 2) = 0 :=
          SRemS_step_zero Q (-(P % Q)) j hQne'
        rw [h_lhs, h_rhs]
      · have hQne' : SRemS Q (-(P % Q)) (j + 1) ≠ 0 := by rw [← ih1]; exact hQne
        rw [SRemS_step_ne P Q (j + 1) hQne, SRemS_step_ne Q (-(P % Q)) j hQne',
          ih1, ih2]

omit [IsStrictOrderedRing K] in
/-- **Head decomposition for `SRemSList`.** With `R' = P % Q` and `Q ≠ 0`,
    `SRemSList P Q (n+1) = P :: SRemSList Q (-R') n`. -/
lemma SRemSList_succ (P Q : K[X]) (hQ : Q ≠ 0) (n : ℕ) :
    SRemSList P Q (n + 1) = P :: SRemSList Q (-(P % Q)) n := by
  unfold SRemSList
  rw [List.range_succ_eq_map, List.map_cons]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  show SRemS P Q (i + 1) = SRemS Q (-(P % Q)) i
  exact SRemS_succ P Q hQ i

omit [IsStrictOrderedRing K] in
/-- **Var step under `cons`.** For values `a, b : K` with `a ≠ 0` and
    `b ≠ 0`, prepending `a` to `b :: L` adds `1` to `Var` exactly when
    `a · b < 0`. -/
lemma Var_cons_cons_of_ne_zero (a b : K) (L : List K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Var (a :: b :: L) = Var (b :: L) + (if a * b < 0 then 1 else 0) := by
  classical
  have hf_a : ((a :: b :: L).filter (· ≠ 0) : List K) =
      a :: ((b :: L).filter (· ≠ 0)) :=
    List.filter_cons_of_pos (by simpa)
  have hf_b : ((b :: L).filter (· ≠ 0) : List K) =
      b :: (L.filter (· ≠ 0)) :=
    List.filter_cons_of_pos (by simpa)
  rw [Var_eq_varNonzero_filter, Var_eq_varNonzero_filter,
    hf_a, hf_b, varNonzero_cons_cons]
  ring

omit [IsStrictOrderedRing K] in
/-- **`varAt` step under `cons`.** For polynomials `P, Q : K[X]` and
    `a : ExtendedPoint K` with `evalPoly P a ≠ 0` and `evalPoly Q a ≠ 0`:
    `varAt (P :: Q :: L) a = varAt (Q :: L) a + [evalPoly P a · evalPoly Q a < 0]`. -/
lemma varAt_cons_cons_of_ne_zero
    (P Q : K[X]) (L : List K[X]) (a : ExtendedPoint K)
    (hP : ExtendedPoint.evalPoly P a ≠ 0) (hQ : ExtendedPoint.evalPoly Q a ≠ 0) :
    varAt (P :: Q :: L) a =
      varAt (Q :: L) a +
        (if ExtendedPoint.evalPoly P a * ExtendedPoint.evalPoly Q a < 0 then 1 else 0) := by
  unfold varAt
  simp only [List.map_cons]
  exact Var_cons_cons_of_ne_zero _ _ _ hP hQ

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Helper: peel the head off `SRemSList`. This holds regardless of whether
    `Q = 0`, in contrast to `SRemSList_succ` (which uses the SRemS recursion). -/
lemma SRemSList_head_decomp (P Q : K[X]) (n : ℕ) :
    SRemSList P Q (n + 1) =
      P :: ((List.range n).map (fun i => SRemS P Q (i + 1))) := by
  unfold SRemSList
  rw [List.range_succ_eq_map, List.map_cons]
  congr 1
  rw [List.map_map]
  rfl

omit [IsStrictOrderedRing K] in
/-- **BPR Lemma 2.59 (pointwise form).** At any `x : ExtendedPoint K` such
    that `evalPoly P x ≠ 0` and `evalPoly Q x ≠ 0`, with `Q ≠ 0` (forced
    by `evalPoly Q x ≠ 0`), the sign-variation count of the signed remainder
    sequence of `P, Q` exceeds that of the signed remainder sequence of
    `Q, −Rem(P, Q)` by `1` if `evalPoly P x · evalPoly Q x < 0`, and by `0`
    otherwise. -/
theorem lemma_2_59_pointwise
    (P Q : K[X]) (hQ_ne : Q ≠ 0) (n : ℕ) (x : ExtendedPoint K)
    (hP : ExtendedPoint.evalPoly P x ≠ 0)
    (hQ : ExtendedPoint.evalPoly Q x ≠ 0) :
    varAt (SRemSList P Q (n + 2)) x =
      varAt (SRemSList Q (-(P % Q)) (n + 1)) x +
        (if ExtendedPoint.evalPoly P x * ExtendedPoint.evalPoly Q x < 0 then 1 else 0) := by
  -- Decompose `SRemSList P Q (n + 2) = P :: SRemSList Q (-(P%Q)) (n + 1)`.
  rw [SRemSList_succ P Q hQ_ne (n + 1)]
  -- Decompose `SRemSList Q (-(P%Q)) (n + 1) = Q :: tail`.
  set L_tail := (List.range n).map (fun i => SRemS Q (-(P % Q)) (i + 1)) with hL_tail_def
  have hL_eq : SRemSList Q (-(P % Q)) (n + 1) = Q :: L_tail :=
    SRemSList_head_decomp Q (-(P % Q)) n
  rw [hL_eq]
  exact varAt_cons_cons_of_ne_zero P Q L_tail x hP hQ

omit [IsStrictOrderedRing K] in
/-- **BPR Lemma 2.59.** If `a, b : ExtendedPoint K` satisfy
    `evalPoly P a · evalPoly Q a ≠ 0` and
    `evalPoly P b · evalPoly Q b ≠ 0`, then with
    `σ(t) = sign(evalPoly P t · evalPoly Q t)`, the change in
    `varAt (SRemSList P Q ·)` between `a` and `b` is the change in
    `varAt (SRemSList Q (-(P%Q)) ·)` between `a` and `b`, plus a
    correction `(σ(b) - σ(a))/2` ∈ `{−1, 0, 1}`:

    * if `σ(a) = σ(b)` (i.e. `σ(a) · σ(b) = 1`): no correction;
    * if `σ(a) ≠ σ(b)` (i.e. `σ(a) · σ(b) = -1`): correction is `σ(b)`. -/
theorem lemma_2_59
    (P Q : K[X]) (hQ_ne : Q ≠ 0) (n : ℕ) (a b : ExtendedPoint K)
    (haP : ExtendedPoint.evalPoly P a ≠ 0)
    (haQ : ExtendedPoint.evalPoly Q a ≠ 0)
    (hbP : ExtendedPoint.evalPoly P b ≠ 0)
    (hbQ : ExtendedPoint.evalPoly Q b ≠ 0) :
    ((varAt (SRemSList P Q (n + 2)) a : ℤ) -
        (varAt (SRemSList P Q (n + 2)) b : ℤ)) =
      ((varAt (SRemSList Q (-(P % Q)) (n + 1)) a : ℤ) -
          (varAt (SRemSList Q (-(P % Q)) (n + 1)) b : ℤ)) +
        ((if ExtendedPoint.evalPoly P a *
              ExtendedPoint.evalPoly Q a < 0 then (1 : ℤ) else 0) -
          (if ExtendedPoint.evalPoly P b *
                ExtendedPoint.evalPoly Q b < 0 then (1 : ℤ) else 0)) := by
  have ha := lemma_2_59_pointwise P Q hQ_ne n a haP haQ
  have hb := lemma_2_59_pointwise P Q hQ_ne n b hbP hbQ
  push_cast [ha, hb]
  ring

end Azurite.BPR
