import Azurite.BasuPollackRoy.Chapter2.CauchyIndex

/-!
# BPR Tarski-query

For `P ≠ 0` and `Q` in `R[X]` (with `R` an ordered field), the
**Tarski-query** of `Q` for `P` on the open interval `(a, b) ⊆ R ∪ {±∞}` is

`TaQ(Q, P; a, b) = ∑_{x ∈ (a, b), P(x) = 0} sign(Q(x))`.

The Tarski-query of `Q` for `P` on all of `R` is `TaQ(Q, P) := TaQ(Q, P; −∞, +∞)`.

We expose:

* `tarskiQueryOn Q P a b` for the interval form, with `a, b : ExtendedPoint R`.
* `tarskiQuery Q P` for the full-line form, equal to
  `tarskiQueryOn Q P .negInf .posInf`.

The sum ranges over the (finitely many) elements of `P.roots.toFinset`
inside the open interval. Membership in the interval is not decidable
in general, so the definition is `noncomputable` and uses classical
decidability for the filter.
-/

open scoped Polynomial

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open Classical in
/-- **BPR Tarski-query.** The Tarski-query of `Q` for `P` on the open
    interval `(a, b)`, for `a, b : ExtendedPoint R`:
    `∑_{x ∈ (a, b), P(x) = 0} sign(Q(x))`. -/
noncomputable def tarskiQueryOn (Q P : R[X]) (a b : ExtendedPoint R) : ℤ :=
  let I := ExtendedPoint.openInterval a b
  ∑ x ∈ P.roots.toFinset.filter (fun x => x ∈ I),
    (SignType.sign (Q.eval x) : ℤ)

/-- **BPR Tarski-query.** The Tarski-query of `Q` for `P` on all of `R`,
    `TaQ(Q, P) := TaQ(Q, P; −∞, +∞)`. -/
noncomputable def tarskiQuery (Q P : R[X]) : ℤ :=
  tarskiQueryOn Q P .negInf .posInf

omit [IsStrictOrderedRing R] in
@[simp] theorem tarskiQuery_eq_tarskiQueryOn_negInf_posInf (Q P : R[X]) :
    tarskiQuery Q P = tarskiQueryOn Q P .negInf .posInf := rfl

omit [IsStrictOrderedRing R] in
open Classical in
/-- The Tarski-query rewritten as a difference of root counts:
    `TaQ(Q, P; a, b) = #{x ∈ (a, b) | P(x) = 0 ∧ Q(x) > 0}
                     − #{x ∈ (a, b) | P(x) = 0 ∧ Q(x) < 0}`.

    Each `P`-root in `(a, b)` contributes `+1`, `0`, or `−1` to the sum
    according to whether `Q(x) > 0`, `Q(x) = 0`, or `Q(x) < 0`. -/
theorem tarskiQueryOn_eq_card_pos_sub_card_neg (Q P : R[X]) (a b : ExtendedPoint R) :
    tarskiQueryOn Q P a b =
    ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧ 0 < Q.eval x)).card : ℤ) -
    ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧ Q.eval x < 0)).card : ℤ) := by
  classical
  unfold tarskiQueryOn
  set I := ExtendedPoint.openInterval a b with hI_def
  set S := P.roots.toFinset.filter (fun x => x ∈ I) with hS_def
  -- Pointwise: `sign(Q.eval x) = [0 < Q.eval x] − [Q.eval x < 0]`.
  have h_sign : ∀ x : R, (SignType.sign (Q.eval x) : ℤ) =
      (if 0 < Q.eval x then (1 : ℤ) else 0) -
      (if Q.eval x < 0 then (1 : ℤ) else 0) := by
    intro x
    rcases lt_trichotomy (Q.eval x) 0 with h | h | h
    · rw [sign_neg h, if_neg (asymm h), if_pos h]; rfl
    · rw [h]; simp
    · rw [sign_pos h, if_pos h, if_neg (asymm h)]; rfl
  rw [Finset.sum_congr rfl (fun x _ => h_sign x), Finset.sum_sub_distrib]
  -- Each indicator sum equals the card of the filter of `S` by the predicate.
  rw [show (∑ x ∈ S, if 0 < Q.eval x then (1 : ℤ) else 0)
        = ((S.filter (fun x => 0 < Q.eval x)).card : ℤ) by
      rw [← Finset.sum_filter]; simp,
    show (∑ x ∈ S, if Q.eval x < 0 then (1 : ℤ) else 0)
        = ((S.filter (fun x => Q.eval x < 0)).card : ℤ) by
      rw [← Finset.sum_filter]; simp]
  -- Identify the filtered Finsets with the target form.
  have h_pos_eq : S.filter (fun x => 0 < Q.eval x) =
      P.roots.toFinset.filter
        (fun x => x ∈ I ∧ 0 < Q.eval x) := by
    ext x
    simp only [Finset.mem_filter, hS_def, and_assoc]
  have h_neg_eq : S.filter (fun x => Q.eval x < 0) =
      P.roots.toFinset.filter
        (fun x => x ∈ I ∧ Q.eval x < 0) := by
    ext x
    simp only [Finset.mem_filter, hS_def, and_assoc]
  rw [h_pos_eq, h_neg_eq]

end Azurite.BPR
