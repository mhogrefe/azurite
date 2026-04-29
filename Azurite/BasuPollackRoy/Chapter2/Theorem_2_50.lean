import Azurite.BasuPollackRoy.Chapter2.Theorem_2_61

/-!
# BPR Theorem 2.50 (Sturm's theorem)

For `P ≠ 0` over a real closed field `R`, with `a < b` in `R ∪ {±∞}`
not roots of `P`,

`Var(SRemS(P, P'); a, b) = #{distinct roots of P in (a, b)}`.

The proof is immediate by taking `Q = 1` in BPR Theorem 2.61: with
`Q = 1`, `TaQ(1, P; a, b) = ∑_{x ∈ (a,b), P(x) = 0} sign(1) = ∑ 1 =
#{P-roots in (a, b)}`, and `P' · 1 = P'`.
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open Classical in
/-- **Tarski query with `Q = 1` counts `P`-roots in the interval.**
    Since `sign(1) = +1` everywhere, `TaQ(1, P; a, b)` collapses to
    `#{x ∈ (a, b) | P(x) = 0}`. -/
theorem tarskiQueryOn_one_eq_card_roots (P : R[X]) (a b : ExtendedPoint R) :
    tarskiQueryOn 1 P a b =
      ((P.roots.toFinset.filter
        (· ∈ ExtendedPoint.openInterval a b)).card : ℤ) := by
  rw [tarskiQueryOn_eq_card_pos_sub_card_neg]
  -- `(1 : R[X]).eval x = 1`, so `0 < 1` always and `1 < 0` never.
  have h_pos : P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          0 < (1 : R[X]).eval x) =
      P.roots.toFinset.filter (· ∈ ExtendedPoint.openInterval a b) := by
    apply Finset.filter_congr
    intro x _
    rw [Polynomial.eval_one]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, one_pos⟩⟩
  have h_neg : P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          (1 : R[X]).eval x < 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x _ ⟨_, h⟩
    rw [Polynomial.eval_one] at h
    exact absurd h (not_lt_of_gt one_pos)
  rw [h_pos, h_neg]
  simp

open Classical in
/-- **BPR Theorem 2.50 (Sturm's theorem).** Let `P ≠ 0` over a real
    closed field `R`, and `a < b` in `R ∪ {±∞}` with `a, b` not roots
    of `P`. Then

    `Var(SRemS(P, P'); a, b) = #{distinct roots of P in (a, b)}`.

    Immediate from BPR Theorem 2.61 with `Q = 1`. -/
theorem theorem_2_50
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly P a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly P b ≠ 0) :
    ((varAt (SRemSList P P.derivative
        (P.derivative.natDegree + 2)) a : ℤ) -
      (varAt (SRemSList P P.derivative
        (P.derivative.natDegree + 2)) b : ℤ)) =
      ((P.roots.toFinset.filter
        (· ∈ ExtendedPoint.openInterval a b)).card : ℤ) := by
  have h61 := theorem_2_61 hIVP P 1 hP a b hab h_aP h_bP
  rw [tarskiQueryOn_one_eq_card_roots] at h61
  rw [mul_one] at h61
  exact h61

end Azurite.BPR
