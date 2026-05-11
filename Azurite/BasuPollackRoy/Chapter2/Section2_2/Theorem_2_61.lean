import Azurite.BasuPollackRoy.Chapter2.Section2_2.Proposition_2_57
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_58

/-!
# BPR Theorem 2.61 (Tarski's theorem)

For polynomials `P, Q` over a real closed field `R`, with `a < b` in
`R ∪ {±∞}` not roots of `P`,

`Var(SRemS(P, P'·Q); a, b) = TaQ(Q, P; a, b)`.

The proof is immediate from BPR Theorem 2.58 (`Var(SRemS) = Ind`) and
BPR Proposition 2.57 (`TaQ = Ind(P' · Q / P)`). To match BPR's statement
(no truncation index in the hypotheses), we prove the SRemS termination
bound `SRemS P Q (Q.natDegree + 2) = 0` and use it as the truncation
index automatically.
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **SRemS termination bound.** For any `P, Q : R[X]`, the signed
    remainder sequence reaches zero by index `Q.natDegree + 2`.

    Proof: If `SRemS P Q (k+1) ≠ 0`, then by the chain-of-degrees
    inequality `(SRemS P Q (k+1)).natDegree + k ≤ Q.natDegree` (induction
    on `k`). Applied at `k = Q.natDegree + 1` this would give
    `(SRemS P Q (Q.natDegree + 2)).natDegree ≤ -1`, contradicting
    `natDegree ≥ 0`. -/
theorem SRemS_eq_zero_natDegree_succ_succ (P Q : R[X]) :
    SRemS P Q (Q.natDegree + 2) = 0 := by
  classical
  -- Auxiliary chain inequality.
  have h_chain : ∀ k : ℕ, SRemS P Q (k + 1) ≠ 0 →
      (SRemS P Q (k + 1)).natDegree + k ≤ Q.natDegree := by
    intro k
    induction k with
    | zero =>
      intro _
      show Q.natDegree + 0 ≤ Q.natDegree
      simp
    | succ k ih =>
      intro h_ne_succ
      -- Normalize `k + 1 + 1` to `k + 2`.
      have h_ne_succ' : SRemS P Q (k + 2) ≠ 0 := h_ne_succ
      -- Cascade backward: SRemS_{k+1} must also be nonzero.
      have h_ne_k : SRemS P Q (k + 1) ≠ 0 := by
        intro h_zero
        exact h_ne_succ' (SRemS_zero_ge P Q k h_zero (k + 2) (by omega))
      have h_lt : (SRemS P Q (k + 2)).degree < (SRemS P Q (k + 1)).degree :=
        degree_SRemS_lt P Q k h_ne_k
      have h_nat_lt : (SRemS P Q (k + 2)).natDegree <
          (SRemS P Q (k + 1)).natDegree := by
        rw [Polynomial.degree_eq_natDegree h_ne_k,
            Polynomial.degree_eq_natDegree h_ne_succ'] at h_lt
        exact_mod_cast h_lt
      have ih' := ih h_ne_k
      show (SRemS P Q (k + 2)).natDegree + (k + 1) ≤ Q.natDegree
      omega
  -- Apply at k = Q.natDegree + 1.
  by_contra h_ne
  have := h_chain (Q.natDegree + 1) h_ne
  omega

/-- **BPR Theorem 2.61 (Tarski).** Let `P ≠ 0`, `Q ∈ R[X]` over a real
    closed field `R`, and `a < b` in `R ∪ {±∞}` not roots of `P`. Then

    `Var(SRemS(P, P'·Q); a, b) = TaQ(Q, P; a, b)`.

    Immediate from BPR Theorem 2.58 + Proposition 2.57. The truncation
    index is `(P' · Q).natDegree + 2`, automatically past the end of
    the SRemS sequence by `SRemS_eq_zero_natDegree_succ_succ`. -/
theorem theorem_2_61
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly P a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly P b ≠ 0) :
    ((varAt (SRemSList P (P.derivative * Q)
        ((P.derivative * Q).natDegree + 2)) a : ℤ) -
      (varAt (SRemSList P (P.derivative * Q)
        ((P.derivative * Q).natDegree + 2)) b : ℤ)) =
      tarskiQueryOn Q P a b := by
  have hn := SRemS_eq_zero_natDegree_succ_succ P (P.derivative * Q)
  rw [theorem_2_58 hIVP P (P.derivative * Q) hP a b hab h_aP h_bP _ hn]
  exact (proposition_2_57 hIVP Q P hP a b).symm

end Azurite.BPR
