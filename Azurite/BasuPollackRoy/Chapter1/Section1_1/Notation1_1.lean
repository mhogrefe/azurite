import Azurite.BasuPollackRoy.Chapter1.Section1_1.Definitions

/-!
# Notation 1.1 — Zero Set

If `poly_set` is a finite subset of `C[X₁, …, Xₖ]`, the **set of zeros** of `poly_set`
in `Cᵏ` is

  Zer(poly_set, Cᵏ) = { x ∈ Cᵏ | ∀ P ∈ poly_set, P(x) = 0 }.

Mathlib already has `MvPolynomial.zeroLocus`, but it takes an `Ideal` rather than
a finite set of polynomials. We define `Zer` to match BPR's notation and prove
it equals Mathlib's `zeroLocus` applied to the spanned ideal.

In the same paragraph, BPR defines a subset `V ⊆ Cᵏ` to be an **algebraic set**
(or **algebraic subset**) if `V = Zer(poly_set, Cᵏ)` for some finite `poly_set`,
and observes that `Cᵏ` itself is algebraic (take `poly_set = ∅`).
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

/-- The set of common zeros of a finite set of polynomials `poly_set` in `Cᵏ`.
BPR notation: Zer(poly_set, Cᵏ). -/
def Zer (poly_set : Finset (MvPolynomial (Fin k) C)) : Set (Fin k → C) :=
  { x | ∀ P ∈ poly_set, MvPolynomial.eval x P = 0}

omit [IsAlgClosed C] in
/-- `Zer poly_set` equals Mathlib's `zeroLocus` of the ideal spanned by poly_set. -/
theorem zer_eq_zeroLocus (poly_set : Finset (MvPolynomial (Fin k) C)) :
    Zer poly_set = MvPolynomial.zeroLocus C (Ideal.span (↑poly_set : Set (MvPolynomial (Fin k) C))) := by
  ext x
  simp only [Zer, Set.mem_ofPred_eq, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    have eval_eq : ∀ q : MvPolynomial (Fin k) C,
        MvPolynomial.eval x q = (MvPolynomial.aeval x) q := by
      intro q; simp [MvPolynomial.aeval_def]
    rw [← eval_eq]
    induction hp using Submodule.span_induction with
    | mem q hq => exact h q (Finset.mem_coe.mp hq)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a q _ hq => rw [smul_eq_mul, map_mul, hq, mul_zero]
  · intro h p hp
    have := h p (Ideal.subset_span (Finset.mem_coe.mpr hp))
    simpa [MvPolynomial.aeval_def] using this

/-- A subset V of Cᵏ is algebraic if it is the zero set of some finite set of polynomials. -/
def IsAlgebraicSet (V : Set (Fin k → C)) : Prop :=
  ∃ poly_set : Finset (MvPolynomial (Fin k) C), V = Zer poly_set

omit [IsAlgClosed C] in
/-- Cᵏ is an algebraic set (take poly_set = ∅). -/
theorem isAlgebraicSet_univ : IsAlgebraicSet (Set.univ : Set (Fin k → C)) :=
  ⟨∅, by ext x; simp [Zer]⟩

end Azurite.BPR
