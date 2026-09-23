import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1

/-!
# BPR Section 2.3 — Zero sets as zero sets of a single polynomial

An important way in which the real closed case differs from the algebraically
closed case is that the common zeros of a finite set of polynomials
`𝒫 ⊆ R[X₁, …, Xₖ]` are also the zeros of a *single* polynomial:

  Q  :=  ∑ P ∈ 𝒫, P²

since in a linearly ordered field a sum of squares is zero iff each summand is
zero. So every algebraic set of `Rᵏ` is the zero set of a single polynomial.
-/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Over a linearly ordered field, the common zeros of a finite set of
polynomials `poly_set` coincide with the zero set of the single polynomial
`∑ P ∈ poly_set, P²`. -/
theorem zer_eq_zer_singleton_sumSq
    (poly_set : Finset (MvPolynomial (Fin k) R)) :
    Zer poly_set = Zer {∑ P ∈ poly_set, P ^ 2} := by
  ext x
  simp only [Zer, Set.mem_ofPred_eq, Finset.mem_singleton, forall_eq,
    map_sum, map_pow]
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro P hP
    rw [h P hP]; ring
  · intro h P hP
    have hsq : (eval x P) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun Q _ => sq_nonneg _)).mp h P hP
    exact sq_eq_zero_iff.mp hsq

/-- Every algebraic set of `Rᵏ` is the zero set of a *single* polynomial. -/
theorem IsAlgebraicSet.exists_singleton
    {V : Set (Fin k → R)} (hV : IsAlgebraicSet V) :
    ∃ Q : MvPolynomial (Fin k) R, V = Zer {Q} := by
  obtain ⟨poly_set, rfl⟩ := hV
  exact ⟨∑ P ∈ poly_set, P ^ 2, zer_eq_zer_singleton_sumSq poly_set⟩

end Azurite.BPR
