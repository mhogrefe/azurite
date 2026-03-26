/-
  Addition for AzMvPolynomial via sorted merge.

  Defined as `mergeSorted id …`, which applies the identity function
  to the second list's coefficients (i.e. plain addition).
-/
import Azurite.AzMvPolynomial.MergeSorted

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

omit [DecidableEq R] in
theorem id_preserves_ne_zero : ∀ (x : R), x ≠ 0 → id x ≠ 0 :=
  fun _ h => h

/-- Add two `AzMvPolynomial`s by merging their sorted term lists. -/
def AzMvPolynomial.add (p q : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  ⟨(mergeSorted id id_preserves_ne_zero p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]
      exact mergeSorted_sorted id id_preserves_ne_zero _ _ p.sorted q.sorted⟩

instance : Add (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.add⟩

end Azurite
