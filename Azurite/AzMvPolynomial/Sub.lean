/-
  Subtraction for AzMvPolynomial via sorted merge.

  Defined as `mergeSorted Neg.neg …`, which negates each coefficient
  from the second list before combining (i.e. subtraction).
-/
import Azurite.AzMvPolynomial.MergeSorted

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Ring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

omit [DecidableEq R] in
theorem neg_preserves_ne_zero : ∀ (x : R), x ≠ 0 → -x ≠ 0 :=
  fun _ h => neg_ne_zero.mpr h

/-- Subtract two `AzMvPolynomial`s by merging their sorted term lists,
    negating each coefficient from the second polynomial. -/
def AzMvPolynomial.sub (p q : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  ⟨(mergeSorted Neg.neg neg_preserves_ne_zero p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]
      exact mergeSorted_sorted Neg.neg neg_preserves_ne_zero _ _ p.sorted q.sorted⟩

instance : Sub (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.sub⟩

end Azurite
