/-
  Subtraction for `AzMvPolynomialNew` via sorted merge.
-/
import Azurite.AzMvPolynomial.New.MergeSorted

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [Ring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem neg_preserves_ne_zero_new : ∀ (x : R), x ≠ 0 → -x ≠ 0 :=
  fun _ h => neg_ne_zero.mpr h

/-- Subtract two `AzMvPolynomialNew`s by merging their sorted term lists,
    negating each coefficient from the second polynomial. -/
def AzMvPolynomialNew.sub (p q : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  ⟨(mergeSortedNew Neg.neg neg_preserves_ne_zero_new p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]
      exact mergeSortedNew_sorted Neg.neg neg_preserves_ne_zero_new _ _ p.sorted q.sorted⟩

instance : Sub (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.sub⟩

end Azurite
