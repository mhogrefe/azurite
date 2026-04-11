/-
  Addition for `AzMvPolynomialNew` via sorted merge.
-/
import Azurite.AzMvPolynomial.New.MergeSorted

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [Semiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem id_preserves_ne_zero_new : ∀ (x : R), x ≠ 0 → id x ≠ 0 :=
  fun _ h => h

/-- Add two `AzMvPolynomialNew`s by merging their sorted term lists. -/
def AzMvPolynomialNew.add (p q : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  ⟨(mergeSortedNew id id_preserves_ne_zero_new p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]
      exact mergeSortedNew_sorted id id_preserves_ne_zero_new _ _ p.sorted q.sorted⟩

instance : Add (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.add⟩

end Azurite
