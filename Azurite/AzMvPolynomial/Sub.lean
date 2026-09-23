/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Subtraction for `AzMvPolynomial` via sorted merge.
-/
import Azurite.AzMvPolynomial.MergeSorted

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Ring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem neg_preserves_ne_zero : ∀ (x : R), x ≠ 0 → -x ≠ 0 :=
  fun _ h => neg_ne_zero.mpr h

/-- Subtract two `AzMvPolynomial`s by merging their sorted term lists,
    negating each coefficient from the second polynomial. -/
def AzMvPolynomial.sub (p q : AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  ⟨(mergeSorted Neg.neg neg_preserves_ne_zero p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]
      exact mergeSorted_sorted Neg.neg neg_preserves_ne_zero _ _ p.sorted q.sorted⟩

instance instAzMvPolynomialSub : Sub (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.sub⟩

end Azurite
