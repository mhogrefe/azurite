/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Addition for `AzMvPolynomial` via sorted merge.
-/
import Azurite.AzMvPolynomial.MergeSorted

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem id_preserves_ne_zero : ∀ (x : R), x ≠ 0 → id x ≠ 0 :=
  fun _ h => h

/-- Add two `AzMvPolynomial`s by merging their sorted term lists. -/
def AzMvPolynomial.add (p q : AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  ⟨(mergeSorted id id_preserves_ne_zero p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]
      exact mergeSorted_sorted id id_preserves_ne_zero _ _ p.sorted q.sorted⟩

instance instAzMvPolynomialAdd : Add (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.add⟩

end Azurite
