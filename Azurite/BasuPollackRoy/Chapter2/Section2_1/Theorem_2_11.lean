/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_a_b
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_c
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_d
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_c_a
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_d_a
import Mathlib.Data.List.TFAE

/-!
# BPR Theorem 2.11: Characterizations of Real Closed Fields

**Theorem 2.11 (BPR).** If R is a field, the following are equivalent:
- (a) R is real closed.
- (b) R is ordered and R[i] = R[X]/(X² + 1) is algebraically closed.
- (c) R has the intermediate value property
      (which presupposes a linear order on R).
- (d) R is a real field with no non-trivial real algebraic extension.

The "ordered" condition in (b) is an existential over the order; the order
in (c) is bound inside `HasIntermediateValueProperty`. Each implication is
proved in its own file:

- `Theorem_2_11_a_b` (a) ⇒ (b): builds the order from `IsRealClosed.toLinearOrder`
  and forwards `isAlgClosed_Ri`.
- `Theorem_2_11_b_c` (b) ⇒ (c): the IVP holds under the ordered field structure.
- `Theorem_2_11_c_a` (c) ⇒ (a).
- `Theorem_2_11_b_d` (b) ⇒ (d).
- `Theorem_2_11_d_a` (d) ⇒ (a).
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial Azurite.BPR

variable {R : Type*} [Field R]

/-- **BPR Theorem 2.11.** For a field R, the following are equivalent:
1. R is real closed.
2. R is ordered (admits some linear order making it a strictly ordered ring)
   and R[i] is algebraically closed.
3. R has the intermediate value property under some linear order making R
   a strictly ordered ring.
4. R is a real field with no non-trivial real algebraic extension.

The "ordered" content of (2) and (3) is an existential over the order; by
uniqueness of the compatible order on a real closed field
(`isRealClosed_le_unique`), the witness order is the canonical one supplied
by `IsRealClosed.toLinearOrder`. -/
theorem theorem_2_11_tfae :
    [IsRealClosed R,
     ∃ (lo : LinearOrder R) (h : @IsStrictOrderedRing R _ lo.toPartialOrder),
       letI : LinearOrder R := lo
       letI : @IsStrictOrderedRing R _ lo.toPartialOrder := h
       IsAlgClosed (Ri R),
     ∃ (lo : LinearOrder R) (h : @IsStrictOrderedRing R _ lo.toPartialOrder),
       @HasIntermediateValueProperty R _ lo h,
     HasNoNontrivialRealAlgebraicExtension R].TFAE := by
  tfae_have 1 → 2 := fun _ => by
    refine ⟨IsRealClosed.toLinearOrder, ?_, ?_⟩
    · let : LinearOrder R := IsRealClosed.toLinearOrder
      have : @IsOrderedRing R _ IsRealClosed.toLinearOrder.toPartialOrder :=
        IsRealClosed.toIsOrderedRing
      exact inferInstance
    · let : LinearOrder R := IsRealClosed.toLinearOrder
      exact isAlgClosed_Ri
  tfae_have 2 → 3 := fun ⟨lo, hlo, halgClosed⟩ => by
    let := lo
    let := hlo
    have := halgClosed
    exact ⟨lo, hlo, theorem_2_11_b_c⟩
  tfae_have 3 → 1 := fun ⟨lo, hlo, hIVP⟩ => by
    let := lo
    let := hlo
    exact theorem_2_11_c_a hIVP
  tfae_have 2 → 4 := fun ⟨lo, hlo, halgClosed⟩ => by
    let := lo
    let := hlo
    have := halgClosed
    exact theorem_2_11_b_d
  tfae_have 4 → 1 := theorem_2_11_d_a
  tfae_finish

end Azurite.BPR.Theorem2_11
