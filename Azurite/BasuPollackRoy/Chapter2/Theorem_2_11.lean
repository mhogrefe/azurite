import Azurite.BasuPollackRoy.Chapter2.Theorem_2_11_a_b
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_11_b_c
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_11_b_d
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_11_c_a
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_11_d_a
import Mathlib.Data.List.TFAE

/-!
# BPR Theorem 2.11: Characterizations of Real Closed Fields

**Theorem 2.11 (BPR).** If R is an ordered field, the following are equivalent:
- (a) R is real closed.
- (b) R[i] = R[X]/(X² + 1) is algebraically closed.
- (c) R has the intermediate value property.
- (d) R is a real field with no non-trivial real algebraic extension.

Note: BPR states this for a general field, but condition (c) requires a linear
order to state (the IVP involves `<`), and the b⇒c proof also uses the order.
The d⇒a direction (`theorem_2_11_d_a`) requires only `[Field R]`.
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Theorem 2.11.** For an ordered field R, the following are equivalent:
1. R is real closed.
2. R[i] is algebraically closed.
3. R has the intermediate value property.
4. R is a real field with no non-trivial real algebraic extension. -/
theorem theorem_2_11_tfae :
    [IsRealClosed R,
     IsAlgClosed (Ri R),
     Azurite.BPR.HasIntermediateValueProperty R,
     Azurite.BPR.HasNoNontrivialRealAlgebraicExtension R].TFAE := by
  tfae_have 1 → 2 := fun h => @isAlgClosed_Ri R _ h
  tfae_have 2 → 3 := fun h => @theorem_2_11_b_c R _ _ _ h
  tfae_have 3 → 1 := fun h => theorem_2_11_c_a h
  tfae_have 2 → 4 := fun h => @theorem_2_11_b_d R _ _ _ h
  tfae_have 4 → 1 := fun h => theorem_2_11_d_a h
  tfae_finish

end Azurite.BPR.Theorem2_11
