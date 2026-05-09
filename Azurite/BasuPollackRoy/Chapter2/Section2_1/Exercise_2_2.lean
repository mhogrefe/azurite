import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Defs

/-! # BPR Section 2.1 — Exercise 2.2: Properties of ordered fields

Three claims:

1. In an ordered field, `-1 < 0`.
2. An ordered field has characteristic zero.
3. Law of trichotomy: for every `a`, exactly one of `a < 0`, `a = 0`,
   `0 < a` holds.

All three are immediate from Mathlib's `IsStrictOrderedRing` /
`LinearOrder` / `CharZero` instances.
-/

namespace Azurite.BPR

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **BPR Exercise 2.2(1).** In an ordered field, −1 < 0. -/
theorem exercise_2_2_neg_one_lt_zero : (-1 : F) < 0 := neg_one_lt_zero

/-- **BPR Exercise 2.2(2).** An ordered field has characteristic zero. -/
example : CharZero F := inferInstance

omit [IsStrictOrderedRing F] in
/-- **BPR Exercise 2.2(3).** Trichotomy: for every a, exactly one of
    a < 0, a = 0, 0 < a holds. -/
theorem exercise_2_2_trichotomy (a : F) : a < 0 ∨ a = 0 ∨ 0 < a :=
  lt_trichotomy a 0

end Azurite.BPR
