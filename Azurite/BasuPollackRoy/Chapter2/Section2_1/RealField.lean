import Azurite.BasuPollackRoy.Chapter2.Section2_1.SumOfSquares
import Mathlib.Algebra.Ring.Semireal.Defs

/-! # BPR Section 2.1 — Real fields

**Definition (BPR p.37).** A field `K` is a *real field* if `−1 ∉ ΣK^{(2)}`,
i.e., `−1` cannot be expressed as a sum of squares in `K`.

In Mathlib this is `IsSemireal K` (from `Mathlib.Algebra.Ring.Semireal.Defs`),
defined by the equivalent condition `∀ s, IsSumSq s → 1 + s ≠ 0`.
Every ordered field is semireal.
-/

namespace Azurite.BPR

variable (F : Type*) [Field F]

/-- **BPR Definition (p.37).** A field `F` is a *real field* if `−1 ∉ ΣF^{(2)}`,
    i.e., `−1` cannot be expressed as a sum of squares in `F`.

    In Mathlib this is `IsSemireal F` (from `Mathlib.Algebra.Ring.Semireal.Defs`),
    which is defined by the equivalent condition `∀ s, IsSumSq s → 1 + s ≠ 0`.
    Every ordered field is semireal. -/
abbrev IsRealField : Prop := IsSemireal F

/-- A field is real iff `−1 ∉ ΣF^{(2)}`. -/
lemma isRealField_iff : IsRealField F ↔ ¬ IsSumSq (-1 : F) :=
  isSemireal_iff_not_isSumSq_neg_one

/-- A field is real iff `−1 ∉ ΣF^{(2)}` (stated using `sumOfSquares`). -/
lemma isRealField_iff_neg_one_notMem :
    IsRealField F ↔ (-1 : F) ∉ sumOfSquares F := by
  rw [isRealField_iff, Subsemiring.mem_sumSq]

/-- A real field has characteristic zero
    (Mathlib synthesizes `CharZero F` from `IsSemireal F`). -/
theorem isRealField_charZero (h : IsRealField F) : CharZero F :=
  haveI : IsSemireal F := h; inferInstance

end Azurite.BPR
