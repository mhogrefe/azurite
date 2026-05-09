import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_8
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealClosedField
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SumOfSquares
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # BPR Section 2.1 — Order structure on a real closed field

`IsRealClosed R` in Mathlib is a purely algebraic predicate (no built-in
order). The lemmas in this file bridge that algebraic notion to the ordered
notion `IsRealClosedField` of BPR:

* **Existence** (`IsRealClosed.toLinearOrder`,
  `IsRealClosed.toIsOrderedRing`). Build a `LinearOrder R` and the matching
  `IsOrderedRing R` from the sum-of-squares proper cone, extended to a total
  cone via Proposition 2.8. Both instances share the same total cone via
  `Classical.choose` so they are automatically compatible.

* **Uniqueness** (`isRealClosed_le_unique`). In a real closed field, any two
  compatible orderings necessarily agree, since both are characterised by
  `a ≤ b ↔ IsSquare (b - a)`, and `IsSquare` is purely algebraic.

These results are not numbered in BPR (BPR's `IsRealClosedField` already
presupposes an order); they are recorded here as the order-side counterpart of
the algebraic `IsRealClosed`.
-/

namespace Azurite.BPR

section IsRealClosedOrder

variable {R : Type*} [Field R] [IsRealClosed R]

private lemma isProperCone_sumOfSquares_realClosed :
    IsProperCone (sumOfSquares R) :=
  ⟨isCone_sumOfSquares (F := R),
   (isRealField_iff_neg_one_notMem R).mp (IsRealClosedField.isRealField R)⟩

-- The canonical total cone: the sum-of-squares cone extended to a total cone
-- via Prop. 2.8. Using `Classical.choose` ensures both instances share the
-- same cone and hence produce compatible orders.
private noncomputable def isRealClosed_totalCone : RingCone R :=
  Classical.choose (prop_2_8 isProperCone_sumOfSquares_realClosed)

private lemma isRealClosed_totalCone_total :
    HasMemOrNegMem (isRealClosed_totalCone (R := R)) :=
  (Classical.choose_spec (prop_2_8 isProperCone_sumOfSquares_realClosed)).2

/-- A real closed field carries a noncomputable linear order, with
    `a ≤ b ↔ b - a` lies in the total cone extending `ΣR^{(2)}`. -/
noncomputable instance IsRealClosed.toLinearOrder : LinearOrder R :=
  haveI : DecidablePred (· ∈ (isRealClosed_totalCone (R := R)).toAddGroupCone) :=
    Classical.decPred _
  haveI : HasMemOrNegMem (isRealClosed_totalCone (R := R)).toAddGroupCone :=
    ⟨fun a => (isRealClosed_totalCone_total (R := R)).mem_or_neg_mem a⟩
  LinearOrder.mkOfAddGroupCone (isRealClosed_totalCone (R := R)).toAddGroupCone

/-- The linear order on a real closed field is compatible with the ring structure. -/
noncomputable instance IsRealClosed.toIsOrderedRing :
    @IsOrderedRing R _ IsRealClosed.toLinearOrder.toPartialOrder :=
  IsOrderedRing.mkOfCone (isRealClosed_totalCone (R := R))

end IsRealClosedOrder

section UniqueOrder

/-- In a real closed field with a given compatible ordering, `a ≤ b` iff `b - a` is a square.
    This is the key lemma: since `IsSquare` is order-independent, any two orderings
    satisfying this must agree. -/
private lemma isRealClosed_characterize_le
    {R : Type*} [Field R] [IsRealClosed R]
    (lo : LinearOrder R) (hlo : @IsStrictOrderedRing R _ lo.toPartialOrder)
    {a b : R} :
    @LE.le R lo.toLE a b ↔ IsSquare (b - a) := by
  letI : LinearOrder R := lo
  letI : IsStrictOrderedRing R := hlo
  exact sub_nonneg.symm.trans IsRealClosed.nonneg_iff_isSquare

/-- **Uniqueness of the order on a real closed field.**

Any two linear orderings making `R` into a strictly ordered ring must agree on every
comparison `a ≤ b`.

**Proof.** In any ordered field, `a ≤ b ↔ 0 ≤ b - a`, and in a real closed field
`0 ≤ x ↔ IsSquare x`. Since `IsSquare` is purely algebraic (independent of the ordering),
both orderings satisfy `a ≤ b ↔ IsSquare (b - a)` and must agree.

Equivalently: the positive cone of any compatible ordering necessarily contains `R^{(2)}`
(squares are always nonneg in an ordered ring); the real closed condition forces the positive
cone to be *exactly* `R^{(2)}`, leaving no room for a second ordering. -/
theorem isRealClosed_le_unique
    {R : Type*} [Field R] [IsRealClosed R]
    (lo₁ lo₂ : LinearOrder R)
    (h₁ : @IsStrictOrderedRing R _ lo₁.toPartialOrder)
    (h₂ : @IsStrictOrderedRing R _ lo₂.toPartialOrder)
    {a b : R} :
    @LE.le R lo₁.toLE a b ↔ @LE.le R lo₂.toLE a b :=
  (isRealClosed_characterize_le lo₁ h₁).trans (isRealClosed_characterize_le lo₂ h₂).symm

end UniqueOrder

end Azurite.BPR
