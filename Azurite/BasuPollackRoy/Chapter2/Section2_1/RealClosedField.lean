import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # BPR Section 2.1 — Real closed fields

**Definition (BPR p.38).** A field `R` is *real closed* if:

1. `R` is an ordered field whose positive cone is the set of squares
   `R^{(2)}`, i.e., `0 ≤ x ↔ IsSquare x`.
2. Every polynomial in `R[X]` of odd degree has a root in `R`.

**Mathlib correspondence.** Mathlib's `IsRealClosed R` (in
`Mathlib.FieldTheory.IsRealClosed.Basic`) uses an equivalent formulation
without requiring a linear order as data:

- `IsSemireal R`: `-1` is not a sum of squares.
- `IsSquare x ∨ IsSquare (-x)` for every `x`: every element or its negative
  is a square.
- Every odd-degree polynomial has a root.

The BPR ordered-field form is a special case:
`IsRealClosed.of_linearOrderedField` derives `IsRealClosed` from it.
Conversely, `IsRealClosed.nonneg_iff_isSquare` (for any linear order on an
`IsRealClosed` field) shows the positive cone equals the squares.
-/

namespace Azurite.BPR

open Polynomial

variable (R : Type*) [Field R]

/-- **BPR Definition (Real closed field).** `R` is a *real closed field* if it
    is an ordered field whose positive cone equals the set of squares, and
    every odd-degree polynomial has a root.

    We define this as `IsRealClosed R` from Mathlib, which uses an equivalent
    algebraically intrinsic formulation not requiring a linear order as data. -/
def IsRealClosedField : Prop := IsRealClosed R

/-- A real closed field is a real field. -/
theorem IsRealClosedField.isRealField [IsRealClosed R] : IsRealField R :=
  (isRealField_iff R).mpr (IsSemireal.not_isSumSq_neg_one R)

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR (ordered form).** Given an ordered field, `R` is real closed iff
    (1) the positive cone equals the squares, and (2) odd-degree polynomials
    have roots. -/
theorem isRealClosedField_iff :
    IsRealClosedField R ↔
    (∀ x : R, 0 ≤ x ↔ IsSquare x) ∧
    (∀ f : R[X], Odd f.natDegree → ∃ x, f.IsRoot x) := by
  constructor
  · intro h
    have : IsRealClosed R := h
    exact ⟨fun _ => IsRealClosed.nonneg_iff_isSquare,
           fun f hf => IsRealClosed.exists_isRoot_of_odd_natDegree hf⟩
  · intro ⟨hcone, hroots⟩
    exact IsRealClosed.of_linearOrderedField
      (fun hx => (hcone _).mp hx) (fun {f} hf => hroots f hf)

/-- In a real closed ordered field, `x ≥ 0 ↔ x` is a square. -/
theorem IsRealClosedField.nonneg_iff_isSquare [IsRealClosed R] {x : R} :
    0 ≤ x ↔ IsSquare x :=
  IsRealClosed.nonneg_iff_isSquare

end Azurite.BPR
