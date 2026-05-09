import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Complex.Basic

/-! # BPR Section 2.1 — Exercise 2.6

Three claims:

1. A real field has characteristic 0.
2. The field ℂ of complex numbers is not a real field.
3. Every ordered field is a real field.

*Proofs.*
1. In a semireal ring, if `char R = p > 0` then `p = 0` in `R` and `p`
   is a sum of squares of `1`s, giving `0 = p ∈ ΣR^{(2)}` with
   `1 + p = 1 ≠ 0` — a contradiction. Mathlib derives `CharZero` from
   `IsSemireal` automatically.
2. In ℂ we have `i² = −1`, so `−1 = i·i + 0` is a sum of squares, hence
   `−1 ∈ Σℂ^{(2)}` and ℂ is not real.
3. In an ordered field, every sum of squares is non-negative, so
   `−1 < 0` cannot be a sum of squares. Mathlib provides a
   `IsSemireal` instance for any `[IsStrictOrderedRing]`.
-/

namespace Azurite.BPR

/-- **BPR Exercise 2.6(1).** A real field has characteristic 0.
    (This is a restatement of `isRealField_charZero`.) -/
theorem exercise_2_6_charZero {F : Type*} [Field F] (h : IsRealField F) : CharZero F :=
  haveI : IsSemireal F := h; inferInstance

/-- **BPR Exercise 2.6(2).** The field ℂ of complex numbers is not a real field.
    *Proof.* `i² = −1` in ℂ, so `−1 = i·i ∈ Σℂ^{(2)}`. -/
theorem exercise_2_6_complex_not_real : ¬ IsRealField ℂ := by
  rw [IsRealField, isSemireal_iff_not_isSumSq_neg_one]
  push Not
  have : (-1 : ℂ) = Complex.I * Complex.I := by simp
  rw [this]
  exact IsSumSq.mul_self _

/-- **BPR Exercise 2.6(3).** Every ordered field is a real field.
    *Proof.* Sums of squares are non-negative in an ordered ring, so `−1 < 0`
    cannot be a sum of squares. Mathlib provides the `IsSemireal` instance
    for `[IsStrictOrderedRing]`. -/
theorem exercise_2_6_ordered_is_real
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    IsRealField F :=
  haveI : IsSemireal F := inferInstance; this

end Azurite.BPR
