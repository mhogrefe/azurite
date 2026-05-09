import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Complex.Basic

/-! # BPR Section 2.1 — Exercise 2.3: ℂ cannot be ordered

> Show that it is not possible to order the field of complex numbers
> ℂ so that it becomes an ordered field.

In any ordered field, `x² ≥ 0` for all `x`. But `i² = −1`, so we
would need `0 ≤ −1`, contradicting `−1 < 0`.
-/

namespace Azurite.BPR

open Complex in
/-- **BPR Exercise 2.3.** ℂ cannot be made into an ordered field. -/
theorem exercise_2_3 :
    ¬ ∃ (_ : LinearOrder ℂ), IsStrictOrderedRing ℂ := by
  rintro ⟨ord, hord⟩
  letI := ord; letI := hord
  have hsq : 0 ≤ I * I := mul_self_nonneg I
  rw [I_mul_I] at hsq
  exact not_le.mpr neg_one_lt_zero hsq

end Azurite.BPR
