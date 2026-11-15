/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanPi
import Azurite.AzFloat.Equiv.AtanWithPeriod
import Azurite.AzFloat.Equiv.AtanRatWithPeriod

/-!
# Equivalence: `arctan (x) / π`

`Spec.atanPi : EReal → Option EReal` (`±1/2` at `±∞`), `Spec.atanWithPeriod_two`,
`atanPiPrecRound_eq_liftVal : atanPiPrecRound x p mode = liftVal Spec.atanPi x p mode` and
`atanPiRatPrecRound_eq : atanPiRatPrecRound q p mode = roundVal p mode (Spec.atanPi q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `arctan (a) / π`: `±1/2` at `±∞`. -/
noncomputable def atanPi (a : EReal) : Option EReal :=
  some (if a = ⊤ then ((1 / 2 : ℝ) : EReal) else if a = ⊥ then ((-(1 / 2) : ℝ) : EReal)
    else ((Real.arctan a.toReal / Real.pi : ℝ) : EReal))

theorem atanPi_coe (r : ℝ) : atanPi (r : EReal) = some ((Real.arctan r / Real.pi : ℝ) : EReal) := by
  unfold atanPi
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem atanPi_top : atanPi ⊤ = some ((1 / 2 : ℝ) : EReal) := by
  unfold atanPi
  rw [ite_eq_left rfl]

@[simp] theorem atanPi_bot : atanPi ⊥ = some ((-(1 / 2) : ℝ) : EReal) := by
  unfold atanPi
  rw [ite_eq_right (by simp), ite_eq_left rfl]

/-- `arctan (a) / π` is the period-`2` case of `atanWithPeriod`. -/
theorem atanWithPeriod_two (a : EReal) : atanWithPeriod a 2 = atanPi a := by
  have hpi := Real.pi_pos
  induction a using EReal.rec with
  | bot =>
    rw [atanWithPeriod_bot, atanPi_bot]
    norm_num
  | top =>
    rw [atanWithPeriod_top, atanPi_top]
    norm_num
  | coe r =>
    rw [atanWithPeriod_coe, atanPi_coe]
    congr 2
    push_cast
    field_simp

end Spec

/-- **`arctan (x) / π` is correctly rounded.** -/
theorem atanPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atanPiPrecRound x p mode = liftVal Spec.atanPi x p mode := by
  unfold atanPiPrecRound liftVal
  rw [atanWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.atanWithPeriod_two a

/-- **`arctan (q) / π` of a rational is correctly rounded.** -/
theorem atanPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atanPiRatPrecRound q p mode
      = roundVal p mode (Spec.atanPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold atanPiRatPrecRound
  rw [atanRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.atanWithPeriod_two _)

end Azurite.AzFloat
