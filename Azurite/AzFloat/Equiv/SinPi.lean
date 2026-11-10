/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinPi
import Azurite.AzFloat.Equiv.SinWithPeriod
import Azurite.AzFloat.Equiv.SinRatWithPeriod

/-!
# Equivalence: `sin (π x)`

`Spec.sinPi : EReal → Option EReal` (undefined at `±∞`),
`sinPiPrecRound_eq_liftVal : sinPiPrecRound x p mode = liftVal Spec.sinPi x p mode` and
`sinPiRatPrecRound_eq : sinPiRatPrecRound q p mode = roundVal p mode (Spec.sinPi q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `sin (π a)`: undefined (`NaN`) at `±∞`. -/
noncomputable def sinPi (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some ((Real.sin (Real.pi * a.toReal) : ℝ) : EReal)

theorem sinPi_coe (r : ℝ) : sinPi (r : EReal) = some ((Real.sin (Real.pi * r) : ℝ) : EReal) := by
  unfold sinPi
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem sinPi_top : sinPi ⊤ = none := by
  unfold sinPi
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem sinPi_bot : sinPi ⊥ = none := by
  unfold sinPi
  rw [ite_eq_left (Or.inr rfl)]

/-- `sin (π a)` is the period-`2` case of `sinWithPeriod`. -/
theorem sinWithPeriod_two (a : EReal) : sinWithPeriod a 2 = sinPi a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [sinWithPeriod_coe r (by norm_num), sinPi_coe]
    congr 3
    push_cast
    ring

end Spec

/-- **`sin (π x)` is correctly rounded.** -/
theorem sinPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinPiPrecRound x p mode = liftVal Spec.sinPi x p mode := by
  unfold sinPiPrecRound liftVal
  rw [sinWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.sinWithPeriod_two a

/-- **`sin (π q)` of a rational is correctly rounded.** -/
theorem sinPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinPiRatPrecRound q p mode
      = roundVal p mode (Spec.sinPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold sinPiRatPrecRound
  rw [sinRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.sinWithPeriod_two _)

end Azurite.AzFloat
