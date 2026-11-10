/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosPi
import Azurite.AzFloat.Equiv.CosWithPeriod
import Azurite.AzFloat.Equiv.CosRatWithPeriod

/-!
# Equivalence: `cos (π x)`

`Spec.cosPi : EReal → Option EReal` (undefined at `±∞`),
`cosPiPrecRound_eq_liftVal : cosPiPrecRound x p mode = liftVal Spec.cosPi x p mode` and
`cosPiRatPrecRound_eq : cosPiRatPrecRound q p mode = roundVal p mode (Spec.cosPi q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `cos (π a)`: undefined (`NaN`) at `±∞`. -/
noncomputable def cosPi (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some ((Real.cos (Real.pi * a.toReal) : ℝ) : EReal)

theorem cosPi_coe (r : ℝ) : cosPi (r : EReal) = some ((Real.cos (Real.pi * r) : ℝ) : EReal) := by
  unfold cosPi
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem cosPi_top : cosPi ⊤ = none := by
  unfold cosPi
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cosPi_bot : cosPi ⊥ = none := by
  unfold cosPi
  rw [ite_eq_left (Or.inr rfl)]

/-- `cos (π a)` is the period-`2` case of `cosWithPeriod`. -/
theorem cosWithPeriod_two (a : EReal) : cosWithPeriod a 2 = cosPi a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [cosWithPeriod_coe r (by norm_num), cosPi_coe]
    congr 3
    push_cast
    ring

end Spec

/-- **`cos (π x)` is correctly rounded.** -/
theorem cosPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cosPiPrecRound x p mode = liftVal Spec.cosPi x p mode := by
  unfold cosPiPrecRound liftVal
  rw [cosWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.cosWithPeriod_two a

/-- **`cos (π q)` of a rational is correctly rounded.** -/
theorem cosPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cosPiRatPrecRound q p mode
      = roundVal p mode (Spec.cosPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold cosPiRatPrecRound
  rw [cosRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.cosWithPeriod_two _)

end Azurite.AzFloat
