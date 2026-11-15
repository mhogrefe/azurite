/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Pi
import Azurite.AzFloat.Equiv.Atan2WithPeriod
import Azurite.AzFloat.Equiv.Atan2RatWithPeriod

/-!
# Equivalence: `atan2 (y, x) / π`

`Spec.atan2Pi y x = (Spec.atan2 y x) / π`, `Spec.atan2WithPeriod_two`,
`atan2PiPrecRound_eq_liftVal₂ : atan2PiPrecRound y x p mode = liftVal₂ Spec.atan2Pi y x p mode`
and `atan2PiRatPrecRound_eq : atan2PiRatPrecRound y x p mode = roundVal p mode (Spec.atan2Pi y x)`,
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `atan2 (y, x) / π`: the angle `Spec.atan2 y x` in half-turns. -/
noncomputable def atan2Pi (y x : EReal) : Option EReal :=
  (atan2 y x).map fun θ => ((θ.toReal / π : ℝ) : EReal)

/-- `atan2 (y, x) / π` is the period-`2` case of `atan2WithPeriod`. -/
theorem atan2WithPeriod_two (y x : EReal) : atan2WithPeriod y x 2 = atan2Pi y x := by
  unfold atan2WithPeriod atan2Pi
  congr 1
  funext θ
  congr 1
  have hpi := pi_ne_zero
  push_cast
  field_simp

theorem atan2Pi_coe_coe (b a : ℝ) :
    atan2Pi (b : EReal) (a : EReal) = some ((Complex.arg ⟨a, b⟩ / π : ℝ) : EReal) := by
  unfold atan2Pi
  rw [atan2_coe_coe, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`atan2 (y, x) / π` is correctly rounded.** -/
theorem atan2PiPrecRound_eq_liftVal₂ (y x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atan2PiPrecRound y x p mode = liftVal₂ Spec.atan2Pi y x p mode := by
  unfold atan2PiPrecRound liftVal₂
  rw [atan2WithPeriodPrecRound_eq]
  congr 2
  funext a
  congr 1
  funext b
  exact Spec.atan2WithPeriod_two a b

/-- **`atan2 (y, x) / π` of rationals is correctly rounded.** -/
theorem atan2PiRatPrecRound_eq (y x : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atan2PiRatPrecRound y x p mode
      = roundVal p mode (Spec.atan2Pi (((AzRat.toRat y : ℚ) : ℝ) : EReal)
        (((AzRat.toRat x : ℚ) : ℝ) : EReal)) := by
  unfold atan2PiRatPrecRound
  rw [atan2RatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.atan2WithPeriod_two _ _)

end Azurite.AzFloat
