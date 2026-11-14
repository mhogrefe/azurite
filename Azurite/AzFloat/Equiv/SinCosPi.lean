/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosPi
import Azurite.AzFloat.Equiv.SinPi
import Azurite.AzFloat.Equiv.CosPi
import Azurite.AzFloat.Equiv.SinCosWithPeriod
import Azurite.AzFloat.Equiv.SinCosRatWithPeriod

/-!
# Equivalence: `sin (π x)` and `cos (π x)` together

* `sinCosPiPrecRound_eq : sinCosPiPrecRound x p mode = (sinPiPrecRound x p mode,
  cosPiPrecRound x p mode)` and `sinCosPiRatPrecRound_eq` (every `p`).
* `sinCosPiPrecRound_eq_liftVal`, `sinCosPiRatPrecRound_eq_roundVal`: both values are correctly
  rounded (`p ≠ 0`).
* `sinCosPi_eq`, `sinCosPiRat_eq`.
-/

namespace Azurite.AzFloat

/-- **The joint computation agrees with the separate ones.** -/
theorem sinCosPiPrecRound_eq (x : AzFloat) (p : ℕ) (mode : RoundingMode) :
    sinCosPiPrecRound x p mode = (sinPiPrecRound x p mode, cosPiPrecRound x p mode) :=
  sinCosWithPeriodPrecRound_eq x 2 p mode

/-- **`sin (π x)` and `cos (π x)` are both correctly rounded.** -/
theorem sinCosPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinCosPiPrecRound x p mode = (liftVal Spec.sinPi x p mode, liftVal Spec.cosPi x p mode) := by
  rw [sinCosPiPrecRound_eq, sinPiPrecRound_eq_liftVal, cosPiPrecRound_eq_liftVal]

/-- `sinCosPi x = (sinPi x, cosPi x)`. -/
theorem sinCosPi_eq (x : AzFloat) : sinCosPi x = (sinPi x, cosPi x) := by
  unfold sinCosPi sinPi cosPi
  rw [sinCosPiPrecRound_eq]

/-- **The joint computation agrees with the separate ones**, for a rational. -/
theorem sinCosPiRatPrecRound_eq (q : AzRat) (p : ℕ) (mode : RoundingMode) :
    sinCosPiRatPrecRound q p mode = (sinPiRatPrecRound q p mode, cosPiRatPrecRound q p mode) :=
  sinCosRatWithPeriodPrecRound_eq q 2 p mode

/-- **`sin (π q)` and `cos (π q)` of a rational are both correctly rounded.** -/
theorem sinCosPiRatPrecRound_eq_roundVal (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinCosPiRatPrecRound q p mode
      = (roundVal p mode (Spec.sinPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)),
        roundVal p mode (Spec.cosPi (((AzRat.toRat q : ℚ) : ℝ) : EReal))) := by
  rw [sinCosPiRatPrecRound_eq, sinPiRatPrecRound_eq, cosPiRatPrecRound_eq]

/-- `sinCosPiRat q p = (sinPiRat q p, cosPiRat q p)`. -/
theorem sinCosPiRat_eq (q : AzRat) (p : ℕ) : sinCosPiRat q p = (sinPiRat q p, cosPiRat q p) := by
  unfold sinCosPiRat sinPiRat cosPiRat
  rw [sinCosPiRatPrecRound_eq]

end Azurite.AzFloat
