/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosPi
import Azurite.AzFloat.Equiv.AcosWithPeriod
import Azurite.AzFloat.Equiv.AcosRatWithPeriod

/-!
# Equivalence: `arccos (x) / π`

`Spec.acosPi a = (Spec.acos a) / π`, `Spec.acosWithPeriod_two`,
`acosPiPrecRound_eq_liftVal : acosPiPrecRound x p mode = liftVal Spec.acosPi x p mode` and
`acosPiRatPrecRound_eq : acosPiRatPrecRound q p mode = roundVal p mode (Spec.acosPi q)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arccos (a) / π`: undefined outside `[−1, 1]`. -/
noncomputable def acosPi (a : EReal) : Option EReal :=
  (acos a).map fun θ => ((θ.toReal / π : ℝ) : EReal)

/-- `arccos (a) / π` is the period-`2` case of `acosWithPeriod`. -/
theorem acosWithPeriod_two (a : EReal) : acosWithPeriod a 2 = acosPi a := by
  unfold acosWithPeriod acosPi
  congr 1
  funext θ
  congr 1
  have hpi := pi_ne_zero
  push_cast
  field_simp

theorem acosPi_coe {r : ℝ} (hr : |r| ≤ 1) :
    acosPi (r : EReal) = some ((arccos r / π : ℝ) : EReal) := by
  unfold acosPi
  rw [acos_coe hr, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`arccos (x) / π` is correctly rounded.** -/
theorem acosPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acosPiPrecRound x p mode = liftVal Spec.acosPi x p mode := by
  unfold acosPiPrecRound liftVal
  rw [acosWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.acosWithPeriod_two a

/-- **`arccos (q) / π` of a rational is correctly rounded.** -/
theorem acosPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acosPiRatPrecRound q p mode
      = roundVal p mode (Spec.acosPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acosPiRatPrecRound
  rw [acosRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.acosWithPeriod_two _)

end Azurite.AzFloat
