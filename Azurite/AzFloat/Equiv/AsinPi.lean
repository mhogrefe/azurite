/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinPi
import Azurite.AzFloat.Equiv.AsinWithPeriod
import Azurite.AzFloat.Equiv.AsinRatWithPeriod

/-!
# Equivalence: `arcsin (x) / π`

`Spec.asinPi a = (Spec.asin a) / π`, `Spec.asinWithPeriod_two`,
`asinPiPrecRound_eq_liftVal : asinPiPrecRound x p mode = liftVal Spec.asinPi x p mode` and
`asinPiRatPrecRound_eq : asinPiRatPrecRound q p mode = roundVal p mode (Spec.asinPi q)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arcsin (a) / π`: undefined outside `[−1, 1]`. -/
noncomputable def asinPi (a : EReal) : Option EReal :=
  (asin a).map fun θ => ((θ.toReal / π : ℝ) : EReal)

/-- `arcsin (a) / π` is the period-`2` case of `asinWithPeriod`. -/
theorem asinWithPeriod_two (a : EReal) : asinWithPeriod a 2 = asinPi a := by
  unfold asinWithPeriod asinPi
  congr 1
  funext θ
  congr 1
  have hpi := pi_ne_zero
  push_cast
  field_simp

theorem asinPi_coe {r : ℝ} (hr : |r| ≤ 1) :
    asinPi (r : EReal) = some ((arcsin r / π : ℝ) : EReal) := by
  unfold asinPi
  rw [asin_coe hr, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`arcsin (x) / π` is correctly rounded.** -/
theorem asinPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asinPiPrecRound x p mode = liftVal Spec.asinPi x p mode := by
  unfold asinPiPrecRound liftVal
  rw [asinWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.asinWithPeriod_two a

/-- **`arcsin (q) / π` of a rational is correctly rounded.** -/
theorem asinPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asinPiRatPrecRound q p mode
      = roundVal p mode (Spec.asinPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold asinPiRatPrecRound
  rw [asinRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.asinWithPeriod_two _)

end Azurite.AzFloat
