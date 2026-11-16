/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotPi
import Azurite.AzFloat.Equiv.AcotWithPeriod
import Azurite.AzFloat.Equiv.AcotRat

/-!
# Equivalence: `arccot (x) / π`

`Spec.acotPi a = (Spec.acot a) / π`, `Spec.acotWithPeriod_two`,
`acotPiPrecRound_eq_liftVal : acotPiPrecRound x p mode = liftVal Spec.acotPi x p mode` and
`acotPiRatPrecRound_eq : acotPiRatPrecRound q p mode = roundVal p mode (Spec.acotPi q)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arccot (a) / π`: `1/2` at `0`, `0` at `±∞`. -/
noncomputable def acotPi (a : EReal) : Option EReal :=
  (acot a).map fun θ => ((θ.toReal / π : ℝ) : EReal)

/-- `arccot (a) / π` is the period-`2` case of `acotWithPeriod`. -/
theorem acotWithPeriod_two (a : EReal) : acotWithPeriod a 2 = acotPi a := by
  unfold acotWithPeriod acotPi
  congr 1
  funext θ
  congr 1
  have hpi := pi_ne_zero
  push_cast
  field_simp

theorem acotPi_coe {r : ℝ} (hr : r ≠ 0) :
    acotPi (r : EReal) = some ((arctan r⁻¹ / π : ℝ) : EReal) := by
  unfold acotPi
  rw [acot_coe hr, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`arccot (x) / π` is correctly rounded.** -/
theorem acotPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acotPiPrecRound x p mode = liftVal Spec.acotPi x p mode := by
  unfold acotPiPrecRound liftVal
  rw [acotWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.acotWithPeriod_two a

/-- **`arccot (q) / π` of a rational is correctly rounded.** -/
theorem acotPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acotPiRatPrecRound q p mode
      = roundVal p mode (Spec.acotPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acotPiRatPrecRound
  rw [acotRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.acotWithPeriod_two _)

end Azurite.AzFloat
