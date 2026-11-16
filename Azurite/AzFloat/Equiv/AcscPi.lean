/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscPi
import Azurite.AzFloat.Equiv.AcscWithPeriod
import Azurite.AzFloat.Equiv.AcscRat

/-!
# Equivalence: `arccsc (x) / π`

`Spec.acscPi a = (Spec.acsc a) / π`, `Spec.acscWithPeriod_two`,
`acscPiPrecRound_eq_liftVal : acscPiPrecRound x p mode = liftVal Spec.acscPi x p mode` and
`acscPiRatPrecRound_eq : acscPiRatPrecRound q p mode = roundVal p mode (Spec.acscPi q)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arccsc (a) / π`: `0` at `±∞`, undefined inside `(−1, 1)`. -/
noncomputable def acscPi (a : EReal) : Option EReal :=
  (acsc a).map fun θ => ((θ.toReal / π : ℝ) : EReal)

/-- `arccsc (a) / π` is the period-`2` case of `acscWithPeriod`. -/
theorem acscWithPeriod_two (a : EReal) : acscWithPeriod a 2 = acscPi a := by
  unfold acscWithPeriod acscPi
  congr 1
  funext θ
  congr 1
  have hpi := pi_ne_zero
  push_cast
  field_simp

theorem acscPi_coe {r : ℝ} (hr : 1 ≤ |r|) :
    acscPi (r : EReal) = some ((arcsin r⁻¹ / π : ℝ) : EReal) := by
  unfold acscPi
  rw [acsc_coe hr, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`arccsc (x) / π` is correctly rounded.** -/
theorem acscPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acscPiPrecRound x p mode = liftVal Spec.acscPi x p mode := by
  unfold acscPiPrecRound liftVal
  rw [acscWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.acscWithPeriod_two a

/-- **`arccsc (q) / π` of a rational is correctly rounded.** -/
theorem acscPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acscPiRatPrecRound q p mode
      = roundVal p mode (Spec.acscPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acscPiRatPrecRound
  rw [acscRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.acscWithPeriod_two _)

end Azurite.AzFloat
