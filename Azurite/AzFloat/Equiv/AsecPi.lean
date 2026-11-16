/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecPi
import Azurite.AzFloat.Equiv.AsecWithPeriod
import Azurite.AzFloat.Equiv.AsecRat

/-!
# Equivalence: `arcsec (x) / π`

`Spec.asecPi a = (Spec.asec a) / π`, `Spec.asecWithPeriod_two`,
`asecPiPrecRound_eq_liftVal : asecPiPrecRound x p mode = liftVal Spec.asecPi x p mode` and
`asecPiRatPrecRound_eq : asecPiRatPrecRound q p mode = roundVal p mode (Spec.asecPi q)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arcsec (a) / π`: `1/2` at `±∞`, undefined inside `(−1, 1)`. -/
noncomputable def asecPi (a : EReal) : Option EReal :=
  (asec a).map fun θ => ((θ.toReal / π : ℝ) : EReal)

/-- `arcsec (a) / π` is the period-`2` case of `asecWithPeriod`. -/
theorem asecWithPeriod_two (a : EReal) : asecWithPeriod a 2 = asecPi a := by
  unfold asecWithPeriod asecPi
  congr 1
  funext θ
  congr 1
  have hpi := pi_ne_zero
  push_cast
  field_simp

theorem asecPi_coe {r : ℝ} (hr : 1 ≤ |r|) :
    asecPi (r : EReal) = some ((arccos r⁻¹ / π : ℝ) : EReal) := by
  unfold asecPi
  rw [asec_coe hr, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`arcsec (x) / π` is correctly rounded.** -/
theorem asecPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asecPiPrecRound x p mode = liftVal Spec.asecPi x p mode := by
  unfold asecPiPrecRound liftVal
  rw [asecWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.asecWithPeriod_two a

/-- **`arcsec (q) / π` of a rational is correctly rounded.** -/
theorem asecPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asecPiRatPrecRound q p mode
      = roundVal p mode (Spec.asecPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold asecPiRatPrecRound
  rw [asecRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.asecWithPeriod_two _)

end Azurite.AzFloat
