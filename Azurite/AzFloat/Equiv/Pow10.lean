/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pow10
import Azurite.AzFloat.Equiv.PowBase
import Azurite.AzFloat.Equiv.PowBaseM1
import Azurite.AzFloat.Equiv.PowBaseM1Rat
import Azurite.AzFloat.Equiv.PowBaseRat

/-!
# Equivalence: the base-`10` powers

The specifications of `pow10`, `pow10Rat`, `pow10M1` and `pow10M1Rat` are the base-`10`
instances of those of `powBase`, `powBaseRat`, `powBaseM1` and `powBaseM1Rat`: `Spec.powBase 10`
and `Spec.powBaseM1 10` (`(10 : UInt64).toNat = 10`).
-/

namespace Azurite.AzFloat

/-- **`10^x` is correctly rounded.** -/
theorem pow10PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow10PrecRound x p mode = liftVal (Spec.powBase 10) x p mode := by
  unfold pow10PrecRound
  rw [powBasePrecRound_eq_liftVal]
  rfl

/-- **`10^q` is correctly rounded.** -/
theorem pow10RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow10RatPrecRound q p mode
      = roundVal p mode (Spec.powBase 10 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold pow10RatPrecRound
  rw [powBaseRatPrecRound_eq]
  rfl

/-- **`10^x − 1` is correctly rounded.** -/
theorem pow10M1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow10M1PrecRound x p mode = liftVal (Spec.powBaseM1 10) x p mode := by
  unfold pow10M1PrecRound
  rw [powBaseM1PrecRound_eq_liftVal]
  rfl

/-- **`10^q − 1` is correctly rounded.** -/
theorem pow10M1RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow10M1RatPrecRound q p mode
      = roundVal p mode (Spec.powBaseM1 10 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold pow10M1RatPrecRound
  rw [powBaseM1RatPrecRound_eq]
  rfl

end Azurite.AzFloat
