/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log10
import Azurite.AzFloat.Equiv.LogBase
import Azurite.AzFloat.Equiv.LogBaseP1
import Azurite.AzFloat.Equiv.LogBaseRat

/-!
# Equivalence: base-10 logarithms

`Spec.log10 = Spec.logBase 10`, and the three wrappers are correctly rounded:
`log10PrecRound_eq_liftVal`, `log10RatPrecRound_eq`, `log10P1PrecRound_eq_liftVal`.
-/

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `log₁₀`. -/
noncomputable def log10 : EReal → Option EReal := logBase 10

end Spec

theorem toNat_ten : (10 : UInt64).toNat = 10 := by decide

/-- **`log₁₀` is correctly rounded.** -/
theorem log10PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10PrecRound x p mode = liftVal Spec.log10 x p mode := by
  unfold log10PrecRound Spec.log10
  rw [logBasePrecRound_eq_liftVal x 10 (by decide) p mode, toNat_ten]

/-- **`log₁₀` of a rational is correctly rounded.** -/
theorem log10RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10RatPrecRound q p mode = roundVal p mode (Spec.log10 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold log10RatPrecRound Spec.log10
  rw [logBaseRatPrecRound_eq q 10 (by decide) p mode, toNat_ten]

/-- **`log₁₀ (1 + x)` is correctly rounded.** -/
theorem log10P1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10P1PrecRound x p mode = liftVal (fun a => Spec.log10 (a + 1)) x p mode := by
  unfold log10P1PrecRound Spec.log10
  rw [logBaseP1PrecRound_eq_liftVal x 10 (by decide) p mode, toNat_ten]

end Azurite.AzFloat
