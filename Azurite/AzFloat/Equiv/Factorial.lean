/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Factorial
import Azurite.AzFloat.Equiv.Gamma

/-!
# Equivalence: the factorial as a float

`factorialPrecRound_eq_or`: `factorialPrecRound n p mode` is the correct rounding of
`n.toNat !`, or `(nan, .eq)` when the fuel of the `Γ` loop runs out.
-/

namespace Azurite.AzFloat

/-- **The factorial is correctly rounded, or the fuel ran out.** -/
theorem factorialPrecRound_eq_or (n : AzNat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    factorialPrecRound n p mode
        = roundVal p mode (some (((n.toNat.factorial : ℕ) : ℝ) : EReal)) ∨
      factorialPrecRound n p mode = (nan, .eq) := by
  unfold factorialPrecRound
  rw [ite_eq_right (NeZero.ne p)]
  split_ifs
  · left
    rw [setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_factorial]
  · have hval : (ofAzNat (n + 1)).toVal = some (((n.toNat : ℝ) + 1 : ℝ) : EReal) := by
      rw [toVal_ofAzNat, AzNat.toNat_add, AzNat.toNat_one]
      push_cast
      rfl
    have hpos : (0 : ℝ) < (n.toNat : ℝ) + 1 := by positivity
    rcases gammaPrecRound_eq_or (ofAzNat (n + 1)) p mode with h | h
    · left
      rw [h, liftVal, hval, Option.bind_some,
        Spec.gamma_coe hpos.ne' (fun hc => absurd hc.1 (not_lt.mpr hpos.le)),
        Real.Gamma_nat_eq_factorial]
    · right; exact h

end Azurite.AzFloat
