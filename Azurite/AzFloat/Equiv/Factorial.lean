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

**`factorialPrecRound_eq`**: `factorialPrecRound n p mode` is the correct rounding of
`n.toNat !`, unconditionally.  Up to `gammaIntBound p` the factorial is computed exactly;
beyond, `Γ(n + 1)` at an integer float runs a certified Ziv loop — `n!` is no rounding
boundary there (`factorial_not_boundary`, `gammaPrecRound_eq_of_isInteger`).
-/

namespace Azurite.AzFloat

/-- **The factorial is correctly rounded.** -/
theorem factorialPrecRound_eq (n : AzNat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    factorialPrecRound n p mode
      = roundVal p mode (some (((n.toNat.factorial : ℕ) : ℝ) : EReal)) := by
  unfold factorialPrecRound
  rw [ite_eq_right (NeZero.ne p)]
  split_ifs
  · rw [setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_factorial]
  · have hval : (ofAzNat (n + 1)).toVal = some (((n.toNat : ℝ) + 1 : ℝ) : EReal) := by
      rw [toVal_ofAzNat, AzNat.toNat_add, AzNat.toNat_one]
      push_cast
      rfl
    have hpos : (0 : ℝ) < (n.toNat : ℝ) + 1 := by positivity
    have hint : isInteger (ofAzNat (n + 1)) = true :=
      (isInteger_iff_of_toVal hval).mpr ⟨(n.toNat : ℤ) + 1, by push_cast; rfl⟩
    rw [gammaPrecRound_eq_of_isInteger _ p mode hint, liftVal, hval, Option.bind_some,
      Spec.gamma_coe hpos.ne' (fun hc => absurd hc.1 (not_lt.mpr hpos.le)),
      Real.Gamma_nat_eq_factorial]

/-- The factorial is correctly rounded (the weaker form, kept for its users). -/
theorem factorialPrecRound_eq_or (n : AzNat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    factorialPrecRound n p mode
        = roundVal p mode (some (((n.toNat.factorial : ℕ) : ℝ) : EReal)) ∨
      factorialPrecRound n p mode = (nan, .eq) :=
  Or.inl (factorialPrecRound_eq n p mode)

end Azurite.AzFloat
