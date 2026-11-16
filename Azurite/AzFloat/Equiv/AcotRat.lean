/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotRat
import Azurite.AzFloat.Equiv.AtanRat
import Azurite.AzFloat.Equiv.AtanRatWithPeriod
import Azurite.AzFloat.Equiv.AcotWithPeriod
import Azurite.AzFloat.Equiv.AsecRat

/-!
# Equivalence: `arccot q` for a rational `q`, plain and with a period

`acotRatPrecRound_eq : acotRatPrecRound q p mode = roundVal p mode (Spec.acot q)` and
`acotRatWithPeriodPrecRound_eq :
  acotRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.acotWithPeriod q u)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- **`arccot q` is correctly rounded.** -/
theorem acotRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acotRatPrecRound q p mode
      = roundVal p mode (Spec.acot (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acotRatPrecRound
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.acot_zero,
      piDiv2PrecRound_eq_liftVal₀]
    rfl
  · have hq0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h =>
      h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h))
    rw [ite_eq_right h0, atanRatPrecRound_eq, coe_toRat_inv, Spec.atan_coe, Spec.acot_coe hq0]

/-- **`arccot (q) u / (2π)` of a rational is correctly rounded.** -/
theorem acotRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    acotRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.acotWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  unfold acotRatWithPeriodPrecRound
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0]
    exact quarterTurn_round u p mode
  · have hq0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h =>
      h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h))
    rw [ite_eq_right h0, atanRatWithPeriodPrecRound_eq, coe_toRat_inv, Spec.atanWithPeriod_coe,
      Spec.acotWithPeriod_coe hq0]

end Azurite.AzFloat
