/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanRat
import Azurite.AzFloat.Equiv.Tan

/-!
# Equivalence: `tan q` for a rational `q`

`tanRatPrecRound_eq : tanRatPrecRound q p mode = roundVal p mode (Spec.tan q)` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`tan q` is correctly rounded.** -/
theorem tanRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tanRatPrecRound q p mode
      = roundVal p mode (Spec.tan (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold tanRatPrecRound
  rw [Spec.tan_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.tan_zero, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    split
    · next r hT => exact tanTinyRat?_eq q h0 hT
    exact zivLoopCertified_eq_or_none p mode _ (Real.tan (AzRat.toRat q : ℝ))
      (not_mem_floatSet_of_irrational p (irrational_tan_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => tanRatApprox_valid_or_none q h0
        (by unfold zivGuardBits at hw; omega) p mode) _

end Azurite.AzFloat
