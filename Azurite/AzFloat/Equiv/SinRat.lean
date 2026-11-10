/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinRat
import Azurite.AzFloat.Equiv.Sin

/-!
# Equivalence: `sin q` for a rational `q`

`sinRatPrecRound_eq : sinRatPrecRound q p mode = roundVal p mode (Spec.sin q)` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`sin q` is correctly rounded.** -/
theorem sinRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinRatPrecRound q p mode
      = roundVal p mode (Spec.sin (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold sinRatPrecRound
  rw [Spec.sin_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.sin_zero, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    split
    · next r hT => exact sinTinyRat?_eq q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ (Real.sin (AzRat.toRat q : ℝ))
      (not_mem_floatSet_of_irrational p (irrational_sin_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          sinRatApprox_spec q h0 (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
