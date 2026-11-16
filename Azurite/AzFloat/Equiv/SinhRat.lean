/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhRat
import Azurite.AzFloat.Equiv.Sinh
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `sinh q` for a rational `q`

`sinhRatPrecRound_eq : sinhRatPrecRound q p mode = roundVal p mode (Spec.sinh q)` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`sinh q` is correctly rounded.** -/
theorem sinhRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinhRatPrecRound q p mode
      = roundVal p mode (Spec.sinh (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold sinhRatPrecRound
  rw [Spec.sinh_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.sinh_zero, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    split
    · next r hT => exact tanTinyRat?_eq_of Real.sinh_neg sinh_tiny_bounds q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_sinh_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          sinhRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
