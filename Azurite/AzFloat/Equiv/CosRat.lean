/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRat
import Azurite.AzFloat.Equiv.Cos

/-!
# Equivalence: `cos q` for a rational `q`

`cosRatPrecRound_eq : cosRatPrecRound q p mode = roundVal p mode (Spec.cos q)` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`cos q` is correctly rounded.** -/
theorem cosRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cosRatPrecRound q p mode
      = roundVal p mode (Spec.cos (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold cosRatPrecRound
  rw [dite_eq_right hp]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero, ← EReal.coe_zero,
      Spec.cos_coe, Real.cos_zero, setPrecRound_eq_roundVal toVal_one']
  · rw [dite_eq_right h0, Spec.cos_coe]
    split
    · next r hT =>
      refine cosTiny?_eq (lt_of_lt_of_le (abs_toRat_lt_two_zpow q) ?_)
        (irrational_cos_toRat q h0) hT
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact zivLoopCertified_eq_threshold' p mode _ (Real.cos (AzRat.toRat q : ℝ))
      (not_mem_floatSet_of_irrational p (irrational_cos_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          cosRatApprox_spec q (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
