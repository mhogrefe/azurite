/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnRat
import Azurite.AzFloat.Equiv.Ln

/-!
# Equivalence: the natural logarithm of a rational

`lnRatPrecRound_eq : lnRatPrecRound q p mode = roundVal p mode (Spec.log q)` for `p ≠ 0`: `ln q`
is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`ln` of a rational is correctly rounded.** -/
theorem lnRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnRatPrecRound q p mode = roundVal p mode (Spec.log ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold lnRatPrecRound
  split_ifs with h0 hs h1 hp
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0]
    simp only [EReal.coe_zero, Spec.log_zero, roundVal_bot]
  · rw [toRat_eq_one_of_num_eq_den q hs h1]
    simp only [Rat.cast_one]
    rw [Spec.log_coe _ one_pos, Real.log_one, EReal.coe_zero, roundVal_zero]
  · exact absurd hp (NeZero.ne p)
  · have hq := toRat_pos_of_sign q hs h0
    have hq1 := toRat_ne_one_of_num_ne_den q hs h1
    rw [Spec.log_coe _ (by exact_mod_cast hq)]
    exact zivLoopCertified_eq_threshold p mode _ (Real.log (AzRat.toRat q : ℝ)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          lnRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hq hq1
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
  · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
    rw [Spec.log_coe_neg _ hneg, roundVal_none]

end Azurite.AzFloat
