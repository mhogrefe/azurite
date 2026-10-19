/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2Rat
import Azurite.AzFloat.Equiv.Log2

/-!
# Equivalence: the base-2 logarithm of a rational

`log2RatPrecRound_eq : log2RatPrecRound q p mode = roundVal p mode (Spec.log2 q)` for `p ≠ 0`:
`log₂ q` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`log₂` of a rational is correctly rounded.** -/
theorem log2RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2RatPrecRound q p mode = roundVal p mode (Spec.log2 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold log2RatPrecRound
  split_ifs with h0 hs hp h2
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0]
    simp only [EReal.coe_zero, Spec.log2_zero, roundVal_bot]
  · exact absurd hp (NeZero.ne p)
  · have hq := toRat_pos_of_sign q hs h0
    have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
    rw [setPrecRound_eq_roundVal (toVal_ofAzInt _), Spec.log2_coe _ hqr, toRat_of_isPowerOfTwo q h2,
      logb_two_zpow]
  · have hq := toRat_pos_of_sign q hs h0
    have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
    rw [Spec.log2_coe _ hqr]
    exact zivLoopCertified_eq_threshold p mode _ (Real.logb 2 (AzRat.toRat q : ℝ)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          log2RatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hq
            (Bool.eq_false_iff.mpr h2)
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
  · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
    rw [Spec.log2_coe_neg _ hneg, roundVal_none]

end Azurite.AzFloat
