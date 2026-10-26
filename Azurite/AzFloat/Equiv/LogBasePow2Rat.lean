/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Log2Rat
import Azurite.AzFloat.Equiv.LogBasePow2
import Azurite.AzFloat.LogBasePow2Rat
import Azurite.AzRat.Equiv.Construct

/-!
# Equivalence: the logarithm of a rational in a power-of-two base

`logBasePow2RatPrecRound_eq : logBasePow2RatPrecRound q k p mode = roundVal p mode
(Spec.logBasePow2 k.toInt (toRat q))` for `k ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`log_{2^k}` of a rational is correctly rounded.** -/
theorem logBasePow2RatPrecRound_eq (q : AzRat) (k : AzInt) (hk : k ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBasePow2RatPrecRound q k p mode
      = roundVal p mode (Spec.logBasePow2 k.toInt ((AzRat.toRat q : ℝ) : EReal)) := by
  have hkI := toInt_ne_zero_of_ne_zero hk
  unfold logBasePow2RatPrecRound
  rw [dite_eq_right hk]
  split_ifs with h0 hs hp
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, EReal.coe_zero, Spec.logBasePow2_zero _ hkI,
      sign_eq_decide_pos_toInt k hk]
    rcases lt_or_gt_of_ne hkI with h | h
    · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
      exact (roundVal_inf p mode true).symm
    · rw [ite_eq_left h, decide_eq_true h]
      exact (roundVal_inf p mode false).symm
  · exact absurd hp (NeZero.ne p)
  · have hq := toRat_pos_of_sign q hs h0
    have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
    rw [Spec.logBasePow2_coe _ _ hqr]
    split
    · rename_i j hj
      obtain ⟨h2, rfl⟩ := AzRat.checkedLogBase2_eq_some q j hj
      rw [ofAzRatRound_eq_roundVal, AzRat.toRat_ofAzInts, AzRat.toRat_of_isPowerOfTwo q h2,
        logb_two_zpow]
      push_cast
      rfl
    · rename_i hj
      have h2 := AzRat.isPowerOfTwo_eq_false_of_checkedLogBase2_eq_none q hj
      exact zivLoopCertified_eq_threshold p mode _ (Real.logb 2 (AzRat.toRat q : ℝ) / k.toInt) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
            logBasePow2RatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hq h2 k hk
          exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
  · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
    rw [Spec.logBasePow2_coe_neg _ _ hneg, roundVal_none]

end Azurite.AzFloat
