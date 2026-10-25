/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRat
import Azurite.AzFloat.Equiv.LogBase
import Azurite.AzFloat.Equiv.LogBasePow2Rat

/-!
# Equivalence: the logarithm of a rational in a natural base

* `logBaseRatPrecRound_eq : logBaseRatPrecRound q b p mode = roundVal p mode (Spec.logBase
  b.toNat (toRat q))` for `2 ≤ b`: `log_b` of a rational is correctly rounded in every mode, with
  the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`log_b` of a rational is correctly rounded.** -/
theorem logBaseRatPrecRound_eq (q : AzRat) (b : UInt64) (hb : 2 ≤ b.toNat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseRatPrecRound q b p mode
      = roundVal p mode (Spec.logBase b.toNat ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold logBaseRatPrecRound
  rw [dite_eq_right (not_lt.mpr hb)]
  split
  · -- a power-of-two base delegates
    next k hk =>
      have hbk : b.toNat = 2 ^ k := by
        have := (AzNat.checkedLogBase2_eq_some_iff _ k).mp hk
        rwa [AzNat.toNat_ofNat] at this
      have hk0 : (AzNat.ofNat k).toAzInt ≠ 0 := by
        intro h0
        have h1 := congrArg AzInt.toInt h0
        rw [toInt_toAzInt, AzNat.toNat_ofNat, show (0 : AzInt).toInt = 0 from rfl] at h1
        have : k = 0 := by exact_mod_cast h1
        subst this
        omega
      rw [logBasePow2RatPrecRound_eq q _ hk0 p mode, toInt_toAzInt, AzNat.toNat_ofNat, hbk,
        Spec.logBase_two_pow]
  · next =>
    split_ifs with h0 hs hp
    · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, EReal.coe_zero, Spec.logBase_zero _ hb]
      exact (roundVal_inf p mode false).symm
    · exact absurd hp (NeZero.ne p)
    · have hq := toRat_pos_of_sign q hs h0
      have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
      rw [Spec.logBase_coe _ hb _ hqr]
      split
      · rename_i r hx
        have hval := logBaseExactRat?_some q hq _ (by rw [AzNat.toNat_ofNat]; exact hb)
          (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt) r hx
        rw [AzNat.toNat_ofNat] at hval
        rw [ofAzRatRound_eq_roundVal, ← hval]
      · rename_i hx
        exact zivLoopCertified_eq_threshold p mode _
          (Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat) _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              logBaseRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hq b hb
                (AzNat.toNat_ofNat b.toNat ▸
                  irrational_of_logBaseExactRat?_none q hq (AzNat.ofNat b.toNat)
                    (by rw [AzNat.toNat_ofNat]; exact hb)
                    (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt) hx)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
      rw [Spec.logBase_coe_neg _ _ hneg, roundVal_none]

end Azurite.AzFloat
