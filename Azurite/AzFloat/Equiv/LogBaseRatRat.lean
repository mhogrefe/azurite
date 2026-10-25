/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatRat
import Azurite.AzFloat.Equiv.LogBaseRatFloat

/-!
# Equivalence: the logarithm of a rational in a rational base

`logBaseRatRatPrecRound_eq : logBaseRatRatPrecRound q b p mode = roundVal p mode
(Spec.logBaseFloat (toRat q) (toRat b))`: `log_b q` with rationals is correctly rounded in every
mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The general case rounds `ln q / ln b`. -/
theorem logBaseRatRatFinite_eq (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatRatFinite q hq hq1 b hb hb1 p mode
      = roundVal p mode
          (some ((Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ) : ℝ) : EReal)) := by
  unfold logBaseRatRatFinite
  split
  · rename_i r hx
    rw [ofAzRatRound_eq_roundVal, logBaseRatRat_exact_value q (sign_eq_true_of_toRat_pos q hq)
      (num_ne_zero_of_toRat_pos q hq) b (sign_eq_true_of_toRat_pos b hb)
      (num_ne_zero_of_toRat_pos b hb) hb1 r hx]
  · rename_i hx
    have hirr := irrational_logBaseRatRat_of_none q (sign_eq_true_of_toRat_pos q hq)
      (num_ne_zero_of_toRat_pos q hq) hq1 b (sign_eq_true_of_toRat_pos b hb)
      (num_ne_zero_of_toRat_pos b hb) hb1 hx
    exact zivLoopCertified_eq_threshold p mode _ _ _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBaseRatRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hq b hb hb1
            hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- `b > 0`, `b ≠ 1`: the dispatch on `q` rounds the specification. -/
theorem logBaseRatRatPos_eq (q b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatRatPos q b hb hb1 p mode
      = roundVal p mode
          (Spec.logBaseFloat ((AzRat.toRat q : ℝ) : EReal) ((AzRat.toRat b : ℝ) : EReal)) := by
  have hbv : (0 : ℝ) < (AzRat.toRat b : ℝ) := by exact_mod_cast hb
  have hs := sign_eq_true_of_toRat_pos b hb
  have hlt := one_lt_toRat_iff b hs
  unfold logBaseRatRatPos
  split_ifs with hq0 hge hqs hq1 hp
  · -- `q = 0`, `b > 1`
    rw [(AzRat.toRat_eq_zero_iff q).mpr hq0, EReal.coe_zero, Spec.logBaseFloat_zero_left hbv,
      ite_eq_left (hlt.mpr hge).le]
    exact (roundVal_inf p mode false).symm
  · -- `q = 0`, `b < 1`
    rw [(AzRat.toRat_eq_zero_iff q).mpr hq0, EReal.coe_zero, Spec.logBaseFloat_zero_left hbv,
      ite_eq_right (fun h' => hge (hlt.mp (lt_of_le_of_ne h' (Ne.symm hb1))))]
    exact (roundVal_inf p mode true).symm
  · -- `q = 1`
    have hq := toRat_pos_of_sign q hqs hq0
    have hqv : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
    rw [Spec.logBaseFloat_coe_coe hqv hbv hb1, (toRat_eq_one_iff q hqs).mpr hq1, Rat.cast_one,
      Real.log_one, zero_div, EReal.coe_zero, roundVal_zero]
  · exact absurd hp (NeZero.ne p)
  · have hq := toRat_pos_of_sign q hqs hq0
    have hqv : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
    rw [Spec.logBaseFloat_coe_coe hqv hbv hb1]
    exact logBaseRatRatFinite_eq q _ _ b hb hb1 p mode
  · have hneg := toRat_neg_of_sign q (by simpa using hqs) hq0
    rw [Spec.logBaseFloat_neg_left (EReal.coe_neg'.mpr hneg), roundVal_none]

/-- **`log_b q` with rationals is correctly rounded.** -/
theorem logBaseRatRatPrecRound_eq (q b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatRatPrecRound q b p mode
      = roundVal p mode
          (Spec.logBaseFloat ((AzRat.toRat q : ℝ) : EReal) ((AzRat.toRat b : ℝ) : EReal)) := by
  unfold logBaseRatRatPrecRound
  split_ifs with h0 hs h1
  · rw [(AzRat.toRat_eq_zero_iff b).mpr h0, EReal.coe_zero, logBaseRatFloatPrecRound_eq]
    simp only [toVal_zero, Option.bind_some]
  · rw [(toRat_eq_one_iff b hs).mpr h1, Rat.cast_one, EReal.coe_one, logBaseRatFloatPrecRound_eq]
    simp only [toVal_one', Option.bind_some, EReal.coe_one]
  · exact logBaseRatRatPos_eq q b _ _ p mode
  · have hneg := toRat_neg_of_sign b (by simpa using hs) h0
    rw [Spec.logBaseFloat_neg_right _ (EReal.coe_neg'.mpr hneg), roundVal_none]

end Azurite.AzFloat
