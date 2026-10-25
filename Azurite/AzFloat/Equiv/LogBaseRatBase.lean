/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatBase
import Azurite.AzFloat.Equiv.LogBaseFloat

/-!
# Equivalence: the logarithm in a rational base

`logBaseRatBasePrecRound_eq : logBaseRatBasePrecRound x b p mode = roundVal p mode (x.toVal.bind
fun a => Spec.logBaseFloat a (toRat b))`: `log_b x` with a rational base is correctly rounded in
every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The general case rounds `ln x / ln b`. -/
theorem logBaseRatBaseFinite_eq (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (hx1 : finiteVal true ex mx ≠ 1) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatBaseFinite ex hvx hx1 b hb hb1 p mode
      = roundVal p mode
          (some ((Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ) : ℝ) :
            EReal)) := by
  unfold logBaseRatBaseFinite
  split
  · rename_i r hx
    rw [ofAzRatRound_eq_roundVal, logBaseRatBase_exact_value ex hvx b
      (sign_eq_true_of_toRat_pos b hb) (num_ne_zero_of_toRat_pos b hb) hb1 r hx]
  · rename_i hx
    have hirr := irrational_logBaseRatBase_of_none ex hvx hx1 b (sign_eq_true_of_toRat_pos b hb)
      (num_ne_zero_of_toRat_pos b hb) hb1 hx
    exact zivLoopCertified_eq_threshold p mode _ _ _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBaseRatBaseApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) ex hvx b hb hb1
            hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- `b > 0`, `b ≠ 1`: the dispatch on `x` rounds the specification. -/
theorem logBaseRatBasePos_eq (x : AzFloat) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatBasePos x b hb hb1 p mode
      = roundVal p mode
          (x.toVal.bind fun a => Spec.logBaseFloat a ((AzRat.toRat b : ℝ) : EReal)) := by
  have hbv : (0 : ℝ) < (AzRat.toRat b : ℝ) := by exact_mod_cast hb
  have hs := sign_eq_true_of_toRat_pos b hb
  have hlt := one_lt_toRat_iff b hs
  cases x with
  | nan => rfl
  | infinity sx =>
    cases sx
    · simp only [logBaseRatBasePos, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, Spec.logBaseFloat_neg_left EReal.bot_lt_zero, roundVal_none]
    · simp only [logBaseRatBasePos, toVal_infinity, ↓reduceIte, Option.bind_some,
        Spec.logBaseFloat_top_left hbv]
      by_cases hge : b.den < b.num
      · rw [ite_eq_left hge, ite_eq_left (hlt.mpr hge).le]
        exact (roundVal_inf p mode true).symm
      · rw [ite_eq_right hge,
          ite_eq_right (fun h' => hge (hlt.mp (lt_of_le_of_ne h' (Ne.symm hb1))))]
        exact (roundVal_inf p mode false).symm
  | zero =>
    simp only [logBaseRatBasePos, toVal_zero, Option.bind_some, Spec.logBaseFloat_zero_left hbv]
    by_cases hge : b.den < b.num
    · rw [ite_eq_left hge, ite_eq_left (hlt.mpr hge).le]
      exact (roundVal_inf p mode false).symm
    · rw [ite_eq_right hge,
        ite_eq_right (fun h' => hge (hlt.mp (lt_of_le_of_ne h' (Ne.symm hb1))))]
      exact (roundVal_inf p mode true).symm
  | finite sx ex qx mx hvx =>
    cases sx with
    | false =>
      simp only [logBaseRatBasePos, toVal_finite, Option.bind_some]
      rw [finiteVal_false, Spec.logBaseFloat_neg_left
        (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos ex hvx))), roundVal_none]
    | true =>
      have hx := finiteVal_true_pos ex hvx
      simp only [logBaseRatBasePos, toVal_finite, Option.bind_some]
      split_ifs with hx1 hp
      · rw [Spec.logBaseFloat_coe_coe hx hbv hb1, finiteVal_eq_one_of_eqIEEE ex hvx hx1,
          Real.log_one, zero_div, EReal.coe_zero, roundVal_zero]
      · exact absurd hp (NeZero.ne p)
      · rw [Spec.logBaseFloat_coe_coe hx hbv hb1]
        exact logBaseRatBaseFinite_eq ex hvx _ b hb hb1 p mode

/-- **`log_b x` with a rational base is correctly rounded.** -/
theorem logBaseRatBasePrecRound_eq (x : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseRatBasePrecRound x b p mode
      = roundVal p mode
          (x.toVal.bind fun a => Spec.logBaseFloat a ((AzRat.toRat b : ℝ) : EReal)) := by
  unfold logBaseRatBasePrecRound
  split_ifs with h0 hs h1
  · rw [(AzRat.toRat_eq_zero_iff b).mpr h0, EReal.coe_zero, logBaseFloatPrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_zero, Option.bind_some]
  · rw [(toRat_eq_one_iff b hs).mpr h1, Rat.cast_one, EReal.coe_one,
      logBaseFloatPrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_one', Option.bind_some, EReal.coe_one]
  · exact logBaseRatBasePos_eq x b _ _ p mode
  · have hneg := toRat_neg_of_sign b (by simpa using hs) h0
    rw [bind_none_of_forall (fun a => Spec.logBaseFloat_neg_right a (EReal.coe_neg'.mpr hneg)),
      roundVal_none]

end Azurite.AzFloat
