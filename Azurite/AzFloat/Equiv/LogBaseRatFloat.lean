/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatFloat
import Azurite.AzFloat.Equiv.LogBaseFloat

/-!
# Equivalence: the logarithm of a rational in a float base

`logBaseRatFloatPrecRound_eq : logBaseRatFloatPrecRound q b p mode = roundVal p mode
(b.toVal.bind fun bv => Spec.logBaseFloat (toRat q) bv)`: `log_b q` is correctly rounded in
every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The general case rounds `ln q / ln b`. -/
theorem logBaseRatFloatFinite_eq (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatFloatFinite q hq hq1 eb hvb hb1 p mode
      = roundVal p mode
          (some ((Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb) : ℝ) :
            EReal)) := by
  unfold logBaseRatFloatFinite
  split
  · rename_i r hx
    rw [ofAzRatRound_eq_roundVal, logBaseRatFloat_exact_value q (sign_eq_true_of_toRat_pos q hq)
      (num_ne_zero_of_toRat_pos q hq) eb hvb hb1 r hx]
  · rename_i hx
    have hirr := irrational_logBaseRatFloat_of_none q (sign_eq_true_of_toRat_pos q hq)
      (num_ne_zero_of_toRat_pos q hq) hq1 eb hvb hb1 hx
    exact zivLoopCertified_eq_threshold p mode _ _ _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBaseRatFloatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hq eb hvb hb1
            hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- `q > 0`, `q ≠ 1`: the dispatch on the base rounds the specification. -/
theorem logBaseRatFloatPos_eq (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatFloatPos q hq hq1 b p mode
      = roundVal p mode
          (b.toVal.bind fun bv => Spec.logBaseFloat ((AzRat.toRat q : ℝ) : EReal) bv) := by
  have hx : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  have hs := sign_eq_true_of_toRat_pos q hq
  cases b with
  | nan => rfl
  | infinity sb =>
    cases sb
    · simp only [logBaseRatFloatPos, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, Spec.logBaseFloat_neg_right _ EReal.bot_lt_zero, roundVal_none]
    · simp only [logBaseRatFloatPos, toVal_infinity, ↓reduceIte, Option.bind_some,
        Spec.logBaseFloat_coe_top hx, roundVal_zero]
  | zero =>
    simp only [logBaseRatFloatPos, toVal_zero, Option.bind_some, Spec.logBaseFloat_coe_zero hx,
      roundVal_zero]
  | finite sb eb qb mb hvb =>
    cases sb with
    | false =>
      simp only [logBaseRatFloatPos, toVal_finite, Option.bind_some]
      rw [finiteVal_false, Spec.logBaseFloat_neg_right _
        (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos eb hvb))), roundVal_none]
    | true =>
      have hb := finiteVal_true_pos eb hvb
      simp only [logBaseRatFloatPos, toVal_finite, Option.bind_some]
      split_ifs with hb1 hgt hp
      · rw [finiteVal_eq_one_of_eqIEEE eb hvb hb1, EReal.coe_one, Spec.logBaseFloat_coe_one hx,
          ite_eq_right hq1, ite_eq_left ((one_lt_toRat_iff q hs).mpr hgt)]
        exact (roundVal_inf p mode true).symm
      · rw [finiteVal_eq_one_of_eqIEEE eb hvb hb1, EReal.coe_one, Spec.logBaseFloat_coe_one hx,
          ite_eq_right hq1, ite_eq_right (mt (one_lt_toRat_iff q hs).mp hgt)]
        exact (roundVal_inf p mode false).symm
      · exact absurd hp (NeZero.ne p)
      · have hbne := finiteVal_ne_one_of_not_eqIEEE eb hvb hb1
        rw [Spec.logBaseFloat_coe_coe hx hb hbne]
        exact logBaseRatFloatFinite_eq q hq hq1 eb hvb hbne p mode

/-- **`log_b q` with a float base is correctly rounded.** -/
theorem logBaseRatFloatPrecRound_eq (q : AzRat) (b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseRatFloatPrecRound q b p mode
      = roundVal p mode
          (b.toVal.bind fun bv => Spec.logBaseFloat ((AzRat.toRat q : ℝ) : EReal) bv) := by
  unfold logBaseRatFloatPrecRound
  split_ifs with h0 hs h1
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, EReal.coe_zero, logBaseFloatPrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_zero, Option.bind_some]
  · rw [(toRat_eq_one_iff q hs).mpr h1, Rat.cast_one, EReal.coe_one,
      logBaseFloatPrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_one', Option.bind_some, EReal.coe_one]
  · exact logBaseRatFloatPos_eq q _ _ b p mode
  · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
    rw [bind_none_of_forall (Spec.logBaseFloat_neg_left (EReal.coe_neg'.mpr hneg)), roundVal_none]

end Azurite.AzFloat
