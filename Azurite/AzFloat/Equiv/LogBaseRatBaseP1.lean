/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatBaseP1
import Azurite.AzFloat.Equiv.LogBaseFloatP1
import Azurite.AzFloat.Equiv.LogBaseRatBase

/-!
# Equivalence: `log_b (1 + x)` in a rational base

`logBaseRatBaseP1PrecRound_eq : logBaseRatBaseP1PrecRound x b p mode = roundVal p mode
(x.toVal.bind fun a => Spec.logBaseFloat (a + 1) (toRat b))`: `log_b (1 + x)` with a rational
base is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The general case rounds `ln (1 + x) / ln b`. -/
theorem logBaseRatBaseP1Finite_eq (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatBaseP1Finite s e hv hgt b hb hb1 p mode
      = roundVal p mode
          (some ((Real.log (1 + finiteVal s e m) / Real.log (AzRat.toRat b : ℝ) : ℝ) :
            EReal)) := by
  unfold logBaseRatBaseP1Finite
  split
  · rename_i r hx
    rw [ofAzRatRound_eq_roundVal, logBaseRatBaseP1_exact_value s e hv hgt b
      (sign_eq_true_of_toRat_pos b hb) (num_ne_zero_of_toRat_pos b hb) hb1 r hx]
  · rename_i hx
    have hirr := irrational_logBaseRatBaseP1_of_none s e hv hgt b (sign_eq_true_of_toRat_pos b hb)
      (num_ne_zero_of_toRat_pos b hb) hb1 hx
    exact zivLoopCertified_eq_threshold p mode _ _ _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBaseRatBaseP1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
            (toVal_finite s e q m hv) hgt b hb hb1 hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- Finite `x > −1`: the precision check rounds the specification at `1 + x`. -/
theorem logBaseRatBaseP1Pos_eq (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatBaseP1Pos s e hv hgt b hb hb1 p mode
      = roundVal p mode
          (Spec.logBaseFloat ((1 + finiteVal s e m : ℝ) : EReal)
            ((AzRat.toRat b : ℝ) : EReal)) := by
  have hx : 0 < 1 + finiteVal s e m := by linarith
  have hbv : (0 : ℝ) < (AzRat.toRat b : ℝ) := by exact_mod_cast hb
  unfold logBaseRatBaseP1Pos
  rw [dite_eq_right (NeZero.ne p), Spec.logBaseFloat_coe_coe hx hbv hb1]
  exact logBaseRatBaseP1Finite_eq s e hv hgt b hb hb1 p mode

/-- `b > 0`, `b ≠ 1`: the dispatch on `x` rounds the specification at `1 + x`. -/
theorem logBaseRatBaseP1Dispatch_eq (x : AzFloat) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatBaseP1Dispatch x b hb hb1 p mode
      = roundVal p mode
          (x.toVal.bind fun a => Spec.logBaseFloat (a + 1) ((AzRat.toRat b : ℝ) : EReal)) := by
  have hbv : (0 : ℝ) < (AzRat.toRat b : ℝ) := by exact_mod_cast hb
  have hs := sign_eq_true_of_toRat_pos b hb
  have hlt := one_lt_toRat_iff b hs
  cases x with
  | nan => rfl
  | infinity sx =>
    cases sx
    · simp only [logBaseRatBaseP1Dispatch, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, EReal.bot_add, Spec.logBaseFloat_neg_left EReal.bot_lt_zero,
        roundVal_none]
    · simp only [logBaseRatBaseP1Dispatch, toVal_infinity, ↓reduceIte, Option.bind_some,
        EReal.top_add_of_ne_bot one_ne_bot, Spec.logBaseFloat_top_left hbv]
      by_cases hge : b.den < b.num
      · rw [ite_eq_left hge, ite_eq_left (hlt.mpr hge).le]
        exact (roundVal_inf p mode true).symm
      · rw [ite_eq_right hge,
          ite_eq_right (fun h' => hge (hlt.mp (lt_of_le_of_ne h' (Ne.symm hb1))))]
        exact (roundVal_inf p mode false).symm
  | zero =>
    simp only [logBaseRatBaseP1Dispatch, toVal_zero, Option.bind_some, zero_add]
    rw [← EReal.coe_one, Spec.logBaseFloat_coe_coe one_pos hbv hb1, Real.log_one, zero_div,
      EReal.coe_zero, roundVal_zero]
  | finite sx ex qx mx hvx =>
    cases sx with
    | true =>
      simp only [logBaseRatBaseP1Dispatch, toVal_finite, Option.bind_some]
      rw [logBaseRatBaseP1Pos_eq, ← EReal.coe_one, ← EReal.coe_add,
        add_comm (finiteVal true ex mx) 1]
    | false =>
      simp only [logBaseRatBaseP1Dispatch, toVal_finite, Option.bind_some]
      split_ifs with hneg heq hge
      · -- `x = −1`: `log_b 0 = −∞`
        obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.logBaseFloat_zero_left hbv, ite_eq_left (hlt.mpr hge).le]
        exact (roundVal_inf p mode false).symm
      · -- `x = −1`: `log_b 0 = ∞`
        obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.logBaseFloat_zero_left hbv,
          ite_eq_right (fun h' => hge (hlt.mp (lt_of_le_of_ne h' (Ne.symm hb1))))]
        exact (roundVal_inf p mode true).symm
      · -- `x < −1`
        have hle := finiteVal_false_le_neg_one ex hvx hneg
        have hne : finiteVal false ex mx ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt' : finiteVal false ex mx + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBaseFloat_neg_left (EReal.coe_neg'.mpr hlt'),
          roundVal_none]
      · rw [logBaseRatBaseP1Pos_eq, ← EReal.coe_one, ← EReal.coe_add,
          add_comm (finiteVal false ex mx) 1]

/-- **`log_b (1 + x)` with a rational base is correctly rounded.** -/
theorem logBaseRatBaseP1PrecRound_eq (x : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseRatBaseP1PrecRound x b p mode
      = roundVal p mode
          (x.toVal.bind fun a => Spec.logBaseFloat (a + 1) ((AzRat.toRat b : ℝ) : EReal)) := by
  unfold logBaseRatBaseP1PrecRound
  split_ifs with h0 hs h1
  · rw [(AzRat.toRat_eq_zero_iff b).mpr h0, EReal.coe_zero, logBaseFloatP1PrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_zero, Option.bind_some]
  · rw [(toRat_eq_one_iff b hs).mpr h1, Rat.cast_one, EReal.coe_one,
      logBaseFloatP1PrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_one', Option.bind_some, EReal.coe_one]
  · exact logBaseRatBaseP1Dispatch_eq x b _ _ p mode
  · have hneg := toRat_neg_of_sign b (by simpa using hs) h0
    rw [bind_none_of_forall (fun a => Spec.logBaseFloat_neg_right _ (EReal.coe_neg'.mpr hneg)),
      roundVal_none]

end Azurite.AzFloat
