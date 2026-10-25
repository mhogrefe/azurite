/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloatP1
import Azurite.AzFloat.Equiv.LogBaseFloat

/-!
# Equivalence: `log_b (1 + x)` in a float base

`logBaseFloatP1PrecRound_eq_liftVal₂ : logBaseFloatP1PrecRound x b p mode = liftVal₂ (fun a bv
=> Spec.logBaseFloat (a + 1) bv) x b p mode`: `log_b (1 + x)` is correctly rounded in every
mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

theorem one_ne_bot : (1 : EReal) ≠ ⊥ := by rw [← EReal.coe_one]; exact EReal.coe_ne_bot 1

/-- The general case rounds `ln (1 + x) / ln b`. -/
theorem logBaseFloatP1Finite_eq (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseFloatP1Finite s e hv hgt eb hvb hb1 p mode
      = roundVal p mode
          (some ((Real.log (1 + finiteVal s e m) / Real.log (finiteVal true eb mb) : ℝ) :
            EReal)) := by
  unfold logBaseFloatP1Finite
  split
  · rename_i r hx
    rw [ofAzRatRound_eq_roundVal, logBaseFloatP1_exact_value s e hv hgt eb hvb hb1 r hx]
  · rename_i hx
    have hirr := irrational_logBaseFloatP1_of_none s e hv hgt eb hvb hb1 hx
    exact zivLoopCertified_eq_threshold p mode _ _ _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBaseFloatP1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
            (toVal_finite s e q m hv) hgt eb hvb hb1 hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- Finite `x > −1`: the dispatch on the base rounds the specification at `1 + x`. -/
theorem logBaseFloatP1Pos_eq (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseFloatP1Pos s e hv hgt b p mode
      = roundVal p mode
          (b.toVal.bind fun bv => Spec.logBaseFloat ((1 + finiteVal s e m : ℝ) : EReal) bv) := by
  have hx : 0 < 1 + finiteVal s e m := by linarith
  have hx1 : 1 + finiteVal s e m ≠ 1 := fun h => finiteVal_ne_zero s e hv (by linarith)
  cases b with
  | nan => rfl
  | infinity sb =>
    cases sb
    · simp only [logBaseFloatP1Pos, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, Spec.logBaseFloat_neg_right _ EReal.bot_lt_zero, roundVal_none]
    · simp only [logBaseFloatP1Pos, toVal_infinity, ↓reduceIte, Option.bind_some,
        Spec.logBaseFloat_coe_top hx, roundVal_zero]
  | zero =>
    simp only [logBaseFloatP1Pos, toVal_zero, Option.bind_some, Spec.logBaseFloat_coe_zero hx,
      roundVal_zero]
  | finite sb eb qb mb hvb =>
    cases sb with
    | false =>
      simp only [logBaseFloatP1Pos, toVal_finite, Option.bind_some]
      rw [finiteVal_false, Spec.logBaseFloat_neg_right _
        (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos eb hvb))), roundVal_none]
    | true =>
      have hb := finiteVal_true_pos eb hvb
      simp only [logBaseFloatP1Pos, toVal_finite, Option.bind_some]
      split_ifs with hb1 hp
      · -- `b = 1`: `±∞` by the sign of `x`
        rw [finiteVal_eq_one_of_eqIEEE eb hvb hb1, EReal.coe_one, Spec.logBaseFloat_coe_one hx,
          ite_eq_right hx1]
        cases s with
        | true =>
          rw [ite_eq_left (by linarith [finiteVal_true_pos e hv])]
          exact (roundVal_inf p mode true).symm
        | false =>
          have := finiteVal_true_pos e hv
          rw [finiteVal_false] at hgt ⊢
          rw [ite_eq_right (by push Not; linarith)]
          exact (roundVal_inf p mode false).symm
      · exact absurd hp (NeZero.ne p)
      · have hbne := finiteVal_ne_one_of_not_eqIEEE eb hvb hb1
        rw [Spec.logBaseFloat_coe_coe hx hb hbne]
        exact logBaseFloatP1Finite_eq s e hv hgt eb hvb hbne p mode

/-- **`log_b (1 + x)` with a float base is correctly rounded.** -/
theorem logBaseFloatP1PrecRound_eq_liftVal₂ (x b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseFloatP1PrecRound x b p mode
      = liftVal₂ (fun a bv => Spec.logBaseFloat (a + 1) bv) x b p mode := by
  cases x with
  | nan => rfl
  | infinity sx =>
    cases sx with
    | false =>
      unfold liftVal₂
      simp only [logBaseFloatP1PrecRound, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, EReal.bot_add]
      rw [bind_none_of_forall (Spec.logBaseFloat_neg_left EReal.bot_lt_zero), roundVal_none]
    | true =>
      simp only [logBaseFloatP1PrecRound]
      rw [logBaseFloatPrecRound_eq_liftVal₂]
      unfold liftVal₂
      simp only [toVal_infinity, ↓reduceIte, Option.bind_some, EReal.top_add_of_ne_bot one_ne_bot]
  | zero =>
    simp only [logBaseFloatP1PrecRound]
    rw [logBaseFloatPrecRound_eq_liftVal₂]
    unfold liftVal₂
    simp only [toVal_zero, toVal_one', Option.bind_some, zero_add, EReal.coe_one]
  | finite sx ex qx mx hvx =>
    cases sx with
    | true =>
      unfold liftVal₂
      simp only [logBaseFloatP1PrecRound, toVal_finite, Option.bind_some]
      rw [logBaseFloatP1Pos_eq, ← EReal.coe_one, ← EReal.coe_add, add_comm (finiteVal true ex mx) 1]
    | false =>
      simp only [logBaseFloatP1PrecRound]
      split_ifs with hneg heq
      · -- `x = −1`: `log_b 0`
        rw [logBaseFloatPrecRound_eq_liftVal₂]
        unfold liftVal₂
        obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        simp only [toVal_zero, toVal_finite, Option.bind_some]
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero]
      · -- `x < −1`
        unfold liftVal₂
        have hle := finiteVal_false_le_neg_one ex hvx hneg
        have hne : finiteVal false ex mx ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false ex mx + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        simp only [toVal_finite, Option.bind_some]
        rw [← EReal.coe_one, ← EReal.coe_add,
          bind_none_of_forall (Spec.logBaseFloat_neg_left (EReal.coe_neg'.mpr hlt)), roundVal_none]
      · unfold liftVal₂
        simp only [toVal_finite, Option.bind_some]
        rw [logBaseFloatP1Pos_eq, ← EReal.coe_one, ← EReal.coe_add,
          add_comm (finiteVal false ex mx) 1]

end Azurite.AzFloat
