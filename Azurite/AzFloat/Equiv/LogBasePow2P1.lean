/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBasePow2P1
import Azurite.AzFloat.Equiv.LogBasePow2
import Azurite.AzFloat.Equiv.Log2p1

/-!
# Equivalence: `log_{2^k} (1 + x)`

`logBasePow2P1PrecRound_eq_liftVal : logBasePow2P1PrecRound x k p mode = liftVal (fun a =>
Spec.logBasePow2 k.toInt (a + 1)) x p mode` for `k ≠ 0`: `log_{2^k} (1 + x)` is correctly rounded
in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The finite case: the exact branch and the Ziv loop round `log₂ (1 + x) / k`. -/
theorem logBasePow2P1Finite_eq (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (k : AzInt) (hk : k ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBasePow2P1Finite s e hv hgt k hk p mode
      = roundVal p mode
          (some ((Real.logb 2 (1 + finiteVal s e m) / k.toInt : ℝ) : EReal)) := by
  have hpos : 0 < 1 + finiteVal s e m := by linarith
  have hw : NeZero (p + zivGuardBits + leadingZeroBits e) := ⟨by unfold zivGuardBits; omega⟩
  unfold logBasePow2P1Finite
  split
  · rename_i j hj
    rw [ofAzRatRound_eq_roundVal, AzRat.toRat_ofAzInts,
      onePlusPow2Exponent?_some (toVal_finite s e q m hv) _ hj, logb_two_zpow]
    push_cast
    rfl
  · rename_i hj
    have hirr := Irrational.div_intCast
      (irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
        (w := p + zivGuardBits + leadingZeroBits e) (by unfold zivGuardBits; omega) hpos hj)
      (toInt_ne_zero_of_ne_zero hk)
    exact zivLoopCertified_eq_threshold p mode _
      (Real.logb 2 (1 + finiteVal s e m) / k.toInt) _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBasePow2P1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
            (toVal_finite s e q m hv) hgt k hk hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- **`log_{2^k} (1 + x)` is correctly rounded.** -/
theorem logBasePow2P1PrecRound_eq_liftVal (x : AzFloat) (k : AzInt) (hk : k ≠ 0) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    logBasePow2P1PrecRound x k p mode
      = liftVal (fun a => Spec.logBasePow2 k.toInt (a + 1)) x p mode := by
  have hkI := toInt_ne_zero_of_ne_zero hk
  unfold logBasePow2P1PrecRound liftVal
  rw [dite_eq_right hk]
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some, EReal.bot_add,
        Spec.logBasePow2_bot, roundVal_none]
    · simp only [toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.logBasePow2_top _ hkI,
        sign_eq_decide_pos_toInt k hk]
      rcases lt_or_gt_of_ne hkI with h | h
      · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
        exact (roundVal_inf p mode false).symm
      · rw [ite_eq_left h, decide_eq_true h]
        exact (roundVal_inf p mode true).symm
  | zero =>
    simp only [toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.logBasePow2_coe _ _ one_pos, Real.logb_one, zero_div,
      EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBasePow2_coe _ _ (by linarith),
        add_comm (finiteVal true e m) 1]
      exact logBasePow2P1Finite_eq true e hv _ k hk p mode
    | false =>
      simp only [toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.logBasePow2_zero _ hkI, sign_eq_decide_pos_toInt k hk]
        rcases lt_or_gt_of_ne hkI with h | h
        · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
          exact (roundVal_inf p mode true).symm
        · rw [ite_eq_left h, decide_eq_true h]
          exact (roundVal_inf p mode false).symm
      · have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBasePow2_coe_neg _ _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBasePow2_coe _ _ (by linarith),
          add_comm (finiteVal false e m) 1]
        exact logBasePow2P1Finite_eq false e hv hgt k hk p mode

end Azurite.AzFloat
