/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseP1
import Azurite.AzFloat.Equiv.LogBase
import Azurite.AzFloat.Equiv.Log2p1

/-!
# Equivalence: `log_b (1 + x)`

`logBaseP1PrecRound_eq_liftVal : logBaseP1PrecRound x b p mode = liftVal (fun a => Spec.logBase
b.toNat (a + 1)) x p mode` for `2 ≤ b`: `log_b (1 + x)` is correctly rounded in every mode, with
the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The finite case: both exact branches and both Ziv loops round `ln (1 + x) / ln b`. -/
theorem logBaseP1Finite_eq (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : UInt64) (hb : 2 ≤ b.toNat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseP1Finite s e hv hgt b hb p mode
      = roundVal p mode
          (some ((Real.log (1 + finiteVal s e m) / Real.log b.toNat : ℝ) : EReal)) := by
  have hpos : 0 < 1 + finiteVal s e m := by linarith
  have hw : NeZero (p + zivGuardBits + leadingZeroBits e) := ⟨by unfold zivGuardBits; omega⟩
  unfold logBaseP1Finite
  split
  · -- a power-of-two base
    next k hk =>
      have hbk : b.toNat = 2 ^ k := by
        have := (AzNat.checkedLogBase2_eq_some_iff _ k).mp hk
        rwa [AzNat.toNat_ofNat] at this
      split
      · next j hj =>
        rw [ofAzRatRound_eq_roundVal, AzRat.toRat_ofAzInts, toInt_toAzInt, AzNat.toNat_ofNat,
          onePlusPow2Exponent?_some (toVal_finite s e q m hv) _ hj, hbk, log_div_log_two_pow,
          logb_two_zpow]
        push_cast
        rfl
      · next hj =>
        have hirr := irrational_log_div_log_one_add_of_pow2 s e hv hgt b hb hk
          (w := p + zivGuardBits + leadingZeroBits e) (by unfold zivGuardBits; omega) hj
        exact zivLoopCertified_eq_threshold p mode _
          (Real.log (1 + finiteVal s e m) / Real.log b.toNat) _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              logBaseP1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
                (toVal_finite s e q m hv) hgt b hb hirr
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
  · next hk =>
    split
    · next r hx =>
      obtain ⟨v, hvv, -, hval⟩ :=
        logBaseP1Exact?_some _ _ (by rw [AzNat.toNat_ofNat]; exact hb) r hx
      rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hvv
      rw [ofAzRatRound_eq_roundVal, ← hval, hvv, AzNat.toNat_ofNat]
    · next hx =>
      have hirr := AzNat.toNat_ofNat b.toNat ▸
        irrational_of_logBaseP1Exact?_none s e hv (AzNat.ofNat b.toNat)
          (by rw [AzNat.toNat_ofNat]; exact hb) (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt)
          ((AzNat.checkedLogBase2_eq_none_iff _).mp hk) hgt hx
      exact zivLoopCertified_eq_threshold p mode _
        (Real.log (1 + finiteVal s e m) / Real.log b.toNat) _ (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
            logBaseP1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
              (toVal_finite s e q m hv) hgt b hb hirr
          exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- **`log_b (1 + x)` is correctly rounded.** -/
theorem logBaseP1PrecRound_eq_liftVal (x : AzFloat) (b : UInt64) (hb : 2 ≤ b.toNat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    logBaseP1PrecRound x b p mode
      = liftVal (fun a => Spec.logBase b.toNat (a + 1)) x p mode := by
  unfold logBaseP1PrecRound liftVal
  rw [dite_eq_right (not_lt.mpr hb)]
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some, EReal.bot_add,
        Spec.logBase_bot, roundVal_none]
    · simp only [toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.logBase_top _ hb, roundVal_top]
  | zero =>
    simp only [toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.logBase_coe _ hb _ one_pos, Real.log_one, zero_div,
      EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBase_coe _ hb _ (by linarith),
        add_comm (finiteVal true e m) 1]
      exact logBaseP1Finite_eq true e hv _ b hb p mode
    | false =>
      simp only [toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.logBase_zero _ hb, roundVal_bot]
      · have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBase_coe_neg _ _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBase_coe _ hb _ (by linarith),
          add_comm (finiteVal false e m) 1]
        exact logBaseP1Finite_eq false e hv hgt b hb p mode

end Azurite.AzFloat
