/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2p1
import Azurite.AzFloat.Equiv.Log2

/-!
# Equivalence: `log₂ (1 + x)`

`log2p1PrecRound_eq_liftVal : log2p1PrecRound x p mode = liftVal (fun a => Spec.log2 (a + 1)) x p
mode`: `log₂ (1 + x)` is correctly rounded in every mode, with the exact comparison, and
without fuel.
-/

namespace Azurite.AzFloat

/-- The finite case of `log2p1PrecRound`: the exact branch or the Ziv loop. -/
theorem log2p1_finite_eq (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool) (e : AzInt) {q : ℕ}
    {m : AzNat} (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) :
    (match h : onePlusPow2Exponent? (finite s e q m hv) (p + zivGuardBits + leadingZeroBits e)
        with
      | some k => setPrecRound (ofAzInt k) p mode
      | none =>
        zivLoopCertified (log2p1Approx (finite s e q m hv)) p mode
          (p + zivGuardBits + leadingZeroBits e)
          (log2p1Approx_isSome_exists p mode (toVal_finite s e q m hv) hgt
            (irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
              (by unfold zivGuardBits; omega) (by linarith) h)
            _ (by unfold zivGuardBits; omega)))
      = roundVal p mode (some ((Real.logb 2 (1 + finiteVal s e m) : ℝ) : EReal)) := by
  have hpos : 0 < 1 + finiteVal s e m := by linarith
  have hw : NeZero (p + zivGuardBits + leadingZeroBits e) := ⟨by unfold zivGuardBits; omega⟩
  split
  · rename_i k h
    rw [setPrecRound_eq_roundVal (toVal_ofAzInt k),
      onePlusPow2Exponent?_some (toVal_finite s e q m hv) _ h, logb_two_zpow]
  · rename_i h
    have hirr := irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
      (w := p + zivGuardBits + leadingZeroBits e) (by unfold zivGuardBits; omega) hpos h
    exact zivLoopCertified_eq_threshold p mode _ (Real.logb 2 (1 + finiteVal s e m)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          log2p1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
            (toVal_finite s e q m hv) hgt hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- **`log₂ (1 + x)` is correctly rounded.** -/
theorem log2p1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2p1PrecRound x p mode = liftVal (fun a => Spec.log2 (a + 1)) x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [log2p1PrecRound, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, EReal.bot_add, Spec.log2_bot, roundVal_none]
    · simp only [log2p1PrecRound, toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.log2_top, roundVal_top]
  | zero =>
    simp only [log2p1PrecRound, toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.log2_coe _ one_pos, Real.logb_one, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [log2p1PrecRound, toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.log2_coe _ (by linarith),
        add_comm (finiteVal true e m) 1]
      exact log2p1_finite_eq p mode true e hv (by linarith)
    | false =>
      simp only [log2p1PrecRound, toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.log2_zero, roundVal_bot]
      · have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log2_coe_neg _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log2_coe _ (by linarith),
          add_comm (finiteVal false e m) 1]
        exact log2p1_finite_eq p mode false e hv hgt

end Azurite.AzFloat
