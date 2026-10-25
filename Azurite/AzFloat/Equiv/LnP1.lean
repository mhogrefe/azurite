/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnP1
import Azurite.AzFloat.Equiv.Ln

/-!
# Equivalence: `ln (1 + x)`

`lnP1PrecRound_eq_liftVal : lnP1PrecRound x p mode = liftVal (fun a => Spec.log (a + 1)) x p mode`:
`ln (1 + x)` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`ln (1 + x)` is correctly rounded.** -/
theorem lnP1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnP1PrecRound x p mode = liftVal (fun a => Spec.log (a + 1)) x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [lnP1PrecRound, toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
        EReal.bot_add, Spec.log_bot, roundVal_none]
    · simp only [lnP1PrecRound, toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.log_top, roundVal_top]
  | zero =>
    simp only [lnP1PrecRound, toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.log_coe _ one_pos, Real.log_one, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [lnP1PrecRound, toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.log_coe _ (by linarith),
        add_comm (finiteVal true e m) 1]
      exact zivLoopCertified_eq_threshold p mode _ (Real.log (1 + finiteVal true e m)) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
            lnP1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
              (toVal_finite true e q m hv) (by linarith) hpos.ne'
          exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    | false =>
      simp only [lnP1PrecRound, toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · -- `x = −1`
        obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, Spec.log_zero,
          roundVal_bot]
      · -- `x < −1`
        have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log_coe_neg _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log_coe _ (by linarith),
          add_comm (finiteVal false e m) 1]
        exact zivLoopCertified_eq_threshold p mode _ (Real.log (1 + finiteVal false e m)) _
          (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              lnP1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
                (toVal_finite false e q m hv) hgt (finiteVal_false_ne_zero e hv)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
