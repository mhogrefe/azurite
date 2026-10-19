/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2
import Azurite.AzFloat.Equiv.Ln

/-!
# Equivalence: the base-2 logarithm

* `Spec.log2`: the extended-real `log₂` (`NaN` on negatives and `−∞`, `log₂ 0 = −∞`,
  `log₂ ∞ = ∞`).
* `log2PrecRound_eq_liftVal : log2PrecRound x p mode = liftVal Spec.log2 x p mode`: `log₂` is
  correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real base-2 logarithm: undefined (`NaN`) on negatives (including `−∞`),
`log₂ 0 = −∞`, `log₂ ∞ = ∞`. -/
noncomputable def log2 (a : EReal) : Option EReal :=
  if a < 0 then none else if a = 0 then some ⊥ else if a = ⊤ then some ⊤
  else some ((Real.logb 2 a.toReal : ℝ) : EReal)

theorem log2_coe (r : ℝ) (hr : 0 < r) : log2 (r : EReal) = some ((Real.logb 2 r : ℝ) : EReal) := by
  unfold log2
  rw [ite_eq_right (not_lt.mpr (EReal.coe_nonneg.mpr hr.le)),
    ite_eq_right (mt EReal.coe_eq_zero.mp hr.ne'), ite_eq_right (EReal.coe_ne_top r),
    EReal.toReal_coe]

theorem log2_coe_neg (r : ℝ) (hr : r < 0) : log2 (r : EReal) = none := by
  unfold log2
  rw [ite_eq_left (EReal.coe_neg'.mpr hr)]

@[simp] theorem log2_top : log2 ⊤ = some ⊤ := by
  unfold log2
  rw [ite_eq_right (not_lt.mpr le_top), ite_eq_right (EReal.zero_ne_top).symm, ite_eq_left rfl]

@[simp] theorem log2_bot : log2 ⊥ = none := by
  unfold log2
  rw [ite_eq_left EReal.bot_lt_zero]

@[simp] theorem log2_zero : log2 0 = some ⊥ := by
  unfold log2
  rw [ite_eq_right (lt_irrefl 0), ite_eq_left rfl]

end Spec

/-! ### The equivalence -/

/-- **`log₂` is correctly rounded.** -/
theorem log2PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2PrecRound x p mode = liftVal Spec.log2 x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [log2PrecRound]
  | zero => simp [log2PrecRound]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hv0 := finiteVal_true_pos e hv
      simp only [log2PrecRound, toVal_finite, Option.bind_some, Spec.log2_coe _ hv0]
      split_ifs with hp h2
      · exact absurd hp (NeZero.ne p)
      · -- an exact power of two
        rw [setPrecRound_eq_roundVal (toVal_ofAzInt _), finiteVal_true_of_isPowerOfTwo e m h2,
          logb_two_zpow, AzInt.toInt_sub]
        rfl
      · rw [← Real.log_div_log]
        exact zivLoopCertified_eq_threshold p mode _
          (Real.log (finiteVal true e m) / Real.log 2) _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              log2Approx_spec (w := w) (by unfold zivGuardBits at hw; omega) e hv
                (Bool.eq_false_iff.mpr h2)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    | false =>
      simp only [log2PrecRound, toVal_finite]
      rw [finiteVal_false, Option.bind_some,
        Spec.log2_coe_neg _ (neg_neg_iff_pos.mpr (finiteVal_true_pos e hv)), roundVal_none]

end Azurite.AzFloat
