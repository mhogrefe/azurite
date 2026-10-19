/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln

/-!
# Equivalence: the natural logarithm

* `Spec.log`: the extended-real logarithm (`NaN` on negatives and `−∞`, `log 0 = −∞`,
  `log ∞ = ∞`).
* `lnPrecRound_eq_liftVal : lnPrecRound x p mode = liftVal Spec.log x p mode`: `ln` is correctly
  rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real logarithm: undefined (`NaN`) on negatives (including `−∞`), `log 0 = −∞`,
`log ∞ = ∞`. -/
noncomputable def log (a : EReal) : Option EReal :=
  if a < 0 then none else if a = 0 then some ⊥ else if a = ⊤ then some ⊤
  else some ((Real.log a.toReal : ℝ) : EReal)

theorem log_coe (r : ℝ) (hr : 0 < r) : log (r : EReal) = some ((Real.log r : ℝ) : EReal) := by
  unfold log
  rw [ite_eq_right (not_lt.mpr (EReal.coe_nonneg.mpr hr.le)),
    ite_eq_right (mt EReal.coe_eq_zero.mp hr.ne'), ite_eq_right (EReal.coe_ne_top r),
    EReal.toReal_coe]

theorem log_coe_neg (r : ℝ) (hr : r < 0) : log (r : EReal) = none := by
  unfold log
  rw [ite_eq_left (EReal.coe_neg'.mpr hr)]

@[simp] theorem log_top : log ⊤ = some ⊤ := by
  unfold log
  rw [ite_eq_right (not_lt.mpr le_top), ite_eq_right (EReal.zero_ne_top).symm, ite_eq_left rfl]

@[simp] theorem log_bot : log ⊥ = none := by
  unfold log
  rw [ite_eq_left EReal.bot_lt_zero]

@[simp] theorem log_zero : log 0 = some ⊥ := by
  unfold log
  rw [ite_eq_right (lt_irrefl 0), ite_eq_left rfl]

end Spec

/-! ### The equivalence -/

/-- **`ln` is correctly rounded.** -/
theorem lnPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnPrecRound x p mode = liftVal Spec.log x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [lnPrecRound]
  | zero => simp [lnPrecRound]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hv0 := finiteVal_true_pos e hv
      simp only [lnPrecRound, toVal_finite, Option.bind_some, Spec.log_coe _ hv0]
      split_ifs with h1 hp
      · obtain ⟨v, hx, h1v⟩ := (eqIEEE_iff _ _).mp h1
        rw [toVal_finite] at hx
        rw [toVal_one', ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1v
        rw [← h1v, Real.log_one, EReal.coe_zero, roundVal_zero]
      · exact absurd hp (NeZero.ne p)
      · exact zivLoopCertified_eq_threshold p mode _ (Real.log (finiteVal true e m)) _
          (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              lnApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) e hv
                (finiteVal_ne_one_of_not_eqIEEE e hv h1)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    | false =>
      simp only [lnPrecRound, toVal_finite]
      rw [finiteVal_false, Option.bind_some,
        Spec.log_coe_neg _ (neg_neg_iff_pos.mpr (finiteVal_true_pos e hv)), roundVal_none]

end Azurite.AzFloat
