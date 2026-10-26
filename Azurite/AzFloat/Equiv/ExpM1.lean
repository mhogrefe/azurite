/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpM1
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: `exp x − 1`

* `Spec.expM1`: the extended-real `exp a − 1` (`∞ ↦ ∞`, `−∞ ↦ −1`).
* `expM1PrecRound_eq_liftVal : expM1PrecRound x p mode = liftVal Spec.expM1 x p mode`:
  `exp x − 1` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `exp a − 1`: `∞ ↦ ∞`, `−∞ ↦ −1`. -/
noncomputable def expM1 (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then some ((-1 : ℝ) : EReal)
  else some ((Real.exp a.toReal - 1 : ℝ) : EReal)

theorem expM1_coe (r : ℝ) : expM1 (r : EReal) = some ((Real.exp r - 1 : ℝ) : EReal) := by
  unfold expM1
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem expM1_top : expM1 ⊤ = some ⊤ := by
  unfold expM1
  rw [ite_eq_left rfl]

@[simp] theorem expM1_bot : expM1 ⊥ = some ((-1 : ℝ) : EReal) := by
  unfold expM1
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **`exp x − 1` is correctly rounded.** -/
theorem expM1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    expM1PrecRound x p mode = liftVal Spec.expM1 x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [expM1PrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.expM1_bot]
      have h1 : (-one).toVal = some ((-1 : ℝ) : EReal) := by
        rw [toVal_neg, toVal_one', Option.map_some, EReal.coe_neg]
      rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal h1]
    · simp [expM1PrecRound]
  | zero =>
    simp only [expM1PrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.expM1_coe, Real.exp_zero, sub_self, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [expM1PrecRound, toVal_finite, Option.bind_some, Spec.expM1_coe]
    rw [dite_eq_right (NeZero.ne p)]
    exact zivLoopCertified_eq_threshold p mode _ (Real.exp (finiteVal s e m) - 1) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          expM1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega) s e hv
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
