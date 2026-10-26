/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Pow2
import Azurite.AzFloat.Pow2M1

/-!
# Equivalence: `2^x − 1`

* `Spec.pow2M1`: the extended-real `2^a − 1` (`∞ ↦ ∞`, `−∞ ↦ −1`).
* `pow2M1PrecRound_eq_liftVal : pow2M1PrecRound x p mode = liftVal Spec.pow2M1 x p mode`:
  `2^x − 1` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `2^a − 1`: `∞ ↦ ∞`, `−∞ ↦ −1`. -/
noncomputable def pow2M1 (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then some ((-1 : ℝ) : EReal)
  else some (((2 : ℝ) ^ a.toReal - 1 : ℝ) : EReal)

theorem pow2M1_coe (r : ℝ) : pow2M1 (r : EReal) = some (((2 : ℝ) ^ r - 1 : ℝ) : EReal) := by
  unfold pow2M1
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem pow2M1_top : pow2M1 ⊤ = some ⊤ := by
  unfold pow2M1
  rw [ite_eq_left rfl]

@[simp] theorem pow2M1_bot : pow2M1 ⊥ = some ((-1 : ℝ) : EReal) := by
  unfold pow2M1
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **`2^x − 1` is correctly rounded.** -/
theorem pow2M1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow2M1PrecRound x p mode = liftVal Spec.pow2M1 x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [pow2M1PrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.pow2M1_bot]
      have h1 : (-one).toVal = some ((-1 : ℝ) : EReal) := by
        rw [toVal_neg, toVal_one', Option.map_some, EReal.coe_neg]
      rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal h1]
    · simp [pow2M1PrecRound]
  | zero =>
    simp only [pow2M1PrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.pow2M1_coe, Real.rpow_zero, sub_self, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [pow2M1PrecRound, toVal_finite, Option.bind_some, Spec.pow2M1_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split_ifs with hi
    · rw [subPrecRound_eq_liftVal₂, liftVal₂, toVal_powerOf2, toVal_one', Option.bind_some,
        Option.bind_some, Spec.sub, ← EReal.coe_neg, Spec.add_coe_coe,
        ← truncToAzInt_of_isInteger s e hv hi, Real.rpow_intCast, sub_eq_add_neg]
    · exact zivLoopCertified_eq_threshold p mode _ ((2 : ℝ) ^ finiteVal s e m - 1) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
            pow2M1Approx_spec (w := w) (by unfold zivGuardBits at hw; omega) s e hv hi
          exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
