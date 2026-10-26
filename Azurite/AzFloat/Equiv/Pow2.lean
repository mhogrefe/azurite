/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Exp
import Azurite.AzFloat.Pow2

/-!
# Equivalence: `2^x`

* `Spec.pow2`: the extended-real `2^a` (`∞ ↦ ∞`, `−∞ ↦ 0`).
* `pow2PrecRound_eq_liftVal : pow2PrecRound x p mode = liftVal Spec.pow2 x p mode`: `2^x` is
  correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `2^a`: `∞ ↦ ∞`, `−∞ ↦ 0`. -/
noncomputable def pow2 (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then some 0 else some (((2 : ℝ) ^ a.toReal : ℝ) : EReal)

theorem pow2_coe (r : ℝ) : pow2 (r : EReal) = some (((2 : ℝ) ^ r : ℝ) : EReal) := by
  unfold pow2
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem pow2_top : pow2 ⊤ = some ⊤ := by
  unfold pow2
  rw [ite_eq_left rfl]

@[simp] theorem pow2_bot : pow2 ⊥ = some 0 := by
  unfold pow2
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- An integer float truncates to itself. -/
theorem truncToAzInt_of_isInteger (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hi : isInteger (finite s e q m hv) = true) :
    ((truncToAzInt (finite s e q m hv)).toInt : ℝ) = finiteVal s e m := by
  obtain ⟨n, hn⟩ := (isInteger_finite s e hv).mp hi
  obtain ⟨h1, -⟩ := truncToAzInt_spec (toVal_finite s e q m hv)
  rw [hn] at h1 ⊢
  have h2 : |(((truncToAzInt (finite s e q m hv)).toInt - n : ℤ) : ℝ)| < 1 := by
    push_cast; exact h1
  have h3 : |(truncToAzInt (finite s e q m hv)).toInt - n| < 1 := by exact_mod_cast h2
  have h4 : (truncToAzInt (finite s e q m hv)).toInt - n = 0 := Int.abs_lt_one_iff.mp h3
  have h5 : (truncToAzInt (finite s e q m hv)).toInt = n := by omega
  rw [h5]

/-- **`2^x` is correctly rounded.** -/
theorem pow2PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow2PrecRound x p mode = liftVal Spec.pow2 x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [pow2PrecRound]
  | zero =>
    simp only [pow2PrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.pow2_coe, Real.rpow_zero,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [pow2PrecRound, toVal_finite, Option.bind_some, Spec.pow2_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split_ifs with hi
    · rw [setPrecRound_eq_roundVal (toVal_powerOf2 _), ← truncToAzInt_of_isInteger s e hv hi,
        Real.rpow_intCast]
    · exact zivLoopCertified_eq_threshold p mode _ ((2 : ℝ) ^ finiteVal s e m) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
            pow2Approx_spec (w := w) (by unfold zivGuardBits at hw; omega) s e hv hi
          exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
