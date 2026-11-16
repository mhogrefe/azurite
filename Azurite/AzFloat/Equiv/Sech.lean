/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sech
import Azurite.AzFloat.SechRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `sech x` and `sech q`

`Spec.sech a = 1 / cosh a` (`0` at `±∞`),
`sechPrecRound_eq_liftVal : sechPrecRound x p mode = liftVal Spec.sech x p mode` and
`sechRatPrecRound_eq : sechRatPrecRound q p mode = roundVal p mode (Spec.sech q)`, for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `sech`: `±∞ ↦ 0`. -/
noncomputable def sech (a : EReal) : Option EReal :=
  some (if a = ⊤ ∨ a = ⊥ then ((0 : ℝ) : EReal) else (((Real.cosh a.toReal)⁻¹ : ℝ) : EReal))

theorem sech_coe (r : ℝ) : sech (r : EReal) = some (((Real.cosh r)⁻¹ : ℝ) : EReal) := by
  unfold sech
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem sech_top : sech ⊤ = some ((0 : ℝ) : EReal) := by
  unfold sech
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem sech_bot : sech ⊥ = some ((0 : ℝ) : EReal) := by
  unfold sech
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`sech` is correctly rounded.** -/
theorem sechPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sechPrecRound x p mode = liftVal Spec.sech x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [sechPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.sech_top, Spec.sech_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [sechPrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.sech_coe, Real.cosh_zero, inv_one,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [sechPrecRound, toVal_finite, Option.bind_some, Spec.sech_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx0 := finiteVal_ne_zero s e hv
    split
    · next r hT => exact sechTiny_eq hx0 (abs_finiteVal_bounds s e hv).2 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_sech_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := sechApprox_spec (toVal_finite s e q m hv)
          (abs_finiteVal_bounds s e hv).2 (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`sech q` is correctly rounded.** -/
theorem sechRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sechRatPrecRound q p mode
      = roundVal p mode (Spec.sech (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold sechRatPrecRound
  rw [Spec.sech_coe, dite_eq_right hp]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.cosh_zero, inv_one,
      setPrecRound_eq_roundVal toVal_one']
  · rw [dite_eq_right h0]
    split
    · next r hT => exact sechRatTiny_eq q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_sech_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          sechRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
