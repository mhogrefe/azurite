/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cosh
import Azurite.AzFloat.CoshRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `cosh x` and `cosh q`

`Spec.cosh a = cosh a` (`+∞` at `±∞`),
`coshPrecRound_eq_liftVal : coshPrecRound x p mode = liftVal Spec.cosh x p mode` and
`coshRatPrecRound_eq : coshRatPrecRound q p mode = roundVal p mode (Spec.cosh q)`, for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `cosh`: `±∞ ↦ +∞`. -/
noncomputable def cosh (a : EReal) : Option EReal :=
  some (if a = ⊤ ∨ a = ⊥ then ⊤ else ((Real.cosh a.toReal : ℝ) : EReal))

theorem cosh_coe (r : ℝ) : cosh (r : EReal) = some ((Real.cosh r : ℝ) : EReal) := by
  unfold cosh
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem cosh_top : cosh ⊤ = some ⊤ := by
  unfold cosh
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cosh_bot : cosh ⊥ = some ⊤ := by
  unfold cosh
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`cosh` is correctly rounded.** -/
theorem coshPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    coshPrecRound x p mode = liftVal Spec.cosh x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [coshPrecRound]
  | zero =>
    simp only [coshPrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.cosh_coe, Real.cosh_zero,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [coshPrecRound, toVal_finite, Option.bind_some, Spec.cosh_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx0 := finiteVal_ne_zero s e hv
    split
    · next r hT => exact coshTiny_eq hx0 (abs_finiteVal_bounds s e hv).2 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_cosh_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := coshApprox_spec (toVal_finite s e q m hv)
          (abs_finiteVal_bounds s e hv).2 (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`cosh q` is correctly rounded.** -/
theorem coshRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    coshRatPrecRound q p mode
      = roundVal p mode (Spec.cosh (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold coshRatPrecRound
  rw [Spec.cosh_coe, dite_eq_right hp]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.cosh_zero,
      setPrecRound_eq_roundVal toVal_one']
  · rw [dite_eq_right h0]
    split
    · next r hT => exact coshRatTiny_eq q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_cosh_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          coshRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
