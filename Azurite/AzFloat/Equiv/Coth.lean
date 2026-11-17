/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Coth
import Azurite.AzFloat.CothRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `coth x` and `coth q`

`Spec.coth a = 1 / tanh a` (`±1` at `±∞`, `+∞` at `0`),
`cothPrecRound_eq_liftVal : cothPrecRound x p mode = liftVal Spec.coth x p mode` and
`cothRatPrecRound_eq : cothRatPrecRound q p mode = roundVal p mode (Spec.coth q)`, for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `coth`: `±∞ ↦ ±1`, `0 ↦ +∞` (there is one zero only). -/
noncomputable def coth (a : EReal) : Option EReal :=
  some (if a = ⊤ then ((1 : ℝ) : EReal) else if a = ⊥ then ((-1 : ℝ) : EReal)
    else if a.toReal = 0 then ⊤ else (((Real.tanh a.toReal)⁻¹ : ℝ) : EReal))

theorem coth_coe {r : ℝ} (hr : r ≠ 0) :
    coth (r : EReal) = some (((Real.tanh r)⁻¹ : ℝ) : EReal) := by
  unfold coth
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe,
    ite_eq_right hr]

theorem coth_zero : coth ((0 : ℝ) : EReal) = some ⊤ := by
  unfold coth
  rw [ite_eq_right (EReal.coe_ne_top 0), ite_eq_right (EReal.coe_ne_bot 0), EReal.toReal_coe,
    ite_eq_left rfl]

@[simp] theorem coth_top : coth ⊤ = some ((1 : ℝ) : EReal) := by
  unfold coth
  rw [ite_eq_left rfl]

@[simp] theorem coth_bot : coth ⊥ = some ((-1 : ℝ) : EReal) := by
  unfold coth
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **`coth` is correctly rounded.** -/
theorem cothPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cothPrecRound x p mode = liftVal Spec.coth x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [cothPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.coth_bot]
      rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal toVal_neg_one_float]
    · simp only [cothPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some, Spec.coth_top]
      rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal toVal_one']
  | zero =>
    simp only [cothPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.coth_zero, roundVal_top]
  | finite s e q m hv =>
    have hx0 := finiteVal_ne_zero s e hv
    simp only [cothPrecRound, toVal_finite, Option.bind_some]
    rw [Spec.coth_coe hx0, dite_eq_right (NeZero.ne p)]
    split
    · next r hT => exact cothTiny?_eq hv p mode hT
    split
    · next r hT =>
      rw [cothNearOne?_eq (tanhFloatN_le (toVal_finite s e q m hv)
          (abs_finiteVal_bounds s e hv).1) hT,
        coth_sign_eq (finiteVal_sign_iff s e hv) hx0]
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_coth_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := cothApprox_spec (toVal_finite s e q m hv) hx0
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (w := w)
          (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`coth q` is correctly rounded.** -/
theorem cothRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cothRatPrecRound q p mode
      = roundVal p mode (Spec.coth (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold cothRatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.coth_zero, roundVal_top]
  · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
    rw [dite_eq_right h0, dite_eq_right hp, Spec.coth_coe hq0]
    split
    · next r hT => exact cothTinyRat?_eq q h0 hT
    split
    · next r hT =>
      rw [cothNearOne?_eq (tanhRatN_le q) hT, coth_sign_eq (toRat_sign_iff q h0) hq0]
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_coth_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          cothRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
