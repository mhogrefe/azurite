/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.WrightOmega
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: the Wright `ω` function on the real line

`Spec.wrightOmega : EReal → Option EReal` is the exact function on the extended reals
(`ω(+∞) = +∞`, `ω(−∞) = 0`), and `wrightOmegaPrecRound_eq` (floats),
`wrightOmegaRatPrecRound_eq` (rationals) say that the drivers are its correct roundings in
every mode, with the exact comparison and without fuel.  The Ziv loop `wrightOmegaLoop` is
proven once for any enclosed rational target other than `1` (`wrightOmegaLoop_eq`).
-/

open Real Azurite.DLMF Azurite.WrightOmega

namespace Azurite.AzFloat

namespace Spec

/-- `ω` on the extended reals: `+∞ ↦ +∞`, `−∞ ↦ 0`. -/
noncomputable def wrightOmega (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then some 0
  else some ((wrightOmegaReal a.toReal : ℝ) : EReal)

theorem wrightOmega_top : wrightOmega ⊤ = some ⊤ := by simp [wrightOmega]

theorem wrightOmega_bot : wrightOmega ⊥ = some 0 := by
  unfold wrightOmega
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

theorem wrightOmega_coe (xv : ℝ) :
    wrightOmega (xv : EReal) = some ((wrightOmegaReal xv : ℝ) : EReal) := by
  unfold wrightOmega
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe]

end Spec

/-- `wrightOmegaLoop` is the correct rounding of `ω(x)` for a rational target `x ≠ 1`. -/
theorem wrightOmegaLoop_eq (xAt eAt : ℕ → AzFloat × AzFloat) (h : OmegaTarget xAt eAt) {xv : ℝ}
    (hX : XEncl xAt xv) (hE : XEncl eAt (Real.exp xv)) (hrat : ∃ r : ℚ, xv = r) (h1 : xv ≠ 1)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    wrightOmegaLoop xAt eAt h p mode
      = roundVal p mode (some ((wrightOmegaReal xv : ℝ) : EReal)) := by
  obtain ⟨r, hr⟩ := hrat
  obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Pos_spec hE (Real.exp_pos xv) (le_refl 64)
  have hirr : Irrational (wrightOmegaReal xv) := by
    rw [hr]
    exact irrational_wrightOmegaReal (by rintro rfl; exact h1 (by rw [hr, Rat.cast_one]))
  unfold wrightOmegaLoop
  exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
    (by unfold zivGuardBits; omega)
    (fun w _ => by
      obtain ⟨lv, hv', k1, k2, k3, k4, -⟩ := wrightApprox_spec hX hE ha₀ hb₀ haW hWb
        (omegaSideCert h) w
      exact ⟨lv, hv', k1, k2, k3, k4⟩) _

/-- **`ω` is correctly rounded.** -/
theorem wrightOmegaPrecRound_eq (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    wrightOmegaPrecRound x p mode = liftVal Spec.wrightOmega x p mode := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => simp [wrightOmegaPrecRound, toVal_nan]
  | infinity s =>
    cases s
    · simp only [wrightOmegaPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.wrightOmega_bot, roundVal_zero]
    · simp only [wrightOmegaPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.wrightOmega_top, roundVal_top]
  | zero =>
    simp only [wrightOmegaPrecRound, toVal_zero, Option.bind_some, dite_eq_right hp]
    rw [← EReal.coe_zero, Spec.wrightOmega_coe]
    exact wrightOmegaLoop_eq _ _ _ (floatAt_encl toVal_zero') (expAt_encl toVal_zero')
      ⟨0, by rw [Rat.cast_zero]⟩ zero_ne_one p mode
  | finite s e q m hv =>
    simp only [wrightOmegaPrecRound, toVal_finite, Option.bind_some, dite_eq_right hp,
      Spec.wrightOmega_coe]
    by_cases h1 : isOne (finite s e q m hv) = true
    · rw [dite_eq_left h1, (isOne_iff (toVal_finite s e q m hv)).mp h1, wrightOmegaReal_one,
        setPrecRound_eq_roundVal toVal_one']
    · rw [dite_eq_right h1]
      split
      · next r hT =>
        have hnx : (-(finite s e q m hv)).toVal = some ((-finiteVal s e m : ℝ) : EReal) := by
          rw [toVal_neg, toVal_finite, Option.map_some, EReal.coe_neg]
        have hR := rounds_setPrecRound (isFinite_of_toVal_coe hnx)
        rw [fval_of_toVal_coe hnx] at hR
        exact wrightOmegaHuge?_eq hR hnx le_rfl (toVal_finite s e q m hv) le_rfl
          (lt_of_le_of_lt (le_abs_self _) (abs_finiteVal_bounds s e hv).2) hT
      · exact wrightOmegaLoop_eq _ _ _ (floatAt_encl (toVal_finite s e q m hv))
          (expAt_encl (toVal_finite s e q m hv)) (finiteVal_rat s e hv)
          (fun h => h1 ((isOne_iff (toVal_finite s e q m hv)).mpr h)) p mode

/-- **`ω` of a rational is correctly rounded.** -/
theorem wrightOmegaRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    wrightOmegaRatPrecRound q p mode
      = roundVal p mode (Spec.wrightOmega (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold wrightOmegaRatPrecRound
  rw [dite_eq_right hp, Spec.wrightOmega_coe]
  by_cases h1 : q.sign = true ∧ q.num = q.den
  · have hq : ((AzRat.toRat q : ℚ) : ℝ) = 1 := by
      have := (coe_toRat_eq_one_iff q).mpr h1
      rwa [← EReal.coe_one, EReal.coe_eq_coe_iff] at this
    rw [dite_eq_left h1, hq, wrightOmegaReal_one, setPrecRound_eq_roundVal toVal_one']
  · rw [dite_eq_right h1]
    have hne : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1 := fun h =>
      h1 ((coe_toRat_eq_one_iff q).mp (by rw [h, EReal.coe_one]))
    split
    · next r hT =>
      have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
      have hneg : ((AzRat.toRat (-q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) := by
        rw [AzRat.toRat_neg]; push_cast; rfl
      have hR : Rounds (fun P M => ofAzRatRound (-q) P M) (-((AzRat.toRat q : ℚ) : ℝ)) := by
        intro P _ M
        show ofAzRatRound (-q) P M = _
        rw [ofAzRatRound_eq_roundVal, hneg]
      obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs (-q) (p + zivGuardBits + 8)
      rw [hneg] at hc1
      obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q 64
      refine wrightOmegaHuge?_eq hR hc hc1 hl hl1
        (lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le (abs_toRat_lt_two_zpow q) ?_))
        (eq_some_of_guardedBy hT)
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    · exact wrightOmegaLoop_eq _ _ _ (ratAt_encl q) (expRatAt_encl q) ⟨_, rfl⟩ hne p mode

end Azurite.AzFloat
