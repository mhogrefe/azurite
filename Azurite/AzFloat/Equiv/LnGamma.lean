/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Equiv.LnGammaBracket
import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzFloat.Equiv.Pow

/-!
# Equivalence: `ln Γ`

`Spec.lnGamma` on the extended reals (`+∞` at `0` and `+∞`, `NaN` below `0`, `ln Γ(x)` for
`x > 0`); `lnGammaApprox_spec` (the bracket, strict at the lower end); and
`lnGammaPrecRound_eq_or`: `lnGammaPrecRound x p mode` is the correctly rounded value
(`liftVal Spec.lnGamma`) unless the fuel runs out (`(nan, .eq)`).
-/

namespace Azurite.AzFloat

namespace Spec

/-- `ln Γ` on the extended reals: `+∞` at `0` (from the right) and at `+∞`, `NaN` below `0`. -/
noncomputable def lnGamma (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a < 0 then none else if a = 0 then some ⊤
  else some ((Real.log (Real.Gamma a.toReal) : ℝ) : EReal)

theorem lnGamma_top : lnGamma ⊤ = some ⊤ := by simp [lnGamma]

theorem lnGamma_bot : lnGamma ⊥ = none := by
  unfold lnGamma
  rw [ite_eq_right bot_ne_top, ite_eq_left (by exact EReal.bot_lt_zero)]

theorem lnGamma_zero : lnGamma 0 = some ⊤ := by
  unfold lnGamma
  rw [ite_eq_right EReal.zero_ne_top, ite_eq_right (lt_irrefl _), ite_eq_left rfl]

theorem lnGamma_coe_of_neg {xv : ℝ} (h : xv < 0) : lnGamma (xv : EReal) = none := by
  unfold lnGamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_left (by exact_mod_cast h)]

theorem lnGamma_coe_of_pos {xv : ℝ} (h : 0 < xv) :
    lnGamma (xv : EReal) = some ((Real.log (Real.Gamma xv) : ℝ) : EReal) := by
  unfold lnGamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (not_lt.mpr (by exact_mod_cast h.le)),
    ite_eq_right (by exact_mod_cast h.ne'), EReal.toReal_coe]

end Spec

/-- A bracket as `Roundable`s encloses its value, strictly from below. -/
theorem lnGammaApproxOf_spec {b : Encl} {v : ℝ} (hb : IsEncl b v) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (lnGammaApproxOf b w).1 lv ∧ Rounds (lnGammaApproxOf b w).2 hv ∧
      lv < v ∧ v ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := hb
  have : NeZero (2 * w + 64) := ⟨by omega⟩
  have ht : (powerOf2 (-(AzNat.ofNat (4 * w)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (4 * w) : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
      zpow_natCast, one_div_pow, one_div]
  obtain ⟨r, hr, hrle, -⟩ := subFloor_le hlo ht (2 * w + 64)
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (4 * w) := by positivity
  refine ⟨r, hi, ?_, ?_, by linarith, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hr)
    rw [fval_of_toVal_coe hr] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- The bracket as `Roundable`s encloses `ln Γ(x)`, strictly from below. -/
theorem lnGammaApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hpos : 0 < xv) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (lnGammaApprox x e w).1 lv ∧ Rounds (lnGammaApprox x e w).2 hv ∧
      lv < Real.log (Real.Gamma xv) ∧ Real.log (Real.Gamma xv) ≤ hv :=
  lnGammaApproxOf_spec (lnGammaBracket_spec hx hpos e hw) w

/-- **`ln Γ` is correctly rounded unless the fuel runs out.** -/
theorem lnGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnGammaPrecRound x p mode = liftVal Spec.lnGamma x p mode ∨
      lnGammaPrecRound x p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [lnGammaPrecRound, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [lnGammaPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.lnGamma_bot, roundVal_none]
    · simp only [lnGammaPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.lnGamma_top, roundVal_top]
  | zero =>
    left
    simp only [lnGammaPrecRound, toVal_zero, Option.bind_some, Spec.lnGamma_zero, roundVal_top]
  | finite s e q m hv =>
    cases s with
    | false =>
      left
      simp only [lnGammaPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.lnGamma_coe_of_neg (finiteVal_false_neg e hv), roundVal_none]
    | true =>
      have hpos := finiteVal_true_pos e hv
      have hx := toVal_finite true e q m hv
      simp only [lnGammaPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.lnGamma_coe_of_pos hpos]
      split_ifs with h12
      · left
        have hval : finiteVal true e m = 1 ∨ finiteVal true e m = 2 := by
          rcases Bool.or_eq_true _ _ ▸ h12 with h | h
          · left
            rw [eqIEEE_one_iff, toVal_finite, Option.some.injEq] at h
            exact_mod_cast h
          · right
            rw [eqIEEE_iff] at h
            obtain ⟨v, h1, h2⟩ := h
            rw [toVal_ofAzNat_ofNat] at h2
            rw [toVal_finite, ← h2, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
            exact_mod_cast h1
        have h0 : Real.log (Real.Gamma (finiteVal true e m)) = 0 := by
          rcases hval with h | h <;> rw [h]
          · rw [Real.Gamma_one, Real.log_one]
          · rw [Real.Gamma_two, Real.log_one]
        rw [h0, EReal.coe_zero, roundVal_zero]
      · rcases eq_or_ne (zivLoop (lnGammaApprox (finite true e q m hv) e) p mode lnGammaFuel
          (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))) (nan, .eq)
          with hz | hz
        · right; exact hz
        · left
          exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
            (fun w hw => by
              obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ := lnGammaApprox_spec hx hpos e hw
              exact ⟨lv, hv', hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
            _ _ (le_max_left _ _) hz

end Azurite.AzFloat
