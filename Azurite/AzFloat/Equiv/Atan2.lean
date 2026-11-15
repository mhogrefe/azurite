/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2
import Azurite.AzFloat.Equiv.Atan
import Azurite.AzFloat.Equiv.PiConstants

/-!
# Equivalence: `atan2 (y, x)`

`Spec.atan2 : EReal → EReal → Option EReal` — `Complex.arg (x + iy)` for real arguments, and the
IEEE 754 table at the infinities (`±π/4`, `±3π/4`, `±π/2`, `0`, `±π`) —
`piThreeQuartersPrecRound_eq_liftVal₀`, `signedRound_eq`, and
`atan2PrecRound_eq_liftVal₂ : atan2PrecRound y x p mode = liftVal₂ Spec.atan2 y x p mode` for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `atan2 (y, x)`: the argument of `x + iy` for real `y`, `x`, in `(−π, π]`; at
the infinities `±π/4` (`x = +∞`), `±3π/4` (`x = −∞`) and `±π/2` (finite `x`) for `y = ±∞`, and
`0` (`x = +∞`), `±π` (`x = −∞`, the sign of `y`, `π` for `y = 0`) for a finite `y`. -/
noncomputable def atan2 (y x : EReal) : Option EReal :=
  some (
    if y = ⊤ then
      (if x = ⊤ then ((π / 4 : ℝ) : EReal) else if x = ⊥ then ((3 * π / 4 : ℝ) : EReal)
        else ((π / 2 : ℝ) : EReal))
    else if y = ⊥ then
      (if x = ⊤ then ((-(π / 4) : ℝ) : EReal) else if x = ⊥ then ((-(3 * π / 4) : ℝ) : EReal)
        else ((-(π / 2) : ℝ) : EReal))
    else if x = ⊤ then ((0 : ℝ) : EReal)
    else if x = ⊥ then (if y.toReal < 0 then ((-π : ℝ) : EReal) else ((π : ℝ) : EReal))
    else ((Complex.arg ⟨x.toReal, y.toReal⟩ : ℝ) : EReal))

theorem atan2_coe_coe (b a : ℝ) :
    atan2 (b : EReal) (a : EReal) = some ((Complex.arg ⟨a, b⟩ : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_coe_top (b : ℝ) : atan2 (b : EReal) ⊤ = some ((0 : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_coe_bot (b : ℝ) :
    atan2 (b : EReal) ⊥ = some (if b < 0 then ((-π : ℝ) : EReal) else ((π : ℝ) : EReal)) := by
  unfold atan2
  rw [ite_eq_right (EReal.coe_ne_top b), ite_eq_right (EReal.coe_ne_bot b),
    ite_eq_right (by simp : ¬ (⊥ : EReal) = ⊤), ite_eq_left rfl]
  by_cases h : b < 0
  · rw [ite_eq_left h, ite_eq_left (by rwa [EReal.toReal_coe] : (b : EReal).toReal < 0)]
  · rw [ite_eq_right h, ite_eq_right (by rwa [EReal.toReal_coe] : ¬ (b : EReal).toReal < 0)]

theorem atan2_top_top : atan2 ⊤ ⊤ = some ((π / 4 : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_top_bot : atan2 ⊤ ⊥ = some ((3 * π / 4 : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_top_coe (a : ℝ) : atan2 ⊤ (a : EReal) = some ((π / 2 : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_bot_top : atan2 ⊥ ⊤ = some ((-(π / 4) : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_bot_bot : atan2 ⊥ ⊥ = some ((-(3 * π / 4) : ℝ) : EReal) := by
  unfold atan2
  simp

theorem atan2_bot_coe (a : ℝ) : atan2 ⊥ (a : EReal) = some ((-(π / 2) : ℝ) : EReal) := by
  unfold atan2
  simp

end Spec

/-- `3π/4` is correctly rounded. -/
theorem piThreeQuartersPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piThreeQuartersPrecRound p mode = liftVal₀ (some ((3 * π / 4 : ℝ) : EReal)) p mode := by
  unfold piThreeQuartersPrecRound liftVal₀
  rw [dite_eq_right (NeZero.ne p)]
  exact zivLoopCertified_eq_threshold' p mode _ (3 * π / 4)
    (not_mem_floatSet_of_irrational p irrational_three_pi_div_four) _
    (by unfold zivGuardBits; omega)
    (fun w _ => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := piThreeQuartersApprox_spec w
      exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- A signed constant is correctly rounded. -/
theorem signedRound_eq {c : Nat → RoundingMode → AzFloat × Ordering} {v : ℝ}
    (hc : ∀ (p : ℕ) [NeZero p] (mode : RoundingMode),
      c p mode = liftVal₀ (some (v : EReal)) p mode)
    (pos : Bool) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    signedRound pos c p mode
      = roundVal p mode (some (((if pos then v else -v : ℝ)) : EReal)) := by
  unfold signedRound
  cases pos with
  | true =>
    simp only [↓reduceIte]
    rw [hc p mode]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [roundVal_neg, hc p (-mode)]
    rfl

/-- The angle of a point of the imaginary axis. -/
theorem arg_zero_re {y : ℝ} (hy : y ≠ 0) :
    Complex.arg ⟨0, y⟩ = if 0 < y then π / 2 else -(π / 2) := by
  rcases lt_or_gt_of_ne hy with h | h
  · rw [ite_eq_right (not_lt.mpr h.le)]
    have e : (⟨0, y⟩ : ℂ) = ((-y : ℝ) : ℂ) * (-Complex.I) := by
      apply Complex.ext <;> simp
    rw [e, Complex.arg_real_mul _ (neg_pos.mpr h), Complex.arg_neg_I]
  · rw [ite_eq_left h]
    have e : (⟨0, y⟩ : ℂ) = ((y : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e, Complex.arg_real_mul _ h, Complex.arg_I]

/-- **`atan2 (y, x)` is correctly rounded.** -/
theorem atan2PrecRound_eq_liftVal₂ (y x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atan2PrecRound y x p mode = liftVal₂ Spec.atan2 y x p mode := by
  unfold liftVal₂
  have hp := NeZero.ne p
  have hpi := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piPrecRound_eq_liftVal₀ p m
  have hpi2 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv2PrecRound_eq_liftVal₀ p m
  have hpi4 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv4PrecRound_eq_liftVal₀ p m
  have hpi34 := fun (p : ℕ) [NeZero p] (m : RoundingMode) =>
    piThreeQuartersPrecRound_eq_liftVal₀ p m
  cases y with
  | nan => rfl
  | zero =>
    cases x with
    | nan => rfl
    | zero =>
      simp only [atan2PrecRound, toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.atan2_coe_coe]
      have h : Complex.arg ⟨0, 0⟩ = 0 := Complex.arg_zero
      rw [h, EReal.coe_zero, roundVal_zero]
    | infinity sx =>
      cases sx with
      | true =>
        simp only [atan2PrecRound, toVal_zero, toVal_infinity, Option.bind_some, ↓reduceIte]
        rw [← EReal.coe_zero, Spec.atan2_coe_top, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [atan2PrecRound, toVal_zero, toVal_infinity, Option.bind_some,
          Bool.false_eq_true, ↓reduceIte]
        rw [← EReal.coe_zero, Spec.atan2_coe_bot, ite_eq_right (lt_irrefl 0),
          piPrecRound_eq_liftVal₀]
        rfl
    | finite sx ex qx mx hvx =>
      simp only [atan2PrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.atan2_coe_coe]
      have hs := finiteVal_sign_iff sx ex hvx
      have hx0 := finiteVal_ne_zero sx ex hvx
      cases sx with
      | true =>
        have h : Complex.arg ⟨finiteVal true ex mx, 0⟩ = 0 :=
          Complex.arg_ofReal_of_nonneg (hs.mp rfl).le
        simp only [↓reduceIte]
        rw [h, EReal.coe_zero, roundVal_zero]
      | false =>
        have hneg : finiteVal false ex mx < 0 := by
          rcases lt_or_gt_of_ne hx0 with h | h
          · exact h
          · exact absurd (hs.mpr h) (by simp)
        have h : Complex.arg ⟨finiteVal false ex mx, 0⟩ = π := Complex.arg_ofReal_of_neg hneg
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h, piPrecRound_eq_liftVal₀]
        rfl
  | infinity sy =>
    cases x with
    | nan => cases sy <;> rfl
    | zero =>
      simp only [atan2PrecRound, toVal_zero, toVal_infinity, Option.bind_some]
      rw [signedRound_eq hpi2, ← EReal.coe_zero]
      cases sy with
      | true => simp only [↓reduceIte, Spec.atan2_top_coe]
      | false => simp only [Bool.false_eq_true, ↓reduceIte, Spec.atan2_bot_coe]
    | infinity sx =>
      simp only [atan2PrecRound, toVal_infinity, Option.bind_some]
      cases sx with
      | true =>
        simp only [↓reduceIte]
        rw [signedRound_eq hpi4]
        cases sy with
        | true => simp only [↓reduceIte, Spec.atan2_top_top]
        | false => simp only [Bool.false_eq_true, ↓reduceIte, Spec.atan2_bot_top]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [signedRound_eq hpi34]
        cases sy with
        | true => simp only [↓reduceIte, Spec.atan2_top_bot]
        | false => simp only [Bool.false_eq_true, ↓reduceIte, Spec.atan2_bot_bot]
    | finite sx ex qx mx hvx =>
      simp only [atan2PrecRound, toVal_finite, toVal_infinity, Option.bind_some]
      rw [signedRound_eq hpi2]
      cases sy with
      | true => simp only [↓reduceIte, Spec.atan2_top_coe]
      | false => simp only [Bool.false_eq_true, ↓reduceIte, Spec.atan2_bot_coe]
  | finite sy ey qy my hvy =>
    have hsy := finiteVal_sign_iff sy ey hvy
    have hy0 := finiteVal_ne_zero sy ey hvy
    have hneg := finiteVal_neg_iff sy ey hvy
    cases x with
    | nan => rfl
    | zero =>
      simp only [atan2PrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [signedRound_eq hpi2, ← EReal.coe_zero, Spec.atan2_coe_coe, arg_zero_re hy0]
      cases sy with
      | true => rw [ite_eq_left (hsy.mp rfl)]; rfl
      | false =>
        rw [ite_eq_right (not_lt.mpr (hneg.mp rfl).le)]
        rfl
    | infinity sx =>
      cases sx with
      | true =>
        simp only [atan2PrecRound, toVal_finite, toVal_infinity, Option.bind_some, ↓reduceIte]
        rw [Spec.atan2_coe_top, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [atan2PrecRound, toVal_finite, toVal_infinity, Option.bind_some,
          Bool.false_eq_true, ↓reduceIte]
        rw [signedRound_eq hpi, Spec.atan2_coe_bot]
        cases sy with
        | true => rw [ite_eq_right (not_lt.mpr (hsy.mp rfl).le)]; rfl
        | false => rw [ite_eq_left (hneg.mp rfl)]; rfl
    | finite sx ex qx mx hvx =>
      simp only [atan2PrecRound, toVal_finite, Option.bind_some, Spec.atan2_coe_coe]
      rw [dite_eq_right hp]
      have hx0 := finiteVal_ne_zero sx ex hvx
      have hxpos := finiteVal_sign_iff sx ex hvx
      have hval := arg_eq_atan2Abs hx0 hy0 hneg hxpos
      have hirr := irrational_atan2Abs_of_toVal (toVal_finite sy ey qy my hvy)
        (toVal_finite sx ex qx mx hvx) hy0 hx0 hxpos
      have key : ∀ m : RoundingMode,
          zivLoopCertified
            (atan2Approx true (finite sy ey qy my hvy) (finite sx ex qx mx hvx) ey ex sx) p m
            (p + zivGuardBits)
            (atan2Approx_isSome_exists p m true (toVal_finite sy ey qy my hvy)
              (toVal_finite sx ex qx mx hvx) hy0 hx0 hxpos (abs_finiteVal_bounds sy ey hvy).2
              (abs_finiteVal_bounds sx ex hvx).1 (p + zivGuardBits)
              (by unfold zivGuardBits; omega))
          = roundVal p m (some ((-atan2Abs |finiteVal sy ey my| |finiteVal sx ex mx| sx : ℝ)
            : EReal)) := fun m =>
        zivLoopCertified_eq_threshold' p m _ _
          (not_mem_floatSet_of_irrational p hirr.neg) _ (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := atan2Approx_spec true
              (toVal_finite sy ey qy my hvy) (toVal_finite sx ex qx mx hvx) hy0 hx0
              (abs_finiteVal_bounds sy ey hvy).2 (abs_finiteVal_bounds sx ex hvx).1 sx w
            simp only [↓reduceIte, neg_one_mul] at hlo hhi
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
      cases sy with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [key mode, hval]
        simp
      | true =>
        simp only [↓reduceIte]
        rw [key (-mode), hval]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [← roundVal_neg, neg_neg]

end Azurite.AzFloat
