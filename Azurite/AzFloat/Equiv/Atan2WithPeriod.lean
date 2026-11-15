/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriod
import Azurite.AzFloat.Equiv.Atan2

/-!
# Equivalence: `atan2 (y, x) u / (2π)`

`Spec.atan2WithPeriod y x u = (Spec.atan2 y x) · u / (2π)` (so `±u/8`, `±3u/8`, `±u/4`, `0`,
`±u/2` at the infinities), `toVal_turnFracN`, `turnFracN_round_pos`, `turnFracN_round_neg`, and
`atan2WithPeriodPrecRound_eq :
  atan2WithPeriodPrecRound y x u p mode
    = roundVal p mode (y.toVal.bind fun a => x.toVal.bind fun b => Spec.atan2WithPeriod a b u)`
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `atan2 (y, x) u / (2π)`: the angle `Spec.atan2 y x` in `u`ths of a turn. -/
noncomputable def atan2WithPeriod (y x : EReal) (u : ℕ) : Option EReal :=
  (atan2 y x).map fun θ => ((θ.toReal * u / (2 * π) : ℝ) : EReal)

theorem atan2WithPeriod_of {y x : EReal} {θ : ℝ} (h : atan2 y x = some ((θ : ℝ) : EReal))
    (u : ℕ) : atan2WithPeriod y x u = some ((θ * u / (2 * π) : ℝ) : EReal) := by
  unfold atan2WithPeriod
  rw [h, Option.map_some, EReal.toReal_coe]

end Spec

/-- The value of `turnFracN`: `± n u / 2^k`. -/
theorem toVal_turnFracN (pos : Bool) (n : ℕ) (u : UInt64) (k : ℕ) :
    (turnFracN pos n u k).toVal
      = some (((if pos then 1 else -1) * ((n : ℝ) * u.toNat / 2 ^ k) : ℝ) : EReal) := by
  have h : (ofAzNat (AzNat.ofNat (n * u.toNat)) <<< AzInt.ofInt (-(k : Int))).toVal
      = some (((n : ℝ) * u.toNat / 2 ^ k : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat (AzNat.ofNat (n * u.toNat)))
      (AzInt.ofInt (-(k : Int)))
    rw [h, AzNat.toNat_ofNat, AzInt.toInt_ofInt, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    push_cast
    rfl
  unfold turnFracN
  cases pos with
  | true => simp only [↓reduceIte, one_mul]; exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [toVal_neg, h, Option.map_some, EReal.coe_neg]

/-- A positive rational fraction of a turn is returned correctly rounded. -/
theorem turnFracN_round_pos (n : ℕ) (u : UInt64) (k : ℕ) (p : ℕ) [NeZero p]
    (mode : RoundingMode) {θ : ℝ} (h : θ * u.toNat / (2 * π) = (n : ℝ) * u.toNat / 2 ^ k) :
    setPrecRound (turnFracN true n u k) p mode
      = roundVal p mode (some ((θ * u.toNat / (2 * π) : ℝ) : EReal)) := by
  rw [h, setPrecRound_eq_roundVal (toVal_turnFracN true n u k) p mode]
  simp only [↓reduceIte, one_mul]

/-- A negative rational fraction of a turn is returned correctly rounded. -/
theorem turnFracN_round_neg (n : ℕ) (u : UInt64) (k : ℕ) (p : ℕ) [NeZero p]
    (mode : RoundingMode) {θ : ℝ} (h : θ * u.toNat / (2 * π) = -((n : ℝ) * u.toNat / 2 ^ k)) :
    setPrecRound (turnFracN false n u k) p mode
      = roundVal p mode (some ((θ * u.toNat / (2 * π) : ℝ) : EReal)) := by
  rw [h, setPrecRound_eq_roundVal (toVal_turnFracN false n u k) p mode]
  simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]

/-- **`atan2 (y, x) u / (2π)` is correctly rounded.** -/
theorem atan2WithPeriodPrecRound_eq (y x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    atan2WithPeriodPrecRound y x u p mode
      = roundVal p mode
        (y.toVal.bind fun a => x.toVal.bind fun b => Spec.atan2WithPeriod a b u.toNat) := by
  have hp := NeZero.ne p
  have hpi0 : π ≠ 0 := pi_ne_zero
  have hzero : ∀ {θ : ℝ}, θ = 0 →
      ((zero, Ordering.eq) : AzFloat × Ordering)
        = roundVal p mode (some ((θ * u.toNat / (2 * π) : ℝ) : EReal)) := fun h => by
    rw [h, zero_mul, zero_div, EReal.coe_zero, roundVal_zero]
  have hbot0 : Spec.atan2 ((0 : ℝ) : EReal) ⊥ = some ((π : ℝ) : EReal) := by
    rw [Spec.atan2_coe_bot, ite_eq_right (lt_irrefl 0)]
  cases y with
  | nan => rfl
  | zero =>
    cases x with
    | nan => rfl
    | zero =>
      simp only [atan2WithPeriodPrecRound, toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.atan2WithPeriod_of (Spec.atan2_coe_coe 0 0)]
      exact hzero Complex.arg_zero
    | infinity sx =>
      cases sx with
      | true =>
        simp only [atan2WithPeriodPrecRound, toVal_zero, toVal_infinity, Option.bind_some,
          ↓reduceIte]
        rw [← EReal.coe_zero, Spec.atan2WithPeriod_of (Spec.atan2_coe_top 0)]
        exact hzero rfl
      | false =>
        simp only [atan2WithPeriodPrecRound, toVal_zero, toVal_infinity, Option.bind_some,
          Bool.false_eq_true, ↓reduceIte]
        rw [← EReal.coe_zero, Spec.atan2WithPeriod_of hbot0]
        exact turnFracN_round_pos 1 u 1 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
    | finite sx ex qx mx hvx =>
      simp only [atan2WithPeriodPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.atan2WithPeriod_of (Spec.atan2_coe_coe _ _)]
      have hs := finiteVal_sign_iff sx ex hvx
      have hx0 := finiteVal_ne_zero sx ex hvx
      cases sx with
      | true =>
        simp only [↓reduceIte]
        exact hzero (Complex.arg_ofReal_of_nonneg (hs.mp rfl).le)
      | false =>
        have hneg : finiteVal false ex mx < 0 := by
          rcases lt_or_gt_of_ne hx0 with h | h
          · exact h
          · exact absurd (hs.mpr h) (by simp)
        have h : Complex.arg ⟨finiteVal false ex mx, 0⟩ = π := Complex.arg_ofReal_of_neg hneg
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h]
        exact turnFracN_round_pos 1 u 1 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
  | infinity sy =>
    cases x with
    | nan => cases sy <;> rfl
    | zero =>
      simp only [atan2WithPeriodPrecRound, toVal_zero, toVal_infinity, Option.bind_some]
      rw [← EReal.coe_zero]
      cases sy with
      | true =>
        simp only [↓reduceIte]
        rw [Spec.atan2WithPeriod_of (Spec.atan2_top_coe 0)]
        exact turnFracN_round_pos 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Spec.atan2WithPeriod_of (Spec.atan2_bot_coe 0)]
        exact turnFracN_round_neg 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
    | infinity sx =>
      simp only [atan2WithPeriodPrecRound, toVal_infinity, Option.bind_some]
      cases sx with
      | true =>
        cases sy with
        | true =>
          simp only [↓reduceIte]
          rw [Spec.atan2WithPeriod_of Spec.atan2_top_top]
          exact turnFracN_round_pos 1 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Spec.atan2WithPeriod_of Spec.atan2_bot_top]
          exact turnFracN_round_neg 1 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
      | false =>
        cases sy with
        | true =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Spec.atan2WithPeriod_of Spec.atan2_top_bot]
          exact turnFracN_round_pos 3 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Spec.atan2WithPeriod_of Spec.atan2_bot_bot]
          exact turnFracN_round_neg 3 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
    | finite sx ex qx mx hvx =>
      simp only [atan2WithPeriodPrecRound, toVal_finite, toVal_infinity, Option.bind_some]
      cases sy with
      | true =>
        simp only [↓reduceIte]
        rw [Spec.atan2WithPeriod_of (Spec.atan2_top_coe _)]
        exact turnFracN_round_pos 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Spec.atan2WithPeriod_of (Spec.atan2_bot_coe _)]
        exact turnFracN_round_neg 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
  | finite sy ey qy my hvy =>
    have hsy := finiteVal_sign_iff sy ey hvy
    have hy0 := finiteVal_ne_zero sy ey hvy
    have hneg := finiteVal_neg_iff sy ey hvy
    cases x with
    | nan => rfl
    | zero =>
      simp only [atan2WithPeriodPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.atan2WithPeriod_of (Spec.atan2_coe_coe _ _), arg_zero_re hy0]
      cases sy with
      | true =>
        rw [ite_eq_left (hsy.mp rfl)]
        exact turnFracN_round_pos 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
      | false =>
        rw [ite_eq_right (not_lt.mpr (hneg.mp rfl).le)]
        exact turnFracN_round_neg 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
    | infinity sx =>
      cases sx with
      | true =>
        simp only [atan2WithPeriodPrecRound, toVal_finite, toVal_infinity, Option.bind_some,
          ↓reduceIte]
        rw [Spec.atan2WithPeriod_of (Spec.atan2_coe_top _)]
        exact hzero rfl
      | false =>
        simp only [atan2WithPeriodPrecRound, toVal_finite, toVal_infinity, Option.bind_some,
          Bool.false_eq_true, ↓reduceIte]
        cases sy with
        | true =>
          have h : Spec.atan2 ((finiteVal true ey my : ℝ) : EReal) ⊥
              = some ((π : ℝ) : EReal) := by
            rw [Spec.atan2_coe_bot, ite_eq_right (not_lt.mpr (hsy.mp rfl).le)]
          rw [Spec.atan2WithPeriod_of h]
          exact turnFracN_round_pos 1 u 1 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
        | false =>
          have h : Spec.atan2 ((finiteVal false ey my : ℝ) : EReal) ⊥
              = some ((-π : ℝ) : EReal) := by
            rw [Spec.atan2_coe_bot, ite_eq_left (hneg.mp rfl)]
          rw [Spec.atan2WithPeriod_of h]
          exact turnFracN_round_neg 1 u 1 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
    | finite sx ex qx mx hvx =>
      simp only [atan2WithPeriodPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.atan2WithPeriod_of (Spec.atan2_coe_coe _ _)]
      set yv := finiteVal sy ey my with hyv
      set xv := finiteVal sx ex mx with hxv
      have hx0 : xv ≠ 0 := finiteVal_ne_zero sx ex hvx
      have hxpos : sx = true ↔ 0 < xv := finiteVal_sign_iff sx ex hvx
      have hval := arg_eq_atan2Abs hx0 hy0 hneg hxpos
      have hya : (finite sy ey qy my hvy).abs.toVal = some ((|yv| : ℝ) : EReal) := by
        rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
        congr 1
      have hxa : (finite sx ex qx mx hvx).abs.toVal = some ((|xv| : ℝ) : EReal) := by
        rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
        congr 1
      by_cases hu : u.toNat = 0
      · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
          roundVal_zero]
      · rw [dite_eq_right hu]
        by_cases h1 : eqIEEE (finite sy ey qy my hvy).abs (finite sx ex qx mx hvx).abs = true
        · rw [dite_eq_left h1]
          obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
          rw [hya] at hv1
          rw [hxa] at hv2
          have habs : |yv| = |xv| := by
            have := hv1.trans hv2.symm
            exact_mod_cast Option.some.inj this
          have hb0 : |xv| ≠ 0 := abs_ne_zero.mpr hx0
          have hquot : arctan (|xv| / |xv|) = π / 4 := by rw [div_self hb0, arctan_one]
          rw [habs] at hval
          unfold atan2Abs at hval
          rw [hquot] at hval
          rw [hval]
          cases sy <;> cases sx <;>
            simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
          · exact turnFracN_round_neg 3 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
          · exact turnFracN_round_neg 1 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
          · exact turnFracN_round_pos 3 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
          · exact turnFracN_round_pos 1 u 3 p mode (by
            push_cast
            rw [div_eq_iff (by positivity)]
            ring)
        · rw [dite_eq_right h1, dite_eq_right hp]
          have hxy : |yv| ≠ |xv| := fun h =>
            h1 ((eqIEEE_iff _ _).mpr ⟨_, hya, by rw [h]; exact hxa⟩)
          have hper := arg_period_eq hx0 hy0 hneg hxpos (u.toNat : ℝ)
          have hirr := irrational_atan2AbsPeriod_of_toVal (toVal_finite sy ey qy my hvy)
            (toVal_finite sx ex qx mx hvx) hy0 hx0 hxy hxpos hu
          set ψ := atan2Abs |yv| |xv| sx * u.toNat / (2 * π) with hψ
          have key : ∀ (o : Bool) (m : RoundingMode),
              zivLoopCertified
                (atan2PeriodApprox o (finite sy ey qy my hvy) (finite sx ex qx mx hvx) ey ex sx
                  (AzNat.ofNat u.toNat)) p m (p + zivGuardBits)
                (atan2PeriodApprox_isSome_exists p m o (toVal_finite sy ey qy my hvy)
                  (toVal_finite sx ex qx mx hvx) hy0 hx0 hxy hxpos
                  (abs_finiteVal_bounds sy ey hvy).2 (abs_finiteVal_bounds sx ex hvx).1
                  (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
                  (by unfold zivGuardBits; omega))
              = roundVal p m (some (((if o then -1 else 1) * ψ : ℝ) : EReal)) := fun o m =>
            zivLoopCertified_eq_threshold' p m _ _
              (not_mem_floatSet_of_irrational p (by
                cases o with
                | false => simpa using hirr
                | true => simpa using hirr.neg)) _ (by unfold zivGuardBits; omega)
              (fun w _ => by
                obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := atan2PeriodApprox_spec o
                  (toVal_finite sy ey qy my hvy) (toVal_finite sx ex qx mx hvx) hy0 hx0
                  (abs_finiteVal_bounds sy ey hvy).2 (abs_finiteVal_bounds sx ex hvx).1 sx
                  (AzNat.ofNat u.toNat) w
                rw [AzNat.toNat_ofNat] at hlo hhi
                exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
          rw [hper]
          set o := atan2PeriodOrient (finite sy ey qy my hvy) (finite sx ex qx mx hvx) sx
            with hodef
          rw [key o (if o = !sy then mode else -mode)]
          by_cases ho : o = !sy
          · rw [ite_eq_left ho, ite_eq_left ho, ho]
          · rw [ite_eq_right ho, ite_eq_right ho]
            have hflip : ∀ a b : Bool, ¬ a = !b → (if (!b) = true then (-1 : ℝ) else 1) * ψ
                = -((if a = true then (-1 : ℝ) else 1) * ψ) := by
              intro a b h
              cases a <;> cases b <;> simp at h ⊢
            rw [hflip o sy ho, roundVal_neg]

end Azurite.AzFloat
