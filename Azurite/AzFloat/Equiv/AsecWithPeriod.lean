/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecWithPeriod
import Azurite.AzFloat.Equiv.Asec
import Azurite.AzFloat.Equiv.AcosWithPeriod

/-!
# Equivalence: `arcsec (x) u / (2π)`

`Spec.asecWithPeriod a u = (Spec.asec a) · u / (2π)` (so `u/4` at `±∞`, undefined inside
`(−1, 1)`) and
`asecWithPeriodPrecRound_eq :
  asecWithPeriodPrecRound x u p mode = roundVal p mode (x.toVal.bind (Spec.asecWithPeriod · u))`
for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `arcsec (a) u / (2π)`: `u/4` at `±∞`, undefined inside `(−1, 1)`. -/
noncomputable def asecWithPeriod (a : EReal) (u : ℕ) : Option EReal :=
  (asec a).map fun θ => ((θ.toReal * u / (2 * π) : ℝ) : EReal)

theorem asecWithPeriod_coe {r : ℝ} (hr : 1 ≤ |r|) (u : ℕ) :
    asecWithPeriod (r : EReal) u = some ((arccos r⁻¹ * u / (2 * π) : ℝ) : EReal) := by
  unfold asecWithPeriod
  rw [asec_coe hr, Option.map_some, EReal.toReal_coe]

theorem asecWithPeriod_coe_of_lt_one {r : ℝ} (hr : |r| < 1) (u : ℕ) :
    asecWithPeriod (r : EReal) u = none := by
  unfold asecWithPeriod
  rw [asec_coe_of_lt_one hr, Option.map_none]

theorem asecWithPeriod_top (u : ℕ) :
    asecWithPeriod ⊤ u = some ((π / 2 * u / (2 * π) : ℝ) : EReal) := by
  unfold asecWithPeriod
  rw [asec_top, Option.map_some, EReal.toReal_coe]

theorem asecWithPeriod_bot (u : ℕ) :
    asecWithPeriod ⊥ u = some ((π / 2 * u / (2 * π) : ℝ) : EReal) := by
  unfold asecWithPeriod
  rw [asec_bot, Option.map_some, EReal.toReal_coe]

end Spec

/-- **`arcsec (x) u / (2π)` is correctly rounded.** -/
theorem asecWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    asecWithPeriodPrecRound x u p mode
      = roundVal p mode (x.toVal.bind fun a => Spec.asecWithPeriod a u.toNat) := by
  have hp := NeZero.ne p
  obtain ⟨hv0, hvm1, hvh, hvmh⟩ := acosPeriod_values (u.toNat : ℝ)
  have hquarter : π / 2 * (u.toNat : ℝ) / (2 * π) = (1 : ℕ) * (u.toNat : ℝ) / (4 : ℕ) := by
    rw [← arccos_zero]
    exact hv0
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [asecWithPeriodPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.asecWithPeriod_top, Spec.asecWithPeriod_bot] <;>
      rw [ite_eq_right hp] <;> exact turnRatio_eq u 1 4 p mode hquarter
  | zero =>
    simp only [asecWithPeriodPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.asecWithPeriod_coe_of_lt_one (by simp), roundVal_none]
  | finite s e q m hv =>
    simp only [asecWithPeriodPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [dite_eq_left h1]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.asecWithPeriod_coe habs1.ge, eq_signed_of_abs_eq hsgn hx0 habs1]
      cases s with
      | true =>
        simp only [↓reduceIte]
        rw [inv_one, arccos_one, zero_mul, zero_div, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right hp, inv_neg, inv_one]
        exact turnRatio_eq u 1 2 p mode hvm1
    · rw [dite_eq_right h1]
      have hne1 : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he]
        have hgt : 1 < |xv| := one_lt_abs_of_exponent hb.1 he hne1
        rw [Spec.asecWithPeriod_coe hgt.le]
        by_cases hu : u.toNat = 0
        · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
            roundVal_zero]
        · rw [dite_eq_right hu, dite_eq_right hp]
          have htwo : (one <<< AzInt.ofInt 1).toVal = some ((2 : ℝ) : EReal) := by
            rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
            norm_num
          by_cases h2 : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt 1) = true
          · rw [dite_eq_left h2]
            obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h2
            rw [habs] at hv1
            rw [htwo] at hv2
            have habs2 : |xv| = 2 := by
              have := hv1.trans hv2.symm
              exact_mod_cast Option.some.inj this
            rw [eq_signed_of_abs_eq hsgn hx0 habs2]
            cases s with
            | true =>
              simp only [↓reduceIte]
              rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
              exact turnRatio_eq u 1 6 p mode hvh
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [show (-2 : ℝ)⁻¹ = -(1 / 2) by norm_num]
              exact turnRatio_eq u 1 3 p mode hvmh
          · rw [dite_eq_right h2]
            have hne2 : |xv| ≠ 2 := fun h =>
              h2 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact htwo⟩)
            have hirr := irrational_asecPeriod_of_toVal (toVal_finite s e q m hv) hgt hne2 hu
            set ψ := arccos xv⁻¹ * u.toNat / (2 * π) with hψ
            have key : ∀ (o : Bool) (m' : RoundingMode),
                zivLoopCertified
                  (asecPeriodApprox o s (finite s e q m hv) (AzNat.ofNat u.toNat)) p m'
                  (p + zivGuardBits)
                  (asecPeriodApprox_isSome_exists p m' o (toVal_finite s e q m hv) hgt hne2
                    hsgn (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
                    (by unfold zivGuardBits; omega))
                = roundVal p m' (some (((if o then -1 else 1) * ψ : ℝ) : EReal)) :=
              fun o m' =>
              zivLoopCertified_eq_threshold' p m' _ _
                (not_mem_floatSet_of_irrational p (by
                  cases o with
                  | false => simpa using hirr
                  | true => simpa using hirr.neg)) _ (by unfold zivGuardBits; omega)
                (fun w _ => by
                  obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := asecPeriodApprox_spec o
                    (toVal_finite s e q m hv) hgt hsgn (AzNat.ofNat u.toNat) w
                  rw [AzNat.toNat_ofNat] at hlo hhi
                  exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
            set o := acosPeriodOrientOf
              (le (one <<< AzInt.ofInt 1) (finite s e q m hv).abs) s with hodef
            rw [key o (if o then -mode else mode)]
            exact orient_roundVal o p mode ψ
      · rw [dite_eq_right he]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.asecWithPeriod_coe_of_lt_one hlt1, roundVal_none]

end Azurite.AzFloat
