/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBaseM1Rat
import Azurite.AzFloat.Equiv.PowBaseM1

/-!
# Equivalence: `u^q − 1` for a natural base and a rational exponent

`powBaseM1RatPrecRound_eq : powBaseM1RatPrecRound u q p mode
  = roundVal p mode (Spec.powBaseM1 u q)` for `p ≠ 0`: `u^q − 1` is correctly rounded in every
mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`u^q − 1` is correctly rounded.** -/
theorem powBaseM1RatPrecRound_eq (u : UInt64) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    powBaseM1RatPrecRound u q p mode
      = roundVal p mode (Spec.powBaseM1 u.toNat ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold powBaseM1RatPrecRound
  rw [Spec.powBaseM1_coe]
  by_cases h0 : u.toNat = 0
  · rw [dite_eq_left h0]
    by_cases hq0 : q.num = 0
    · rw [ite_eq_left hq0, (AzRat.toRat_eq_zero_iff q).mpr hq0,
        ite_eq_right (fun h => lt_irrefl _ h.2), Real.rpow_zero, sub_self, EReal.coe_zero,
        roundVal_zero]
    · rw [ite_eq_right hq0]
      by_cases hs : q.sign = true
      · have hpos := toRat_pos_of_sign q hs hq0
        have hposR : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hpos
        rw [ite_eq_left hs, ite_eq_right (fun h => lt_asymm hposR h.2), h0, Nat.cast_zero,
          Real.zero_rpow hposR.ne', negOneRound_eq]
        norm_num
      · have hneg := toRat_neg_of_sign q (by simpa using hs) hq0
        rw [ite_eq_right hs, ite_eq_left ⟨h0, hneg⟩]
        simp
  rw [dite_eq_right h0, ite_eq_right (fun h => h0 h.1)]
  by_cases h1 : u.toNat = 1
  · rw [dite_eq_left h1, h1, Nat.cast_one, Real.one_rpow, sub_self, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h1]
    by_cases hq0 : q.num = 0
    · rw [dite_eq_left hq0, (AzRat.toRat_eq_zero_iff q).mpr hq0, Real.rpow_zero, sub_self,
        EReal.coe_zero, roundVal_zero]
    · rw [dite_eq_right hq0, dite_eq_right (NeZero.ne p)]
      have hu2 : 2 ≤ (AzNat.ofNat u.toNat).toNat := by rw [AzNat.toNat_ofNat]; omega
      split
      · rename_i r n hx
        obtain ⟨hr, hval⟩ := powBaseRatExact?_some q _ hu2 hx
        rw [AzNat.toNat_ofNat] at hval
        obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec (AzNat.ofNat u.toNat) hu2
        rw [← hr] at hc2
        have hrR : (0 : ℝ) < (r.toNat : ℝ) ^ n.abs.toNat := by positivity
        rw [hval, toInt_eq_of_sign]
        split_ifs with hs
        · rw [zpow_natCast, subPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzNat, toVal_one',
            Option.bind_some, Option.bind_some, Spec.sub, ← EReal.coe_neg, Spec.add_coe_coe,
            AzNat.toNat_pow, Nat.cast_pow, sub_eq_add_neg]
        · rw [zpow_neg, zpow_natCast, divPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzInt,
            toVal_ofAzNat, Option.bind_some, Option.bind_some, AzNat.toNat_pow, Nat.cast_pow,
            Spec.div_coe_coe _ _ hrR.ne', AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_pow]
          have h1' : ((1 : AzInt)).toInt = 1 := rfl
          rw [h1']
          have hval' : ((1 - (r.toNat ^ n.abs.toNat : ℕ) : ℤ) : ℝ) / (r.toNat : ℝ) ^ n.abs.toNat
              = ((r.toNat : ℝ) ^ n.abs.toNat)⁻¹ - 1 := by
            push_cast
            field_simp
          rw [hval']
      · rename_i hx
        exact zivLoopCertified_eq_threshold p mode _
          ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1) _
          (by unfold powBaseM1RatStart zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ := powBaseM1RatApprox_spec (w := w) q hq0 u
              (by omega)
              (AzNat.toNat_ofNat u.toNat ▸
                irrational_sub_one_of_powBaseRatExact?_none q (AzNat.ofNat u.toNat) hu2
                  (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
              (by unfold powBaseM1RatStart at hw; omega)
            exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
