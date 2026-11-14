/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanRatWithPeriod
import Azurite.AzFloat.Equiv.TanWithPeriod
import Azurite.AzFloat.Equiv.SinRatWithPeriod

/-!
# Equivalence: `tan (2π q / u)` for a rational `q`

`tanRatWithPeriodPrecRound_eq :
  tanRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.tanWithPeriod q u)` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`tan (2π q / u)` of a rational is correctly rounded**, with the IEEE 754 poles. -/
theorem tanRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    tanRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.tanWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold tanRatWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu, Spec.tanWithPeriod_zero_period, roundVal_none]
  rw [dite_eq_right hu, Spec.tanWithPeriod_coe _ hu]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, mul_zero, zero_div,
      Spec.tanPole_of_cos_ne_zero (by rw [Real.cos_zero]; norm_num), Real.tan_zero,
      EReal.coe_zero, roundVal_zero]
  rw [dite_eq_right h0, dite_eq_right hp]
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  have hUn : 0 < u.toNat := Nat.pos_of_ne_zero hu
  have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
  have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast hUn
  have hpi0 := Real.pi_pos
  have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  have hax := abs_pos.mpr hq0
  have hneg : (!q.sign) = true ↔ qv < 0 := by
    have hpos := toRat_sign_iff q h0
    rw [Bool.not_eq_true', ← Bool.not_eq_true, hpos, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h hq0, le_of_lt⟩
  split
  · next r hT =>
    obtain ⟨hs, he⟩ := tanPeriodTiny?_cond hT
    unfold zivGuardBits at he
    set E := ratExpBound q + AzInt.ofInt 2 with hE
    have htoInt : E.toInt = if E.sign then (E.abs.toNat : ℤ) else -(E.abs.toNat : ℤ) := rfl
    rw [hs] at htoInt
    simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
    have he2 : E.toInt = (ratExpBound q).toInt + 2 := by
      rw [hE, AzInt.toInt_add, AzInt.toInt_ofInt]
    have hq := abs_toRat_lt_two_zpow q
    rw [← hqv] at hq
    have hpi4 := Real.pi_le_four
    have ht : (2 : ℝ) ^ E.toInt = 8 * (2 : ℝ) ^ ((ratExpBound q).toInt - 1) := by
      rw [he2, show (ratExpBound q).toInt + 2 = ((ratExpBound q).toInt - 1) + 3 by ring,
        zpow_add₀ two_ne_zero]
      norm_num; ring
    have hsmall : (2 : ℝ) ^ E.toInt ≤ 1 / 2 := by
      rw [htoInt, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
      calc (1 / 2 : ℝ) ^ E.abs.toNat ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    have hdiv : |qv| / u.toNat ≤ |qv| := div_le_self hax.le hU1
    have hbound : 2 * Real.pi * (|qv| / u.toNat) < (2 : ℝ) ^ E.toInt := by
      rw [ht]
      nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have hirr : Irrational (Real.tan (2 * Real.pi * (|qv| / u.toNat))) := by
      have hr : |qv| / u.toNat = ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
        push_cast; rfl
      rw [hr]
      apply irrational_tan_two_pi_mul_rat_of_small
      · have h1 : (0 : ℝ) < ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
          rw [← hr]; exact div_pos hax hU
        exact_mod_cast h1
      · have h1 : ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) < ((1 / 8 : ℚ) : ℝ) := by
          rw [← hr]; push_cast; linarith
        exact_mod_cast h1
    have hm : 0 < q.num.toNat :=
      Nat.pos_of_ne_zero fun h => h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
    have hD : 0 < (q.den * AzNat.ofNat u.toNat).toNat := by
      rw [AzNat.toNat_mul, AzNat.toNat_ofNat]
      exact Nat.mul_pos (AzRat.den_toNat_pos q) hUn
    have hy_eq : (q.num.toNat : ℝ) * (2 : ℝ) ^ (AzInt.ofInt 0).toInt
        / ((q.den * AzNat.ofNat u.toNat).toNat : ℝ) = |qv| / u.toNat := by
      rw [AzInt.toInt_ofInt, zpow_zero, mul_one, AzNat.toNat_mul, AzNat.toNat_ofNat, hqv,
        abs_coe_toRat, div_div]
      push_cast
      rfl
    have key := tanPeriodTiny?_eq hm hD (by rw [hy_eq]; exact hbound)
      (by rw [hy_eq]; exact hirr) hT
    rw [hy_eq] at key
    rw [Spec.tanPole_of_small hneg hU (by linarith)]
    exact key
  have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
    rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
  obtain ⟨k, hk, hr0, hr1⟩ := periodFracRat_spec q hun
  rw [AzNat.toNat_ofNat, ← hqv] at hk
  rw [tanPeriodCore_eq, Spec.tanPole_two_pi_div_bool hneg hk]

end Azurite.AzFloat
