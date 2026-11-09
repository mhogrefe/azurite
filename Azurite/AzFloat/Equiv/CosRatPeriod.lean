/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRatPeriod
import Azurite.AzFloat.Equiv.CosPeriod
import Azurite.AzFloat.Equiv.CosRat

/-!
# Equivalence: `cos (2π q / u)` for a rational `q`

`cosRatWithPeriodPrecRound_eq :
  cosRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.cosWithPeriod q u)` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`cos (2π q / u)` is correctly rounded.** -/
theorem cosRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cosRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.cosWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold cosRatWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu, hu, Spec.cosWithPeriod_zero_period, roundVal_none]
  rw [dite_eq_right hu, dite_eq_right hp, Spec.cosWithPeriod_coe _ hu]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, mul_zero, zero_div,
      Real.cos_zero, setPrecRound_eq_roundVal toVal_one']
  rw [dite_eq_right h0]
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  have hU : (0 : ℝ) < u.toNat := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hU1 : (1 : ℝ) ≤ u.toNat := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hax := abs_nonneg qv
  have habs : |2 * Real.pi * qv / u.toNat| = 2 * Real.pi * (|qv| / u.toNat) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hU, mul_div_assoc]
  split
  · next r hT =>
    obtain ⟨hs, he⟩ := cosTiny?_cond hT
    set E := ratExpBound q + AzInt.ofInt 2 with hE
    have htoInt : E.toInt = if E.sign then (E.abs.toNat : ℤ) else -(E.abs.toNat : ℤ) := rfl
    rw [hs] at htoInt
    simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
    have he2 : E.toInt = (ratExpBound q).toInt + 2 := by
      rw [hE, AzInt.toInt_add, AzInt.toInt_ofInt]
    have hq := abs_toRat_lt_two_zpow q
    rw [← hqv] at hq
    have hpi4 := Real.pi_le_four
    have hpi0 := Real.pi_pos
    have ht : (2 : ℝ) ^ E.toInt = 8 * (2 : ℝ) ^ ((ratExpBound q).toInt - 1) := by
      rw [he2, show (ratExpBound q).toInt + 2 = ((ratExpBound q).toInt - 1) + 3 by ring,
        zpow_add₀ two_ne_zero]
      norm_num; ring
    have hsmall : (2 : ℝ) ^ E.toInt ≤ 1 / 2 := by
      rw [htoInt, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
      calc (1 / 2 : ℝ) ^ E.abs.toNat ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    have hdiv : |qv| / u.toNat ≤ |qv| := div_le_self hax hU1
    have hbound : |2 * Real.pi * qv / u.toNat| < (2 : ℝ) ^ E.toInt := by
      rw [habs, ht]
      nlinarith [mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    refine cosTiny?_eq hbound ?_ hT
    have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
    have hr : |qv| / u.toNat = ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
      push_cast; rfl
    rw [← Real.cos_abs, habs, hr]
    apply irrational_cos_two_pi_mul_rat_of_small
    · have h1 : (0 : ℝ) < ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) := by
        rw [← hr]; exact div_pos (abs_pos.mpr hq0) hU
      exact_mod_cast h1
    · have h1 : ((|AzRat.toRat q| / (u.toNat : ℚ) : ℚ) : ℝ) < ((1 / 6 : ℚ) : ℝ) := by
        rw [← hr]; push_cast; linarith
      exact_mod_cast h1
  dsimp only
  set r := periodFracRat q (AzNat.ofNat u.toNat) with hr
  have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
    rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
  obtain ⟨k, hk, hr0, hr1⟩ := periodFracRat_spec q hun
  rw [AzNat.toNat_ofNat, ← hqv] at hk
  have hcos : Real.cos (2 * Real.pi * qv / u.toNat)
      = Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) := by
    rw [← Real.cos_abs, habs, hk,
      show 2 * Real.pi * ((k : ℝ) + (AzRat.toRat r : ℝ))
        = 2 * Real.pi * (AzRat.toRat r : ℝ) + k * (2 * Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi _ k
  rw [hcos]
  split_ifs with h1 h2 h4 h3 h6
  · rw [cos_two_pi_mul_rat_of_den_eq_one (den_toRat_eq h1),
      setPrecRound_eq_roundVal toVal_one']
  · rw [cos_two_pi_mul_rat_of_den_eq_two (den_toRat_eq h2),
      setPrecRound_eq_roundVal toVal_neg_one]
  · rw [cos_two_pi_mul_rat_of_den_eq_four (den_toRat_eq h4), EReal.coe_zero, roundVal_zero]
  · rw [cos_two_pi_mul_rat_of_den_eq_three (den_toRat_eq h3),
      setPrecRound_eq_roundVal toVal_neg_one_half]
  · rw [cos_two_pi_mul_rat_of_den_eq_six (den_toRat_eq h6),
      setPrecRound_eq_roundVal toVal_one_half]
  · exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          cosPeriodApprox_spec r hr0 hr1 (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
