/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.Equiv.PowBase

/-!
# Equivalence: `u^q` for a natural base and a rational exponent

`powBaseRatPrecRound_eq : powBaseRatPrecRound u q p mode = roundVal p mode (Spec.powBase u q)`
for `p ≠ 0`: `u^q` is correctly rounded in every mode, with the exact comparison, and without
fuel.
-/

namespace Azurite.AzFloat

/-- **`u^q` is correctly rounded.** -/
theorem powBaseRatPrecRound_eq (u : UInt64) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    powBaseRatPrecRound u q p mode
      = roundVal p mode (Spec.powBase u.toNat ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold powBaseRatPrecRound
  rw [Spec.powBase_coe]
  by_cases h0 : u.toNat = 0
  · rw [dite_eq_left h0]
    by_cases hq0 : q.num = 0
    · rw [ite_eq_left hq0, ite_eq_right (NeZero.ne p), (AzRat.toRat_eq_zero_iff q).mpr hq0,
        ite_eq_right (fun h => lt_irrefl _ h.2), Real.rpow_zero,
        setPrecRound_eq_roundVal toVal_one']
    · rw [ite_eq_right hq0]
      by_cases hs : q.sign = true
      · have hpos := toRat_pos_of_sign q hs hq0
        have hposR : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hpos
        rw [ite_eq_left hs, ite_eq_right (fun h => lt_asymm hposR h.2), h0, Nat.cast_zero,
          Real.zero_rpow hposR.ne']
        simp
      · have hneg := toRat_neg_of_sign q (by simpa using hs) hq0
        rw [ite_eq_right hs, ite_eq_left ⟨h0, hneg⟩]
        simp
  rw [dite_eq_right h0, dite_eq_right (NeZero.ne p), ite_eq_right (fun h => h0 h.1)]
  by_cases h1 : u.toNat = 1
  · rw [dite_eq_left h1, h1, Nat.cast_one, Real.one_rpow, setPrecRound_eq_roundVal toVal_one']
  · rw [dite_eq_right h1]
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
      · rw [zpow_natCast, setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_pow,
          Nat.cast_pow]
      · rw [zpow_neg, zpow_natCast, divPrecRound_eq_liftVal₂, liftVal₂, toVal_one',
          toVal_ofAzNat, Option.bind_some, Option.bind_some, AzNat.toNat_pow, Nat.cast_pow,
          Spec.div_coe_coe _ _ hrR.ne', one_div]
    · rename_i hx
      exact zivLoopCertified_eq_threshold p mode _ ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ)) _
        (by unfold powBaseRatStart zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ := powBaseRatApprox_spec (w := w) q u (by omega)
            (AzNat.toNat_ofNat u.toNat ▸
              irrational_of_powBaseRatExact?_none q (AzNat.ofNat u.toNat) hu2
                (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
            (by unfold powBaseRatStart at hw; omega)
          exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
