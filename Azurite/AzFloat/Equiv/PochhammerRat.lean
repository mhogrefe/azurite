/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PochhammerRat
import Azurite.AzFloat.Equiv.Pochhammer
import Azurite.AzFloat.Equiv.BetaRat
import Azurite.AzNat.Equiv.Compare

/-!
# Equivalence: Pochhammer's symbol of a rational

`pochhammerRatPrecRound_eq_or`: `pochhammerRatPrecRound q n p mode` is the correct rounding of
`Spec.pochhammer n q` (`Equiv/Pochhammer.lean`), or `(nan, .eq)` when the fuel of the Ziv loop
runs out.  The steps: `pochRatHasZero_spec`, `pochRatSplit_le`, `pochRatCore_spec`.
-/

namespace Azurite.AzFloat

open Finset

/-- A vanishing factor. -/
theorem pochRatHasZero_spec {q : AzRat} {n : ℕ} (h : pochRatHasZero q n = true) :
    ∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j) = 0 := by
  unfold pochRatHasZero at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq, AzNat.compare_eq_compare_toNat,
    AzNat.toNat_ofNat, Nat.compare_eq_lt] at h
  obtain ⟨⟨hd, hs⟩, hlt⟩ := h
  have hval : ((AzRat.toRat q : ℚ) : ℝ) = -(q.num.toNat : ℝ) := by
    rcases hs with h0 | hs
    · rw [coe_toRat_eq_zero_of_num_eq_zero q h0, h0, AzNat.toNat_zero]
      simp
    · rw [coe_toRat_eq_mkNorm_of_den_one q hd, AzNat.toInt_mkNorm, hs]
      simp
  refine prod_eq_zero (i := q.num.toNat) (mem_range.mpr hlt) ?_
  rw [hval]
  ring

theorem pochRatSplit_le (q : AzRat) (n : ℕ) : pochRatSplit q n ≤ n := by
  unfold pochRatSplit
  split_ifs <;> first | exact Nat.zero_le n | exact le_rfl | exact min_le_left _ _

/-- **`pochRatCore` answers with the sign and a positive enclosure of `|(q)ₙ|`.** -/
theorem pochRatCore_spec (q : AzRat) {n w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : pochRatCore q n w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * ∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j)) :=
  pochCoreOf_spec (fun V _ => lnGammaRatEncl_isEncl q V) (pochRatSplit_le q n) hw h

/-- **Pochhammer's symbol of a rational is correctly rounded, or the fuel ran out.** -/
theorem pochhammerRatPrecRound_eq_or (q : AzRat) (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochhammerRatPrecRound q n p mode
        = roundVal p mode (Spec.pochhammer n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      pochhammerRatPrecRound q n p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold pochhammerRatPrecRound
  by_cases hn : n = 0
  · left
    subst hn
    rw [ite_eq_left rfl, ite_eq_right hp, Spec.pochhammer_zero,
      setPrecRound_eq_roundVal toVal_one', EReal.coe_one]
  rw [ite_eq_right hn, Spec.pochhammer_coe hn]
  by_cases hz : pochRatHasZero q n = true
  · left
    rw [ite_eq_left hz, pochRatHasZero_spec hz, EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right hz, ite_eq_right hp]
  split
  · next r hr =>
    left
    unfold pochRatExact? at hr
    split_ifs at hr
    rw [Option.some.injEq] at hr
    subst hr
    exact pochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real q)
      (mkNorm_div_den_eq q) n p mode
  · rcases eq_or_ne (zivLoop (pochRatApprox q n) p mode (gammaFuel p) (max 64 (p + 32)))
      (nan, .eq) with hzv | hzv
    · right; exact hzv
    · left
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => gammaApproxOf_valid_or_none (fun _ _ hc => pochRatCore_spec q hw hc) w p
          mode)
        _ _ (le_max_left _ _) hzv

end Azurite.AzFloat
