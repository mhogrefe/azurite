/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammerRat
import Azurite.AzFloat.Equiv.GenPochhammer
import Azurite.AzFloat.Equiv.PochhammerRat
import Azurite.AzFloat.Equiv.BetaRat

/-!
# Equivalence: the generalized Pochhammer symbol of two rationals

`genPochhammerRatPrecRound_eq_or`: `genPochhammerRatPrecRound x y p mode` is the correct
rounding of `Spec.genPochhammerReal x y` (`Equiv/GenPochhammer.lean`), or `(nan, .eq)` when
the fuel of the Ziv loop runs out.
-/

namespace Azurite.AzFloat

open Finset

/-- **`genPochRatPole` decides whether `(x − n) ⋯ (x − 1)` vanishes.** -/
theorem genPochRatPole_iff (x : AzRat) (n : ℕ) :
    genPochRatPole x n = true ↔
      ∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j) = 0 := by
  unfold genPochRatPole
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne, AzNat.compare_eq_compare_toNat,
    AzNat.toNat_ofNat, prod_eq_zero_iff]
  constructor
  · rintro ⟨⟨⟨hd, hs⟩, hnum⟩, hle⟩
    have hval := toRat_eq_of_int_den_one x hs hd
    have hkn : x.num.toNat ≤ n := by
      by_contra hgt
      exact hle (Nat.compare_eq_gt.mpr (by omega))
    by_cases h0 : x.num.toNat = 0
    · exfalso
      exact hnum (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero]))
    · refine ⟨n - x.num.toNat, mem_range.mpr (by omega), ?_⟩
      rw [hval, Nat.cast_sub hkn]
      ring
  · rintro ⟨j, hj, h0⟩
    have hjn : j < n := mem_range.mp hj
    have hxv : ((AzRat.toRat x : ℚ) : ℝ) = ((n - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub hjn.le]; linarith
    have hpos : (0 : ℝ) < ((AzRat.toRat x : ℚ) : ℝ) := by
      rw [hxv]; exact_mod_cast Nat.sub_pos_of_lt hjn
    have hd : x.den = 1 := by
      by_contra hd
      exact not_exists_int_of_den_ne_one x hd ⟨((n - j : ℕ) : ℤ), by rw [hxv]; push_cast; rfl⟩
    have hnum : x.num ≠ 0 := fun h => by
      rw [coe_toRat_eq_zero_of_num_eq_zero x h] at hpos
      exact lt_irrefl _ hpos
    have hs : x.sign = true := (toRat_sign_iff x hnum).mpr (by exact_mod_cast hpos)
    refine ⟨⟨⟨hd, hs⟩, hnum⟩, ?_⟩
    have hval := toRat_eq_of_int_den_one x hs hd
    have : x.num.toNat = n - j := by
      have : ((x.num.toNat : ℕ) : ℝ) = ((n - j : ℕ) : ℝ) := by rw [← hval, hxv]
      exact_mod_cast this
    intro hgt
    have := Nat.compare_eq_gt.mp hgt
    omega

/-- `genPochRatNegInt` is the correct rounding of `Γ(x − n)/Γ(x)`, or the fuel ran out. -/
theorem genPochRatNegInt_eq_or (x : AzRat) {n : ℕ} (hn : n ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    genPochRatNegInt x n p mode
        = roundVal p mode (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) (-(n : ℝ))) ∨
      genPochRatNegInt x n p mode = (nan, .eq) := by
  unfold genPochRatNegInt
  rw [Spec.genPochhammerReal_neg_nat _ hn]
  by_cases hpole : genPochRatPole x n = true
  · left
    rw [ite_eq_left hpole, ite_eq_left ((genPochRatPole_iff x n).mp hpole), roundVal_none]
  have hne : ∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j) ≠ 0 :=
    fun h0 => hpole ((genPochRatPole_iff x n).mpr h0)
  rw [ite_eq_right hpole, ite_eq_right (NeZero.ne p), ite_eq_right hne]
  split_ifs
  · left
    exact recipPochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real x)
      (mkNorm_div_den_eq x) hne p mode
  · rcases eq_or_ne (zivLoop (recipPochRatApprox (x - (n : AzRat)) n) p mode (gammaFuel p)
      (max 64 (p + 32))) (nan, .eq) with hzv | hzv
    · right; exact hzv
    · left
      refine zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => gammaApproxOf_valid_or_none (fun _ _ hc => ?_) w p mode)
        _ _ (le_max_left _ _) hzv
      have := recipPochCoreOf_spec (fun V _ => lnGammaRatEncl_isEncl (x - (n : AzRat)) V)
        (pochRatSplit_le _ n) hw hc
      rwa [AzRat.toRat_sub, AzRat.toRat_natCast, Rat.cast_sub, Rat.cast_natCast] at this

open Classical in
/-- **The generalized Pochhammer symbol of two rationals is correctly rounded, or the fuel ran
out.** -/
theorem genPochhammerRatPrecRound_eq_or (x y : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    genPochhammerRatPrecRound x y p mode
        = roundVal p mode (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ)
          ((AzRat.toRat y : ℚ) : ℝ)) ∨
      genPochhammerRatPrecRound x y p mode = (nan, .eq) := by
  unfold genPochhammerRatPrecRound
  by_cases hd : y.den = 1
  · rw [ite_eq_left hd]
    by_cases hs : y.sign = true ∨ y.num = 0
    · rw [ite_eq_left hs]
      have hyv : ((AzRat.toRat y : ℚ) : ℝ) = (y.num.toNat : ℝ) := by
        rcases hs with hs | h0
        · exact toRat_eq_of_int_den_one y hs hd
        · rw [coe_toRat_eq_zero_of_num_eq_zero y h0, h0, AzNat.toNat_zero, Nat.cast_zero]
      rw [hyv, Spec.genPochhammerReal_nat]
      have := pochhammerRatPrecRound_eq_or x y.num.toNat p mode
      by_cases hn : y.num.toNat = 0
      · rw [hn] at this ⊢
        rwa [Spec.pochhammer_zero, show (some (1 : EReal)) = some ((∏ j ∈ range 0,
          (((AzRat.toRat x : ℚ) : ℝ) + j) : ℝ) : EReal) by simp] at this
      · rwa [Spec.pochhammer_coe hn] at this
    · rw [ite_eq_right hs]
      push Not at hs
      obtain ⟨hsf, h0⟩ := hs
      have hsf' : y.sign = false := by simpa using hsf
      have hn : y.num.toNat ≠ 0 := fun h =>
        h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
      have hyv : ((AzRat.toRat y : ℚ) : ℝ) = -(y.num.toNat : ℝ) := by
        rw [coe_toRat_eq_mkNorm_of_den_one y hd, AzNat.toInt_mkNorm, hsf']
        simp
      rw [hyv]
      exact genPochRatNegInt_eq_or x hn p mode
  rw [ite_eq_right hd]
  have hni : ¬ ∃ k : ℤ, ((AzRat.toRat y : ℚ) : ℝ) = k := not_exists_int_of_den_ne_one y hd
  have hsum : ((AzRat.toRat (x + y) : ℚ) : ℝ)
      = ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) := by
    rw [AzRat.toRat_add]; push_cast; rfl
  have hspec : Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) ((AzRat.toRat y : ℚ) : ℝ) =
      if ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) ≤ 0
          ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) = k then none
      else some ((Real.Gamma (((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ))
        / Real.Gamma ((AzRat.toRat x : ℚ) : ℝ) : ℝ) : EReal) := by
    unfold Spec.genPochhammerReal
    rw [ite_eq_right hni]
  rw [hspec]
  by_cases hxp : x.den = 1 ∧ (x.num = 0 ∨ x.sign = false)
  · left
    rw [ite_eq_left hxp]
    obtain ⟨hle, k, hk⟩ := (nonpos_int_iff x).mp hxp
    have hns : ¬ (((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) ≤ 0
        ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) = k) := by
      rintro ⟨-, j, hj⟩
      exact hni ⟨j - k, by push_cast; linarith⟩
    rw [ite_eq_right hns, gamma_eq_zero_of_nonpos_int hle hk, div_zero, EReal.coe_zero,
      roundVal_zero]
  rw [ite_eq_right hxp]
  by_cases hs : (x + y).den = 1 ∧ ((x + y).num = 0 ∨ (x + y).sign = false)
  · left
    have := (nonpos_int_iff (x + y)).mp hs
    rw [hsum] at this
    rw [ite_eq_left hs, ite_eq_left this, roundVal_none]
  have hns : ¬ (((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) ≤ 0
      ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) = k) := by
    intro h
    rw [← hsum] at h
    exact hs ((nonpos_int_iff (x + y)).mpr h)
  rw [ite_eq_right hs, ite_eq_right (NeZero.ne p), ite_eq_right hns]
  rcases eq_or_ne (zivLoop (genPochRatApprox x (x + y)) p mode (gammaFuel p) (max 64 (p + 32)))
    (nan, .eq) with hzv | hzv
  · right; exact hzv
  · left
    refine zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApproxOf_valid_or_none (fun _ _ hc => ?_) w p mode)
      _ _ (le_max_left _ _) hzv
    have := gammaQuotEnclOf_spec (fun V _ => lnGammaRatEncl_isEncl x V)
      (fun V _ => lnGammaRatEncl_isEncl (x + y) V)
      (fun W σ k E _ hF => gammaRatFrac_spec x hF)
      (fun W σ k E _ hF => gammaRatFrac_spec (x + y) hF) hw hc
    rwa [hsum] at this

end Azurite.AzFloat
