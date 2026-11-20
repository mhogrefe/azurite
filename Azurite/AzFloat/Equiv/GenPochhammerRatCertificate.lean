/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammerRatBracket
import Azurite.AzFloat.Equiv.GenPochhammer
import Azurite.AzFloat.Equiv.PochhammerRatCertificate

/-!
# The Ziv certificate of the reciprocal branch of the generalized Pochhammer symbol

`recipPochRatApprox_cert`: at a rational `x` whose denominator is not a power of two and
`n ≥ 4` (`recipPochRatSpecial`), some level of the bracket of `1/((x − n)ₙ)` is accepted by
`roundingPossible`.  The bracket converges (`recipPochRat_coreConv`: the reciprocal of
`pochCoreOf_coreConv`), and the value is not dyadic (`not_isDyadic_inv_prod_rat`).

This file does not import the function it certifies: `AzFloat/GenPochhammerRat.lean` imports
it.
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

/-- The value of `x − n`. -/
theorem coe_toRat_sub_natCast (x : AzRat) (n : ℕ) :
    ((AzRat.toRat (x - (n : AzRat)) : ℚ) : ℝ) = ((AzRat.toRat x : ℚ) : ℝ) - n := by
  rw [AzRat.toRat_sub, AzRat.toRat_natCast, Rat.cast_sub, Rat.cast_natCast]

/-- **The core of `1/((x − n)ₙ)` converges** off the poles. -/
theorem recipPochRat_coreConv (x : AzRat) {n : ℕ}
    (hne : ∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j) ≠ 0) (bits : ℕ) :
    CoreConv (recipPochCoreOf (lnGammaRatEncl (x - (n : AzRat)))
      (pochRatSplit (x - (n : AzRat)) n) n bits)
      (∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j))⁻¹ := by
  have hsv := coe_toRat_sub_natCast x n
  have hz : pochRatHasZero (x - (n : AzRat)) n = false := by
    rcases Bool.eq_false_or_eq_true (pochRatHasZero (x - (n : AzRat)) n) with h | h
    · have := pochRatHasZero_spec h
      rw [hsv] at this
      exact absurd this hne
    · exact h
  obtain ⟨h1, h2⟩ := pochRatSplit_facts (x - (n : AzRat)) hz
  have hconv := (pochCoreOf_coreConv
    (fun V _ => lnGammaRatEncl_level (x - (n : AzRat)) V) (pochRatSplit_le _ n) h1 h2
    bits).recip
  rw [hsv] at hconv
  exact hconv

/-- The bracket of `1/((x − n)ₙ)` is valid, or rejected. -/
theorem recipPochRatApprox_valid_or_none (x : AzRat) (n : ℕ) {w : ℕ} (hw : 64 ≤ w) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (recipPochRatApprox (x - (n : AzRat)) n w).1 lv ∧
        Rounds (recipPochRatApprox (x - (n : AzRat)) n w).2 hv ∧
        lv ≤ (∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j))⁻¹ ∧
        (∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j))⁻¹ ≤ hv ∧
        (lv = (∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j))⁻¹ →
          hv = (∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j))⁻¹)) ∨
      roundingPossible (recipPochRatApprox (x - (n : AzRat)) n w).1
        (recipPochRatApprox (x - (n : AzRat)) n w).2 p mode = none := by
  refine gammaApproxOf_valid_or_none (fun _ _ hcw => ?_) w p mode
  have := recipPochCoreOf_spec (fun V _ => lnGammaRatEncl_isEncl (x - (n : AzRat)) V)
    (pochRatSplit_le _ n) hw hcw
  rwa [coe_toRat_sub_natCast] at this

/-- What `recipPochRatSpecial` says. -/
theorem recipPochRatSpecial_spec {x : AzRat} {n : ℕ} (h : recipPochRatSpecial x n = true) :
    pochRatSpecial x = true ∧ 4 ≤ n := by
  unfold recipPochRatSpecial at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- **`1/((x − n)ₙ)` is not dyadic** at the rationals recognized by `recipPochRatSpecial`. -/
theorem not_isDyadic_recipPochRat {x : AzRat} {n : ℕ} (h : recipPochRatSpecial x n = true) :
    ¬ IsDyadic (∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j))⁻¹ := by
  obtain ⟨hs, hn⟩ := recipPochRatSpecial_spec h
  have hd : ¬ ∃ k : ℕ, (AzRat.toRat x - (n : ℚ)).den = 2 ^ k := by
    have : AzRat.toRat x - (n : ℚ) = AzRat.toRat x + ((-(n : ℤ) : ℤ) : ℚ) := by
      push_cast
      ring
    rw [this, Rat.add_intCast_den]
    exact pochRatSpecial_spec hs
  have := not_isDyadic_inv_prod_rat (AzRat.toRat x - (n : ℚ)) hd hn
  rwa [show ((AzRat.toRat x - (n : ℚ) : ℚ) : ℝ) = ((AzRat.toRat x : ℚ) : ℝ) - n by
    push_cast; rfl] at this

/-- **The Ziv certificate of `1/((x − n)ₙ)` at the rationals recognized by
`recipPochRatSpecial`**: some level `w₀ 2^f` is accepted. -/
theorem recipPochRatApprox_cert {x : AzRat} {n : ℕ} (hc : recipPochRatSpecial x n = true)
    (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (recipPochRatApprox (x - (n : AzRat)) n (w₀ * 2 ^ f)).1
      (recipPochRatApprox (x - (n : AzRat)) n (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hnd := not_isDyadic_recipPochRat hc
  have hne : ∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j) ≠ 0 := fun h0 => hnd (by
    rw [h0, inv_zero]
    exact isDyadic_zero)
  exact (gammaApproxOf_bracketConv (recipPochRat_coreConv x hne _)).exists_isSome
    (fun h0 => hnd (h0 ▸ isDyadic_zero)) p (not_mem_floatSet_of_not_isDyadic p hnd) mode w₀ hw₀

end Azurite.AzFloat
