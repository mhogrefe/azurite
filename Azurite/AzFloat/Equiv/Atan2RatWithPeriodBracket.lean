/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2RatWithPeriodBracket
import Azurite.AzFloat.Equiv.Atan2RatBracket
import Azurite.AzFloat.Equiv.Atan2WithPeriodBracket

/-!
# Equivalence: the bracket of `atan2 (y, x) u / (2π)` for rationals

`atanPeriodScale_ratEncl_spec`, `atan2RatPeriodBracket_spec` (width at most `4U 2^(−w)`),
`irrational_atan2AbsPeriod_of_rat`, `atan2RatPeriodApprox_spec`,
`atan2RatPeriodApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-- The scaled enclosure of `arctan |t|` at level `w + 8`: an enclosure of
`arctan |t| U / (2π)` with ends of absolute value at most `2U` and width at most
`U 2^(−w)/64`. -/
theorem atanPeriodScale_ratEncl_spec (t : AzRat) (h0 : t.num ≠ 0) (u : AzNat) (w : ℕ) :
    ∃ sl sh : ℝ, (atanPeriodScale (atanRatAbsEncl t (w + 8)) u (w + 72)).1.toVal
        = some (sl : EReal) ∧
      (atanPeriodScale (atanRatAbsEncl t (w + 8)) u (w + 72)).2.toVal = some (sh : EReal) ∧
      sl ≤ arctan |(AzRat.toRat t : ℝ)| * u.toNat / (2 * π) ∧
      arctan |(AzRat.toRat t : ℝ)| * u.toNat / (2 * π) ≤ sh ∧
      |sl| ≤ 2 * u.toNat ∧ |sh| ≤ 2 * u.toNat ∧
      sh - sl ≤ u.toNat * ((1 / 2 : ℝ) ^ w / 64) := by
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 2 ^ 20 := by
    have h20 : (1 / 2 : ℝ) ^ (w + 20) = (1 / 2 : ℝ) ^ w / 2 ^ 20 := by
      rw [pow_add]
      norm_num
      ring
    rw [← h20]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h72' : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 72) := by positivity
  have hA := atanRatAbsEncl_spec t h0 (w + 8)
  rw [h8] at hA
  set θ := arctan |(AzRat.toRat t : ℝ)| with hθdef
  have hθ0 : 0 ≤ θ := arctan_nonneg.mpr (abs_nonneg _)
  have hθ : θ ≤ 2 := by
    have := arctan_lt_pi_div_two |(AzRat.toRat t : ℝ)|
    linarith [pi_lt_four]
  obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hsw⟩ :=
    atanPeriodScale_spec hA hθ (by linarith) u (V := w + 72) (by omega)
  set U := (u.toNat : ℝ) with hU
  have hU0 : 0 ≤ U := by positivity
  have hπ := pi_gt_three
  have hval0 : 0 ≤ θ * U / (2 * π) := by positivity
  have hval1 : θ * U / (2 * π) ≤ U := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hwb : U * (2 * ((1 / 2 : ℝ) ^ w / 256) + 108 * (1 / 2 : ℝ) ^ (w + 72))
      ≤ U * ((1 / 2 : ℝ) ^ w / 64) := by
    apply mul_le_mul_of_nonneg_left _ hU0
    linarith
  have hwb1 : U * ((1 / 2 : ℝ) ^ w / 64) ≤ U := by
    have := mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ^ w / 64 ≤ 1) hU0
    linarith
  refine ⟨sl, sh, hsl, hsh, hs1, hs2, ?_, ?_, by linarith⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- **The bracket of `atan2 (t, ±1) u / (2π)`** for a positive rational `t`: width at most
`4U 2^(−w)`. -/
theorem atan2RatPeriodBracket_spec (t : AzRat) (ht0 : 0 < (AzRat.toRat t : ℝ)) (xpos : Bool)
    (u : AzNat) (w : ℕ) :
    ∃ lo hi : ℝ, (atan2RatPeriodBracket t xpos u w).1.toVal = some (lo : EReal) ∧
      (atan2RatPeriodBracket t xpos u w).2.toVal = some (hi : EReal) ∧
      lo ≤ atan2Abs (AzRat.toRat t : ℝ) 1 xpos * u.toNat / (2 * π) ∧
      atan2Abs (AzRat.toRat t : ℝ) 1 xpos * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  set tv := ((AzRat.toRat t : ℚ) : ℝ) with htv
  have hnum : t.num ≠ 0 := fun h => ht0.ne' ((AzRat.toRat_eq_zero_iff t).mpr h)
  have habs : |tv| = tv := abs_of_pos ht0
  have : NeZero (w + 72) := ⟨by omega⟩
  set U := (u.toNat : ℝ) with hU
  have hU0 : 0 ≤ U := by positivity
  have hpi := pi_pos
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
    have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
      rw [pow_add]
      norm_num
      ring
    rw [← h10]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h72' : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 72) := by positivity
  have hUw : (0 : ℝ) ≤ U * (1 / 2 : ℝ) ^ w := mul_nonneg hU0 hw0
  have hU72 : U * (1 / 2 : ℝ) ^ (w + 72) ≤ U * ((1 / 2 : ℝ) ^ w / 1024) :=
    mul_le_mul_of_nonneg_left h72 hU0
  have hhalf : (ofAzNat u <<< AzInt.ofInt (-1)).toVal = some ((U / 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat u) (AzInt.ofInt (-1))
    rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
  have hquart : (ofAzNat u <<< AzInt.ofInt (-2)).toVal = some ((U / 4 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat u) (AzInt.ofInt (-2))
    rw [h, AzInt.toInt_ofInt, show ((2 : ℝ) ^ (-2 : ℤ)) = 1 / 4 by norm_num, mul_one_div]
  have hcM2 : |U / 2| ≤ U := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hcM4 : |U / 4| ≤ U := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  unfold atan2RatPeriodBracket
  dsimp only
  by_cases hc : t.num ≤ t.den
  · simp only [hc, ↓reduceIte]
    cases xpos with
    | true =>
      simp only [↓reduceIte, atan2Abs, div_one]
      have hA := atanRatAbsEncl_spec t hnum w
      rw [← htv, habs] at hA
      have hθ : arctan tv ≤ 2 := by
        have := arctan_lt_pi_div_two tv
        linarith [pi_lt_four]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        atanPeriodScale_spec hA hθ hw1 u (V := w + 72) (by omega)
      rw [← hU] at hl hh hwd
      refine ⟨lo, hi, hlo, hhi, hl, hh, hwd.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ hU0
      linarith
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, atan2Abs, div_one]
      obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hslM, hshM, hsw⟩ :=
        atanPeriodScale_ratEncl_spec t hnum u w
      rw [← htv, habs, ← hU] at hs1 hs2
      rw [← hU] at hslM hshM hsw
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec false hhalf hsl hsh hs1 hs2 hcM2 hslM hshM (w + 72)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      have hval : (π - arctan tv) * U / (2 * π) = U / 2 + -(arctan tv * U / (2 * π)) := by
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
  · simp only [hc]
    have hsv : ((AzRat.toRat t⁻¹ : ℚ) : ℝ) = tv⁻¹ := by
      rw [AzRat.toRat_inv, Rat.cast_inv]
    have hs0 : 0 < tv⁻¹ := inv_pos.mpr ht0
    have hsnum : t⁻¹.num ≠ 0 := fun h => by
      have := (AzRat.toRat_eq_zero_iff t⁻¹).mpr h
      rw [hsv] at this
      exact hs0.ne' this
    obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hslM, hshM, hsw⟩ :=
      atanPeriodScale_ratEncl_spec t⁻¹ hsnum u w
    rw [hsv, abs_of_pos hs0, ← hU] at hs1 hs2
    rw [← hU] at hslM hshM hsw
    have hinv : arctan tv = π / 2 - arctan tv⁻¹ := by
      rw [← arctan_inv_of_pos hs0, inv_inv]
    cases xpos with
    | true =>
      simp only [Bool.not_true, ↓reduceIte, atan2Abs, div_one]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec false hquart hsl hsh hs1 hs2 hcM4 hslM hshM (w + 72)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      have hval : arctan tv * U / (2 * π) = U / 4 + -(arctan tv⁻¹ * U / (2 * π)) := by
        rw [hinv]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, atan2Abs, div_one]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec true hquart hsl hsh hs1 hs2 hcM4 hslM hshM (w + 72)
      simp only [↓reduceIte] at hl hh
      have hval : (π - arctan tv) * U / (2 * π) = U / 4 + arctan tv⁻¹ * U / (2 * π) := by
        rw [hinv]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩

/-- `atan2 (|y|, x) U / (2π)` is irrational for nonzero rationals with `|y| ≠ |x|`. -/
theorem irrational_atan2AbsPeriod_of_rat {qy qx : ℚ} (hy0 : qy ≠ 0) (hx0 : qx ≠ 0)
    (hxy : |(qy : ℝ)| ≠ |(qx : ℝ)|) {xpos : Bool} (hxpos : xpos = true ↔ 0 < (qx : ℝ)) {U : ℕ}
    (hU : U ≠ 0) : Irrational (atan2Abs |(qy : ℝ)| |(qx : ℝ)| xpos * U / (2 * π)) := by
  have hy0' : (qy : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hx0' : (qx : ℝ) ≠ 0 := by exact_mod_cast hx0
  have hpos : 0 < |(qy : ℝ)| := abs_pos.mpr hy0'
  have h := arg_period_eq (x := (qx : ℝ)) (y := |(qy : ℝ)|) hx0' hpos.ne' (neg := false)
    (by simp [abs_nonneg]) hxpos (U : ℝ)
  rw [abs_abs] at h
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  rw [← h, ← Rat.cast_abs]
  refine irrational_arg_mul_div_two_pi hx0 (abs_ne_zero.mpr hy0) ?_ hU
  rw [Rat.cast_abs, abs_abs]
  exact hxy

/-- `atan2RatPeriodApprox neg` as a pair of `Roundable`s bracketing
`± atan2 (|y|, x) u / (2π)`. -/
theorem atan2RatPeriodApprox_spec (neg : Bool) (y x : AzRat) (hy : y.num ≠ 0) (hx : x.num ≠ 0)
    (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atan2RatPeriodApprox neg y x u w).1 lv ∧
      Rounds (atan2RatPeriodApprox neg y x u w).2 hv ∧
      lv ≤ (if neg then -1 else 1)
        * (atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign * u.toNat / (2 * π)) ∧
      (if neg then -1 else 1)
        * (atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign * u.toNat / (2 * π))
        ≤ hv ∧
      hv - lv ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  have hy0 := coe_toRat_ne_zero_of_num_ne_zero y hy
  have hx0 := coe_toRat_ne_zero_of_num_ne_zero x hx
  have ht := toRat_abs_div_abs y x
  have ht0 : 0 < ((AzRat.toRat (y.abs / x.abs) : ℚ) : ℝ) := by
    rw [ht]
    exact div_pos (abs_pos.mpr hy0) (abs_pos.mpr hx0)
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    atan2RatPeriodBracket_spec (y.abs / x.abs) ht0 x.sign u w
  have hval : atan2Abs ((AzRat.toRat (y.abs / x.abs) : ℚ) : ℝ) 1 x.sign
      = atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign := by
    unfold atan2Abs
    rw [ht, div_one]
  rw [hval] at h1 h2
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- The Ziv certificate for `± atan2 (|y|, x) u / (2π)`: nonzero rationals with `|y| ≠ |x|`,
`u ≠ 0`. -/
theorem atan2RatPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    (neg : Bool) (y x : AzRat) (hy : y.num ≠ 0) (hx : x.num ≠ 0)
    (hxy : (y.abs / x.abs).num ≠ (y.abs / x.abs).den) {u : AzNat} (hu : u.toNat ≠ 0) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atan2RatPeriodApprox neg y x u (w₀ * 2 ^ f)).1
      (atan2RatPeriodApprox neg y x u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hy0 : AzRat.toRat y ≠ 0 := fun h =>
    coe_toRat_ne_zero_of_num_ne_zero y hy (by rw [h, Rat.cast_zero])
  have hx0 : AzRat.toRat x ≠ 0 := fun h =>
    coe_toRat_ne_zero_of_num_ne_zero x hx (by rw [h, Rat.cast_zero])
  have hx0' := coe_toRat_ne_zero_of_num_ne_zero x hx
  have hne : |(AzRat.toRat y : ℝ)| ≠ |(AzRat.toRat x : ℝ)| := fun h => by
    apply hxy
    apply (abs_toRat_eq_one_iff (y.abs / x.abs)).mp
    rw [toRat_abs_div_abs, h, div_self (abs_ne_zero.mpr hx0'), abs_one]
  have hirr := irrational_atan2AbsPeriod_of_rat hy0 hx0 hne (toRat_sign_iff x hx) hu
  refine exists_isSome_of_irrational_threshold p mode (atan2RatPeriodApprox neg y x u)
    (v := (if neg then -1 else 1)
      * (atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (4 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => atan2RatPeriodApprox_spec neg y x hy hx u w) w₀ hw₀
  · cases neg with
    | false => simpa using hirr
    | true => simpa using hirr.neg
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 4).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
