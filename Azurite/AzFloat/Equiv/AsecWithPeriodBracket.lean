/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecWithPeriodBracket
import Azurite.AzFloat.Equiv.AsecBracket
import Azurite.AzFloat.Equiv.AcosWithPeriodBracket

/-!
# Equivalence: the bracket of `arcsec (x) u / (2π)`

`asecComplement_spec` (the enclosure of `arcsin (1/|x|)`), `asecPeriodBracket_spec` (width at
most `4U 2^(−w)`), `irrational_asecPeriod_of_toVal`, `asecPeriodApprox_spec`,
`asecPeriodApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-- **The enclosure of `arcsin (1/|x|)`** for `|x| > 1`: nonnegative lower end, width at most
`2^(−w−8)`. -/
theorem asecComplement_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) (w : ℕ) :
    IsEncl0W (asecComplement x w) (arcsin |xv|⁻¹) ((1 / 2 : ℝ) ^ (w + 8)) := by
  unfold asecComplement
  have hinv0 : 0 ≤ |xv|⁻¹ := inv_nonneg.mpr (abs_nonneg xv)
  obtain ⟨al, ah, hal, hah, hal0, h1, h2, h3⟩ := asecAbsEncl_spec hx hx1 (w + 9)
  have hacos := arccos_le_pi_div_two.mpr hinv0
  have hπ := pi_lt_four
  have hw9 : (1 / 2 : ℝ) ^ (w + 9) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec true false hal hah hal0 h1 h2
    (by linarith) h3 (V := w + 72) (by omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
  have hcs : arcsin |xv|⁻¹ = π / 2 - arccos |xv|⁻¹ := by
    rw [arccos_eq_pi_div_two_sub_arcsin]
    ring
  have hwid : (1 / 2 : ℝ) ^ (w + 9) + 44 * (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ (w + 8) := by
    have e9 : (1 / 2 : ℝ) ^ (w + 9) = (1 / 2 : ℝ) ^ (w + 8) / 2 := by
      rw [pow_succ]
      ring
    have e72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ (w + 8) / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 8 + 10) = (1 / 2 : ℝ) ^ (w + 8) / 1024 := by
        rw [pow_add (1 / 2 : ℝ) (w + 8) 10]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 8) := by positivity
    linarith
  refine enclClamp0_spec ⟨lo, hi, hlo, hhi, ?_, ?_, hwd.trans hwid⟩ (arcsin_nonneg.mpr hinv0)
  · rw [hcs]
    linarith
  · rw [hcs]
    linarith

/-- **The bracket of `arcsec (x) u / (2π)`** for a finite float with `|x| > 1`. -/
theorem asecPeriodBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) (u : AzNat) (w : ℕ) :
    ∃ lo hi : ℝ, (asecPeriodBracket xpos x u w).1.toVal = some (lo : EReal) ∧
      (asecPeriodBracket xpos x u w).2.toVal = some (hi : EReal) ∧
      lo ≤ arccos xv⁻¹ * u.toNat / (2 * π) ∧ arccos xv⁻¹ * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  have hx0 : xv ≠ 0 := fun h => by
    rw [h, abs_zero] at hx1
    linarith
  have h := acosPeriodOf_spec (le (one <<< AzInt.ofInt 1) x.abs) xpos
    (As8 := fun _ => asecComplement x w) (Acw := fun _ => asecBracket false x w)
    (Ac8 := fun _ => asecBracket false x (w + 8)) (inv_nonneg.mpr (abs_nonneg xv))
    (fun _ => asecComplement_spec hx hx1 w) (asecAbsEncl_spec hx hx1 w)
    (asecAbsEncl_spec hx hx1 (w + 8)) u
  have hsgn : xv⁻¹ = if xpos then |xv|⁻¹ else -|xv|⁻¹ := by
    have := eq_signed_of_abs_eq hxpos hx0 (rfl : |xv| = |xv|)
    cases xpos with
    | true =>
      simp only [↓reduceIte] at this ⊢
      rw [← this]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
      rw [← inv_neg, ← this]
  rw [← hsgn] at h
  exact h

/-- `arcsec (x) U / (2π)` is irrational for a finite float `x` with `|x| > 1`, `|x| ≠ 2`. -/
theorem irrational_asecPeriod_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) (hx2 : |xv| ≠ 2) {U : ℕ} (hU : U ≠ 0) :
    Irrational (arccos xv⁻¹ * U / (2 * π)) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hx0 : xv ≠ 0 := fun h => by
    rw [h, abs_zero] at hx1
    linarith
  have hinv : |xv⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hx1
  have hcast : xv⁻¹ = ((q⁻¹ : ℚ) : ℝ) := by rw [hq, Rat.cast_inv]
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  have hne : ∀ c : ℚ, |(c : ℝ)| = 1 ∨ |(c : ℝ)| = 1 / 2 → q⁻¹ ≠ c := by
    intro c hc h
    have h' : |xv⁻¹| = |(c : ℝ)| := by rw [hcast, h]
    rcases hc with hc | hc
    · rw [hc] at h'
      linarith
    · rw [hc, abs_inv] at h'
      apply hx2
      have hpos : 0 < |xv| := by linarith
      field_simp at h'
      linarith
  rw [hcast]
  refine irrational_arccos_rat_mul_div_two_pi (inv_ne_zero hq0) (hne 1 ?_) (hne (-1) ?_)
    (hne (1 / 2) ?_) (hne (-1 / 2) ?_) ?_ hU
  · left; norm_num
  · left; norm_num
  · right; norm_num
  · right
    push_cast
    rw [abs_div, abs_neg, abs_one, abs_two]
  · rw [← hcast]
    exact hinv.le

/-- `asecPeriodApprox o` as a pair of `Roundable`s bracketing `± arcsec (x) u / (2π)`. -/
theorem asecPeriodApprox_spec (o : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|) {xpos : Bool}
    (hxpos : xpos = true ↔ 0 < xv) (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (asecPeriodApprox o xpos x u w).1 lv ∧
      Rounds (asecPeriodApprox o xpos x u w).2 hv ∧
      lv ≤ (if o then -1 else 1) * (arccos xv⁻¹ * u.toNat / (2 * π)) ∧
      (if o then -1 else 1) * (arccos xv⁻¹ * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := asecPeriodBracket_spec hx hx1 hxpos u w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec o hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- The Ziv certificate for `± arcsec (x) u / (2π)`: `|x| > 1`, `|x| ≠ 2`, `u ≠ 0`. -/
theorem asecPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (o : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|)
    (hx2 : |xv| ≠ 2) {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) {u : AzNat}
    (hu : u.toNat ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asecPeriodApprox o xpos x u (w₀ * 2 ^ f)).1
      (asecPeriodApprox o xpos x u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hirr := irrational_asecPeriod_of_toVal hx hx1 hx2 hu
  refine exists_isSome_of_irrational_threshold p mode (asecPeriodApprox o xpos x u)
    (v := (if o then -1 else 1) * (arccos xv⁻¹ * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (4 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => asecPeriodApprox_spec o hx hx1 hxpos u w) w₀ hw₀
  · cases o with
    | false => simpa using hirr
    | true => simpa using hirr.neg
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 4).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
