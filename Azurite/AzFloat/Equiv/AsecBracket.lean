/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecBracket
import Azurite.AzFloat.Equiv.AcosBracket

/-!
# Equivalence: the bracket of `arcsec x`

`arccos_inv_eq_two_arctan` (`arccos (1/a) = 2 arctan √((a − 1)/(a + 1))` for `a ≥ 1`),
`asecAbsEncl_spec` (the enclosure of `arccos (1/|x|)`, nonnegative lower end),
`asecBracket_spec` (width at most `2^(−w)`), `asecApprox_spec`, `irrational_asec_of_toVal`,
`asecApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-- `arccos (1/a) = 2 arctan √((a − 1)/(a + 1))` for `a ≥ 1`. -/
theorem arccos_inv_eq_two_arctan {a : ℝ} (h1 : 1 ≤ a) :
    arccos a⁻¹ = 2 * arctan (√((a - 1) / (a + 1))) := by
  have ha0 : 0 < a := by linarith
  have hinv0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hinv1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  rw [arccos_eq_two_arctan hinv0 hinv1]
  congr 3
  field_simp

/-- **The enclosure of `arccos (1/|x|)`** by `asecBracket false`: nonnegative lower end, width
at most `2^(−w)`, for any finite float with `|x| > 1`. -/
theorem asecAbsEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) (w : ℕ) :
    IsEncl0W (asecBracket false x w) (arccos |xv|⁻¹) ((1 / 2 : ℝ) ^ w) := by
  set a := |xv| with ha
  have ha0 : 0 < a := by linarith
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hT1 : √((a - 1) / (a + 1)) ≤ 1 := by
    apply sqrt_le_one.mpr
    rw [div_le_one (by linarith)]
    linarith
  have hid := arccos_inv_eq_two_arctan hx1.le
  unfold asecBracket
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hKw : w + 8 ≤ asecWork x.abs w := by
    unfold asecWork
    omega
  obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
    diffQuotSqrt_spec habs toVal_one' one_pos hx1 (P := asecWork x.abs w + 64 + 8) (by omega)
  obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
    atanDouble_spec hT1 hKw htl hth htl0 htl1 hth1 htw
  rw [← hid] at h1 h2
  exact ⟨lo, hi, hlo, hhi, hlo0, h1, h2, by linarith⟩

/-- **The bracket of `arcsec x`** for `|x| > 1`: width at most `2^(−w)`. -/
theorem asecBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) {neg : Bool} (hneg : neg = true ↔ xv < 0) (w : ℕ) :
    ∃ lo hi : ℝ, (asecBracket neg x w).1.toVal = some (lo : EReal) ∧
      (asecBracket neg x w).2.toVal = some (hi : EReal) ∧ lo ≤ arccos xv⁻¹ ∧
      arccos xv⁻¹ ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set a := |xv| with ha
  have ha0 : 0 < a := by linarith
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  cases neg with
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    have hxa : xv = a := by rw [ha, abs_of_nonneg hpos]
    obtain ⟨lo, hi, hlo, hhi, -, h1, h2, h3⟩ := asecAbsEncl_spec hx hx1 w
    rw [hxa]
    exact ⟨lo, hi, hlo, hhi, h1, h2, h3⟩
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    have hxa : xv = -a := by rw [ha, abs_of_neg hlt, neg_neg]
    have hT1 : √((a - 1) / (a + 1)) ≤ 1 := by
      apply sqrt_le_one.mpr
      rw [div_le_one (by linarith)]
      linarith
    have hid := arccos_inv_eq_two_arctan hx1.le
    unfold asecBracket
    simp only [↓reduceIte]
    obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
      diffQuotSqrt_spec habs toVal_one' one_pos hx1 (P := w + 8 + 64 + 8) (by omega)
    obtain ⟨al, ah, hal, hah, hal0, h1, h2, hah4, h3⟩ :=
      atanDouble_spec hT1 (le_refl (w + 8)) htl hth htl0 htl1 hth1 htw
    rw [← hid] at h1 h2
    obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec false false
      (A := ((atanWiden (diffQuotSqrt x.abs one (w + 8 + 64 + 8)).1
        (diffQuotSqrt x.abs one (w + 8 + 64 + 8)).2 (w + 8) (w + 8 + 64)).1 <<< AzInt.ofInt 1,
        (atanWiden (diffQuotSqrt x.abs one (w + 8 + 64 + 8)).1
        (diffQuotSqrt x.abs one (w + 8 + 64 + 8)).2 (w + 8) (w + 8 + 64)).2 <<< AzInt.ofInt 1))
      hal hah hal0 h1 h2 hah4 h3 (V := w + 72) (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
    have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
        rw [pow_add]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [hxa, inv_neg, arccos_neg]
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩

/-- `asecApprox neg` as a pair of `Roundable`s bracketing `arcsec x`. -/
theorem asecApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) {neg : Bool} (hneg : neg = true ↔ xv < 0) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (asecApprox neg x w).1 lv ∧ Rounds (asecApprox neg x w).2 hv ∧
      lv ≤ arccos xv⁻¹ ∧ arccos xv⁻¹ ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := asecBracket_spec hx hx1 hneg w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arcsec x` is irrational for a finite float `x` with `|x| > 1`. -/
theorem irrational_asec_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) : Irrational (arccos xv⁻¹) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hinv : |xv⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hx1
  obtain ⟨h1, h2⟩ := abs_lt.mp hinv
  rw [hq, ← Rat.cast_inv] at h1 h2 ⊢
  exact irrational_arccos_rat h1.le h2

/-- The Ziv certificate for `arcsec x`, `x` a finite float with `|x| > 1`. -/
theorem asecApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|)
    (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asecApprox neg x (w₀ * 2 ^ f)).1
      (asecApprox neg x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (asecApprox neg x)
    (irrational_asec_of_toVal hx hx1) (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => asecApprox_spec hx hx1 hneg w) w₀ hw₀

/-- A float of positive exponent that is not `±1` has absolute value above `1`. -/
theorem one_lt_abs_of_exponent {xv : ℝ} {e : AzInt} (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|)
    (he : e.sign = true ∧ e.abs.toNat ≠ 0) (hne : |xv| ≠ 1) : 1 < |xv| := by
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  have h1e : 1 ≤ e.toInt := by
    rw [htoInt, he.1]
    simp only [↓reduceIte]
    have := he.2
    omega
  have hge : 1 ≤ |xv| := le_trans (one_le_zpow₀ (by norm_num) (by omega)) hex1
  exact lt_of_le_of_ne hge (Ne.symm hne)

end Azurite.AzFloat
