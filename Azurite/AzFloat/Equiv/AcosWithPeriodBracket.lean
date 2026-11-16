/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosWithPeriodBracket
import Azurite.AzFloat.Equiv.AcosRatBracket
import Azurite.AzFloat.Equiv.AsinRatWithPeriodBracket
import Azurite.AzFloat.Equiv.Atan2WithPeriodBracket
import Azurite.Transcendental.Niven

/-!
# Equivalence: the bracket of `arccos (x) u / (2π)`

* **`irrational_arccos_rat_mul_div_two_pi`**: `arccos (q) U / (2π)` is irrational for a rational
  `q ∈ [−1, 1]` other than `0`, `±1/2`, `±1`, and `U ≠ 0` (Niven's theorem for the cosine).
* `atanPeriodScale_level8_spec` (the scaled enclosure at level `w + 8`), `acosAbsEncl_spec`,
  **`acosPeriodOf_spec`** (the generic combination, width at most `4U 2^(−w)`), and the float
  and rational instances `acosPeriodBracket_spec`, `acosRatPeriodBracket_spec`, with their
  `Roundable` forms and Ziv certificates.
-/

open Real

namespace Azurite.AzFloat

/-! ### Irrationality -/

/-- `arccos (q) U / (2π)` is irrational for a rational `q ∈ [−1, 1]` other than `0`, `±1/2`,
`±1`. -/
theorem irrational_arccos_rat_mul_div_two_pi {q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hqm : q ≠ -1) (hqh : q ≠ 1 / 2) (hqmh : q ≠ -1 / 2) (hle : |(q : ℝ)| ≤ 1) {U : ℕ}
    (hU : U ≠ 0) : Irrational (arccos q * U / (2 * π)) := by
  rintro ⟨v, hv⟩
  have hU0 : (0 : ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hU
  have hpi := pi_pos
  obtain ⟨hl1, hl2⟩ := abs_le.mp hle
  set r : ℚ := v / U with hrdef
  have hr : 2 * π * (r : ℝ) = arccos q := by
    rw [hrdef, Rat.cast_div, Rat.cast_natCast, hv]
    field_simp
  have hcos : cos (2 * π * (r : ℝ)) = q := by rw [hr, cos_arccos hl1 hl2]
  rcases cos_two_pi_mul_rat_mem_of_rat r hcos with h | h | h | h | h
  · exact hqm h
  · exact hqmh h
  · exact hq0 h
  · exact hqh h
  · exact hq1 h

/-- `arccos (x) U / (2π)` is irrational for a finite float `x` with `|x| < 1`,
`|x| ∉ {0, 1/2}`. -/
theorem irrational_acosPeriod_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) (hxh : |xv| ≠ 1 / 2) {U : ℕ} (hU : U ≠ 0) :
    Irrational (arccos xv * U / (2 * π)) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 hx1 hxh ⊢
  refine irrational_arccos_rat_mul_div_two_pi ?_ ?_ ?_ ?_ ?_ hx1.le hU
  · rintro rfl
    exact hx0 (by rw [Rat.cast_zero])
  · rintro rfl
    rw [Rat.cast_one, abs_one] at hx1
    exact lt_irrefl _ hx1
  · rintro rfl
    rw [Rat.cast_neg, Rat.cast_one, abs_neg, abs_one] at hx1
    exact lt_irrefl _ hx1
  · rintro rfl
    exact hxh (by push_cast; norm_num)
  · rintro rfl
    exact hxh (by push_cast; norm_num)

/-- `arccos (q) U / (2π)` is irrational for a rational `q` with `|q| < 1`, `|q| ∉ {0, 1/2}`. -/
theorem irrational_acosPeriod_toRat (q : AzRat) (h0 : q.num ≠ 0)
    (h1 : |(AzRat.toRat q : ℝ)| < 1) (hh : |(AzRat.toRat q : ℝ)| ≠ 1 / 2) {U : ℕ}
    (hU : U ≠ 0) : Irrational (arccos (AzRat.toRat q : ℝ) * U / (2 * π)) := by
  have hq0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  refine irrational_arccos_rat_mul_div_two_pi
    (fun h => hq0 (by rw [h, Rat.cast_zero])) ?_ ?_ ?_ ?_ h1.le hU
  · intro h
    rw [h, Rat.cast_one, abs_one] at h1
    exact lt_irrefl _ h1
  · intro h
    rw [h, Rat.cast_neg, Rat.cast_one, abs_neg, abs_one] at h1
    exact lt_irrefl _ h1
  · intro h
    exact hh (by rw [h]; push_cast; norm_num)
  · intro h
    exact hh (by rw [h]; push_cast; norm_num)

/-! ### The enclosures -/

/-- The scaled enclosure at level `w + 8`: for a nonnegative enclosure `A` of `0 ≤ θ ≤ 2` of
width `2^(−w−8)`, `atanPeriodScale A u (w + 72)` encloses `θ U / (2π)` with ends of absolute
value at most `2U` and width at most `U 2^(−w)/64`. -/
theorem atanPeriodScale_level8_spec {A : Encl} {θ : ℝ} {w : ℕ}
    (hA : IsEncl0W A θ ((1 / 2 : ℝ) ^ (w + 8))) (hθ : θ ≤ 2) (u : AzNat) :
    ∃ sl sh : ℝ, (atanPeriodScale A u (w + 72)).1.toVal = some (sl : EReal) ∧
      (atanPeriodScale A u (w + 72)).2.toVal = some (sh : EReal) ∧
      sl ≤ θ * u.toNat / (2 * π) ∧ θ * u.toNat / (2 * π) ≤ sh ∧
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
  have hθ0 : 0 ≤ θ := hA.nonneg
  rw [h8] at hA
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

/-- **The enclosure of `arccos |x|`** by `acosBracket false`: nonnegative lower end, width at
most `2^(−w)`, for any finite float with `0 < |x| < 1`. -/
theorem acosAbsEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) (w : ℕ) :
    IsEncl0W (acosBracket false x w) (arccos |xv|) ((1 / 2 : ℝ) ^ w) := by
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hT1 : √((1 - a) / (1 + a)) ≤ 1 := by
    apply sqrt_le_one.mpr
    rw [div_le_one (by linarith)]
    linarith
  have hid := arccos_eq_two_arctan ha0.le hx1.le
  unfold acosBracket
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hKw : w + 8 ≤ acosWork x.abs w := by
    unfold acosWork
    omega
  obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
    acosArg_spec habs ha0 hx1 (P := acosWork x.abs w + 64 + 8) (by omega)
  obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
    atanDouble_spec hT1 hKw htl hth htl0 htl1 hth1 htw
  rw [← hid] at h1 h2
  exact ⟨lo, hi, hlo, hhi, hlo0, h1, h2, by linarith⟩

/-- **The generic combination**: from enclosures of `arcsin a` and `arccos a` (`0 ≤ a ≤ 1`) at
the stated levels, `acosPeriodOf` encloses `arccos (± a) U / (2π)` with width at most
`4U 2^(−w)`, whatever `small` is. -/
theorem acosPeriodOf_spec (small xpos : Bool) {As8 Acw Ac8 : Unit → Encl} {a : ℝ} {w : ℕ}
    (ha0 : 0 ≤ a)
    (hs : small = true → IsEncl0W (As8 ()) (arcsin a) ((1 / 2 : ℝ) ^ (w + 8)))
    (hc : IsEncl0W (Acw ()) (arccos a) ((1 / 2 : ℝ) ^ w))
    (hc8 : IsEncl0W (Ac8 ()) (arccos a) ((1 / 2 : ℝ) ^ (w + 8))) (u : AzNat) :
    ∃ lo hi : ℝ, (acosPeriodOf small xpos As8 Acw Ac8 u w).1.toVal = some (lo : EReal) ∧
      (acosPeriodOf small xpos As8 Acw Ac8 u w).2.toVal = some (hi : EReal) ∧
      lo ≤ arccos (if xpos then a else -a) * u.toNat / (2 * π) ∧
      arccos (if xpos then a else -a) * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  have : NeZero (w + 72) := ⟨by omega⟩
  set U := (u.toNat : ℝ) with hU
  have hU0 : 0 ≤ U := by positivity
  have hpi := pi_pos
  have hpi4 := pi_lt_four
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
    have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
      rw [pow_add]
      norm_num
      ring
    rw [← h10]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
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
  have hasin : arcsin a ≤ 2 := by
    have := arcsin_le_pi_div_two a
    linarith
  have hacos : arccos a ≤ 2 := by
    have := arccos_le_pi_div_two.mpr ha0
    linarith
  have hcs : arccos a = π / 2 - arcsin a := arccos_eq_pi_div_two_sub_arcsin a
  unfold acosPeriodOf
  dsimp only
  cases small with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hslM, hshM, hsw⟩ :=
      atanPeriodScale_level8_spec (hs rfl) hasin u
    rw [← hU] at hs1 hs2 hslM hshM hsw
    cases xpos with
    | true =>
      simp only [Bool.not_true, ↓reduceIte]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec false hquart hsl hsh hs1 hs2 hcM4 hslM hshM (w + 72)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      have hval : arccos a * U / (2 * π) = U / 4 + -(arcsin a * U / (2 * π)) := by
        rw [hcs]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec true hquart hsl hsh hs1 hs2 hcM4 hslM hshM (w + 72)
      simp only [↓reduceIte] at hl hh
      have hval : arccos (-a) * U / (2 * π) = U / 4 + arcsin a * U / (2 * π) := by
        rw [arccos_neg, hcs]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases xpos with
    | true =>
      simp only [↓reduceIte]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := asinPeriodScale_spec hc hacos u
      rw [← hU] at hl hh hwd
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hslM, hshM, hsw⟩ :=
        atanPeriodScale_level8_spec hc8 hacos u
      rw [← hU] at hs1 hs2 hslM hshM hsw
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec false hhalf hsl hsh hs1 hs2 hcM2 hslM hshM (w + 72)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      have hval : arccos (-a) * U / (2 * π) = U / 2 + -(arccos a * U / (2 * π)) := by
        rw [arccos_neg]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩

/-- **The bracket of `arccos (x) u / (2π)`** for a finite float with `0 < |x| < 1`. -/
theorem acosPeriodBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt)
    {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) (u : AzNat) (w : ℕ) :
    ∃ lo hi : ℝ, (acosPeriodBracket xpos x ex u w).1.toVal = some (lo : EReal) ∧
      (acosPeriodBracket xpos x ex u w).2.toVal = some (hi : EReal) ∧
      lo ≤ arccos xv * u.toNat / (2 * π) ∧ arccos xv * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  have h := acosPeriodOf_spec (le x.abs (one <<< AzInt.ofInt (-1))) xpos
    (As8 := fun _ => asinAbsEncl x ex (w + 8)) (Acw := fun _ => acosBracket false x w)
    (Ac8 := fun _ => acosBracket false x (w + 8)) (abs_nonneg xv)
    (fun _ => asinAbsEncl_spec hx hx0 hx1 hex (w + 8)) (acosAbsEncl_spec hx hx0 hx1 w)
    (acosAbsEncl_spec hx hx0 hx1 (w + 8)) u
  rw [← eq_signed_of_abs_eq hxpos hx0 rfl] at h
  exact h

/-- `acosPeriodApprox o` as a pair of `Roundable`s bracketing `± arccos (x) u / (2π)`. -/
theorem acosPeriodApprox_spec (o : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) (hx1 : |xv| < 1) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) (u : AzNat)
    (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acosPeriodApprox o xpos x ex u w).1 lv ∧
      Rounds (acosPeriodApprox o xpos x ex u w).2 hv ∧
      lv ≤ (if o then -1 else 1) * (arccos xv * u.toNat / (2 * π)) ∧
      (if o then -1 else 1) * (arccos xv * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := acosPeriodBracket_spec hx hx0 hx1 hex hxpos u w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec o hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- The Ziv certificate for `± arccos (x) u / (2π)`: `0 < |x| < 1`, `|x| ≠ 1/2`, `u ≠ 0`. -/
theorem acosPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (o : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hx1 : |xv| < 1) (hxh : |xv| ≠ 1 / 2) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt)
    {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) {u : AzNat} (hu : u.toNat ≠ 0) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acosPeriodApprox o xpos x ex u (w₀ * 2 ^ f)).1
      (acosPeriodApprox o xpos x ex u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hirr := irrational_acosPeriod_of_toVal hx hx0 hx1 hxh hu
  refine exists_isSome_of_irrational_threshold p mode (acosPeriodApprox o xpos x ex u)
    (v := (if o then -1 else 1) * (arccos xv * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (4 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => acosPeriodApprox_spec o hx hx0 hx1 hex hxpos u w) w₀ hw₀
  · cases o with
    | false => simpa using hirr
    | true => simpa using hirr.neg
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 4).const_mul (u.toNat : ℝ)
    simpa using h

/-- **The bracket of `arccos (q) u / (2π)`** for a rational `0 < |q| < 1`. -/
theorem acosRatPeriodBracket_spec (q : AzRat) (h0 : q.num ≠ 0)
    (h1 : |(AzRat.toRat q : ℝ)| < 1) (u : AzNat) (w : ℕ) :
    ∃ lo hi : ℝ, (acosRatPeriodBracket q u w).1.toVal = some (lo : EReal) ∧
      (acosRatPeriodBracket q u w).2.toVal = some (hi : EReal) ∧
      lo ≤ arccos (AzRat.toRat q : ℝ) * u.toNat / (2 * π) ∧
      arccos (AzRat.toRat q : ℝ) * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  have hq0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  have h := acosPeriodOf_spec (ratAbsLeHalf q) q.sign
    (As8 := fun _ => asinRatAbsEncl q (w + 8)) (Acw := fun _ => acosRatBracket false q w)
    (Ac8 := fun _ => acosRatBracket false q (w + 8)) (abs_nonneg (AzRat.toRat q : ℝ))
    (fun _ => asinRatAbsEncl_spec q h0 h1 (w + 8)) (acosRatAbsEncl_spec q h0 h1 w)
    (acosRatAbsEncl_spec q h0 h1 (w + 8)) u
  rw [← eq_signed_of_abs_eq (toRat_sign_iff q h0) hq0 rfl] at h
  exact h

/-- `acosRatPeriodApprox o` as a pair of `Roundable`s bracketing `± arccos (q) u / (2π)`. -/
theorem acosRatPeriodApprox_spec (o : Bool) (q : AzRat) (h0 : q.num ≠ 0)
    (h1 : |(AzRat.toRat q : ℝ)| < 1) (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acosRatPeriodApprox o q u w).1 lv ∧
      Rounds (acosRatPeriodApprox o q u w).2 hv ∧
      lv ≤ (if o then -1 else 1) * (arccos (AzRat.toRat q : ℝ) * u.toNat / (2 * π)) ∧
      (if o then -1 else 1) * (arccos (AzRat.toRat q : ℝ) * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨lo, hi, hlo, hhi, hl, hh, hwid⟩ := acosRatPeriodBracket_spec q h0 h1 u w
  obtain ⟨lv, hv, hR1, hR2, hl', hh', he⟩ := enclApprox_spec o hlo hhi hl hh
  exact ⟨lv, hv, hR1, hR2, hl', hh', by rw [he]; exact hwid⟩

/-- The Ziv certificate for `± arccos (q) u / (2π)`: `0 < |q| < 1`, `|q| ≠ 1/2`, `u ≠ 0`. -/
theorem acosRatPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (o : Bool)
    (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (hh : |(AzRat.toRat q : ℝ)| ≠ 1 / 2) {u : AzNat} (hu : u.toNat ≠ 0) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acosRatPeriodApprox o q u (w₀ * 2 ^ f)).1
      (acosRatPeriodApprox o q u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hirr := irrational_acosPeriod_toRat q h0 h1 hh hu
  refine exists_isSome_of_irrational_threshold p mode (acosRatPeriodApprox o q u)
    (v := (if o then -1 else 1) * (arccos (AzRat.toRat q : ℝ) * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (4 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => acosRatPeriodApprox_spec o q h0 h1 u w) w₀ hw₀
  · cases o with
    | false => simpa using hirr
    | true => simpa using hirr.neg
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 4).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
