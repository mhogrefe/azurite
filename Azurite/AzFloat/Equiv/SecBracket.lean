/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SecBracket
import Azurite.AzFloat.Equiv.TanBracket

/-!
# Equivalence: the bracket of `sec x`

`irrational_sec_of_toVal`, `secEps`/`tendsto_secEps`, `secBracket_width`,
`secApprox_valid_or_none`, `secApprox_isSome_exists` (the Ziv certificate), `secTiny?_eq`.
-/

namespace Azurite.AzFloat

/-- `sec x = 1 / cos x` is irrational for a nonzero finite float `x`. -/
theorem irrational_sec_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (1 / Real.cos xv) := by
  rw [one_div]
  exact (irrational_cos_of_toVal hx hx0).inv

theorem isEnclW_one_cosBracket {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (Encl.exact one, cosBracket x ex w).1 1 0 ∧
      IsEnclW (Encl.exact one, cosBracket x ex w).2 (Real.cos xv) (cosEps ex w) :=
  ⟨(isEncl0W_exact toVal_one' zero_le_one).toW, cosBracket_spec hx hex hw⟩

/-- The width of `secBracket` once the bracket of `cos x` is at most half of `c = |cos x|`. -/
noncomputable def secEps (c : ℝ) (ex : AzInt) (w : ℕ) : ℝ :=
  (0 + 2 * cosEps ex w / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

/-- `secEps c ex w → 0` as `w → ∞`. -/
theorem tendsto_secEps (c : ℝ) (ex : AzInt) :
    Filter.Tendsto (secEps c ex) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := (((tendsto_cosEps ex).const_mul (2 / (c / 2))).add (h2.const_mul 8)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, secEps]
  ring

/-- **`secBracket` encloses `sec x`** with width at most `secEps |cos x| ex w`, as soon as
`cosEps ex w ≤ |cos x| / 2`. -/
theorem secBracket_width {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) (hc0 : 0 < |Real.cos xv|)
    (hc : cosEps ex w ≤ |Real.cos xv| / 2) :
    IsEnclW (secBracket x ex w) (1 / Real.cos xv) (secEps |Real.cos xv| ex w) := by
  obtain ⟨hS, hC⟩ := isEnclW_one_cosBracket hx hex hw
  exact tanOfSinCos_width hS hC (by norm_num) zero_le_one (by omega) hc0 hc

/-- At every level `w ≥ 64` the bracket of `secApprox` encloses `sec x` or is rejected by
`roundingPossible`. -/
theorem secApprox_valid_or_none {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (secApprox x ex w).1 lv ∧ Rounds (secApprox x ex w).2 hv ∧
        lv ≤ 1 / Real.cos xv ∧ 1 / Real.cos xv ≤ hv) ∨
      roundingPossible (secApprox x ex w).1 (secApprox x ex w).2 p mode = none := by
  obtain ⟨hS, hC⟩ := isEnclW_one_cosBracket hx hex hw
  have h := tanOfSinCos_valid_or_none false hS hC (by norm_num) zero_le_one
    (V := w + 12) (by omega) p mode
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  exact h

/-- The Ziv certificate for `sec x`, `x` a nonzero finite float. -/
theorem secApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (secApprox x ex (w₀ * 2 ^ f)).1 (secApprox x ex (w₀ * 2 ^ f)).2 p
      mode).isSome = true := by
  have hc0 : 0 < |Real.cos xv| := abs_pos.mpr (irrational_cos_of_toVal hx hx0).ne_zero
  obtain ⟨W₁, hW₁⟩ := ((tendsto_cosEps ex).eventually
    (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  refine exists_isSome_of_irrational_threshold p mode (secApprox x ex)
    (irrational_sec_of_toVal hx hx0) (secEps |Real.cos xv| ex) (tendsto_secEps _ ex) (max 64 W₁)
    (fun w hw => ?_) w₀ hw₀
  have h := negSwapApprox_of_isEnclW false (secBracket_width hx hex (le_of_max_le_left hw) hc0
    (hW₁ w (le_of_max_le_right hw)).le)
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  exact h

/-- `secTiny?` answers only for a tiny exponent. -/
theorem secTiny?_cond {e : AzInt} {p : ℕ} {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : secTiny? e p mode = some r) : e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat := by
  unfold secTiny? at h
  dsimp only at h
  by_contra hc
  rw [ite_eq_right hc] at h
  cases h

/-- The tiny-argument path answers with the rounding of `sec v`, for any `|v| < 2^e` with an
irrational secant. -/
theorem secTiny?_eq {e : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {v : ℝ} (hv : |v| < (2 : ℝ) ^ e.toInt)
    (hirr : Irrational (1 / Real.cos v)) (h : secTiny? e p mode = some r) :
    r = roundVal p mode (some ((1 / Real.cos v : ℝ) : EReal)) := by
  unfold secTiny? at h
  dsimp only at h
  by_cases hc : e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  have ht1 : t ≤ 1 := by
    rw [ht, htoInt, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hd : ((one <<< e) <<< e).toVal = some ((1 * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal toVal_one' e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs toVal_one' hd (p + zivGuardBits + 8)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := v)
  have hsq : v ^ 2 ≤ t * t := by
    rw [← sq_abs, sq]
    exact mul_le_mul hv.le hv.le (abs_nonneg v) ht0.le
  have htt : t * t ≤ 1 := by nlinarith
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hcpos : 0 < Real.cos v := by linarith
  have hlow : 1 ≤ 1 / Real.cos v := by
    rw [le_div_iff₀ hcpos, one_mul]
    exact Real.cos_le_one v
  have hup : 1 / Real.cos v ≤ 1 + t * t := by
    rw [div_le_iff₀ hcpos]
    have h1 : 1 ≤ (1 + v ^ 2) * (1 - v ^ 2 / 2) := by nlinarith
    calc (1 : ℝ) ≤ (1 + v ^ 2) * (1 - v ^ 2 / 2) := h1
      _ ≤ (1 + t * t) * Real.cos v :=
        mul_le_mul (by linarith) hcos (by linarith) (by linarith)
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe toVal_one')
  rw [fval_of_toVal_coe toVal_one'] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact roundingPossible_eq' p mode hR1 hR2 hlow (by linarith)
    (Or.inr (not_mem_floatSet_of_irrational p hirr)) h

end Azurite.AzFloat
