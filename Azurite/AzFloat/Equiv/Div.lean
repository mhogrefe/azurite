/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Div
import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzInt.Equiv.DivRound
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.IsMultipleOfPow2

/-!
# Correctness of division

`Spec.div` is `EReal` division with `0 / 0` and `∞ / ∞` undefined and `x / 0 = ±∞` by the sign of
`x`; `divPrecRound_eq_liftVal₂` says `divPrecRound` is the lifted specification.  The core is
`divCores_eq_gen`, the rounded quotient of two arbitrary nonzero integers at any scale, which also
gives `ofFractionRound_eq` for unreduced fractions.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real division: `∞ / ∞` and `0 / 0` are undefined (`NaN`); `a / 0 = ±∞` with the sign
of `a` (not Mathlib's `a / 0 = 0`); otherwise `EReal` division, whose `a / ∞ = 0` and
`∞ / a = ±∞` are the float conventions. -/
noncomputable def div (a b : EReal) : Option EReal :=
  if ((a = ⊤ ∨ a = ⊥) ∧ (b = ⊤ ∨ b = ⊥)) ∨ (a = 0 ∧ b = 0) then none
  else if b = 0 then some (if 0 < a then ⊤ else ⊥)
  else some (a / b)

theorem div_coe_coe (x y : ℝ) (hy : y ≠ 0) :
    div (x : EReal) (y : EReal) = some ((x / y : ℝ) : EReal) := by
  unfold div
  rw [ite_eq_right (by simp [hy]), ite_eq_right (by simpa using hy), EReal.coe_div]

theorem div_coe_zero (x : ℝ) (hx : x ≠ 0) :
    div (x : EReal) 0 = some (if 0 < x then ⊤ else ⊥) := by
  unfold div
  rw [ite_eq_right (by simp [hx]), ite_eq_left rfl]
  simp [EReal.coe_pos]

theorem div_inf_coe (s : Bool) (r : ℝ) (hr : r ≠ 0) :
    div (if s then ⊤ else ⊥) (r : EReal) = some (if (s == decide (0 < r)) then ⊤ else ⊥) := by
  unfold div
  rw [ite_eq_right (by cases s <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero, hr]),
    ite_eq_right (by simpa using hr)]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [decide_eq_false (not_lt.mpr h.le)]
    have h' : (r : EReal) < 0 := EReal.coe_neg'.mpr h
    cases s
    · simp [EReal.bot_div_of_neg_ne_bot h' (EReal.coe_ne_bot r)]
    · simp [EReal.top_div_of_neg_ne_bot h' (EReal.coe_ne_bot r)]
  · rw [decide_eq_true h]
    have h' : (0 : EReal) < r := EReal.coe_pos.mpr h
    cases s
    · simp [EReal.bot_div_of_pos_ne_top h' (EReal.coe_ne_top r)]
    · simp [EReal.top_div_of_pos_ne_top h' (EReal.coe_ne_top r)]

theorem div_inf_zero (s : Bool) : div (if s then ⊤ else ⊥) 0 = some (if s then ⊤ else ⊥) := by
  unfold div
  rw [ite_eq_right (by cases s <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero]), ite_eq_left rfl]
  cases s <;> simp [EReal.zero_lt_top]

theorem div_coe_inf (r : ℝ) (t : Bool) : div (r : EReal) (if t then ⊤ else ⊥) = some 0 := by
  unfold div
  rw [ite_eq_right (by cases t <;> simp),
    ite_eq_right (by cases t <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero])]
  cases t <;> simp [EReal.div_top, EReal.div_bot]

theorem div_zero_coe (r : ℝ) (hr : r ≠ 0) : div 0 (r : EReal) = some 0 := by
  unfold div
  rw [ite_eq_right (by simp [EReal.zero_ne_top, EReal.zero_ne_bot, hr]),
    ite_eq_right (by simpa using hr), EReal.zero_div]

theorem div_zero_inf (t : Bool) : div 0 (if t then ⊤ else ⊥) = some 0 := by
  unfold div
  rw [ite_eq_right (by cases t <;> simp [EReal.zero_ne_top, EReal.zero_ne_bot]),
    ite_eq_right (by cases t <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero])]
  cases t <;> simp [EReal.div_top, EReal.div_bot]

end Spec

theorem signed_div (s t : Bool) (a b : ℝ) :
    ((if s then 1 else -1) * a) / ((if t then 1 else -1) * b)
      = (if (s == t) then 1 else -1) * (a / b) := by
  cases s <;> cases t <;> simp [neg_div, div_neg]

/-- The `p`-bit quotient scaling: with `g = p + p₂ − p₁ − [N₂ / 2^p₂ ≤ N₁ / 2^p₁]`,
`N₁ · 2^g / N₂ ∈ [2^(p−1), 2^p)`. -/
theorem quotient_scale_bounds (N₁ N₂ : ℝ) (p₁ p₂ p : ℕ)
    (h₁ : (2 : ℝ) ^ ((p₁ : ℤ) - 1) ≤ N₁ ∧ N₁ < (2 : ℝ) ^ (p₁ : ℤ))
    (h₂ : (2 : ℝ) ^ ((p₂ : ℤ) - 1) ≤ N₂ ∧ N₂ < (2 : ℝ) ^ (p₂ : ℤ)) (hge : Bool)
    (hcase : hge = true ↔ N₂ / (2 : ℝ) ^ (p₂ : ℤ) ≤ N₁ / (2 : ℝ) ^ (p₁ : ℤ)) :
    (2 : ℝ) ^ ((p : ℤ) - 1) ≤ N₁ * (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁ - (if hge then 1 else 0)) / N₂ ∧
      N₁ * (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁ - (if hge then 1 else 0)) / N₂ < (2 : ℝ) ^ (p : ℤ) := by
  set a : ℝ := (2 : ℝ) ^ (p₁ : ℤ) with ha_def
  set b : ℝ := (2 : ℝ) ^ (p₂ : ℤ) with hb_def
  set P : ℝ := (2 : ℝ) ^ ((p : ℤ) - 1) with hP_def
  have ha : (0 : ℝ) < a := zpow_pos (by norm_num) _
  have hb : (0 : ℝ) < b := zpow_pos (by norm_num) _
  have hP : (0 : ℝ) < P := zpow_pos (by norm_num) _
  have hP2 : (2 : ℝ) ^ (p : ℤ) = P * 2 := by
    rw [hP_def, ← zpow_add_one₀ (two_ne_zero)]; congr 1; ring
  have ha2 : a = (2 : ℝ) ^ ((p₁ : ℤ) - 1) * 2 := by
    rw [ha_def, ← zpow_add_one₀ (two_ne_zero)]; congr 1; ring
  have hb2 : b = (2 : ℝ) ^ ((p₂ : ℤ) - 1) * 2 := by
    rw [hb_def, ← zpow_add_one₀ (two_ne_zero)]; congr 1; ring
  have hN₁ : 0 < N₁ := lt_of_lt_of_le (zpow_pos (by norm_num) _) h₁.1
  have hN₂ : 0 < N₂ := lt_of_lt_of_le (zpow_pos (by norm_num) _) h₂.1
  rw [div_le_div_iff₀ hb ha] at hcase
  cases hge with
  | true =>
    have hle : N₂ * a ≤ N₁ * b := hcase.mp rfl
    simp only [↓reduceIte]
    have hg : (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁ - 1) = P * b / a := by
      rw [hP_def, ha_def, hb_def, ← zpow_add₀ (by norm_num), ← zpow_sub₀ (by norm_num)]
      congr 1; ring
    rw [hg]
    constructor
    · rw [le_div_iff₀ hN₂, show N₁ * (P * b / a) = P * (N₁ * b / a) by ring]
      exact mul_le_mul_of_nonneg_left ((le_div_iff₀ ha).mpr hle) hP.le
    · rw [div_lt_iff₀ hN₂, hP2, show N₁ * (P * b / a) = P * (N₁ * b / a) by ring,
        show P * 2 * N₂ = P * (2 * N₂) by ring]
      apply mul_lt_mul_of_pos_left _ hP
      rw [div_lt_iff₀ ha]
      have h1 : N₁ * b < a * b := mul_lt_mul_of_pos_right h₁.2 hb
      have h2 : a * (2 : ℝ) ^ ((p₂ : ℤ) - 1) ≤ a * N₂ := mul_le_mul_of_nonneg_left h₂.1 ha.le
      have h3 : a * b = 2 * (a * (2 : ℝ) ^ ((p₂ : ℤ) - 1)) := by rw [hb2]; ring
      linarith
  | false =>
    have hlt : N₁ * b < N₂ * a := by
      have h := fun h' => hcase.mpr h'
      by_contra hcon
      push Not at hcon
      exact absurd (h hcon) (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
    have hg : (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁) = (2 : ℝ) ^ (p : ℤ) * b / a := by
      rw [ha_def, hb_def, ← zpow_add₀ (by norm_num), ← zpow_sub₀ (by norm_num)]
    rw [hg]
    constructor
    · rw [le_div_iff₀ hN₂, hP2, show N₁ * (P * 2 * b / a) = P * (2 * N₁ * b / a) by ring]
      apply mul_le_mul_of_nonneg_left _ hP.le
      rw [le_div_iff₀ ha]
      have h1 : N₂ * a ≤ b * a := mul_le_mul_of_nonneg_right h₂.2.le ha.le
      have h2 : b * (2 : ℝ) ^ ((p₁ : ℤ) - 1) ≤ b * N₁ := mul_le_mul_of_nonneg_left h₁.1 hb.le
      have h3 : b * a = 2 * (b * (2 : ℝ) ^ ((p₁ : ℤ) - 1)) := by rw [ha2]; ring
      linarith
    · rw [div_lt_iff₀ hN₂, show N₁ * ((2 : ℝ) ^ (p : ℤ) * b / a) = (2 : ℝ) ^ (p : ℤ) * (N₁ * b / a)
        by ring]
      apply mul_lt_mul_of_pos_left _ (zpow_pos (by norm_num) _)
      rw [div_lt_iff₀ ha]; exact hlt

/-- `divCores` on any two nonzero integers of the stated sizes, given the comparison flag,
rounds the exact quotient. -/
theorem divCores_eq_gen (s : Bool) (e₁ : AzInt) (n₁ : AzNat) (p₁ : ℕ) (hn₁0 : n₁ ≠ 0)
    (hs₁ : n₁.size = p₁) (e₂ : AzInt) (n₂ : AzNat) (p₂ : ℕ) (hn₂0 : n₂ ≠ 0) (hs₂ : n₂.size = p₂)
    (hge : Bool)
    (hcase : hge = true ↔
      (n₂.toNat : ℝ) / (2 : ℝ) ^ (p₂ : ℤ) ≤ (n₁.toNat : ℝ) / (2 : ℝ) ^ (p₁ : ℤ))
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    divCores s e₁ n₁ p₁ e₂ n₂ p₂ hge p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true e₁ n₁ / finiteVal true e₂ n₂) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hb₁ : (2 : ℝ) ^ ((p₁ : ℤ) - 1) ≤ (n₁.toNat : ℝ) ∧ (n₁.toNat : ℝ) < (2 : ℝ) ^ (p₁ : ℤ) := by
    obtain ⟨hlo, hhi⟩ := toNat_bounds_of_ne_zero n₁ hn₁0
    rw [hs₁] at hlo hhi
    have hp₁ : 0 < p₁ := hs₁ ▸ size_pos_of_ne_zero hn₁0
    constructor
    · rw [show (p₁ : ℤ) - 1 = ((p₁ - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hlo
    · rw [zpow_natCast]; exact_mod_cast hhi
  have hb₂ : (2 : ℝ) ^ ((p₂ : ℤ) - 1) ≤ (n₂.toNat : ℝ) ∧ (n₂.toNat : ℝ) < (2 : ℝ) ^ (p₂ : ℤ) := by
    obtain ⟨hlo, hhi⟩ := toNat_bounds_of_ne_zero n₂ hn₂0
    rw [hs₂] at hlo hhi
    have hp₂ : 0 < p₂ := hs₂ ▸ size_pos_of_ne_zero hn₂0
    constructor
    · rw [show (p₂ : ℤ) - 1 = ((p₂ - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hlo
    · rw [zpow_natCast]; exact_mod_cast hhi
  set N₁ : ℝ := (n₁.toNat : ℝ) with hN₁
  set N₂ : ℝ := (n₂.toNat : ℝ) with hN₂
  clear_value N₁ N₂
  have hN₁pos : 0 < N₁ := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb₁.1
  have hN₂pos : 0 < N₂ := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb₂.1
  -- unfold
  unfold divCores
  simp only []
  set g := (AzNat.ofNat (p + p₂)).toAzInt -
    (AzNat.ofNat (p₁ + (if hge then 1 else 0))).toAzInt with hg_def
  have hgI : g.toInt = (p : ℤ) + p₂ - p₁ - (if hge then 1 else 0) := by
    rw [hg_def, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
    cases hge <;> simp only [↓reduceIte, Bool.false_eq_true] <;> push_cast <;> ring
  clear_value g
  set A := if g.sign then n₁.shiftLeft g.abs.toNat else n₁ with hA_def
  set B := if g.sign then n₂ else n₂.shiftLeft g.abs.toNat with hB_def
  clear_value A B
  have hshift0 : ∀ (n : AzNat) (k : ℕ), n ≠ 0 → n.shiftLeft k ≠ 0 := by
    intro n k hn h
    have := congrArg AzNat.toNat h
    rw [AzNat.toNat_shiftLeft, AzNat.toNat_zero] at this
    exact Nat.mul_ne_zero (toNat_ne_zero_of_ne_zero hn) (pow_ne_zero _ two_ne_zero) this
  have hA0 : A ≠ 0 := by
    rw [hA_def]; split_ifs
    · exact hshift0 _ _ hn₁0
    · exact hn₁0
  have hB0 : 0 < B.toAzInt.abs.toNat := by
    show 0 < B.toNat
    apply Nat.pos_of_ne_zero
    apply toNat_ne_zero_of_ne_zero
    rw [hB_def]; split_ifs
    · exact hn₂0
    · exact hshift0 _ _ hn₂0
  have habsg : (g.abs.toNat : ℤ) = |g.toInt| := AzInt.abs_toNat_eq g
  have hAB : (A.toNat : ℝ) / (B.toNat : ℝ) = N₁ * (2 : ℝ) ^ g.toInt / N₂ := by
    by_cases hsg : g.sign = true
    · have hg0 : 0 ≤ g.toInt := (AzInt.sign_eq_true_iff g).mp hsg
      rw [hA_def, hB_def, ite_eq_left hsg, ite_eq_left hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((g.abs.toNat : ℕ) : ℤ) = g.toInt by rw [habsg, abs_of_nonneg hg0],
        ← hN₁, ← hN₂]
    · have hg0 : g.toInt < 0 := by
        have := (AzInt.sign_eq_true_iff g).not.mp hsg; push Not at this; exact this
      rw [hA_def, hB_def, ite_eq_right hsg, ite_eq_right hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((g.abs.toNat : ℕ) : ℤ) = -g.toInt by rw [habsg, abs_of_neg hg0],
        zpow_neg, ← hN₁, ← hN₂, div_eq_mul_inv, mul_inv, inv_inv, div_eq_mul_inv]
      ring
  -- the exact value
  set σ : ℝ := if s then 1 else -1 with hσ
  have hσ0 : σ ≠ 0 := by rw [hσ]; cases s <;> norm_num
  have hσabs : |σ| = 1 := by rw [hσ]; cases s <;> simp
  clear_value σ
  set w := e₁ - (AzNat.ofNat p₁).toAzInt - (e₂ - (AzNat.ofNat p₂).toAzInt) - g with hw_def
  have hwI : w.toInt = (e₁.toInt - p₁) - (e₂.toInt - p₂) - g.toInt := by
    rw [hw_def, AzInt.toInt_sub, AzInt.toInt_sub, AzInt.toInt_sub, AzInt.toInt_sub, toInt_toAzInt,
      toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  clear_value w
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := σ * (finiteVal true e₁ n₁ / finiteVal true e₂ n₂) with hv_def
  clear_value v
  have hv : v = σ * ((A.toNat : ℝ) / (B.toNat : ℝ)) * (2 : ℝ) ^ w.toInt := by
    rw [hv_def, hAB, finiteVal_true_eq, finiteVal_true_eq, hs₁, hs₂, ← hN₁, ← hN₂, hwI]
    have hsplit : (2 : ℝ) ^ (e₁.toInt - p₁)
        = 2 ^ ((e₁.toInt - p₁) - (e₂.toInt - p₂) - g.toInt) * 2 ^ g.toInt *
          2 ^ (e₂.toInt - p₂) := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]; congr 1; ring
    rw [hsplit]
    have h2 : (2 : ℝ) ^ (e₂.toInt - p₂) ≠ 0 := zpow_ne_zero _ (by norm_num)
    field_simp
  have hv0 : v ≠ 0 := by
    rw [hv_def]
    exact mul_ne_zero hσ0 (div_ne_zero (finiteVal_ne_zero' true e₁ n₁ hn₁0)
      (finiteVal_ne_zero' true e₂ n₂ hn₂0))
  -- the quotient lies in `[2^(p−1), 2^p)`
  obtain ⟨hqlo, hqhi⟩ := quotient_scale_bounds N₁ N₂ p₁ p₂ p hb₁ hb₂ hge hcase
  rw [← hgI, ← hAB] at hqlo hqhi
  have hABpos : 0 < (A.toNat : ℝ) / (B.toNat : ℝ) := lt_of_lt_of_le (zpow_pos (by norm_num) _) hqlo
  have habsv : |v| = (A.toNat : ℝ) / (B.toNat : ℝ) * (2 : ℝ) ^ w.toInt := by
    rw [hv, abs_mul, abs_mul, hσabs, one_mul, abs_of_pos hABpos, abs_of_pos h2w]
  have hvpos : 0 < |v| := by rw [habsv]; positivity
  have hlog : Int.log 2 |v| = w.toInt + p - 1 := by
    apply le_antisymm
    · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hvpos).mp (by
        rw [habsv, zpow_add₀ (by norm_num), mul_comm]
        exact mul_lt_mul_of_pos_left hqhi h2w)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hvpos).mp (by
        rw [habsv, show w.toInt + p - 1 = ((p : ℤ) - 1) + w.toInt by ring, zpow_add₀ (by norm_num)]
        exact mul_le_mul_of_nonneg_right hqlo h2w.le)
  have hscale : precScale 2 p v = (2 : ℝ) ^ w.toInt := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  -- the integer rounding is `AzInt.divRound`
  set qo := AzInt.divRound (AzInt.mkNorm s A) B.toAzInt mode with hqo
  clear_value qo
  have hz : ((AzInt.mkNorm s A).toInt : ℝ) = σ * (A.toNat : ℝ) := by
    rw [hσ]
    rcases Bool.eq_false_or_eq_true s with hs | hs <;>
      simp [hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false A hA0]
  have hyq : v / (2 : ℝ) ^ w.toInt
      = ((AzInt.mkNorm s A).toInt : ℝ) / (B.toAzInt.toInt : ℝ) := by
    rw [hv, mul_div_cancel_right₀ _ h2w.ne', hz, toInt_toAzInt, Int.cast_natCast, mul_div_assoc]
  have hr := AzInt.toInt_divRound (AzInt.mkNorm s A) B.toAzInt mode hB0
  rw [← hyq, ← hqo] at hr
  have hrI : toInt (round intSet mode (v / 2 ^ w.toInt)) = qo.1.toInt := toInt_eq_of_val hr
  have hround : (round (floatSet p) mode v).val
      = (((qo.1.toInt : ℝ) * 2 ^ w.toInt : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hrI]
  have hyabs : |v / (2 : ℝ) ^ w.toInt| = (A.toNat : ℝ) / (B.toNat : ℝ) := by
    rw [abs_div, habsv, abs_of_pos h2w, mul_div_cancel_right₀ _ h2w.ne']
  obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds p hp mode (v / 2 ^ w.toInt)
    (by rw [hyabs]; exact hqlo) (by rw [hyabs]; exact hqhi)
  rw [hrI] at hb1 hb2
  have habs : (qo.1.abs.toNat : ℤ) = |qo.1.toInt| := AzInt.abs_toNat_eq qo.1
  have hlo' : 2 ^ (p - 1) ≤ qo.1.abs.toNat := by
    have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ (qo.1.abs.toNat : ℤ) := by rw [habs]; exact hb1
    exact_mod_cast this
  have hhi' : qo.1.abs.toNat ≤ 2 ^ p := by
    have : (qo.1.abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by rw [habs]; exact hb2
    exact_mod_cast this
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec qo.1 p hp (w + (AzNat.ofNat p).toAzInt) hlo' hhi'
  have hep : (w + (AzNat.ofNat p).toAzInt).toInt - p = w.toInt := by
    rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; ring
  rw [hep] at hRval
  symm
  refine Prod.ext ?_ ?_
  · have hgoal : (roundVal p mode (some (v : EReal))).1
        = normalizeCarry qo.1 (w + (AzNat.ofNat p).toAzInt) p :=
      toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
        (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
    exact hgoal
  · show (roundVal p mode (some (v : EReal))).2 = qo.2
    rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, hqo,
      AzInt.snd_divRound _ _ _ hB0, ← hqo, ← hyq]
    conv_rhs => rw [← compare_mul_right_pos _ _ _ h2w, div_mul_cancel₀ _ h2w.ne']

/-- `divCores` with the comparison flag from the aligned significands rounds the exact quotient. -/
theorem divCores_eq (s : Bool) (e₁ : AzInt) {p₁ : ℕ} {m₁ : AzNat} (h₁ : FiniteValid p₁ m₁)
    (e₂ : AzInt) {p₂ : ℕ} {m₂ : AzNat} (h₂ : FiniteValid p₂ m₂) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    divCores s e₁ (coreSignificand p₁ m₁) p₁ e₂ (coreSignificand p₂ m₂) p₂
        (compareMagnitude 0 m₁ 0 m₂ != .lt) p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true e₁ (coreSignificand p₁ m₁) /
            finiteVal true e₂ (coreSignificand p₂ m₂)) : ℝ) : EReal)) := by
  apply divCores_eq_gen s e₁ _ p₁ (coreSignificand_ne_zero h₁) (size_coreSignificand h₁) e₂ _ p₂
    (coreSignificand_ne_zero h₂) (size_coreSignificand h₂)
  rw [bne_iff_ne, compareMagnitude_eq 0 h₁ 0 h₂, finiteVal_eq_core true 0 h₁,
    finiteVal_eq_core true 0 h₂, finiteVal_true_eq, finiteVal_true_eq, size_coreSignificand h₁,
    size_coreSignificand h₂, Ne, compare_lt_iff_lt, not_lt, show (0 : AzInt).toInt = 0 from rfl,
    zero_sub, zero_sub, zpow_neg, zpow_neg, ← div_eq_mul_inv, ← div_eq_mul_inv]

/-- `ofFractionRound` rounds the exact fraction. -/
theorem ofFractionRound_eq (s : Bool) (num den : AzNat) (hden : den ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ofFractionRound s num den p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          ((num.toNat : ℝ) / (den.toNat : ℝ)) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold ofFractionRound
  rw [ite_eq_right hp.ne']
  by_cases h0 : num = 0
  · rw [ite_eq_left h0, h0]
    simp only [AzNat.toNat_zero, Nat.cast_zero, zero_div, mul_zero, EReal.coe_zero]
    exact (roundVal_zero p mode).symm
  · rw [ite_eq_right h0]
    have ha : (0 : ℝ) < (2 : ℝ) ^ (num.size : ℤ) := zpow_pos (by norm_num) _
    have hb : (0 : ℝ) < (2 : ℝ) ^ (den.size : ℤ) := zpow_pos (by norm_num) _
    have hcase : (compare (num.shiftLeft den.size) (den.shiftLeft num.size) != .lt) = true ↔
        (den.toNat : ℝ) / (2 : ℝ) ^ (den.size : ℤ)
          ≤ (num.toNat : ℝ) / (2 : ℝ) ^ (num.size : ℤ) := by
      rw [bne_iff_ne,
        show compare (num.shiftLeft den.size) (den.shiftLeft num.size)
          = AzNat.compare (num.shiftLeft den.size) (den.shiftLeft num.size) from rfl,
        AzNat.compare_eq_compare_toNat, ← compare_natCast, AzNat.toNat_shiftLeft,
        AzNat.toNat_shiftLeft, Ne, compare_lt_iff_lt, not_lt, div_le_div_iff₀ hb ha]
      push_cast
      simp only [zpow_natCast]
    rw [divCores_eq_gen s _ num num.size h0 rfl _ den den.size hden rfl _ hcase p mode,
      finiteVal_true_eq, finiteVal_true_eq, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat, sub_self, sub_self, zpow_zero, mul_one, mul_one]

/-- Rounding a fraction agrees with rounding the rational it represents. -/
theorem fst_ofFractionRound (s : Bool) (num den : AzNat) (hden : den ≠ 0) (p : ℕ)
    (mode : RoundingMode) (q : AzRat)
    (hq : (AzRat.toRat q : ℝ) = (if s then 1 else -1) * ((num.toNat : ℝ) / (den.toNat : ℝ))) :
    (ofFractionRound s num den p mode).1 = (ofAzRatRound q p mode).1 := by
  by_cases hp : p = 0
  · subst hp
    unfold ofFractionRound ofAzRatRound
    rw [ite_eq_left rfl, ite_eq_left rfl]
  · have : NeZero p := ⟨hp⟩
    rw [ofFractionRound_eq s num den hden p mode, fst_roundVal, ofVal_some,
      ofAzRatRound_eq_ofEReal, hq]

/-- Division is the float lift of `Spec.div`. -/
theorem divPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    divPrecRound x y p mode = liftVal₂ Spec.div x y p mode := by
  unfold liftVal₂
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t => cases s <;> cases t <;> simp [divPrecRound, Spec.div]
    | zero =>
      simp only [divPrecRound, toVal_infinity, toVal_zero, Option.bind_some, Spec.div_inf_zero,
        roundVal_inf]
    | finite t e q m hv =>
      simp only [divPrecRound, toVal_infinity, toVal_finite, Option.bind_some]
      rw [Spec.div_inf_coe s _ (by
          rw [finiteVal_eq_core t e hv]
          exact finiteVal_ne_zero' t e _ (coreSignificand_ne_zero hv)),
        finiteVal_eq_core t e hv, decide_pos_finiteVal t e _ (coreSignificand_ne_zero hv),
        roundVal_inf]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t =>
      simp only [divPrecRound, toVal_infinity, toVal_zero, Option.bind_some, Spec.div_zero_inf,
        roundVal_zero]
    | zero => simp [divPrecRound, Spec.div]
    | finite t e q m hv =>
      simp only [divPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [Spec.div_zero_coe _ (by
          rw [finiteVal_eq_core t e hv]
          exact finiteVal_ne_zero' t e _ (coreSignificand_ne_zero hv)), roundVal_zero]
  | finite s e₁ p₁ m₁ h₁ =>
    have hx0 : finiteVal s e₁ m₁ ≠ 0 := by
      rw [finiteVal_eq_core s e₁ h₁]
      exact finiteVal_ne_zero' s e₁ _ (coreSignificand_ne_zero h₁)
    cases y with
    | nan => rfl
    | infinity t =>
      simp only [divPrecRound, toVal_infinity, toVal_finite, Option.bind_some, Spec.div_coe_inf,
        roundVal_zero]
    | zero =>
      simp only [divPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [Spec.div_coe_zero _ hx0, finiteVal_eq_core s e₁ h₁]
      simp only [finiteVal_pos_iff s e₁ _ (coreSignificand_ne_zero h₁), roundVal_inf]
    | finite t e₂ p₂ m₂ h₂ =>
      have hy0 : finiteVal t e₂ m₂ ≠ 0 := by
        rw [finiteVal_eq_core t e₂ h₂]
        exact finiteVal_ne_zero' t e₂ _ (coreSignificand_ne_zero h₂)
      simp only [divPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.div_coe_coe _ _ hy0, divCores_eq (s == t) e₁ h₁ e₂ h₂ p mode,
        finiteVal_eq_core s e₁ h₁, finiteVal_eq_core t e₂ h₂, finiteVal_sign s e₁,
        finiteVal_sign t e₂, signed_div]

end Azurite.AzFloat
