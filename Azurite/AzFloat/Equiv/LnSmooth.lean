/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnSmooth
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.AzFloat.Equiv.Interval

/-!
# Equivalence: the logarithm of an integer with no prime factor above `7`

* `atanhInvBracket_spec`: the bracket of `atanh (1/q)` for `q ≥ 2` (partial sums from below,
  `sum_le_atanhInv`; the tail `(4/3) t_N ≤ 2^(−k−5)`, `atanhInv_sub_sum_le`,
  `atanhTerm_le_half_pow`).
* `two_mul_atanhInv_251`, `…_449`, `…_4801`, `…_8749`: the four values in terms of `ln 2`,
  `ln 3`, `ln 5`, `ln 7`, and `smooth_log_eq`: the combination for `a ln 2 + b ln 3 + c ln 5 +
  d ln 7` (linear algebra on the four).
* `lnSmoothBracket_spec`: the bracket encloses that number.  Only validity is proven; the
  width is not (the caller, Euler's constant, runs a loop with fuel).
* `le_nextSmooth`.
-/

namespace Azurite.AzFloat

open Finset BZ

/-- `(2N + 1) b ≥ k + 6` for `N = atanhInvTerms b k`, `b ≥ 1`. -/
theorem atanhInvTerms_spec {b : ℕ} (hb : 1 ≤ b) (k : ℕ) :
    k + 6 ≤ (2 * atanhInvTerms b k + 1) * b := by
  unfold atanhInvTerms
  have h := Nat.div_add_mod (k + 6) (2 * b)
  have hm := Nat.mod_lt (k + 6) (by omega : 0 < 2 * b)
  have e : (2 * ((k + 6) / (2 * b) + 1) + 1) * b = 2 * b * ((k + 6) / (2 * b)) + 3 * b := by ring
  rw [e]
  omega

/-- `atanhInvBracket q k` encloses `atanh (1/q)` (`q ≥ 2`, `k ≥ 4`), with a nonnegative lower
end. -/
theorem atanhInvBracket_spec {q : ℕ} (hq : 2 ≤ q) {k : ℕ} (hk : 4 ≤ k) :
    ∃ lv hv : ℝ, (atanhInvBracket q k).1.toVal = some (lv : EReal) ∧
      (atanhInvBracket q k).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv ≤ atanhInv q ∧ atanhInv q ≤ hv := by
  have : NeZero k := ⟨by omega⟩
  have hq0 : q ≠ 0 := by omega
  have hb : 1 ≤ q.log2 := (Nat.le_log2 hq0).mpr (by simpa using hq)
  have hpow : 2 ^ q.log2 ≤ q := Nat.log2_self_le hq0
  set N := atanhInvTerms q.log2 k with hN
  have hN0 : 0 < N := Nat.succ_pos _
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨lv, hv, hl, hh, hl0, hlS, -, hSh, -⟩ := seriesBracket_spec (by omega : 0 < q) hN0 hk
  have ht := toVal_tail k
  obtain ⟨r, hr, hrge⟩ := addCeiling_ge hh ht k
  have hterm := atanhTerm_le_half_pow hpow (atanhInvTerms_spec hb k)
  rw [← hN] at hterm
  have htail := atanhInv_sub_sum_le hqr N
  have hp : (1 / 2 : ℝ) ^ (k + 6) = (1 / 2 : ℝ) ^ (k + 5) / 2 := by rw [pow_succ]; ring
  have hp0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 5) := by positivity
  refine ⟨lv, r, hl, hr, hl0, hlS.trans (sum_le_atanhInv hqr N), ?_⟩
  rw [hp] at hterm
  linarith

/-! ### The four values -/

theorem two_mul_atanhInv {q : ℝ} (hq : 1 < q) :
    2 * atanhInv q = Real.log ((q + 1) / (q - 1)) := by
  rw [atanhInv_eq hq]; ring

theorem two_mul_atanhInv_251 :
    2 * atanhInv 251 = Real.log 2 + 2 * Real.log 3 - 3 * Real.log 5 + Real.log 7 := by
  rw [two_mul_atanhInv (by norm_num),
    show ((251 : ℝ) + 1) / (251 - 1) = 2 * 3 ^ 2 * 7 / 5 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem two_mul_atanhInv_449 :
    2 * atanhInv 449 = 2 * Real.log 3 + 2 * Real.log 5 - 5 * Real.log 2 - Real.log 7 := by
  rw [two_mul_atanhInv (by norm_num),
    show ((449 : ℝ) + 1) / (449 - 1) = 3 ^ 2 * 5 ^ 2 / (2 ^ 5 * 7) by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem two_mul_atanhInv_4801 :
    2 * atanhInv 4801 = 4 * Real.log 7 - 5 * Real.log 2 - Real.log 3 - 2 * Real.log 5 := by
  rw [two_mul_atanhInv (by norm_num),
    show ((4801 : ℝ) + 1) / (4801 - 1) = 7 ^ 4 / (2 ^ 5 * 3 * 5 ^ 2) by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem two_mul_atanhInv_8749 :
    2 * atanhInv 8749 = 4 * Real.log 5 + Real.log 7 - Real.log 2 - 7 * Real.log 3 := by
  rw [two_mul_atanhInv (by norm_num),
    show ((8749 : ℝ) + 1) / (8749 - 1) = 5 ^ 4 * 7 / (2 * 3 ^ 7) by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `a ln 2 + b ln 3 + c ln 5 + d ln 7` as a combination of the four series. -/
theorem smooth_log_eq (a b c d : ℝ) :
    a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7
      = 2 * (72 * a + 114 * b + 167 * c + 202 * d) * atanhInv 251
        + 2 * (27 * a + 43 * b + 63 * c + 76 * d) * atanhInv 449
        + 2 * (31 * a + 49 * b + 72 * c + 87 * d) * atanhInv 8749
        - 2 * (19 * a + 30 * b + 44 * c + 53 * d) * atanhInv 4801 := by
  linear_combination (-(72 * a + 114 * b + 167 * c + 202 * d)) * two_mul_atanhInv_251
    - (27 * a + 43 * b + 63 * c + 76 * d) * two_mul_atanhInv_449
    + (19 * a + 30 * b + 44 * c + 53 * d) * two_mul_atanhInv_4801
    - (31 * a + 49 * b + 72 * c + 87 * d) * two_mul_atanhInv_8749

/-! ### The bracket -/

set_option maxHeartbeats 400000 in
/-- `lnSmoothBracket a b c d k` encloses `a ln 2 + b ln 3 + c ln 5 + d ln 7` (`k ≥ 4`). -/
theorem lnSmoothBracket_spec (a b c d : ℕ) {k : ℕ} (hk : 4 ≤ k) :
    ∃ lv hv : ℝ, (lnSmoothBracket a b c d k).1.toVal = some (lv : EReal) ∧
      (lnSmoothBracket a b c d k).2.toVal = some (hv : EReal) ∧
      lv ≤ a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 ∧
      a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 ≤ hv := by
  set K₁ := 2 * (72 * a + 114 * b + 167 * c + 202 * d) with hK₁
  set K₂ := 2 * (27 * a + 43 * b + 63 * c + 76 * d) with hK₂
  set K₃ := 2 * (19 * a + 30 * b + 44 * c + 53 * d) with hK₃
  set K₄ := 2 * (31 * a + 49 * b + 72 * c + 87 * d) with hK₄
  set kk := k + (K₁ + K₂ + K₃ + K₄).log2 + 8 with hkk
  have hkk4 : 4 ≤ kk := by omega
  have : NeZero kk := ⟨by omega⟩
  obtain ⟨l₁, h₁, hl₁, hh₁, hl₁0, hl₁A, hA₁h⟩ := atanhInvBracket_spec (q := 251) (by norm_num) hkk4
  obtain ⟨l₂, h₂, hl₂, hh₂, hl₂0, hl₂A, hA₂h⟩ := atanhInvBracket_spec (q := 449) (by norm_num) hkk4
  obtain ⟨l₃, h₃, hl₃, hh₃, hl₃0, hl₃A, hA₃h⟩ :=
    atanhInvBracket_spec (q := 4801) (by norm_num) hkk4
  obtain ⟨l₄, h₄, hl₄, hh₄, hl₄0, hl₄A, hA₄h⟩ :=
    atanhInvBracket_spec (q := 8749) (by norm_num) hkk4
  simp only [Nat.cast_ofNat] at hl₁A hA₁h hl₂A hA₂h hl₃A hA₃h hl₄A hA₄h
  have hF₁ := toVal_ofAzNat_ofNat K₁
  have hF₂ := toVal_ofAzNat_ofNat K₂
  have hF₃ := toVal_ofAzNat_ofNat K₃
  have hF₄ := toVal_ofAzNat_ofNat K₄
  have k₁ : (0 : ℝ) ≤ K₁ := Nat.cast_nonneg _
  have k₂ : (0 : ℝ) ≤ K₂ := Nat.cast_nonneg _
  have k₃ : (0 : ℝ) ≤ K₃ := Nat.cast_nonneg _
  have k₄ : (0 : ℝ) ≤ K₄ := Nat.cast_nonneg _
  -- the lower end
  obtain ⟨p₁, hp₁, f₁⟩ := mulFloor_err hF₁ hl₁ kk (mul_nonneg k₁ hl₁0)
  obtain ⟨p₂, hp₂, f₂⟩ := mulFloor_err hF₂ hl₂ kk (mul_nonneg k₂ hl₂0)
  obtain ⟨p₄, hp₄, f₄⟩ := mulFloor_err hF₄ hl₄ kk (mul_nonneg k₄ hl₄0)
  obtain ⟨p₃, hp₃, c₃⟩ := mulCeiling_err hF₃ hh₃ kk (mul_nonneg k₃ (hl₃0.trans (hl₃A.trans hA₃h)))
  obtain ⟨s₁, hs₁, hs₁le⟩ := addFloor_le hp₁ hp₂ kk
  obtain ⟨s₂, hs₂, hs₂le⟩ := addFloor_le hs₁ hp₄ kk
  obtain ⟨lo, hlo, hlole, -⟩ := subFloor_le hs₂ hp₃ kk
  -- the upper end
  obtain ⟨q₁, hq₁, g₁⟩ := mulCeiling_err hF₁ hh₁ kk (mul_nonneg k₁ (hl₁0.trans (hl₁A.trans hA₁h)))
  obtain ⟨q₂, hq₂, g₂⟩ := mulCeiling_err hF₂ hh₂ kk (mul_nonneg k₂ (hl₂0.trans (hl₂A.trans hA₂h)))
  obtain ⟨q₄, hq₄, g₄⟩ := mulCeiling_err hF₄ hh₄ kk (mul_nonneg k₄ (hl₄0.trans (hl₄A.trans hA₄h)))
  obtain ⟨q₃, hq₃, d₃⟩ := mulFloor_err hF₃ hl₃ kk (mul_nonneg k₃ hl₃0)
  obtain ⟨t₁, ht₁, ht₁ge⟩ := addCeiling_ge hq₁ hq₂ kk
  obtain ⟨t₂, ht₂, ht₂ge⟩ := addCeiling_ge ht₁ hq₄ kk
  obtain ⟨hi, hhi, hhige⟩ := subCeiling_ge ht₂ hq₃ kk
  have e := smooth_log_eq a b c d
  have e₁ : (K₁ : ℝ) = 2 * (72 * a + 114 * b + 167 * c + 202 * d) := by rw [hK₁]; push_cast; ring
  have e₂ : (K₂ : ℝ) = 2 * (27 * a + 43 * b + 63 * c + 76 * d) := by rw [hK₂]; push_cast; ring
  have e₃ : (K₃ : ℝ) = 2 * (19 * a + 30 * b + 44 * c + 53 * d) := by rw [hK₃]; push_cast; ring
  have e₄ : (K₄ : ℝ) = 2 * (31 * a + 49 * b + 72 * c + 87 * d) := by rw [hK₄]; push_cast; ring
  rw [← e₁, ← e₂, ← e₃, ← e₄] at e
  have m₁ := mul_le_mul_of_nonneg_left hl₁A k₁
  have m₂ := mul_le_mul_of_nonneg_left hl₂A k₂
  have m₃ := mul_le_mul_of_nonneg_left hl₃A k₃
  have m₄ := mul_le_mul_of_nonneg_left hl₄A k₄
  have n₁ := mul_le_mul_of_nonneg_left hA₁h k₁
  have n₂ := mul_le_mul_of_nonneg_left hA₂h k₂
  have n₃ := mul_le_mul_of_nonneg_left hA₃h k₃
  have n₄ := mul_le_mul_of_nonneg_left hA₄h k₄
  refine ⟨lo, hi, ?_, ?_, ?_, ?_⟩
  · simp only [lnSmoothBracket]
    exact hlo
  · simp only [lnSmoothBracket]
    exact hhi
  · rw [e]
    linarith [f₁.le, f₂.le, f₄.le, c₃.ge]
  · rw [e]
    linarith [g₁.ge, g₂.ge, g₄.ge, d₃.le]

/-- The search never goes below its start. -/
theorem le_nextSmoothFuel : ∀ fuel n : ℕ, n ≤ nextSmoothFuel fuel n
  | 0, n => le_rfl
  | fuel + 1, n => by
    rw [nextSmoothFuel]
    split_ifs
    · exact le_rfl
    · exact (Nat.le_succ n).trans (le_nextSmoothFuel fuel (n + 1))

theorem le_nextSmooth (n : ℕ) : n ≤ nextSmooth n := le_nextSmoothFuel n n

end Azurite.AzFloat
