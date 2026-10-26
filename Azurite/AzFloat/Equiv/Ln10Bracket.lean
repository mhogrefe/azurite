/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln10Bracket
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.LogBaseFloatBracket

/-!
# Equivalence: the brackets of `ln 10`, `log₁₀ e`, `log₂ 10` and `log₁₀ 2`

`ln10Bracket_spec` (from `lnFloorBracket_spec` at the exact float `10`, lower end `≥ 2`), the
quotient brackets through `divBracketByPosBracket_spec`, the width functions with their limits
(`tendsto_divEps`), the irrationality of the four constants (`irrational_log_ten`,
`irrational_log_ten_div_log_two`) and the `Roundable` specs with the Ziv certificates.
-/

namespace Azurite.AzFloat

theorem toVal_tenF : tenF.toVal = some ((10 : ℝ) : EReal) := by
  rw [tenF, toVal_ofAzNat, AzNat.toNat_ofNat, Nat.cast_ofNat]

/-- `2 < ln 10`, from `e < 2.72`. -/
theorem two_lt_log_ten : (2 : ℝ) < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e2]
  nlinarith [Real.exp_pos 1]

theorem irrational_log_ten : Irrational (Real.log 10) := by
  simpa using irrational_log_rat (r := 10) (by norm_num) (by norm_num)

/-- `log₂ 10 = ln 10 / ln 2` is irrational (`10` is not an integer power of `2`). -/
theorem irrational_log_ten_div_log_two : Irrational (Real.log 10 / Real.log 2) := by
  obtain ⟨h1, h2, h3, -⟩ := maxRootBase_spec (AzNat.ofNat 2) (by rw [AzNat.toNat_ofNat])
  rw [AzNat.toNat_ofNat] at h1
  have hs : (maxRootBase (AzNat.ofNat 2)).1.toNat = 2 := by
    have hle : (maxRootBase (AzNat.ofNat 2)).1.toNat ≤ 2 := by
      have h := Nat.le_self_pow (by omega : (maxRootBase (AzNat.ofNat 2)).2 ≠ 0)
        (maxRootBase (AzNat.ofNat 2)).1.toNat
      rw [← h1] at h
      exact h
    exact le_antisymm hle h3
  have hno : ∀ r : ℤ, ((10 : ℚ) : ℝ) ≠ ((maxRootBase (AzNat.ofNat 2)).1.toNat : ℝ) ^ r := by
    intro r h
    rw [hs] at h
    push_cast at h
    rcases le_or_gt r 3 with hr | hr
    · have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
      norm_num at this
      linarith
    · have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : (4 : ℤ) ≤ r)
      norm_num at this
      linarith
  have h := irrational_log_div_log_of_rat (AzNat.ofNat 2) (by rw [AzNat.toNat_ofNat])
    (by rw [AzNat.toNat_ofNat]; norm_num) 10 (by norm_num) hno
  rw [AzNat.toNat_ofNat] at h
  simpa using h

/-! ### `ln 10` -/

/-- The width bound of `ln10Bracket`. -/
noncomputable def ln10Eps (w : ℕ) : ℝ := lnRatEps (⌊2 * |Real.log 10|⌋₊ + 2) |Real.log 10| w

theorem tendsto_ln10Eps : Filter.Tendsto ln10Eps Filter.atTop (nhds 0) := tendsto_lnRatEps _ _

/-- `ln10Bracket w` encloses `ln 10`, lower end at least `2`, width at most `ln10Eps w`. -/
theorem ln10Bracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, (ln10Bracket w).1.toVal = some (lv : EReal) ∧
      (ln10Bracket w).2.toVal = some (hv : EReal) ∧ 2 ≤ lv ∧
      lv ≤ Real.log 10 ∧ Real.log 10 ≤ hv ∧ hv - lv ≤ ln10Eps w := by
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw toVal_tenF
    (by norm_num : (0 : ℝ) < 10) le_rfl (by have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
                                            nlinarith)
  simp only [ln10Bracket]
  refine ⟨max lv 2, hv, toVal_maxOf hlv toVal_two, hhv, le_max_right _ _,
    max_le hlo two_lt_log_ten.le, hhi, ?_⟩
  have := le_max_left lv 2
  unfold ln10Eps
  linarith

theorem ln10Approx_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (ln10Approx w).1 lv ∧ Rounds (ln10Approx w).2 hv ∧
      lv < Real.log 10 ∧ Real.log 10 < hv ∧ hv - lv ≤ ln10Eps w := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := ln10Bracket_spec hw
  refine ⟨lv, hv, ?_, ?_, ?_, ?_, hwid⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo fun h => irrational_log_ten.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi fun h => irrational_log_ten.ne_rat r (h.trans hr)

/-- The termination certificate for `ln 10`. -/
theorem ln10Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (ln10Approx (w₀ * 2 ^ f)).1 (ln10Approx (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode ln10Approx irrational_log_ten ln10Eps
    tendsto_ln10Eps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := ln10Approx_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The quotients -/

/-- `divEps` tends to `0` with its two widths. -/
theorem tendsto_divEps (K A : ℝ) {ε δ : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => divEps K A (ε w) (δ w) w) Filter.atTop (nhds 0) := by
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (((hε.const_mul 2).add (((hA.add hε).const_mul 8).mul
    ((hδ.const_mul (1 + K)).add hu)))).const_mul (1 + K)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The `Roundable` pair of a bracket is a strict enclosure of an irrational value. -/
theorem rounds_of_bracket {b : AzFloat × AzFloat} {lo hi v : ℝ}
    (hlo : b.1.toVal = some (lo : EReal)) (hhi : b.2.toVal = some (hi : EReal))
    (h1 : lo ≤ v) (h2 : v ≤ hi) (hirr : Irrational v) :
    Rounds (fun p mode => setPrecRound b.1 p mode) lo ∧
      Rounds (fun p mode => setPrecRound b.2 p mode) hi ∧ lo < v ∧ v < hi := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne h1 fun h => hirr.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne h2 fun h => hirr.ne_rat r (h.trans hr)

/-- The width bound of `log10EBracket`. -/
noncomputable def log10EEps (w : ℕ) : ℝ := divEps (1 / 2) 1 0 (ln10Eps w) w

theorem tendsto_log10EEps : Filter.Tendsto log10EEps Filter.atTop (nhds 0) :=
  tendsto_divEps (1 / 2) 1 tendsto_const_nhds tendsto_ln10Eps

theorem log10EBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (log10EBracket w).1.toVal = some (lo : EReal) ∧
      (log10EBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ (Real.log 10)⁻¹ ∧ (Real.log 10)⁻¹ ≤ hi ∧ hi - lo ≤ log10EEps w := by
  obtain ⟨lv, hv, hlv, hhv, h2, hlo, hhi, hwid⟩ := ln10Bracket_spec hw
  obtain ⟨lo, hi, hlo', hhi', h1, h2', h3⟩ :=
    divBracketByPosBracket_spec hw (X := (one, one)) (B := ln10Bracket w) (L := 1)
      (M := Real.log 10) (ε := 0) (δ := ln10Eps w) toVal_one' toVal_one' hlv hhv (by linarith)
      hlo hhi hwid le_rfl le_rfl (by norm_num)
  rw [one_div] at h1 h2'
  rw [abs_one] at h3
  refine ⟨lo, hi, hlo', hhi', h1, h2', ?_⟩
  unfold log10EEps
  refine h3.trans (divEps_mono w ?_ (one_div_pos.mpr (by linarith)).le (by norm_num) le_rfl
    ?_)
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · linarith

theorem log10EApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (log10EApprox w).1 lv ∧ Rounds (log10EApprox w).2 hv ∧
      lv < (Real.log 10)⁻¹ ∧ (Real.log 10)⁻¹ < hv ∧ hv - lv ≤ log10EEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := log10EBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_log_ten.inv
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `log₁₀ e`. -/
theorem log10EApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log10EApprox (w₀ * 2 ^ f)).1 (log10EApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode log10EApprox irrational_log_ten.inv log10EEps
    tendsto_log10EEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := log10EApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-- The width bound of `log2TenBracket`. -/
noncomputable def log2TenEps (w : ℕ) : ℝ :=
  divEps 5 |Real.log 10| (ln10Eps w) (8 * (1 / 2 : ℝ) ^ w) w

theorem tendsto_log2TenEps : Filter.Tendsto log2TenEps Filter.atTop (nhds 0) :=
  tendsto_divEps 5 |Real.log 10| tendsto_ln10Eps (by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (8 : ℝ)
    rwa [mul_zero] at this)

theorem log2TenBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (log2TenBracket w).1.toVal = some (lo : EReal) ∧
      (log2TenBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.log 10 / Real.log 2 ∧ Real.log 10 / Real.log 2 ≤ hi ∧
      hi - lo ≤ log2TenEps w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := ln10Bracket_spec hw
  obtain ⟨lv2, hv2, hlv2, hhv2, hlo2, hhi2, hwid2, h5⟩ := ln2Bracket_spec w
  have hlv5 : 1 / 5 ≤ lv2 := h5 (by omega)
  obtain ⟨lo, hi, hlo', hhi', h1, h2', h3⟩ :=
    divBracketByPosBracket_spec hw (L := Real.log 10) (M := Real.log 2) (ε := ln10Eps w)
      (δ := 8 * (1 / 2 : ℝ) ^ w) hlv hhv hlv2 hhv2 (by linarith) hlo2 hhi2 hwid2 hlo hhi hwid
  refine ⟨lo, hi, hlo', hhi', h1, h2', ?_⟩
  unfold log2TenEps
  refine h3.trans (divEps_mono w ?_ (one_div_pos.mpr (by linarith)).le (abs_nonneg _)
    (by linarith) (by positivity))
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem log2TenApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (log2TenApprox w).1 lv ∧ Rounds (log2TenApprox w).2 hv ∧
      lv < Real.log 10 / Real.log 2 ∧ Real.log 10 / Real.log 2 < hv ∧
      hv - lv ≤ log2TenEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := log2TenBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_log_ten_div_log_two
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `log₂ 10`. -/
theorem log2TenApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log2TenApprox (w₀ * 2 ^ f)).1 (log2TenApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode log2TenApprox irrational_log_ten_div_log_two
    log2TenEps tendsto_log2TenEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := log2TenApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-- The width bound of `log10TwoBracket`. -/
noncomputable def log10TwoEps (w : ℕ) : ℝ :=
  divEps (1 / 2) |Real.log 2| (8 * (1 / 2 : ℝ) ^ w) (ln10Eps w) w

theorem tendsto_log10TwoEps : Filter.Tendsto log10TwoEps Filter.atTop (nhds 0) :=
  tendsto_divEps (1 / 2) |Real.log 2| (by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (8 : ℝ)
    rwa [mul_zero] at this) tendsto_ln10Eps

theorem irrational_log_two_div_log_ten : Irrational (Real.log 2 / Real.log 10) := by
  have h := irrational_log_ten_div_log_two.inv
  rwa [inv_div] at h

theorem log10TwoBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (log10TwoBracket w).1.toVal = some (lo : EReal) ∧
      (log10TwoBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.log 2 / Real.log 10 ∧ Real.log 2 / Real.log 10 ≤ hi ∧
      hi - lo ≤ log10TwoEps w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lv, hv, hlv, hhv, h2, hlo, hhi, hwid⟩ := ln10Bracket_spec hw
  obtain ⟨lv2, hv2, hlv2, hhv2, hlo2, hhi2, hwid2, -⟩ := ln2Bracket_spec w
  obtain ⟨lo, hi, hlo', hhi', h1, h2', h3⟩ :=
    divBracketByPosBracket_spec hw (L := Real.log 2) (M := Real.log 10)
      (ε := 8 * (1 / 2 : ℝ) ^ w) (δ := ln10Eps w) hlv2 hhv2 hlv hhv (by linarith) hlo hhi hwid
      hlo2 hhi2 hwid2
  refine ⟨lo, hi, hlo', hhi', h1, h2', ?_⟩
  unfold log10TwoEps
  refine h3.trans (divEps_mono w ?_ (one_div_pos.mpr (by linarith)).le (abs_nonneg _)
    (by positivity) ?_)
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · linarith

theorem log10TwoApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (log10TwoApprox w).1 lv ∧ Rounds (log10TwoApprox w).2 hv ∧
      lv < Real.log 2 / Real.log 10 ∧ Real.log 2 / Real.log 10 < hv ∧
      hv - lv ≤ log10TwoEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := log10TwoBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_log_two_div_log_ten
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `log₁₀ 2`. -/
theorem log10TwoApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log10TwoApprox (w₀ * 2 ^ f)).1
      (log10TwoApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode log10TwoApprox irrational_log_two_div_log_ten
    log10TwoEps tendsto_log10TwoEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := log10TwoApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
