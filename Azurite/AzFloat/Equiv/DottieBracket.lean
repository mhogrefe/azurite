/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DottieBracket
import Azurite.AzFloat.Equiv.CosRatBracket
import Azurite.AzFloat.Equiv.Constants
import Azurite.Transcendental.Dottie

/-!
# Equivalence: the bracket of the Dottie number

`dottieClamp_spec`, `dottieMvt_spec` (the verified bracket around any float in `[0, 1]`, of
width `4 |n − d| + 2 cosEps + 40·2^(−W)`), `dottieIter_spec` (the contraction), `dottieBracket_spec`
(width `dottieEps w`), `tendsto_dottieEps`, `dottieApprox_spec`, `dottieApprox_isSome_exists`
(the Ziv certificate from `irrational_dottie`).
-/

namespace Azurite.AzFloat

/-- `dottieClamp x` has a value in `[0, 1]`: the projection of the value of `x` when there is
one. -/
theorem dottieClamp_spec (x : AzFloat) :
    ∃ v : ℝ, (dottieClamp x).toVal = some (v : EReal) ∧ 0 ≤ v ∧ v ≤ 1 ∧
      ∀ xv : ℝ, x.toVal = some (xv : EReal) → v = max 0 (min 1 xv) := by
  unfold dottieClamp
  split_ifs with hf
  · have hx := toVal_of_isFinite hf
    refine ⟨max 0 (min 1 (fval x)), toVal_maxOf toVal_zero' (toVal_minOf toVal_one' hx),
      le_max_left _ _, max_le zero_le_one (min_le_left _ _), fun xv hxv => ?_⟩
    rw [fval_of_toVal_coe hxv]
  · refine ⟨1 / 2, toVal_oneHalf, by norm_num, by norm_num, fun xv hxv => ?_⟩
    exact absurd (isFinite_of_toVal_coe hxv) hf

/-- The projection onto `[0, 1]` does not increase the distance to a point of `[0, 1]`. -/
theorem abs_clamp_sub_le {y d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |max 0 (min 1 y) - d| ≤ |y - d| := by
  rcases le_total y 0 with h | h
  · rw [max_eq_left ((min_le_right 1 y).trans h), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total y 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right zero_le_one, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith

theorem abs_lt_two_zpow_one {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    |v| < (2 : ℝ) ^ (AzInt.ofInt 1).toInt := by
  rw [AzInt.toInt_ofInt, zpow_one, abs_of_nonneg h0]
  linarith

/-- **The verified bracket** around a float `n ∈ [0, 1]`. -/
theorem dottieMvt_spec {n : AzFloat} {nv : ℝ} (hn : n.toVal = some (nv : EReal)) (h0 : 0 ≤ nv)
    (h1 : nv ≤ 1) {W : ℕ} (hW : 64 ≤ W) :
    ∃ lo hi : ℝ, (dottieMvt n W).1.toVal = some (lo : EReal) ∧
      (dottieMvt n W).2.toVal = some (hi : EReal) ∧ lo ≤ dottieNumber ∧ dottieNumber ≤ hi ∧
      hi - lo ≤ 4 * |nv - dottieNumber| + 2 * cosEps (AzInt.ofInt 1) W + 40 * (1 / 2 : ℝ) ^ W := by
  have : NeZero W := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW
  have hε1 := cosEps_le_one (AzInt.ofInt 1) hW
  obtain ⟨cl, ch, hcl, hch, hc1, hc2, hcw⟩ := cosBracket_spec hn (abs_lt_two_zpow_one h0 h1) hW
  set ε := cosEps (AzInt.ofInt 1) W with hε
  have hε0 : 0 ≤ ε := by linarith
  have hd := abs_sub_dottie_le h0 h1
  have hcon := abs_cos_sub_dottie_le h0 h1
  set e := |nv - dottieNumber| with he
  have he0 : 0 ≤ e := abs_nonneg _
  have he1 : e ≤ 1 := by
    rw [he, abs_le]; constructor <;> linarith [dottie_nonneg, dottie_le_one]
  -- the residual
  have hres : |nv - Real.cos nv| ≤ 2 * e := by
    have : nv - Real.cos nv = (nv - dottieNumber) - (Real.cos nv - dottieNumber) := by ring
    rw [this]
    exact (abs_sub _ _).trans (by linarith)
  obtain ⟨hr1, hr2⟩ := abs_le.mp hres
  obtain ⟨r1, hr1v, hr1a, hr1b⟩ := subCeiling_abs hch hn W
  obtain ⟨r2, hr2v, hr2a, hr2b⟩ := subCeiling_abs hn hcl W
  rw [← hu] at hr1b hr2b
  have hA1 : |ch - nv| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  have hA2 : |nv - cl| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  have hδ := toVal_maxOf hr1v hr2v
  set δ := max r1 r2 with hδdef
  have hδlo : |nv - Real.cos nv| ≤ δ := by
    rw [abs_le]
    constructor
    · have := le_max_left r1 r2; linarith
    · have := le_max_right r1 r2; linarith
  have hδhi : δ ≤ 2 * e + ε + 6 * u := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_right hA1 hu0]
    · nlinarith [mul_le_mul_of_nonneg_right hA2 hu0]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδlo
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hn hδ W
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hn hδ W
  rw [← hu] at hlo2 hhi2
  have hδ4 : δ ≤ 4 := by linarith
  have hB1 : |nv - δ| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have hB2 : |nv + δ| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨hd1, hd2⟩ := abs_le.mp (hd.trans hδlo)
  refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hB1 hu0, mul_le_mul_of_nonneg_right hB2 hu0]

/-- One step of the contracting iteration. -/
theorem dottieIterStep_spec {W : ℕ} (hW : 64 ≤ W) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (h0 : 0 ≤ xv) (h1 : xv ≤ 1) :
    ∃ v : ℝ, (dottieIterStep W x).toVal = some (v : EReal) ∧ 0 ≤ v ∧ v ≤ 1 ∧
      |v - dottieNumber| ≤ 9 / 10 * |xv - dottieNumber| + cosEps (AzInt.ofInt 1) W := by
  obtain ⟨cl, ch, hcl, hch, hc1, hc2, hcw⟩ := cosBracket_spec hx (abs_lt_two_zpow_one h0 h1) hW
  obtain ⟨v, hv, hv0, hv1, hvp⟩ := dottieClamp_spec (cosBracket x (AzInt.ofInt 1) W).1
  refine ⟨v, hv, hv0, hv1, ?_⟩
  rw [hvp cl hcl]
  refine (abs_clamp_sub_le dottie_nonneg dottie_le_one).trans ?_
  have hcon := abs_cos_sub_dottie_le h0 h1
  have : cl - dottieNumber = (Real.cos xv - dottieNumber) - (Real.cos xv - cl) := by ring
  rw [this]
  refine (abs_sub _ _).trans ?_
  have : |Real.cos xv - cl| ≤ cosEps (AzInt.ofInt 1) W := by
    rw [abs_of_nonneg (by linarith)]; linarith
  linarith

/-- `k` steps of the contracting iteration: the error is at most `(9/10)^k` times the initial
one, plus `10 cosEps`. -/
theorem dottieIter_spec {W : ℕ} (hW : 64 ≤ W) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (h0 : 0 ≤ xv) (h1 : xv ≤ 1) (k : ℕ) :
    ∃ v : ℝ, (dottieIter W k x).toVal = some (v : EReal) ∧ 0 ≤ v ∧ v ≤ 1 ∧
      |v - dottieNumber|
        ≤ (9 / 10 : ℝ) ^ k * |xv - dottieNumber| + 10 * cosEps (AzInt.ofInt 1) W := by
  have hε0 : 0 ≤ cosEps (AzInt.ofInt 1) W := by
    obtain ⟨cl, ch, -, -, hc1, hc2, hcw⟩ := cosBracket_spec hx (abs_lt_two_zpow_one h0 h1) hW
    linarith
  induction k with
  | zero =>
    exact ⟨xv, hx, h0, h1, by rw [pow_zero, one_mul]; linarith⟩
  | succ k ih =>
    obtain ⟨y, hy, hy0, hy1, hye⟩ := ih
    obtain ⟨v, hv, hv0, hv1, hve⟩ := dottieIterStep_spec hW hy hy0 hy1
    refine ⟨v, hv, hv0, hv1, ?_⟩
    rw [pow_succ]
    nlinarith [abs_nonneg (xv - dottieNumber), pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10) k]

theorem nine_tenths_pow_le (W : ℕ) : (9 / 10 : ℝ) ^ (8 * W) ≤ (1 / 2 : ℝ) ^ W := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) W

/-- The width of `dottieBracket w`. -/
noncomputable def dottieEps (w : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ w + 44 * (1 / 2 : ℝ) ^ (w + 8) + 42 * cosEps (AzInt.ofInt 1) (w + 8)

/-- **`dottieBracket` encloses the Dottie number**, with width at most `dottieEps w`. -/
theorem dottieBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (dottieBracket w).1.toVal = some (lo : EReal) ∧
      (dottieBracket w).2.toVal = some (hi : EReal) ∧ lo ≤ dottieNumber ∧ dottieNumber ≤ hi ∧
      hi - lo ≤ dottieEps w := by
  have hW : 64 ≤ w + 8 := by omega
  have hd0 := dottie_nonneg
  have hd1 := dottie_le_one
  have : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 8) := by positivity
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hε0 : 0 ≤ cosEps (AzInt.ofInt 1) (w + 8) := by
    obtain ⟨cl, ch, -, -, hc1, hc2, hcw⟩ :=
      cosBracket_spec toVal_oneHalf (abs_lt_two_zpow_one (by norm_num) (by norm_num)) hW
    linarith
  unfold dottieBracket dottieEps
  dsimp only
  split_ifs with hc
  · obtain ⟨nv, hn, hn0, hn1, -⟩ := dottieClamp_spec
      (dottieRefine (ofFloat64 0.7390851332151607) 64 (w + 8) (w + 8 + 2))
    obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := dottieMvt_spec (W := w + 8) hn hn0 hn1 hW
    have hlo' : (dottieMvt (dottieCandidate (w + 8)) (w + 8)).1.toVal = some (lo : EReal) := hlo
    have hhi' : (dottieMvt (dottieCandidate (w + 8)) (w + 8)).2.toVal = some (hi : EReal) := hhi
    obtain ⟨dv, hdv, hdv1, -⟩ := subCeiling_abs hhi' hlo' 64
    have ht : (one <<< AzInt.ofInt (-(w : Int))).toVal
        = some ((1 * (2 : ℝ) ^ (-(w : ℤ)) : ℝ) : EReal) := by
      rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
    rw [le_eq_true_iff hdv ht, one_mul, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow] at hc
    exact ⟨lo, hi, hlo', hhi', h1, h2, by linarith⟩
  · obtain ⟨v, hv, hv0, hv1, hve⟩ := dottieIter_spec hW toVal_oneHalf (by norm_num)
      (by norm_num) (8 * (w + 8))
    obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := dottieMvt_spec (W := w + 8) hv hv0 hv1 hW
    refine ⟨lo, hi, hlo, hhi, h1, h2, hwid.trans ?_⟩
    have hp := nine_tenths_pow_le (w + 8)
    have he0 : |(1 / 2 : ℝ) - dottieNumber| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hp0 : (0 : ℝ) ≤ (9 / 10 : ℝ) ^ (8 * (w + 8)) := by positivity
    nlinarith [mul_le_mul hp he0 (abs_nonneg _) hu0]

theorem tendsto_dottieEps : Filter.Tendsto dottieEps Filter.atTop (nhds 0) := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h8 := Filter.tendsto_add_atTop_nat 8
  have h2 := (h1.comp h8).const_mul 44
  have h3 := ((tendsto_cosEps (AzInt.ofInt 1)).comp h8).const_mul 42
  have h := (h1.add h2).add h3
  simp only [mul_zero, add_zero] at h
  exact h

/-- `dottieApprox` as a pair of `Roundable`s bracketing the Dottie number. -/
theorem dottieApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (dottieApprox w).1 lv ∧ Rounds (dottieApprox w).2 hv ∧
      lv ≤ dottieNumber ∧ dottieNumber ≤ hv ∧ hv - lv ≤ dottieEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := dottieBracket_spec hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [dottieApprox]
  exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩

/-- The Ziv certificate for the Dottie number. -/
theorem dottieApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (dottieApprox (w₀ * 2 ^ f)).1 (dottieApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode dottieApprox irrational_dottie dottieEps
    tendsto_dottieEps 64 (fun _ hw => dottieApprox_spec hw) w₀ hw₀

end Azurite.AzFloat
