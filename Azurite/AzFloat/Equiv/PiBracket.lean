/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.Equiv.DirectedRounding
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Equivalence: the Brent–Salamin bracket of `π`

`piApprox w` brackets `π` (`piApprox_spec`): the enclosure invariant `PiEncloses` — after `n`
steps at precision `w ≥ 64`, the ends enclose `a_n`, `b_n`, `s_n`, with widths
`(a⁺ − a⁻) + (b⁺ − b⁻) ≤ 2^(2n+4) 2^(−w)` and `s⁺ − s⁻ ≤ 2^(3n+7) 2^(−w)` — is preserved by
`piStep` (`piEncloses_step`, from the three building blocks `mean_step`, `geo_step`,
`diffsq_step`), and the final bracket has width at most `piEps w = 2^19 w³ 2^(−w) → 0`
(`tendsto_piEps`).  With `irrational_pi`, this gives the Ziv certificate
`piApprox_isSome_exists`, and `Pi.lean` needs no fuel.
-/

namespace Azurite.AzFloat

open Azurite.BZ RoundingTarget

local notation "sA" => agmA 1 salaminB0
local notation "sB" => agmB 1 salaminB0

/-! ### Numerical facts -/

theorem salaminS_le_half (n : ℕ) : salaminS n ≤ 1 / 2 := by
  induction n with
  | zero => rw [salaminS_zero]
  | succ n ih =>
    rw [salaminS_succ]
    have : 0 ≤ (2 : ℝ) ^ (n + 1) * ((sA n - sB n) / 2) ^ 2 := by positivity
    linarith

theorem salamin_facts (n : ℕ) : 2 / 3 < sB n ∧ sB n ≤ sA n ∧ sA n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [agmA_zero, agmB_zero]
    exact ⟨salaminB0_gt, salaminB0_lt_one.le, le_rfl⟩
  · exact ⟨salamin_agmB_gt hn, agmB_le_agmA one_pos salaminB0_pos hn, salamin_agmA_le_one hn⟩

theorem cube_mul_le_two_pow {w : ℕ} (hw : 64 ≤ w) : w ^ 3 * 2 ^ 30 ≤ 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    have h64 : 64 * w ^ 2 ≤ w ^ 3 := by
      calc 64 * w ^ 2 ≤ w * w ^ 2 := Nat.mul_le_mul_right _ hw
        _ = w ^ 3 := by ring
    have h3 : 3 * w + 1 ≤ 61 * w ^ 2 := by nlinarith
    have h1 : (w + 1) ^ 3 ≤ 2 * w ^ 3 := by nlinarith
    calc (w + 1) ^ 3 * 2 ^ 30 ≤ 2 * w ^ 3 * 2 ^ 30 := Nat.mul_le_mul_right _ h1
      _ = 2 * (w ^ 3 * 2 ^ 30) := by ring
      _ ≤ 2 * 2 ^ w := by omega
      _ = 2 ^ (w + 1) := by ring

theorem cube_mul_half_pow_le {w : ℕ} (hw : 64 ≤ w) :
    (w : ℝ) ^ 3 * (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 30 := by
  have h : ((w : ℝ) ^ 3 * 2 ^ 30 : ℝ) ≤ 2 ^ w := by exact_mod_cast cube_mul_le_two_pow hw
  rw [one_div_pow, one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem two_pow_piSteps_le {w : ℕ} (hw : 1 ≤ w) : (2 : ℝ) ^ piSteps w ≤ 2 * w := by
  have h : ((2 ^ Nat.log 2 w : ℕ) : ℝ) ≤ w := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : w ≠ 0)
  unfold piSteps
  rw [pow_succ]
  push_cast at h
  linarith

/-- The width bound of the final bracket. -/
noncomputable def piEps (w : ℕ) : ℝ := 2 ^ 19 * (w : ℝ) ^ 3 * (1 / 2 : ℝ) ^ w

theorem two_pow_le_piEps {w : ℕ} (hw : 1 ≤ w) :
    (2 : ℝ) ^ (3 * piSteps w + 16) * (1 / 2 : ℝ) ^ w ≤ piEps w := by
  have h1 := two_pow_piSteps_le hw
  have h3 : (2 : ℝ) ^ (3 * piSteps w + 16) = 2 ^ 16 * ((2 : ℝ) ^ piSteps w) ^ 3 := by
    rw [pow_add, ← pow_mul, mul_comm (piSteps w) 3, mul_comm]
  have h4 : ((2 : ℝ) ^ piSteps w) ^ 3 ≤ (2 * w) ^ 3 := by gcongr
  unfold piEps
  calc (2 : ℝ) ^ (3 * piSteps w + 16) * (1 / 2 : ℝ) ^ w
      = 2 ^ 16 * ((2 : ℝ) ^ piSteps w) ^ 3 * (1 / 2 : ℝ) ^ w := by rw [h3]
    _ ≤ 2 ^ 16 * (2 * w) ^ 3 * (1 / 2 : ℝ) ^ w := by gcongr
    _ = 2 ^ 19 * (w : ℝ) ^ 3 * (1 / 2 : ℝ) ^ w := by ring

theorem piEps_le {w : ℕ} (hw : 64 ≤ w) : piEps w ≤ 1 / 16 := by
  have h := cube_mul_half_pow_le hw
  unfold piEps
  calc 2 ^ 19 * (w : ℝ) ^ 3 * (1 / 2 : ℝ) ^ w = 2 ^ 19 * ((w : ℝ) ^ 3 * (1 / 2 : ℝ) ^ w) := by
        ring
    _ ≤ 2 ^ 19 * (1 / 2 : ℝ) ^ 30 := by gcongr
    _ ≤ 1 / 16 := by norm_num

theorem piSteps_pow_mul_le {w : ℕ} (hw : 64 ≤ w) :
    (2 : ℝ) ^ (3 * piSteps w + 16) * (1 / 2 : ℝ) ^ w ≤ 1 / 16 :=
  (two_pow_le_piEps (by omega)).trans (piEps_le hw)

theorem tendsto_piEps : Filter.Tendsto piEps Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 3
    (by norm_num : |(1 / 2 : ℝ)| < 1)).const_mul (2 ^ 19 : ℝ)
  rw [mul_zero] at h
  refine h.congr fun w => ?_
  simp only [piEps]
  ring

/-! ### Small helpers -/

theorem toVal_double {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    (x <<< (1 : Nat)).toVal = some ((2 * xv : ℝ) : EReal) := by
  rw [toVal_shiftLeft_nat (isFinite_of_toVal_coe hx), fval_of_toVal_coe hx]
  push_cast
  rw [zpow_one, mul_comm]

theorem toVal_powerOf2_one_sub (w : ℕ) :
    (powerOf2 (1 - (w : AzInt))).toVal = some ((2 * (1 / 2 : ℝ) ^ w : ℝ) : EReal) := by
  rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_natCast]
  have h1 : (1 : AzInt).toInt = 1 := rfl
  rw [h1, zpow_sub₀ (by norm_num), zpow_one, zpow_natCast, one_div_pow, one_div, div_eq_mul_inv]

theorem toInt_natCast_sub_one (n : ℕ) : ((n : AzInt) - 1).toInt = (n : ℤ) - 1 := by
  rw [AzInt.toInt_sub, AzInt.toInt_natCast]; rfl

theorem clampNonneg_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    ∃ cv : ℝ, (clampNonneg x).toVal = some (cv : EReal) ∧ 0 ≤ cv ∧ cv ≤ max xv 0 ∧
      (0 ≤ xv → cv = xv) := by
  obtain ⟨hneg, hnonneg⟩ := toVal_sign_of_isNegative hx
  unfold clampNonneg
  cases hb : x.isNegative with
  | true =>
    simp only [↓reduceIte]
    exact ⟨0, by simp, le_rfl, le_max_right _ _, fun h => absurd (hneg hb) (not_lt.mpr h)⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨xv, hx, hnonneg hb, le_max_left _ _, fun _ => rfl⟩

theorem mul_le_one_of {x y : ℝ} (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1) : x * y ≤ 1 := by
  nlinarith

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-! ### The three building blocks of a step

Throughout, `u = 2^(−w)` and `W = (a⁺ − a⁻) + (b⁺ − b⁻)`; the true values satisfy
`2/3 < b ≤ a ≤ 1`, and `W ≤ 1/16`, `u ≤ 1/4096`. -/

variable {w : ℕ} [NeZero w] {aLo aHi bLo bHi : AzFloat} {al ah bl bh a b : ℝ}

/-- The arithmetic mean: `[⌊a⁻ + b⁻⌋/2, ⌈a⁺ + b⁺⌉/2]` encloses `(a + b)/2`, width
`≤ W/2 + 5u`. -/
theorem mean_step (hal : aLo.toVal = some (al : EReal)) (hah : aHi.toVal = some (ah : EReal))
    (hbl : bLo.toVal = some (bl : EReal)) (hbh : bHi.toVal = some (bh : EReal))
    (hal0 : 0 ≤ al) (hala : al ≤ a) (haah : a ≤ ah) (hbl0 : 0 ≤ bl) (hblb : bl ≤ b)
    (hbbh : b ≤ bh) (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hW : (ah - al) + (bh - bl) ≤ 1 / 16) :
    ∃ r1 r2 : ℝ,
      ((addPrecRound aLo bLo w .Floor).1 >>> (1 : Nat)).toVal = some ((r1 / 2 : ℝ) : EReal) ∧
      ((addPrecRound aHi bHi w .Ceiling).1 >>> (1 : Nat)).toVal = some ((r2 / 2 : ℝ) : EReal) ∧
      0 ≤ r1 / 2 ∧ r1 / 2 ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ r2 / 2 ∧
      r2 / 2 - r1 / 2 ≤ ((ah - al) + (bh - bl)) / 2 + 5 * (1 / 2 : ℝ) ^ w := by
  obtain ⟨r1, hr1, hf1⟩ := addFloor_err hal hbl w (by linarith)
  obtain ⟨r2, hr2, hc2⟩ := addCeiling_err hah hbh w (by linarith)
  have hr1ge := hf1.ge_of_le (B := 2) (by linarith)
  have hr2le := hc2.le_of_le (B := 3) (by linarith)
  have hf1le := hf1.le
  have hc2ge := hc2.ge
  exact ⟨r1, r2, toVal_half hr1, toVal_half hr2, by linarith [hf1.nonneg], by linarith,
    by linarith, by linarith⟩

/-- The geometric mean: `[⌊√⌊a⁻ b⁻⌋⌋, ⌈√⌈a⁺ b⁺⌉⌉]` encloses `√(ab)`, width `≤ 2W + 16u`. -/
theorem geo_step (hal : aLo.toVal = some (al : EReal)) (hah : aHi.toVal = some (ah : EReal))
    (hbl : bLo.toVal = some (bl : EReal)) (hbh : bHi.toVal = some (bh : EReal))
    (hala : al ≤ a) (haah : a ≤ ah) (hblb : bl ≤ b) (hbbh : b ≤ bh) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hal23 : 29 / 48 ≤ al) (hbl23 : 29 / 48 ≤ bl) (hW : (ah - al) + (bh - bl) ≤ 1 / 16)
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 4096) :
    ∃ q1 q2 : ℝ,
      (sqrtPrecRound (mulPrecRound aLo bLo w .Floor).1 w .Floor).1.toVal = some (q1 : EReal) ∧
      (sqrtPrecRound (mulPrecRound aHi bHi w .Ceiling).1 w .Ceiling).1.toVal
        = some (q2 : EReal) ∧
      0 ≤ q1 ∧ q1 ≤ Real.sqrt (a * b) ∧ Real.sqrt (a * b) ≤ q2 ∧
      q2 - q1 ≤ 2 * ((ah - al) + (bh - bl)) + 16 * (1 / 2 : ℝ) ^ w := by
  have hu0 : 0 ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hal0 : 0 ≤ al := by linarith
  have hbl0 : 0 ≤ bl := by linarith
  have hWa : 0 ≤ ah - al := by linarith
  have hWb : 0 ≤ bh - bl := by linarith
  have hal1 : al ≤ 1 := by linarith
  have hbl1 : bl ≤ 1 := by linarith
  have hah1 : ah ≤ 1 + 1 / 16 := by linarith
  have hbh1 : bh ≤ 1 + 1 / 16 := by linarith
  have hah0 : 0 ≤ ah := by linarith
  have hbh0 : 0 ≤ bh := by linarith
  -- the product
  obtain ⟨m1, hm1, hfm1⟩ := mulFloor_err hal hbl w (mul_nonneg hal0 hbl0)
  obtain ⟨m2, hm2, hcm2⟩ := mulCeiling_err hah hbh w (mul_nonneg hah0 hbh0)
  have hab1 : al * bl ≤ 1 := mul_le_one_of hal1 hbl0 hbl1
  have hab2 : ah * bh ≤ (1 + 1 / 16) * (1 + 1 / 16) := mul_le_mul hah1 hbh1 hbh0 (by norm_num)
  have hablo : 29 / 48 * (29 / 48) ≤ al * bl := mul_le_mul hal23 hbl23 (by norm_num) hal0
  have hab12 : al * bl ≤ ah * bh := mul_le_mul (by linarith) (by linarith) hbl0 hah0
  have hm1ge := hfm1.ge_of_le (B := 1) hab1
  have hm2le := hcm2.le_of_le (B := 2) (by linarith)
  have hfm1le := hfm1.le
  have hcm2ge := hcm2.ge
  have hm1lo : 9 / 25 ≤ m1 := by linarith
  have hm1le1 : m1 ≤ 1 := by linarith
  have hm2le4 : m2 ≤ 4 := by linarith
  have hm2nn : 0 ≤ m2 := by linarith [mul_nonneg hah0 hbh0]
  have hm12 : m1 ≤ m2 := by linarith
  have hm1nn := hfm1.nonneg
  -- the square roots
  obtain ⟨q1, hq1, hfq1⟩ := sqrtFloor_err hm1 hm1nn w
  obtain ⟨q2, hq2, hcq2⟩ := sqrtCeiling_err hm2 hm2nn w
  have hsqrt_m1 : 3 / 5 ≤ Real.sqrt m1 := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hsq1 : Real.sqrt m1 ≤ 1 := by
    have := Real.sqrt_le_sqrt hm1le1; rwa [Real.sqrt_one] at this
  have hsq2 : Real.sqrt m2 ≤ 2 := by
    have := Real.sqrt_le_sqrt hm2le4; rwa [sqrt_four] at this
  have hq1ge := hfq1.ge_of_le (B := 1) hsq1
  have hq2le := hcq2.le_of_le (B := 2) hsq2
  have hsqdiff : (Real.sqrt m2 - Real.sqrt m1) * (3 / 5) ≤ m2 - m1 := by
    have hle := Real.sqrt_le_sqrt hm12
    have key : (Real.sqrt m2 - Real.sqrt m1) * (Real.sqrt m2 + Real.sqrt m1) = m2 - m1 := by
      ring_nf
      rw [Real.sq_sqrt hm2nn, Real.sq_sqrt hm1nn]
    have h1 : (Real.sqrt m2 - Real.sqrt m1) * (3 / 5)
        ≤ (Real.sqrt m2 - Real.sqrt m1) * (Real.sqrt m2 + Real.sqrt m1) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg m2]) (by linarith)
    linarith
  have hm2m1 : m2 - m1 ≤ (1 + 1 / 16) * (bh - bl) + (ah - al) + 6 * (1 / 2 : ℝ) ^ w := by
    have e0 : ah * bh - al * bl = ah * (bh - bl) + bl * (ah - al) := by ring
    have e1 : ah * (bh - bl) ≤ (1 + 1 / 16) * (bh - bl) := mul_le_mul_of_nonneg_right hah1 hWb
    have e2 : bl * (ah - al) ≤ 1 * (ah - al) := mul_le_mul_of_nonneg_right hbl1 hWa
    linarith
  refine ⟨q1, q2, hq1, hq2, hfq1.nonneg, ?_, ?_, ?_⟩
  · exact hfq1.le.trans (Real.sqrt_le_sqrt (hfm1le.trans (mul_le_mul hala hblb hbl0 (by linarith))))
  · exact (Real.sqrt_le_sqrt ((mul_le_mul haah hbbh (by linarith) hah0).trans hcm2ge)).trans
      hcq2.ge
  · have hsqdiff' : Real.sqrt m2 - Real.sqrt m1 ≤ (m2 - m1) * (5 / 3) := by linarith
    linarith

/-- The squared half-difference: `[⌊(max(⌊a⁻ − b⁺⌋, 0))²⌋, ⌈⌈a⁺ − b⁻⌉²⌉]` encloses `(a − b)²`,
width `≤ 4W + 12u`. -/
theorem diffsq_step (hal : aLo.toVal = some (al : EReal)) (hah : aHi.toVal = some (ah : EReal))
    (hbl : bLo.toVal = some (bl : EReal)) (hbh : bHi.toVal = some (bh : EReal))
    (hala : al ≤ a) (haah : a ≤ ah) (hblb : bl ≤ b) (hbbh : b ≤ bh) (ha1 : a ≤ 1)
    (hb23 : 2 / 3 < b) (hba : b ≤ a) (hW : (ah - al) + (bh - bl) ≤ 1 / 16)
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 4096) :
    ∃ e1 e2 : ℝ,
      (sqrPrecRound (clampNonneg (subPrecRound aLo bHi w .Floor).1) w .Floor).1.toVal
        = some (e1 : EReal) ∧
      (sqrPrecRound (subPrecRound aHi bLo w .Ceiling).1 w .Ceiling).1.toVal
        = some (e2 : EReal) ∧
      0 ≤ e1 ∧ e1 ≤ (a - b) ^ 2 ∧ (a - b) ^ 2 ≤ e2 ∧
      e2 - e1 ≤ 4 * ((ah - al) + (bh - bl)) + 12 * (1 / 2 : ℝ) ^ w := by
  have hu0 : 0 ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hWa : 0 ≤ ah - al := by linarith
  have hWb : 0 ≤ bh - bl := by linarith
  have hg0 : 0 ≤ a - b := by linarith
  have hg13 : a - b ≤ 1 / 3 := by linarith
  have hgW : a - b ≤ ah - bl := by linarith
  obtain ⟨d2, hd2, hcd2⟩ := subCeiling_err hah hbl w (by linarith)
  have hd2le := hcd2.le_of_le (B := 1) (by linarith)
  have hd2ge : a - b ≤ d2 := hgW.trans hcd2.ge
  have hd2one : d2 ≤ 1 := by linarith
  have hc : ∃ c : ℝ, (clampNonneg (subPrecRound aLo bHi w .Floor).1).toVal = some (c : EReal) ∧
      0 ≤ c ∧ c ≤ a - b ∧ d2 - c ≤ 2 * ((ah - al) + (bh - bl)) + 4 * (1 / 2 : ℝ) ^ w := by
    by_cases hpos : 0 ≤ al - bh
    · obtain ⟨d1, hd1, hfd1⟩ := subFloor_err hal hbh w hpos
      obtain ⟨c, hcv, -, -, hceq⟩ := clampNonneg_spec hd1
      have hcd := hceq hfd1.nonneg
      subst hcd
      refine ⟨c, hcv, hfd1.nonneg, by linarith [hfd1.le], ?_⟩
      have := hfd1.ge_of_le (B := 1) (by linarith)
      linarith
    · obtain ⟨d1, hd1, hd1le, -⟩ := subFloor_le hal hbh w
      obtain ⟨c, hcv, hc0, hcle, -⟩ := clampNonneg_spec hd1
      have hneg := not_le.mp hpos
      have hd1neg : d1 < 0 := by linarith
      have hcz : c ≤ 0 := by rw [max_eq_right hd1neg.le] at hcle; exact hcle
      refine ⟨c, hcv, hc0, by linarith, ?_⟩
      have : a - b ≤ (ah - al) + (bh - bl) := by linarith
      linarith
  obtain ⟨c, hcv, hc0, hcg, hd2c⟩ := hc
  obtain ⟨e1, he1, hfe1⟩ := sqrFloor_err hcv w
  obtain ⟨e2, he2, hce2⟩ := sqrCeiling_err hd2 w
  have hcc : c * c ≤ 1 := mul_le_one_of (by linarith) hc0 (by linarith)
  have hdd : d2 * d2 ≤ 1 := mul_le_one_of hd2one (by linarith) hd2one
  have he1ge := hfe1.ge_of_le (B := 1) hcc
  have he2le := hce2.le_of_le (B := 1) hdd
  have hgsq : (a - b) ^ 2 = (a - b) * (a - b) := sq _
  refine ⟨e1, e2, he1, he2, hfe1.nonneg, ?_, ?_, ?_⟩
  · rw [hgsq]; exact hfe1.le.trans (mul_le_mul hcg hcg hc0 hg0)
  · rw [hgsq]; exact (mul_le_mul hd2ge hd2ge hg0 (by linarith)).trans hce2.ge
  · have e0 : d2 * d2 - c * c = (d2 - c) * (d2 + c) := by ring
    have h1 : (d2 - c) * (d2 + c) ≤ (2 * ((ah - al) + (bh - bl)) + 4 * (1 / 2 : ℝ) ^ w) * 2 :=
      mul_le_mul hd2c (by linarith) (by linarith) (by positivity)
    have hfe1le := hfe1.le
    have hce2ge := hce2.ge
    linarith

/-! ### The enclosure invariant -/

/-- After `n` steps at precision `w`: the ends enclose `a_n`, `b_n`, `s_n`, the lower ends are
nonnegative, and the widths are bounded. -/
def PiEncloses (w n : ℕ) (s : PiBounds) : Prop :=
  ∃ al ah bl bh sl sh : ℝ,
    s.aLo.toVal = some (al : EReal) ∧ s.aHi.toVal = some (ah : EReal) ∧
    s.bLo.toVal = some (bl : EReal) ∧ s.bHi.toVal = some (bh : EReal) ∧
    s.sLo.toVal = some (sl : EReal) ∧ s.sHi.toVal = some (sh : EReal) ∧
    0 ≤ al ∧ al ≤ sA n ∧ sA n ≤ ah ∧ 0 ≤ bl ∧ bl ≤ sB n ∧ sB n ≤ bh ∧
    0 ≤ sl ∧ sl ≤ salaminS n ∧ salaminS n ≤ sh ∧
    (ah - al) + (bh - bl) ≤ 2 ^ (2 * n + 4) * (1 / 2 : ℝ) ^ w ∧
    sh - sl ≤ 2 ^ (3 * n + 7) * (1 / 2 : ℝ) ^ w

theorem piEncloses_init (w : ℕ) [NeZero w] : PiEncloses w 0 (piInit w) := by
  have hb0 : salaminB0 = Real.sqrt 2 / 2 := by rw [salaminB0, one_div, inv_sqrt_eq]
  have hx0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h0 := Real.sqrt_nonneg 2
    nlinarith
  have hfl := sqrt2Over2PrecRound_eq_liftVal₀ w .Floor
  have hce := sqrt2Over2PrecRound_eq_liftVal₀ w .Ceiling
  unfold liftVal₀ at hfl hce
  obtain ⟨bl, hbl, hfbl⟩ := roundVal_floor_err w hx0
  obtain ⟨bh, hbh, hcbh⟩ := roundVal_ceiling_err w hx0
  rw [← hfl] at hbl
  rw [← hce] at hbh
  have hu : 0 ≤ (1 / 2 : ℝ) ^ w := by positivity
  refine ⟨1, 1, bl, bh, 1 / 2, 1 / 2, toVal_one', toVal_one', hbl, hbh, toVal_oneHalf,
    toVal_oneHalf, zero_le_one, ?_, ?_, hfbl.nonneg, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp [agmA_zero]
  · simp [agmA_zero]
  · rw [agmB_zero, hb0]; exact hfbl.le
  · rw [agmB_zero, hb0]; exact hcbh.ge
  · rw [salaminS_zero]
  · rw [salaminS_zero]
  · have h1 := hfbl.ge_of_le (B := 1) (by linarith)
    have h2 := hcbh.le_of_le (B := 1) (by linarith)
    have : (2 : ℝ) ^ (2 * 0 + 4) = 16 := by norm_num
    rw [this]
    linarith
  · simp only [sub_self]; positivity

theorem piEncloses_step {w : ℕ} [NeZero w] (hw : 64 ≤ w) {n : ℕ} (hn : n < piSteps w)
    {s : PiBounds} (h : PiEncloses w n s) : PiEncloses w (n + 1) (piStep w n s) := by
  obtain ⟨al, ah, bl, bh, sl, sh, hal, hah, hbl, hbh, hsl, hsh, hal0, hala, hahA, hbl0, hblb,
    hbhB, hsl0, hsls, hshS, hW, hWs⟩ := h
  have hu : 0 < (1 / 2 : ℝ) ^ w := by positivity
  obtain ⟨hb23, hba, ha1⟩ := salamin_facts n
  have hS3 := salaminS_gt n
  have hS2 := salaminS_le_half n
  have hS3' := salaminS_gt (n + 1)
  have hSsucc := salaminS_succ n
  -- smallness
  have hsmall := piSteps_pow_mul_le hw
  have hpowle : ∀ k, k ≤ 3 * piSteps w + 16 → (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ w ≤ 1 / 16 :=
    fun k hk =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hk) hu.le).trans hsmall
  have hW16 : (ah - al) + (bh - bl) ≤ 1 / 16 := hW.trans (hpowle _ (by omega))
  have hWs16 : sh - sl ≤ 1 / 16 := hWs.trans (hpowle _ (by omega))
  have hu4096 : (1 / 2 : ℝ) ^ w ≤ 1 / 4096 := by
    have := hpowle 8 (by omega)
    norm_num at this
    linarith
  have hb1 : sB n ≤ 1 := hba.trans ha1
  -- the three blocks
  obtain ⟨r1, r2, hr1, hr2, hr10, hr1A, hr2A, hWa'⟩ :=
    mean_step (w := w) hal hah hbl hbh hal0 hala hahA hbl0 hblb hbhB ha1 hb1 hW16
  obtain ⟨q1, q2, hq1, hq2, hq10, hq1B, hq2B, hWb'⟩ :=
    geo_step (w := w) hal hah hbl hbh hala hahA hblb hbhB ha1 hb1 (by linarith) (by linarith)
      hW16 hu4096
  obtain ⟨e1, e2, he1, he2, he10, he1g, he2g, he21⟩ :=
    diffsq_step (w := w) hal hah hbl hbh hala hahA hblb hbhB ha1 hb23 hba hW16 hu4096
  -- the scaled squares
  have hPdef : (2 : ℝ) ^ ((n : ℤ) - 1) = 2 ^ n / 2 := by
    rw [zpow_sub_one₀ (by norm_num), zpow_natCast]; ring
  have htLo := toVal_shiftLeft_of_toVal he1 ((n : AzInt) - 1)
  have htHi := toVal_shiftLeft_of_toVal he2 ((n : AzInt) - 1)
  rw [toInt_natCast_sub_one, hPdef] at htLo htHi
  have hQ0 : 0 < (2 : ℝ) ^ n / 2 := by positivity
  have htn : (2 : ℝ) ^ (n + 1) * ((sA n - sB n) / 2) ^ 2 = (sA n - sB n) ^ 2 * (2 ^ n / 2) := by
    ring
  have htLo_le : e1 * (2 ^ n / 2) ≤ (2 : ℝ) ^ (n + 1) * ((sA n - sB n) / 2) ^ 2 := by
    rw [htn]; exact mul_le_mul_of_nonneg_right he1g hQ0.le
  have htHi_ge : (2 : ℝ) ^ (n + 1) * ((sA n - sB n) / 2) ^ 2 ≤ e2 * (2 ^ n / 2) := by
    rw [htn]; exact mul_le_mul_of_nonneg_right he2g hQ0.le
  have htW : e2 * (2 ^ n / 2) - e1 * (2 ^ n / 2) ≤ 2 ^ (3 * n + 6) * (1 / 2 : ℝ) ^ w := by
    have e0 : e2 * (2 ^ n / 2) - e1 * (2 ^ n / 2) = (e2 - e1) * (2 ^ n / 2) := by ring
    have h6 : (6 : ℝ) * 2 ^ n ≤ 2 ^ (3 * n + 5) := by
      calc (6 : ℝ) * 2 ^ n ≤ 2 ^ 5 * 2 ^ n := by
            have : (0 : ℝ) < 2 ^ n := by positivity
            linarith
        _ = 2 ^ (5 + n) := by rw [pow_add]
        _ ≤ 2 ^ (3 * n + 5) := pow_le_pow_right₀ one_le_two (by omega)
    have h2 : (2 : ℝ) ^ (3 * n + 6) = 2 * 2 ^ (3 * n + 5) := by rw [pow_succ]; ring
    rw [e0, h2]
    calc (e2 - e1) * (2 ^ n / 2)
        ≤ (4 * (2 ^ (2 * n + 4) * (1 / 2 : ℝ) ^ w) + 12 * (1 / 2 : ℝ) ^ w) * (2 ^ n / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hQ0.le
      _ = (2 ^ (3 * n + 5) + 6 * 2 ^ n) * (1 / 2 : ℝ) ^ w := by ring
      _ ≤ (2 ^ (3 * n + 5) + 2 ^ (3 * n + 5)) * (1 / 2 : ℝ) ^ w := by gcongr
      _ = 2 * 2 ^ (3 * n + 5) * (1 / 2 : ℝ) ^ w := by ring
  have htW16 : (2 : ℝ) ^ (3 * n + 6) * (1 / 2 : ℝ) ^ w ≤ 1 / 16 := hpowle _ (by omega)
  -- the new `s`
  have hsl1 : 0 ≤ sl - e2 * (2 ^ n / 2) := by linarith
  obtain ⟨s1, hs1, hfs1⟩ := subFloor_err hsl htHi w hsl1
  have htLo0 : 0 ≤ e1 * (2 ^ n / 2) := mul_nonneg he10 hQ0.le
  have htn0 : 0 ≤ (2 : ℝ) ^ (n + 1) * ((sA n - sB n) / 2) ^ 2 := by positivity
  obtain ⟨s2, hs2, hcs2⟩ := subCeiling_err hsh htLo w (by linarith)
  have hs1ge := hfs1.ge_of_le (B := 1) (by linarith)
  have hs2le := hcs2.le_of_le (B := 1) (by linarith)
  have hfs1le := hfs1.le
  have hcs2ge := hcs2.ge
  -- assemble
  refine ⟨r1 / 2, r2 / 2, q1, q2, s1, s2, hr1, hr2, hq1, hq2, hs1, hs2, hr10, ?_, ?_, hq10, ?_,
    ?_, hfs1.nonneg, ?_, ?_, ?_, ?_⟩
  · rw [agmA_succ]; exact hr1A
  · rw [agmA_succ]; exact hr2A
  · rw [agmB_succ]; exact hq1B
  · rw [agmB_succ]; exact hq2B
  · rw [hSsucc]; linarith
  · rw [hSsucc]; linarith
  · -- the width of the AGM enclosure
    have hX : (16 : ℝ) ≤ 2 ^ (2 * n + 4) := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * n + 4) := pow_le_pow_right₀ one_le_two (by omega)
    have hXu : 16 * (1 / 2 : ℝ) ^ w ≤ 2 ^ (2 * n + 4) * (1 / 2 : ℝ) ^ w :=
      mul_le_mul_of_nonneg_right hX hu.le
    have h2 : (2 : ℝ) ^ (2 * (n + 1) + 4) = 4 * 2 ^ (2 * n + 4) := by
      rw [show 2 * (n + 1) + 4 = (2 * n + 4) + 2 by ring, pow_add]; ring
    rw [h2]
    linarith
  · -- the width of the `s` enclosure
    have hY : (128 : ℝ) ≤ 2 ^ (3 * n + 7) := by
      calc (128 : ℝ) = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (3 * n + 7) := pow_le_pow_right₀ one_le_two (by omega)
    have hYu : 128 * (1 / 2 : ℝ) ^ w ≤ 2 ^ (3 * n + 7) * (1 / 2 : ℝ) ^ w :=
      mul_le_mul_of_nonneg_right hY hu.le
    have h67 : (2 : ℝ) ^ (3 * n + 6) * (1 / 2 : ℝ) ^ w ≤ 2 ^ (3 * n + 7) * (1 / 2 : ℝ) ^ w :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hu.le
    have h2 : (2 : ℝ) ^ (3 * (n + 1) + 7) = 8 * 2 ^ (3 * n + 7) := by
      rw [show 3 * (n + 1) + 7 = (3 * n + 7) + 3 by ring, pow_add]; ring
    rw [h2]
    linarith

theorem piEncloses_iter {w : ℕ} [NeZero w] (hw : 64 ≤ w) :
    ∀ n, n ≤ piSteps w → PiEncloses w n (piIter w n (piInit w))
  | 0, _ => piEncloses_init w
  | n + 1, hn => piEncloses_step hw (by omega) (piEncloses_iter hw n (by omega))

/-! ### The final bracket -/

/-- `piBracket w` brackets `π`, strictly from below, with width at most `piEps w`. -/
theorem piBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, (piBracket w).1.toVal = some (lv : EReal) ∧
      (piBracket w).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv < Real.pi ∧ Real.pi ≤ hv ∧ hv - lv ≤ piEps w := by
  have : NeZero w := ⟨by omega⟩
  have hN1 : 1 ≤ piSteps w := one_le_piSteps w
  obtain ⟨al, ah, bl, bh, sl, sh, hal, hah, hbl, hbh, hsl, hsh, hal0, hala, hahA, hbl0, hblb,
    hbhB, hsl0, hsls, hshS, hW, hWs⟩ := piEncloses_iter hw (piSteps w) le_rfl
  have hu : 0 < (1 / 2 : ℝ) ^ w := by positivity
  have hsmall := piSteps_pow_mul_le hw
  have hpowle : ∀ k, k ≤ 3 * piSteps w + 16 → (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ w ≤ 1 / 16 :=
    fun k hk =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hk) hu.le).trans hsmall
  have hW16 : (ah - al) + (bh - bl) ≤ 1 / 16 := hW.trans (hpowle _ (by omega))
  have hWs16 : sh - sl ≤ 1 / 16 := hWs.trans (hpowle _ (by omega))
  have hu4096 : (1 / 2 : ℝ) ^ w ≤ 1 / 4096 := by
    have := hpowle 8 (by omega)
    norm_num at this
    linarith
  obtain ⟨hb23, hba, ha1⟩ := salamin_facts (piSteps w)
  have hb1 : sB (piSteps w) ≤ 1 := hba.trans ha1
  have hS3 := salaminS_gt (piSteps w)
  have hS2 := salaminS_le_half (piSteps w)
  have hpi := abs_salaminApprox_piSteps_sub_pi_le w (by omega)
  rw [abs_le] at hpi
  obtain ⟨hpi1, hpi2⟩ := hpi
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hWa : 0 ≤ ah - al := by linarith
  have hWb : 0 ≤ bh - bl := by linarith
  have hWs0 : 0 ≤ sh - sl := by linarith
  -- `a_{N+1}`
  obtain ⟨r1, r2, hr1, hr2, hr10, hr1A, hr2A, hWa'⟩ :=
    mean_step (w := w) hal hah hbl hbh hal0 hala hahA hbl0 hblb hbhB ha1 hb1 hW16
  rw [← agmA_succ] at hr1A hr2A
  have hA1le : sA (piSteps w + 1) ≤ 1 := salamin_agmA_le_one (by omega)
  have hA0 : 0 < sA (piSteps w + 1) := (salamin_agm_pos _).1
  have hr2le1 : r2 / 2 ≤ 1 + 1 / 16 := by linarith
  -- `2 a_{N+1}²`
  obtain ⟨e1, he1, hfe1⟩ := sqrFloor_err hr1 w
  obtain ⟨e2, he2, hce2⟩ := sqrCeiling_err hr2 w
  have hr1sq1 : r1 / 2 * (r1 / 2) ≤ 1 := mul_le_one_of (by linarith) hr10 (by linarith)
  have hr2sq : r2 / 2 * (r2 / 2) ≤ (1 + 1 / 16) * (1 + 1 / 16) :=
    mul_le_mul hr2le1 hr2le1 (by linarith) (by norm_num)
  have he1ge := hfe1.ge_of_le (B := 1) hr1sq1
  have he2le := hce2.le_of_le (B := 2) (by linarith)
  have hnLo := toVal_double he1
  have hnHi := toVal_double he2
  have hsq1 : r1 / 2 * (r1 / 2) ≤ sA (piSteps w + 1) ^ 2 := by
    rw [sq]; exact mul_le_mul hr1A hr1A hr10 hA0.le
  have hsq2 : sA (piSteps w + 1) ^ 2 ≤ r2 / 2 * (r2 / 2) := by
    rw [sq]; exact mul_le_mul hr2A hr2A hA0.le (by linarith)
  have he1A : e1 ≤ sA (piSteps w + 1) ^ 2 := hfe1.le.trans hsq1
  have he2A : sA (piSteps w + 1) ^ 2 ≤ e2 := hsq2.trans hce2.ge
  have he21 : e2 - e1 ≤ 2 * ((ah - al) + (bh - bl)) + 17 * (1 / 2 : ℝ) ^ w := by
    have e0 : r2 / 2 * (r2 / 2) - r1 / 2 * (r1 / 2) = (r2 / 2 - r1 / 2) * (r2 / 2 + r1 / 2) := by
      ring
    have h1 : (r2 / 2 - r1 / 2) * (r2 / 2 + r1 / 2)
        ≤ (((ah - al) + (bh - bl)) / 2 + 5 * (1 / 2 : ℝ) ^ w) * (33 / 16) :=
      mul_le_mul hWa' (by linarith) (by linarith) (by positivity)
    have hfe1le := hfe1.le
    have hce2ge := hce2.ge
    linarith
  have he10 : 0 ≤ e1 := hfe1.nonneg
  have he2le12 : e2 ≤ 6 / 5 := by linarith
  have he12 : e1 ≤ e2 := he1A.trans he2A
  -- the quotient
  have hsl14 : 1 / 4 ≤ sl := by linarith
  have hsh13 : 1 / 3 < sh := by linarith
  have hsl1 : sl ≤ 1 := by linarith
  have hsl0' : 0 < sl := by linarith
  have hsh0' : 0 < sh := by linarith
  obtain ⟨p1, hp1, hfp1⟩ := divFloor_err hnLo hsh hsh0' (by linarith) w
  obtain ⟨p2, hp2, hcp2⟩ := divCeiling_err hnHi hsl hsl0' (by linarith) w
  have hq1 : 2 * e1 / sh ≤ salaminApprox (piSteps w) := by
    unfold salaminApprox
    rw [div_le_div_iff₀ hsh0' (by linarith)]
    exact mul_le_mul (by linarith) hshS (by linarith) (by positivity)
  have hq2 : salaminApprox (piSteps w) ≤ 2 * e2 / sl := by
    unfold salaminApprox
    rw [div_le_div_iff₀ (by linarith) hsl0']
    exact mul_le_mul (by linarith) hsls hsl0'.le (by linarith)
  have hq2le : 2 * e2 / sl ≤ 10 := by
    rw [div_le_iff₀ hsl0']; linarith
  have hq10 : 0 ≤ 2 * e1 / sh := by positivity
  have hp1ge := hfp1.ge_of_le (B := 5) (by linarith)
  have hp2le := hcp2.le_of_le (B := 10) hq2le
  have hfp1le := hfp1.le
  have hcp2ge := hcp2.ge
  have hqW : 2 * e2 / sl - 2 * e1 / sh
      ≤ 32 * (sh - sl) + 12 * (2 * e2 - 2 * e1) := by
    rw [div_sub_div _ _ hsl0'.ne' hsh0'.ne', div_le_iff₀ (mul_pos hsl0' hsh0')]
    have e0 : 2 * e2 * sh - sl * (2 * e1) = 2 * e2 * (sh - sl) + sl * (2 * e2 - 2 * e1) := by
      ring
    have h1 : 2 * e2 * (sh - sl) ≤ 12 / 5 * (sh - sl) :=
      mul_le_mul_of_nonneg_right (by linarith) hWs0
    have h2 : sl * (2 * e2 - 2 * e1) ≤ 1 * (2 * e2 - 2 * e1) :=
      mul_le_mul_of_nonneg_right hsl1 (by linarith)
    have hprod : 1 / 12 ≤ sl * sh := by
      have := mul_le_mul hsl14 hsh13.le (by norm_num : (0 : ℝ) ≤ 1 / 3) hsl0'.le
      linarith only [this]
    have hC : 0 ≤ 32 * (sh - sl) + 12 * (2 * e2 - 2 * e1) := by linarith only [hWs0, he12]
    have h3 : (32 * (sh - sl) + 12 * (2 * e2 - 2 * e1)) * (1 / 12)
        ≤ (32 * (sh - sl) + 12 * (2 * e2 - 2 * e1)) * (sl * sh) :=
      mul_le_mul_of_nonneg_left hprod hC
    linarith only [e0, h1, h2, h3, hWs0]
  -- the powers
  have hX : (2 : ℝ) ^ (2 * piSteps w + 4) * 48 ≤ 2 ^ (3 * piSteps w + 7) * 8 := by
    have h8 : (2 : ℝ) ^ (2 * piSteps w + 4) * 8 ≤ 2 ^ (3 * piSteps w + 7) := by
      calc (2 : ℝ) ^ (2 * piSteps w + 4) * 8 = 2 ^ (2 * piSteps w + 7) := by ring
        _ ≤ 2 ^ (3 * piSteps w + 7) := pow_le_pow_right₀ one_le_two (by omega)
    have hpos : (0 : ℝ) ≤ 2 ^ (3 * piSteps w + 7) := by positivity
    linarith only [h8, hpos]
  have hY : (512 : ℝ) ≤ 2 ^ (3 * piSteps w + 7) := by
    calc (512 : ℝ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ (3 * piSteps w + 7) := pow_le_pow_right₀ one_le_two (by omega)
  have hXu := mul_le_mul_of_nonneg_right hX hu.le
  have hYu := mul_le_mul_of_nonneg_right hY hu.le
  have hbig : (2 : ℝ) ^ (3 * piSteps w + 7) * 64 * (1 / 2 : ℝ) ^ w
      ≤ 2 ^ (3 * piSteps w + 16) * (1 / 2 : ℝ) ^ w := by
    apply mul_le_mul_of_nonneg_right _ hu.le
    calc (2 : ℝ) ^ (3 * piSteps w + 7) * 64 = 2 ^ (3 * piSteps w + 13) := by ring
      _ ≤ 2 ^ (3 * piSteps w + 16) := pow_le_pow_right₀ one_le_two (by omega)
  have hXpos : 0 ≤ (2 : ℝ) ^ (3 * piSteps w + 7) * (1 / 2 : ℝ) ^ w := by positivity
  have hp21 : p2 - p1 ≤ 2 ^ (3 * piSteps w + 7) * 44 * (1 / 2 : ℝ) ^ w := by
    linarith only [hp2le, hp1ge, hqW, he21, hW, hWs, hXu, hYu, hu.le]
  have hp21_16 : p2 - p1 ≤ 1 / 16 := by
    linarith only [hp21, hbig, hsmall, hXpos]
  have hqlow : salaminApprox (piSteps w) - 1 / 16 ≤ 2 * e1 / sh := by
    linarith only [hqW, hq2, he21, hW, hWs, hXu, hYu, hbig, hsmall, hu.le, hXpos]
  -- the widening by `2^(1−w)`
  have hpow := toVal_powerOf2_one_sub w
  have hp1pos : 0 ≤ p1 - 2 * (1 / 2 : ℝ) ^ w := by
    linarith only [hp1ge, hqlow, hpi1, hpi3, hu4096]
  obtain ⟨lv, hlv, hflv⟩ := subFloor_err hp1 hpow w hp1pos
  obtain ⟨hv, hhv, hchv⟩ := addCeiling_err hp2 hpow w
    (by linarith only [hcp2ge, hq2, hpi1, hpi3, hu.le])
  have hlvge := hflv.ge_of_le (B := 5) (by linarith only [hfp1le, hq1, hpi2, hpi4, hu.le])
  have hhvle := hchv.le_of_le (B := 12) (by linarith only [hp2le, hq2le, hu4096])
  have hflvle := hflv.le
  have hchvge := hchv.ge
  refine ⟨lv, hv, hlv, hhv, hflv.nonneg, by linarith only [hflvle, hfp1le, hq1, hpi2, hu],
    by linarith only [hchvge, hcp2ge, hq2, hpi1, hu.le], ?_⟩
  have := two_pow_le_piEps (w := w) (by omega)
  linarith only [hhvle, hlvge, hp21, hYu, hbig, this, hXpos, hu.le]

/-- `piApprox w` brackets `π`, strictly from below, with width at most `piEps w`. -/
theorem piApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (piApprox w).1 lv ∧ Rounds (piApprox w).2 hv ∧
      lv < Real.pi ∧ Real.pi ≤ hv ∧ hv - lv ≤ piEps w := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwidth⟩ := piBracket_spec hw
  refine ⟨lv, hv, ?_, ?_, hlo, hhi, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR

/-- The Ziv certificate: at some working precision `(p + 64) · 2^f`, rounding is possible. -/
theorem piApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (piApprox (w₀ * 2 ^ f)).1 (piApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode piApprox irrational_pi piEps tendsto_piEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwidth⟩ := piApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi, hwidth⟩) w₀ hw₀

end Azurite.AzFloat
