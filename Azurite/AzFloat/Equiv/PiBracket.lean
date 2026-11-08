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

`piApprox w` brackets `π` (`piApprox_spec`): the invariant `PiPoint` — after `n` rounded-down
steps at precision `w ≥ 64`, the computed `a, b, s` are within `2^(2n+4) 2^(−w)` of `a_n`, `b_n`
and within `2^(3n+7) 2^(−w)` of `s_n` — is preserved by `piStep` (`piPoint_step`, from the three
building blocks `mean_step`, `geo_step`, `diffsq_step`: each operation's rounding is absolutely
small and the step is Lipschitz), the computed `π_N` is within `2^(3N+12) 2^(−w)` of the exact
`π_N` (`piBracketAt_spec`), and the raw bracket `[⌊q − E⌋, ⌈q + E⌉]` with `E = 2^(3N+13) 2^(−w)`
has width at most `2^(3N+16) 2^(−w)`.  Run at `piWork w = w + 3N + 16` bits, this is
`piBracket w`, of width at most `2^(3−w)` (`piBracket_spec_width`; `piWork_le_two_mul`,
`piSteps_piWork_le`) and hence `piEps w = 2^19 w³ 2^(−w) → 0` (`piBracket_spec`,
`tendsto_piEps`).  With `irrational_pi`, this gives the Ziv certificate
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

/-- `piEps` is decreasing from `w = 4` on (`(w+1)³ ≤ 2 w³`). -/
theorem piEps_succ_le {w : ℕ} (hw : 4 ≤ w) : piEps (w + 1) ≤ piEps w := by
  unfold piEps
  have hw' : (4 : ℝ) ≤ w := by exact_mod_cast hw
  have ht : (0 : ℝ) ≤ (w : ℝ) - 4 := by linarith
  have h3 : ((w : ℝ) + 1) ^ 3 ≤ 2 * (w : ℝ) ^ 3 := by
    nlinarith [pow_nonneg ht 3, sq_nonneg ((w : ℝ) - 4), ht]
  have hu : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  push_cast
  rw [pow_succ (1 / 2 : ℝ) w]
  nlinarith [mul_le_mul_of_nonneg_right h3 hu.le]

theorem piEps_antitone {w W : ℕ} (hw : 4 ≤ w) (hW : w ≤ W) : piEps W ≤ piEps w := by
  induction W, hW using Nat.le_induction with
  | base => exact le_rfl
  | succ W hwW ih => exact (piEps_succ_le (by omega)).trans ih

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

Throughout, `u = 2^(−w) ≤ 1/4096` and `W ≤ 1/16` is the current absolute error of `a` and `b`;
the true values satisfy `2/3 < b ≤ a ≤ 1`. -/

variable {w : ℕ} [NeZero w] {aF bF : AzFloat} {av bv a b : ℝ}

/-- The arithmetic mean: `⌊a + b⌋/2` is within `W + 3u` of `(a + b)/2`. -/
theorem mean_step (ha : aF.toVal = some (av : EReal)) (hb : bF.toVal = some (bv : EReal))
    {W : ℝ} (hA : |av - a| ≤ W) (hB : |bv - b| ≤ W) (hW : W ≤ 1 / 16) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hb23 : 2 / 3 < b) (hba : b ≤ a) :
    ∃ r : ℝ, ((addPrecRound aF bF w .Floor).1 >>> (1 : Nat)).toVal = some ((r / 2 : ℝ) : EReal) ∧
      |r / 2 - (a + b) / 2| ≤ W + 3 * (1 / 2 : ℝ) ^ w := by
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  obtain ⟨r, hr, hf⟩ := addFloor_err ha hb w (by linarith)
  have hup := hf.ge_of_le (B := 9 / 4) (by linarith)
  have hle := hf.le
  refine ⟨r, toVal_half hr, ?_⟩
  rw [abs_le]; constructor <;> linarith

/-- The geometric mean: `⌊√⌊ab⌋⌋` is within `4W` of `√(ab)`. -/
theorem geo_step (ha : aF.toVal = some (av : EReal)) (hb : bF.toVal = some (bv : EReal))
    {W : ℝ} (hA : |av - a| ≤ W) (hB : |bv - b| ≤ W) (hW : W ≤ 1 / 16) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hb23 : 2 / 3 < b) (hba : b ≤ a) (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 4096)
    (hWu : 16 * (1 / 2 : ℝ) ^ w ≤ W) :
    ∃ q : ℝ, (sqrtPrecRound (mulPrecRound aF bF w .Floor).1 w .Floor).1.toVal = some (q : EReal) ∧
      |q - Real.sqrt (a * b)| ≤ 4 * W := by
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  have hW0 : 0 ≤ W := by linarith
  have hav0 : 0 ≤ av := by linarith
  have hbv0 : 0 ≤ bv := by linarith
  have hab0 : 0 ≤ a * b := mul_nonneg (by linarith) (by linarith)
  have hAB : 4 / 9 ≤ a * b := by nlinarith
  have hAB1 : a * b ≤ 1 := mul_le_one_of ha1 (by linarith) hb1
  -- the product
  have hp1 : av * bv ≤ a * b + 33 / 16 * W := by
    have : av * bv ≤ (a + W) * (b + W) := mul_le_mul (by linarith) (by linarith) hbv0 (by linarith)
    nlinarith
  have hp2 : a * b - 2 * W ≤ av * bv := by
    have : (a - W) * (b - W) ≤ av * bv := mul_le_mul (by linarith) (by linarith) (by linarith) hav0
    nlinarith
  obtain ⟨m, hm, hfm⟩ := mulFloor_err ha hb w (mul_nonneg hav0 hbv0)
  have hmup := hfm.ge_of_le (B := 2) (by linarith)
  rw [← hu_def] at hmup
  have hmle := hfm.le
  have hm1 : m ≤ a * b + 33 / 16 * W := by linarith
  have hm2 : a * b - 2 * W - 4 * u ≤ m := by linarith
  have hm0 := hfm.nonneg
  have hm2' : m ≤ 4 := by linarith
  -- the square root
  obtain ⟨q, hq, hfq⟩ := sqrtFloor_err hm hm0 w
  have hsm0 := Real.sqrt_nonneg m
  have hsm2 : Real.sqrt m ≤ 2 := by
    have := Real.sqrt_le_sqrt hm2'; rwa [sqrt_four] at this
  have hsAB : 2 / 3 ≤ Real.sqrt (a * b) := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hqup := hfq.ge_of_le (B := 2) hsm2
  rw [← hu_def] at hqup
  have hqle := hfq.le
  -- `|√m − √(ab)| ≤ (3/2)|m − ab|`
  have hkey : (Real.sqrt m - Real.sqrt (a * b)) * (Real.sqrt m + Real.sqrt (a * b))
      = m - a * b := by
    linear_combination Real.sq_sqrt hm0 - Real.sq_sqrt hab0
  have hsum : 2 / 3 ≤ Real.sqrt m + Real.sqrt (a * b) := by linarith
  have hdiff : |Real.sqrt m - Real.sqrt (a * b)| ≤ 3 / 2 * |m - a * b| := by
    have h1 : |Real.sqrt m - Real.sqrt (a * b)| * (2 / 3)
        ≤ |Real.sqrt m - Real.sqrt (a * b)| * (Real.sqrt m + Real.sqrt (a * b)) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    rw [← abs_of_nonneg (by linarith : 0 ≤ Real.sqrt m + Real.sqrt (a * b)), ← abs_mul,
      hkey] at h1
    linarith
  have hmab : |m - a * b| ≤ 33 / 16 * W + 4 * u := by
    rw [abs_le]; constructor <;> linarith
  refine ⟨q, hq, ?_⟩
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
  rw [abs_le]; constructor <;> linarith

/-- The squared difference: `⌊⌊a − b⌋²⌋` is within `2W + 4u` of `(a − b)²`, nonnegative, and at
most `1/2`. -/
theorem diffsq_step (ha : aF.toVal = some (av : EReal)) (hb : bF.toVal = some (bv : EReal))
    {W : ℝ} (hA : |av - a| ≤ W) (hB : |bv - b| ≤ W) (hW : W ≤ 1 / 16) (ha1 : a ≤ 1)
    (hb23 : 2 / 3 < b) (hba : b ≤ a) (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 4096) :
    ∃ e : ℝ, (sqrPrecRound (subPrecRound aF bF w .Floor).1 w .Floor).1.toVal = some (e : EReal) ∧
      0 ≤ e ∧ e ≤ 1 / 2 ∧ |e - (a - b) ^ 2| ≤ 2 * W + 4 * (1 / 2 : ℝ) ^ w := by
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  have hW0 : 0 ≤ W := by linarith
  have hg0 : 0 ≤ a - b := by linarith
  have hg13 : a - b ≤ 1 / 3 := by linarith
  obtain ⟨d, hd, hd1, hd2⟩ := subFloor_abs ha hb w
  rw [← hu_def] at hd2
  have habs : |av - bv| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hd3 : av - bv ≤ d + u := by
    have : 2 * |av - bv| * u ≤ 2 * (1 / 2) * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs (by norm_num)) hu0.le
    linarith
  have hdlo : -(1 / 2) ≤ d := by linarith
  have hdhi : d ≤ 1 / 2 := by linarith
  have hdg : |d - (a - b)| ≤ 2 * W + u := by rw [abs_le]; constructor <;> linarith
  obtain ⟨e, he, hfe⟩ := sqrFloor_err hd w
  have hdd : d * d ≤ 1 / 2 := by nlinarith
  have heup := hfe.ge_of_le (B := 1 / 2) hdd
  rw [← hu_def] at heup
  have hele := hfe.le
  have hsq : |d * d - (a - b) ^ 2| ≤ 2 * W + u := by
    have e0 : d * d - (a - b) ^ 2 = (d - (a - b)) * (d + (a - b)) := by ring
    have h1 : |d + (a - b)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [e0, abs_mul]
    calc |d - (a - b)| * |d + (a - b)| ≤ (2 * W + u) * 1 :=
          mul_le_mul hdg h1 (abs_nonneg _) (by linarith)
      _ = 2 * W + u := mul_one _
  refine ⟨e, he, hfe.nonneg, by linarith, ?_⟩
  obtain ⟨hs1, hs2⟩ := abs_le.mp hsq
  rw [abs_le]; constructor <;> linarith

/-! ### The invariant -/

/-- After `n` rounded-down steps at precision `w`: the computed `a, b, s` are within
`2^(2n+4) 2^(−w)` of `a_n`, `b_n` and within `2^(3n+7) 2^(−w)` of `s_n`. -/
def PiPoint (w n : ℕ) (p : PiPt) : Prop :=
  ∃ av bv sv : ℝ, p.a.toVal = some (av : EReal) ∧ p.b.toVal = some (bv : EReal) ∧
    p.s.toVal = some (sv : EReal) ∧
    |av - sA n| ≤ 2 ^ (2 * n + 4) * (1 / 2 : ℝ) ^ w ∧
    |bv - sB n| ≤ 2 ^ (2 * n + 4) * (1 / 2 : ℝ) ^ w ∧
    |sv - salaminS n| ≤ 2 ^ (3 * n + 7) * (1 / 2 : ℝ) ^ w

theorem piPoint_init (w : ℕ) [NeZero w] : PiPoint w 0 (piInit w) := by
  have hb0 : salaminB0 = Real.sqrt 2 / 2 := by rw [salaminB0, one_div, inv_sqrt_eq]
  have hx0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h0 := Real.sqrt_nonneg 2
    nlinarith
  have hfl := sqrt2Over2PrecRound_eq_liftVal₀ w .Floor
  unfold liftVal₀ at hfl
  obtain ⟨bl, hbl, hfbl⟩ := roundVal_floor_err w hx0
  rw [← hfl] at hbl
  have hu : 0 ≤ (1 / 2 : ℝ) ^ w := by positivity
  refine ⟨1, bl, 1 / 2, toVal_one', hbl, toVal_oneHalf, ?_, ?_, ?_⟩
  · simp [agmA_zero]
  · rw [agmB_zero, hb0]
    have h1 := hfbl.ge_of_le (B := 1) (by linarith)
    have h2 := hfbl.le
    have : (2 : ℝ) ^ (2 * 0 + 4) = 16 := by norm_num
    rw [this, abs_le]; constructor <;> linarith
  · rw [salaminS_zero]; simp

set_option maxHeartbeats 800000 in
theorem piPoint_step {w : ℕ} [NeZero w] (hw : 64 ≤ w) {n : ℕ} (hn : n < piSteps w)
    {p : PiPt} (h : PiPoint w n p) : PiPoint w (n + 1) (piStep w n p) := by
  obtain ⟨av, bv, sv, ha, hb, hs, hA, hB, hS⟩ := h
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  obtain ⟨hb23, hba, ha1⟩ := salamin_facts n
  have hb1 : sB n ≤ 1 := hba.trans ha1
  have hS3 := salaminS_gt n
  have hS2 := salaminS_le_half n
  have hS3' := salaminS_gt (n + 1)
  have hSsucc := salaminS_succ n
  -- smallness
  have hsmall := piSteps_pow_mul_le hw
  have hpowle : ∀ k, k ≤ 3 * piSteps w + 16 → (2 : ℝ) ^ k * u ≤ 1 / 16 :=
    fun k hk =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hk) hu0.le).trans hsmall
  set W := (2 : ℝ) ^ (2 * n + 4) * u with hW_def
  set V := (2 : ℝ) ^ (3 * n + 7) * u with hV_def
  have hW16 : W ≤ 1 / 16 := hpowle _ (by omega)
  have hV16 : V ≤ 1 / 16 := hpowle _ (by omega)
  have hu4096 : u ≤ 1 / 4096 := by
    have := hpowle 8 (by omega)
    norm_num at this
    linarith
  have hWu : 16 * u ≤ W := by
    have : (16 : ℝ) ≤ 2 ^ (2 * n + 4) := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * n + 4) := pow_le_pow_right₀ one_le_two (by omega)
    exact mul_le_mul_of_nonneg_right this hu0.le
  have hVu : 128 * u ≤ V := by
    have : (128 : ℝ) ≤ 2 ^ (3 * n + 7) := by
      calc (128 : ℝ) = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (3 * n + 7) := pow_le_pow_right₀ one_le_two (by omega)
    exact mul_le_mul_of_nonneg_right this hu0.le
  -- the three blocks
  obtain ⟨r, hr, hrA⟩ := mean_step (w := w) ha hb hA hB hW16 ha1 hb1 hb23 hba
  obtain ⟨q, hq, hqB⟩ := geo_step (w := w) ha hb hA hB hW16 ha1 hb1 hb23 hba hu4096 hWu
  obtain ⟨e, he, he0, he12, heg⟩ := diffsq_step (w := w) ha hb hA hB hW16 ha1 hb23 hba hu4096
  -- the scaled square
  have hPdef : (2 : ℝ) ^ ((n : ℤ) - 1) = 2 ^ n / 2 := by
    rw [zpow_sub_one₀ (by norm_num), zpow_natCast]; ring
  have ht := toVal_shiftLeft_of_toVal he ((n : AzInt) - 1)
  rw [toInt_natCast_sub_one, hPdef] at ht
  have hQ0 : 0 < (2 : ℝ) ^ n / 2 := by positivity
  set T := (2 : ℝ) ^ (n + 1) * ((sA n - sB n) / 2) ^ 2 with hT_def
  have htn : T = (sA n - sB n) ^ 2 * (2 ^ n / 2) := by rw [hT_def]; ring
  have hT0 : 0 ≤ T := by rw [hT_def]; positivity
  have hT16 : T ≤ 1 / 6 := by linarith
  have htT : |e * (2 ^ n / 2) - T| ≤ 2 ^ (3 * n + 5) * u := by
    rw [htn, ← sub_mul, abs_mul, abs_of_pos hQ0]
    have h6 : (4 : ℝ) * 2 ^ n ≤ 2 ^ (3 * n + 4) := by
      calc (4 : ℝ) * 2 ^ n = 2 ^ (n + 2) := by rw [pow_add]; ring
        _ ≤ 2 ^ (3 * n + 4) := pow_le_pow_right₀ one_le_two (by omega)
    calc |e - (sA n - sB n) ^ 2| * (2 ^ n / 2) ≤ (2 * W + 4 * u) * (2 ^ n / 2) :=
          mul_le_mul_of_nonneg_right heg hQ0.le
      _ = (2 ^ (3 * n + 4) + 2 * 2 ^ n) * u := by rw [hW_def]; ring
      _ ≤ (2 ^ (3 * n + 4) + 2 ^ (3 * n + 4)) * u := by
          gcongr; linarith
      _ = 2 ^ (3 * n + 5) * u := by ring
  have h35 : (2 : ℝ) ^ (3 * n + 5) * u ≤ 1 / 16 := hpowle _ (by omega)
  obtain ⟨htT1, htT2⟩ := abs_le.mp htT
  obtain ⟨hS1, hS2'⟩ := abs_le.mp hS
  -- the new `s`
  obtain ⟨s', hs', hs'1, hs'2⟩ := subFloor_abs hs ht w
  rw [← hu_def] at hs'2
  have hst : |sv - e * (2 ^ n / 2)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs'3 : sv - e * (2 ^ n / 2) ≤ s' + 2 * u := by
    have : 2 * |sv - e * (2 ^ n / 2)| * u ≤ 2 * 1 * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hst (by norm_num)) hu0.le
    linarith
  -- assemble
  refine ⟨r / 2, q, s', hr, hq, hs', ?_, ?_, ?_⟩
  · rw [agmA_succ]
    have h2 : (2 : ℝ) ^ (2 * (n + 1) + 4) * u = 4 * W := by
      rw [hW_def, show 2 * (n + 1) + 4 = (2 * n + 4) + 2 by ring, pow_add]; ring
    rw [h2]
    exact hrA.trans (by linarith)
  · rw [agmB_succ]
    have h2 : (2 : ℝ) ^ (2 * (n + 1) + 4) * u = 4 * W := by
      rw [hW_def, show 2 * (n + 1) + 4 = (2 * n + 4) + 2 by ring, pow_add]; ring
    rw [h2]
    exact hqB
  · rw [hSsucc]
    have h2 : (2 : ℝ) ^ (3 * (n + 1) + 7) * u = 8 * V := by
      rw [hV_def, show 3 * (n + 1) + 7 = (3 * n + 7) + 3 by ring, pow_add]; ring
    have h57 : (2 : ℝ) ^ (3 * n + 5) * u ≤ V := by
      rw [hV_def]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hu0.le
    rw [h2, abs_le]; constructor <;> linarith

theorem piPoint_iter {w : ℕ} [NeZero w] (hw : 64 ≤ w) :
    ∀ n, n ≤ piSteps w → PiPoint w n (piIter w n (piInit w))
  | 0, _ => piPoint_init w
  | n + 1, hn => piPoint_step hw (by omega) (piPoint_iter hw n (by omega))

/-! ### The final bracket -/

theorem toVal_piErr (w : ℕ) :
    (piErr w).toVal = some (((2 : ℝ) ^ (3 * piSteps w + 13) * (1 / 2 : ℝ) ^ w : ℝ) : EReal) := by
  rw [piErr, toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_natCast, AzInt.toInt_natCast,
    zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow, one_div, div_eq_mul_inv]

set_option maxHeartbeats 800000 in
/-- `piBracket w` brackets `π`, strictly from below, with width at most `piEps w`. -/
theorem piBracketAt_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, (piBracketAt w).1.toVal = some (lv : EReal) ∧
      (piBracketAt w).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv < Real.pi ∧ Real.pi ≤ hv ∧
      hv - lv ≤ 2 ^ (3 * piSteps w + 16) * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  set N := piSteps w with hN_def
  have hN1 : 1 ≤ N := one_le_piSteps w
  obtain ⟨av, bv, sv, ha, hb, hs, hA, hB, hS⟩ := piPoint_iter hw N le_rfl
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  have hsmall := piSteps_pow_mul_le hw
  have hpowle : ∀ k, k ≤ 3 * N + 16 → (2 : ℝ) ^ k * u ≤ 1 / 16 :=
    fun k hk =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hk) hu0.le).trans hsmall
  set W := (2 : ℝ) ^ (2 * N + 4) * u with hW_def
  set V := (2 : ℝ) ^ (3 * N + 7) * u with hV_def
  have hW16 : W ≤ 1 / 16 := hpowle _ (by omega)
  have hV16 : V ≤ 1 / 16 := hpowle _ (by omega)
  have hV8192 : 512 * V ≤ 1 / 16 := by
    have := hpowle (3 * N + 16) le_rfl
    rw [hV_def, show (512 : ℝ) * (2 ^ (3 * N + 7) * u) = 2 ^ (3 * N + 16) * u by
      rw [show 3 * N + 16 = (3 * N + 7) + 9 by ring, pow_add]; ring]
    exact this
  have hu4096 : u ≤ 1 / 4096 := by
    have := hpowle 8 (by omega)
    norm_num at this
    linarith
  have hWV : 16 * W ≤ V := by
    rw [hW_def, hV_def, show (16 : ℝ) * (2 ^ (2 * N + 4) * u) = 2 ^ (2 * N + 8) * u by
      rw [show 2 * N + 8 = (2 * N + 4) + 4 by ring, pow_add]; ring]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hu0.le
  have hVu : 128 * u ≤ V := by
    have : (128 : ℝ) ≤ 2 ^ (3 * N + 7) := by
      calc (128 : ℝ) = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (3 * N + 7) := pow_le_pow_right₀ one_le_two (by omega)
    exact mul_le_mul_of_nonneg_right this hu0.le
  obtain ⟨hb23, hba, ha1⟩ := salamin_facts N
  have hb1 : sB N ≤ 1 := hba.trans ha1
  have hS3 := salaminS_gt N
  have hS2 := salaminS_le_half N
  have hpi := abs_salaminApprox_piSteps_sub_pi_le w (by omega)
  rw [← hN_def, abs_le] at hpi
  obtain ⟨hpi1, hpi2⟩ := hpi
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  obtain ⟨hS1, hS2'⟩ := abs_le.mp hS
  -- `a_{N+1}`
  obtain ⟨r, hr, hrA⟩ := mean_step (w := w) ha hb hA hB hW16 ha1 hb1 hb23 hba
  rw [← agmA_succ] at hrA
  set A' := sA (N + 1) with hA'_def
  have hA'1 : A' ≤ 1 := salamin_agmA_le_one (by omega)
  have hA'0 : 2 / 3 < A' := lt_of_lt_of_le (salamin_agmB_gt (by omega)) (salamin_facts (N + 1)).2.1
  obtain ⟨hr1, hr2⟩ := abs_le.mp hrA
  have hr0 : 0 ≤ r / 2 := by linarith
  have hr17 : r / 2 ≤ 17 / 16 := by linarith
  -- `2 a_{N+1}²`
  obtain ⟨e, he, hfe⟩ := sqrFloor_err hr w
  have hrr : r / 2 * (r / 2) ≤ 2 := by nlinarith
  have heup := hfe.ge_of_le (B := 2) hrr
  rw [← hu_def] at heup
  have hele := hfe.le
  have hsqd : |r / 2 * (r / 2) - A' ^ 2| ≤ 17 / 8 * (W + 3 * u) := by
    have e0 : r / 2 * (r / 2) - A' ^ 2 = (r / 2 - A') * (r / 2 + A') := by ring
    have h1 : |r / 2 + A'| ≤ 17 / 8 := by rw [abs_le]; constructor <;> linarith
    rw [e0, abs_mul]
    calc |r / 2 - A'| * |r / 2 + A'| ≤ (W + 3 * u) * (17 / 8) :=
          mul_le_mul hrA h1 (abs_nonneg _) (by positivity)
      _ = 17 / 8 * (W + 3 * u) := by ring
  obtain ⟨hsq1, hsq2⟩ := abs_le.mp hsqd
  have hn := toVal_double he
  have he0 := hfe.nonneg
  -- the quotient
  have hsv0 : 1 / 4 ≤ sv := by linarith
  have hsv1 : sv ≤ 1 := by linarith
  have hsv0' : 0 < sv := by linarith
  obtain ⟨qv, hqv, hfq⟩ := divFloor_err hn hs hsv0' (by positivity) w
  have hq_le : 2 * e / sv ≤ 16 := by rw [div_le_iff₀ hsv0']; linarith only [hele, hrr, hsv0]
  have hqup := hfq.ge_of_le (B := 16) hq_le
  rw [← hu_def] at hqup
  have hqle := hfq.le
  have hq0 := hfq.nonneg
  -- `|2e/s − π_N|`
  have hπN : salaminApprox N = 2 * A' ^ 2 / salaminS N := rfl
  have hdiff : |2 * e / sv - salaminApprox N| ≤ 27 * V := by
    rw [hπN, div_sub_div _ _ hsv0'.ne' (by linarith), abs_div,
      abs_of_pos (mul_pos hsv0' (by linarith)), div_le_iff₀ (mul_pos hsv0' (by linarith))]
    have e0 : 2 * e * salaminS N - sv * (2 * A' ^ 2)
        = 2 * (e - A' ^ 2) * salaminS N + 2 * A' ^ 2 * (salaminS N - sv) := by ring
    have h1 : |2 * (e - A' ^ 2) * salaminS N| ≤ 2 * (17 / 8 * (W + 3 * u) + 4 * u) * (1 / 2) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < salaminS N), abs_mul, abs_two]
      refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hS2 (by linarith)
        (by positivity)
      rw [abs_le]; constructor <;> linarith
    have h2 : |2 * A' ^ 2 * (salaminS N - sv)| ≤ 2 * V := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * A' ^ 2), abs_sub_comm]
      have : 2 * A' ^ 2 ≤ 2 := by nlinarith
      exact mul_le_mul this hS (abs_nonneg _) (by norm_num)
    have hprod : 1 / 12 ≤ sv * salaminS N := by
      have := mul_le_mul hsv0 hS3.le (by norm_num) hsv0'.le
      linarith
    have hsum : |2 * e * salaminS N - sv * (2 * A' ^ 2)|
        ≤ 17 / 8 * (W + 3 * u) + 4 * u + 2 * V := by
      rw [e0]
      calc _ ≤ |2 * (e - A' ^ 2) * salaminS N| + |2 * A' ^ 2 * (salaminS N - sv)| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hV0 : 0 ≤ V := by linarith only [hVu, hu0]
    have hstep : 17 / 8 * (W + 3 * u) + 4 * u + 2 * V ≤ 27 * V * (1 / 12) := by
      linarith only [hWV, hVu, hu0]
    have hstep2 : 27 * V * (1 / 12) ≤ 27 * V * (sv * salaminS N) :=
      mul_le_mul_of_nonneg_left hprod (by linarith only [hV0])
    exact hsum.trans (hstep.trans hstep2)
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
  -- the computed `q` against `π`
  have hqπ1 : qv ≤ Real.pi + 28 * V := by linarith only [hqle, hd2, hpi2, hVu, hu0]
  have hqπ2 : Real.pi - 28 * V ≤ qv := by linarith only [hqup, hd1, hpi1, hVu, hu0]
  -- the widening by `E = 2^(3N+13) u = 64 V`
  have hE := toVal_piErr w
  rw [← hN_def] at hE
  set E := (2 : ℝ) ^ (3 * N + 13) * u with hE_def
  have hEV : E = 64 * V := by
    rw [hE_def, hV_def, show 3 * N + 13 = (3 * N + 7) + 6 by ring, pow_add]; ring
  have hqE0 : 0 ≤ qv - E := by linarith only [hqπ2, hpi3, hEV, hV8192]
  obtain ⟨lv, hlv, hflv⟩ := subFloor_err hqv hE w hqE0
  obtain ⟨hv, hhv, hchv⟩ := addCeiling_err hqv hE w (by linarith only [hq0, hEV, hVu, hu0])
  have hlvge := hflv.ge_of_le (B := 6) (by linarith only [hqπ1, hpi4, hV16, hEV, hVu, hu0])
  have hhvle := hchv.le_of_le (B := 12) (by linarith only [hqπ1, hpi4, hV16, hEV])
  rw [← hu_def] at hlvge hhvle
  have hflvle := hflv.le
  have hchvge := hchv.ge
  refine ⟨lv, hv, hlv, hhv, hflv.nonneg, by linarith only [hflvle, hqπ1, hEV, hVu, hu0],
    by linarith only [hchvge, hqπ2, hEV, hVu, hu0], ?_⟩
  have h2E : 2 * E ≤ 2 ^ (3 * N + 14) * u := by
    rw [hE_def, show 3 * N + 14 = (3 * N + 13) + 1 by ring, pow_add]; ring_nf; rfl
  have h1416 : (2 : ℝ) ^ (3 * N + 14) * u + 36 * u ≤ 2 ^ (3 * N + 16) * u := by
    have : (2 : ℝ) ^ (3 * N + 16) = 4 * 2 ^ (3 * N + 14) := by
      rw [show 3 * N + 16 = (3 * N + 14) + 2 by ring, pow_add]; ring
    rw [this]
    have h0 : (36 : ℝ) * u ≤ 2 ^ (3 * N + 14) * u := by
      refine mul_le_mul_of_nonneg_right ?_ hu0.le
      calc (36 : ℝ) ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (3 * N + 14) := pow_le_pow_right₀ one_le_two (by omega)
    linarith
  linarith only [hhvle, hlvge, h2E, h1416]

/-- `3 k + 19 < 2^k` from `k = 6` on. -/
theorem three_mul_add_lt_two_pow {k : ℕ} (hk : 6 ≤ k) : 3 * k + 19 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ]; omega

/-- The guard bits of `piWork` are fewer than `w` itself: `piWork w ≤ 2 w`. -/
theorem piWork_le_two_mul {w : ℕ} (hw : 64 ≤ w) : piWork w ≤ 2 * w := by
  have h6 : 6 ≤ Nat.log 2 w := Nat.le_log_of_pow_le one_lt_two (by norm_num; omega)
  have h1 := three_mul_add_lt_two_pow h6
  have h2 := Nat.pow_log_le_self 2 (x := w) (by omega)
  unfold piWork piSteps
  omega

/-- `piSteps (piWork w) ≤ piSteps w + 1`. -/
theorem piSteps_piWork_le {w : ℕ} (hw : 64 ≤ w) : piSteps (piWork w) ≤ piSteps w + 1 := by
  unfold piSteps
  have h := Nat.log_mono_right (b := 2) (piWork_le_two_mul hw)
  rw [mul_comm, Nat.log_mul_base one_lt_two (by omega)] at h
  omega

/-- The bracket of `π` at working precision `w`: ends with values, `0 ≤ lo < π ≤ hi`, width at
most `2^(3−w)`. -/
theorem piBracket_spec_width {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, (piBracket w).1.toVal = some (lv : EReal) ∧
      (piBracket w).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv < Real.pi ∧ Real.pi ≤ hv ∧ hv - lv ≤ 8 * (1 / 2 : ℝ) ^ w := by
  have hw' : 64 ≤ piWork w := by unfold piWork; omega
  obtain ⟨lv, hv, hlv, hhv, h0, hlo, hhi, hwid⟩ := piBracketAt_spec hw'
  refine ⟨lv, hv, hlv, hhv, h0, hlo, hhi, hwid.trans ?_⟩
  set N := piSteps w with hN_def
  have hN' := piSteps_piWork_le hw
  rw [← hN_def] at hN'
  have hpw : piWork w = w + (3 * N + 16) := by unfold piWork; rfl
  calc (2 : ℝ) ^ (3 * piSteps (piWork w) + 16) * (1 / 2 : ℝ) ^ piWork w
      ≤ 2 ^ (3 * N + 19) * (1 / 2 : ℝ) ^ piWork w :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) (by positivity)
    _ = 8 * (1 / 2 : ℝ) ^ w := by
        have h8 : (2 : ℝ) ^ (3 * N + 19) = 2 ^ (3 * N + 16) * 8 := by
          rw [show 3 * N + 19 = (3 * N + 16) + 3 by ring, pow_add]; norm_num
        have h1 : (2 : ℝ) ^ (3 * N + 16) * (1 / 2 : ℝ) ^ (3 * N + 16) = 1 := by
          rw [← mul_pow]; norm_num
        rw [hpw, pow_add (1 / 2 : ℝ) w (3 * N + 16), h8]
        linear_combination (8 * (1 / 2 : ℝ) ^ w) * h1

/-- The bracket of `π` at working precision `w`: ends with values, `0 ≤ lo < π ≤ hi`, width at
most `piEps w`. -/
theorem piBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, (piBracket w).1.toVal = some (lv : EReal) ∧
      (piBracket w).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv < Real.pi ∧ Real.pi ≤ hv ∧ hv - lv ≤ piEps w := by
  obtain ⟨lv, hv, hlv, hhv, h0, hlo, hhi, hwid⟩ := piBracket_spec_width hw
  refine ⟨lv, hv, hlv, hhv, h0, hlo, hhi, hwid.trans ?_⟩
  unfold piEps
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hw3 : (1 : ℝ) ≤ (w : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ w))
  nlinarith

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
