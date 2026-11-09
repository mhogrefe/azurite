/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.Equiv.DirectedRounding
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzRat.Equiv.Order
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Mul
import Azurite.BrentZimmermann.Chapter4.AGMLogBound
import Azurite.Transcendental.Exp

/-!
# Equivalence: the bracket of `ln x`

* `RelLower`: the rounded-down AGM on a single pair (`agmStepLo`) stays below the exact iterates
  and within a *relative* error `δ`, and one step adds at most `8 · 2^(−w)` to `δ`
  (`relLower_agmStepLo`, `relLower_agmIterLoN`): the AGM is homogeneous, so the roundings — each
  within a factor `1 − 2 · 2^(−w)` — compose multiplicatively.  The a priori `δ = (2 + 8S) 2^(−w)`
  after `S` steps is added back as the exact float `lnAgmDelta` (`lnAgm_spec`, `ln_agm_widen`):
  `b_S ≤ AGM(1, k) ≤ ⌈a_S + δ⌉_w`.
* `agm_log_gap`: after `lnSteps w` steps from `(1, k)`, `k ≥ 2^(−2h)`, the gap is at most
  `8 · 2^(−5h)` (`agm_log_iterations`, then two quadratic steps).
* `lnAgmBracket_spec`: for a positive float `x` with exponent `e`, `lnAgmBracket pb lb x e w`
  encloses `ln x` with width at most `lnEps e w = 2^40 (w + |e| + 8)^5 2^(−w)` (`w ≥ 64`), for
  any brackets `pb` of `π` and `lb` of `ln 2` fit for `w` (`PiBracketFor`, `Ln2BracketFor`),
  using `abs_pi_div_AGM_sub_log_le` (MCA's AGM–logarithm error) and `ln_L_spec` (the term
  `ℓ ln 2`).
* The series path: `log_atanh_series_bounds` (DLMF 4.6.4, `2 S_J ≤ ln((1+t)/(1−t)) ≤ 2 S_J +
  (8/3) t^(2J+1)`), `lnSqrtIter_spec` (the rounded-down roots lose at most `6 · 2^(−w)` in
  `ln`), `lnSeriesLoop_spec` (relative invariants of the rounded-down sum and power),
  `lnSeries_final_bounds`, and `lnSeriesBracket_spec` with the same conclusion.
* `lnBracketCore_spec`, `lnBracket_eq_core`, `lnBracket_spec`, `lnBracketWith_spec`: the
  dispatcher and its instances (`piBracket w`, `ln2Bracket w`, or an `LnConsts`).
* `lnApprox_isSome_exists`: the Ziv certificate, from `irrational_log_rat`.
* `lnFloorApprox_spec`: `ln` of a float `y ≤ q ≤ y (1 + 2·2^(−w))`, the upper end widened by
  `2^(2−w) ≥ ln (q/y)`, encloses `ln q` with width `≤ lnRatEps E |ln q| w`, `E = ⌊2 |ln q|⌋ + 2 ≥
  |exponent of y|`; hence `lnRatApprox_spec`/`lnRatApprox_isSome_exists` (`q` a positive rational,
  `y = ⌊q⌋_w`) and `lnP1Approx_spec`/`lnP1Approx_isSome_exists` (`q = 1 + x`, `y = ⌊1 + x⌋_w`).
-/

namespace Azurite.AzFloat

open Azurite.BZ RoundingTarget

/-! ### Elementary bounds -/

theorem sqrt_one_sub_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 1 - t ≤ Real.sqrt (1 - t) := by
  have h2 : (0 : ℝ) ≤ 1 - t := by linarith
  rw [Real.le_sqrt h2 h2]
  nlinarith

theorem sqrt_one_add_le {t : ℝ} (h0 : 0 ≤ t) : Real.sqrt (1 + 2 * t) ≤ 1 + t := by
  calc Real.sqrt (1 + 2 * t) ≤ Real.sqrt ((1 + t) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 + t := Real.sqrt_sq (by linarith)

theorem mul_half_pow_le {w : ℕ} (hw : 64 ≤ w) : (w : ℝ) * (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 32 := by
  have hnat : w * 2 ^ 32 ≤ 2 ^ w := by
    induction w, hw using Nat.le_induction with
    | base => norm_num
    | succ w hw ih =>
      calc (w + 1) * 2 ^ 32 ≤ 2 * w * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * (w * 2 ^ 32) := by ring
        _ ≤ 2 * 2 ^ w := by omega
        _ = 2 ^ (w + 1) := by ring
  have h : ((w : ℝ) * 2 ^ 32 : ℝ) ≤ 2 ^ w := by exact_mod_cast hnat
  rw [one_div_pow, one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- `2^(size n) ≤ 2 n` for `n ≥ 1`. -/
theorem two_pow_size_le (n : ℕ) (hn : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  have hs : 0 < n.size := Nat.size_pos.mpr hn
  have h : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
  calc 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h

variable {a b : ℝ}

/-! ### The one-sided relative error of the rounded-down iteration -/

/-- The pair `s` lies below `(a_n, b_n)`, within the relative error `δ`. -/
def RelLower (a b : ℝ) (n : ℕ) (δ : ℝ) (s : AzFloat × AzFloat) : Prop :=
  ∃ al bl : ℝ, s.1.toVal = some (al : EReal) ∧ s.2.toVal = some (bl : EReal) ∧
    agmA a b n * (1 - δ) ≤ al ∧ al ≤ agmA a b n ∧ agmB a b n * (1 - δ) ≤ bl ∧ bl ≤ agmB a b n

/-- One rounded-down step adds `8 · 2^(−w)` to the relative error (the lower halves of
`relEncloses_agmStep`). -/
theorem relLower_agmStepLo (ha : 0 < a) (hb : 0 < b) {n : ℕ} {δ : ℝ} {s : AzFloat × AzFloat}
    (w : ℕ) [NeZero w] (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8)
    (h : RelLower a b n δ s) :
    RelLower a b (n + 1) (δ + 8 * (1 / 2 : ℝ) ^ w) (agmStepLo w s) := by
  obtain ⟨al, bl, hal, hbl, hal1, hal2, hbl1, hbl2⟩ := h
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  obtain ⟨hA, hB⟩ := agm_pos ha hb n
  set A := agmA a b n with hA_def
  set B := agmB a b n with hB_def
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hal0 : 0 ≤ al := le_trans (mul_nonneg hA.le h1δ) hal1
  have hbl0 : 0 ≤ bl := le_trans (mul_nonneg hB.le h1δ) hbl1
  simp only [agmStepLo]
  obtain ⟨r1, hr1, hf1⟩ := addFloor_err hal hbl w (by linarith)
  obtain ⟨m1, hm1, hfm1⟩ := mulFloor_err hal hbl w (mul_nonneg hal0 hbl0)
  obtain ⟨q1, hq1, hfq1⟩ := sqrtFloor_err hm1 hfm1.nonneg w
  have hAB0 : 0 ≤ A * B := mul_nonneg hA.le hB.le
  have hS0 : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  refine ⟨r1 / 2, q1, toVal_half hr1, hq1, ?_, ?_, ?_, ?_⟩
  · rw [agmA_succ]
    have h1 : (A + B) * (1 - δ) ≤ al + bl := by linarith
    have h2 : (al + bl) * (1 - 2 * u) ≤ r1 := by linarith [hf1.ge]
    have h3 : (A + B) * (1 - δ) * (1 - 2 * u) ≤ (al + bl) * (1 - 2 * u) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h4 : (A + B) * (1 - (δ + 8 * u)) ≤ (A + B) * (1 - δ) * (1 - 2 * u) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  · rw [agmA_succ]; linarith [hf1.le]
  · rw [agmB_succ]
    have hm1ge : al * bl * (1 - 2 * u) ≤ m1 := by linarith [hfm1.ge]
    have hprod : A * (1 - δ) * (B * (1 - δ)) ≤ al * bl :=
      mul_le_mul hal1 hbl1 (mul_nonneg hB.le h1δ) hal0
    have hm1lo : A * B * ((1 - δ) ^ 2 * (1 - 2 * u)) ≤ m1 := by
      calc A * B * ((1 - δ) ^ 2 * (1 - 2 * u)) = A * (1 - δ) * (B * (1 - δ)) * (1 - 2 * u) := by
            ring
        _ ≤ al * bl * (1 - 2 * u) := mul_le_mul_of_nonneg_right hprod (by linarith)
        _ ≤ m1 := hm1ge
    have hsq : Real.sqrt (A * B * ((1 - δ) ^ 2 * (1 - 2 * u))) ≤ Real.sqrt m1 :=
      Real.sqrt_le_sqrt hm1lo
    rw [Real.sqrt_mul hAB0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1δ] at hsq
    have hs2u : 1 - 2 * u ≤ Real.sqrt (1 - 2 * u) := sqrt_one_sub_ge (by linarith) (by linarith)
    have h7 : Real.sqrt (A * B) * (1 - δ) * (1 - 2 * u) ≤ Real.sqrt m1 := by
      calc Real.sqrt (A * B) * (1 - δ) * (1 - 2 * u)
          ≤ Real.sqrt (A * B) * (1 - δ) * Real.sqrt (1 - 2 * u) :=
            mul_le_mul_of_nonneg_left hs2u (mul_nonneg hS0 h1δ)
        _ = Real.sqrt (A * B) * ((1 - δ) * Real.sqrt (1 - 2 * u)) := by ring
        _ ≤ Real.sqrt m1 := hsq
    have h8 : Real.sqrt m1 * (1 - 2 * u) ≤ q1 := by linarith [hfq1.ge]
    have h9 : Real.sqrt (A * B) * (1 - δ) * (1 - 2 * u) * (1 - 2 * u)
        ≤ Real.sqrt m1 * (1 - 2 * u) :=
      mul_le_mul_of_nonneg_right h7 (by linarith)
    have h10 : Real.sqrt (A * B) * (1 - (δ + 8 * u))
        ≤ Real.sqrt (A * B) * (1 - δ) * (1 - 2 * u) * (1 - 2 * u) := by
      have huu : u * u ≤ u / 8 := by
        have := mul_le_mul_of_nonneg_left hu hu0.le; linarith
      have hdu : δ * u ≤ u / 2 := by
        have := mul_le_mul_of_nonneg_right hδ hu0.le; linarith
      have hduu : δ * (u * u) ≤ u / 16 := by
        have := mul_le_mul_of_nonneg_left huu hδ0
        have := mul_le_mul_of_nonneg_right hδ (by positivity : (0 : ℝ) ≤ u / 8)
        nlinarith
      have e : (1 - δ) * (1 - 2 * u) * (1 - 2 * u)
          = 1 - δ - 4 * u + 4 * (u * u) + 4 * (δ * u) - 4 * (δ * (u * u)) := by ring
      have : (1 - (δ + 8 * u)) ≤ (1 - δ) * (1 - 2 * u) * (1 - 2 * u) := by
        rw [e]
        have h1 : 0 ≤ u * u := by positivity
        have h2 : 0 ≤ δ * u := by positivity
        linarith
      calc Real.sqrt (A * B) * (1 - (δ + 8 * u))
          ≤ Real.sqrt (A * B) * ((1 - δ) * (1 - 2 * u) * (1 - 2 * u)) :=
            mul_le_mul_of_nonneg_left this hS0
        _ = _ := by ring
    linarith
  · rw [agmB_succ]
    have h1 : al * bl ≤ A * B := mul_le_mul hal2 hbl2 hbl0 hA.le
    exact hfq1.le.trans (Real.sqrt_le_sqrt (hfm1.le.trans h1))

theorem relLower_agmIterLoN (ha : 0 < a) (hb : 0 < b) (w : ℕ) [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) :
    ∀ (n m : ℕ) {δ : ℝ} {s : AzFloat × AzFloat}, 0 ≤ δ →
      δ + 8 * (1 / 2 : ℝ) ^ w * n ≤ 1 / 2 → RelLower a b m δ s →
      RelLower a b (m + n) (δ + 8 * (1 / 2 : ℝ) ^ w * n) (agmIterLoN w n s)
  | 0, m, δ, s, _, _, h => by
    simp only [agmIterLoN, Nat.cast_zero, mul_zero, add_zero]
    exact h
  | n + 1, m, δ, s, hδ0, hδ, h => by
    have hu0 : 0 < (1 / 2 : ℝ) ^ w := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep := relLower_agmStepLo ha hb w hδ0 (by push_cast at hδ; nlinarith) hu h
    have hrec := relLower_agmIterLoN ha hb w hu n (m + 1) (δ := δ + 8 * (1 / 2 : ℝ) ^ w)
      (by positivity) (by push_cast at hδ ⊢; linarith) hstep
    have e1 : m + (n + 1) = m + 1 + n := by omega
    have e2 : δ + 8 * (1 / 2 : ℝ) ^ w * ((n + 1 : ℕ) : ℝ)
        = δ + 8 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (n : ℝ) := by push_cast; ring
    simp only [agmIterLoN]
    rw [e1, e2]
    exact hrec

/-- The exact float `δ = (8S + 2) · 2^(−w)`. -/
theorem toVal_lnAgmDelta (w S : ℕ) :
    (lnAgmDelta w S).toVal = some ((((8 * S + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ w : ℝ) : EReal) := by
  rw [lnAgmDelta, toVal_shiftLeft_of_toVal (toVal_ofAzNat _), AzNat.toNat_ofNat, AzInt.toInt_neg,
    toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg, zpow_natCast, one_div_pow, one_div]

/-! ### The number of steps -/

/-- One quadratic step from a gap `≤ 8 · 2^(−m)` and `b_j ≥ 2^(−h)` gives a gap
`≤ 8 · 2^(−(2m − h))`. -/
theorem agm_quad_step {k : ℝ} (hk : 0 < k) {j m h : ℕ} (hj : 1 ≤ j)
    (hb : (1 / 2 : ℝ) ^ h ≤ agmB 1 k j) (hg : agmA 1 k j - agmB 1 k j ≤ 8 * (1 / 2 : ℝ) ^ m)
    (hmh : h ≤ 2 * m) :
    agmA 1 k (j + 1) - agmB 1 k (j + 1) ≤ 8 * (1 / 2 : ℝ) ^ (2 * m - h) := by
  have hg0 : 0 ≤ agmA 1 k j - agmB 1 k j := sub_nonneg.mpr (agmB_le_agmA one_pos hk hj)
  have hb0 : 0 < (1 / 2 : ℝ) ^ h := by positivity
  have h1 := agm_gap_succ_le_sq one_pos hk hj
  have h2 : (agmA 1 k j - agmB 1 k j) ^ 2 / (8 * agmB 1 k j)
      ≤ (8 * (1 / 2 : ℝ) ^ m) ^ 2 / (8 * (1 / 2 : ℝ) ^ h) := by
    gcongr
  have h3 : (8 * (1 / 2 : ℝ) ^ m) ^ 2 / (8 * (1 / 2 : ℝ) ^ h) = 8 * (1 / 2 : ℝ) ^ (2 * m - h) := by
    have : (1 / 2 : ℝ) ^ (m * 2) = (1 / 2 : ℝ) ^ (2 * m - h) * (1 / 2 : ℝ) ^ h := by
      rw [← pow_add]; congr 1; omega
    rw [mul_pow, ← pow_mul, this]
    field_simp
  linarith

/-- After `2 ⌈lg 2h⌉ + 3` steps from `(1, k)` with `2^(−2h) ≤ k ≤ 1`, the gap is at most
`8 · 2^(−5h)`. -/
theorem agm_log_gap {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (h : ℕ)
    (hkn : (1 / 2 : ℝ) ^ (2 * h) ≤ k) :
    agmA 1 k (2 * Nat.clog 2 (2 * h) + 3) - agmB 1 k (2 * Nat.clog 2 (2 * h) + 3)
      ≤ 8 * (1 / 2 : ℝ) ^ (5 * h) := by
  set j := 2 * Nat.clog 2 (2 * h) + 1 with hj
  have hj1 : 1 ≤ j := by omega
  have hg0 : agmA 1 k j - agmB 1 k j ≤ 8 * (1 / 2 : ℝ) ^ (2 * h) := by
    have := agm_log_iterations hk hk1 (2 * h) hkn
    rw [div_eq_mul_inv] at this
    rw [one_div_pow, one_div]
    exact this
  -- `b_1 = √k ≥ 2^(−h)` and `b` is monotone from index `1`
  have hb1 : (1 / 2 : ℝ) ^ h ≤ agmB 1 k 1 := by
    rw [agmB_succ, agmA_zero, agmB_zero, one_mul]
    have : (1 / 2 : ℝ) ^ h = Real.sqrt ((1 / 2 : ℝ) ^ (2 * h)) := by
      rw [pow_mul', Real.sqrt_sq (by positivity)]
    rw [this]
    exact Real.sqrt_le_sqrt hkn
  have hbmono : ∀ i, 1 ≤ i → (1 / 2 : ℝ) ^ h ≤ agmB 1 k i := by
    intro i hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hb1.trans (agmB_monotone one_pos hk (Nat.zero_le i'))
  have hg1 := agm_quad_step hk hj1 (hbmono j hj1) hg0 (by omega)
  have hg2 := agm_quad_step hk (by omega : 1 ≤ j + 1) (hbmono (j + 1) (by omega)) hg1 (by omega)
  have e1 : 2 * (2 * h) - h = 3 * h := by omega
  have e2 : 2 * (3 * h) - h = 5 * h := by omega
  rw [e1] at hg2
  rw [e2] at hg2
  have e3 : 2 * Nat.clog 2 (2 * h) + 3 = j + 1 + 1 := by omega
  rw [e3]
  exact hg2

/-! ### The error budget -/

/-- The width bound of `lnBracket`. -/
noncomputable def lnEps (e : ℤ) (w : ℕ) : ℝ :=
  2 ^ 40 * ((w : ℝ) + |(e : ℝ)| + 8) ^ 5 * (1 / 2 : ℝ) ^ w

theorem tendsto_lnEps (e : ℤ) : Filter.Tendsto (lnEps e) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 5
    (by norm_num : |(1 / 2 : ℝ)| < 1)).const_mul (2 ^ 45 : ℝ)
  rw [mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · exact Filter.Eventually.of_forall fun w => by unfold lnEps; positivity
  · have hc : ∀ᶠ w : ℕ in Filter.atTop, |(e : ℝ)| + 8 ≤ (w : ℝ) := by
      rw [Filter.eventually_atTop]
      refine ⟨Nat.ceil (|(e : ℝ)| + 8), fun w hw => ?_⟩
      exact (Nat.le_ceil _).trans (by exact_mod_cast hw)
    refine hc.mono fun w hw => ?_
    unfold lnEps
    have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    have h1 : ((w : ℝ) + |(e : ℝ)| + 8) ^ 5 ≤ (2 * w) ^ 5 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have h2 : (2 * (w : ℝ)) ^ 5 = 2 ^ 5 * (w : ℝ) ^ 5 := by ring
    have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    calc 2 ^ 40 * ((w : ℝ) + |(e : ℝ)| + 8) ^ 5 * (1 / 2 : ℝ) ^ w
        ≤ 2 ^ 40 * (2 ^ 5 * (w : ℝ) ^ 5) * (1 / 2 : ℝ) ^ w := by
          rw [← h2]; gcongr
      _ = 2 ^ 45 * ((w : ℝ) ^ 5 * (1 / 2 : ℝ) ^ w) := by ring

theorem toVal_four : (one <<< (2 : Nat)).toVal = some ((4 : ℝ) : EReal) := by
  rw [toVal_shiftLeft_nat (isFinite_of_toVal_coe toVal_one'), fval_of_toVal_coe toVal_one']
  norm_num

/-! ### The width of the final bracket -/

set_option maxHeartbeats 800000 in
/-- The width of the final bracket, from the widths of its parts (pure real arithmetic). -/
theorem ln_final_bounds {w : ℕ} (hw : 64 ≤ w) {h S : ℕ} (hh2 : 2 ≤ h) (hh4 : w + 5 ≤ 4 * h)
    (hh4' : 4 * h ≤ w + 8) (hSw : (S : ℝ) ≤ w + 11) {e : ℤ} {ℓz : ℝ}
    (hℓ : |ℓz| ≤ (w : ℝ) + |(e : ℝ)| + 8)
    {M ah bl pl ph qLo qHi Ev LLo LHi lo1 lo hi1 hi : ℝ}
    (hblM : bl ≤ M) (hMah : M ≤ ah) (hbllo : 1 / (8 * h + 12) ≤ bl)
    (hah2 : ah ≤ 2)
    (hwidth : ah - bl ≤ 8 * (1 / 2 : ℝ) ^ (5 * h)
      + 3 * (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ)))
    (hpl0 : 0 ≤ pl) (hplπ : pl < Real.pi) (hπph : Real.pi ≤ ph) (hpw : ph - pl ≤ piEps w)
    (hfq : FloorOf w ((pl / 2) / ah) qLo) (hcq : CeilOf w ((ph / 2) / bl) qHi)
    (hEv0 : 0 ≤ Ev) (hEv_le : Ev ≤ (4 * h + 4) * (1 / 2 : ℝ) ^ (4 * h))
    (hLw : LHi - LLo ≤ 12 * |ℓz| * (1 / 2 : ℝ) ^ w) (hLLo_abs : |LLo| ≤ 2 * |ℓz|)
    (hLHi_abs : |LHi| ≤ 2 * |ℓz|)
    (hlo1a : lo1 ≤ qLo - Ev) (hlo1b : qLo - Ev ≤ lo1 + 2 * |qLo - Ev| * (1 / 2 : ℝ) ^ w)
    (hlob : lo1 - LHi ≤ lo + 2 * |lo1 - LHi| * (1 / 2 : ℝ) ^ w)
    (hhi1a : qHi + Ev ≤ hi1) (hhi1b : hi1 ≤ qHi + Ev + 2 * |qHi + Ev| * (1 / 2 : ℝ) ^ w)
    (hhib : hi ≤ hi1 - LLo + 2 * |hi1 - LLo| * (1 / 2 : ℝ) ^ w) :
    hi - lo ≤ lnEps e w := by
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hu8 : u ≤ 1 / 8 := by
    calc u ≤ (1 / 2 : ℝ) ^ 64 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
      _ ≤ 1 / 8 := by norm_num
  have hw64 : (64 : ℝ) ≤ w := by exact_mod_cast hw
  set W : ℝ := (w : ℝ) + |(e : ℝ)| + 8 with hW
  have habs0 : 0 ≤ |(e : ℝ)| := abs_nonneg _
  have hW72 : (72 : ℝ) ≤ W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWw : (w : ℝ) ≤ W := by linarith
  have hh4r : (w : ℝ) + 5 ≤ 4 * h := by exact_mod_cast hh4
  have hh4r' : 4 * (h : ℝ) ≤ w + 8 := by exact_mod_cast hh4'
  have hh2r : (2 : ℝ) ≤ h := by exact_mod_cast hh2
  have h2h3 : 2 * (h : ℝ) + 3 ≤ W := by linarith
  have h8h12 : 8 * (h : ℝ) + 12 ≤ 3 * W := by linarith
  have hℓ_nn : 0 ≤ |ℓz| := abs_nonneg _
  -- positivity
  have hbl0 : 0 < bl := lt_of_lt_of_le (by positivity) hbllo
  have hM0 : 0 < M := lt_of_lt_of_le hbl0 hblM
  have hah0 : 0 < ah := lt_of_lt_of_le hM0 hMah
  have hahbl0 : 0 ≤ ah - bl := by linarith
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hpeps := piEps_le hw
  have hpeps0 : 0 ≤ piEps w := by unfold piEps; positivity
  have hph : ph ≤ 5 := by linarith
  -- `1/bl ≤ 3W`
  have hbl3W : 1 ≤ bl * (3 * W) := by
    have h1 : 1 / (8 * h + 12) * (3 * W) ≤ bl * (3 * W) :=
      mul_le_mul_of_nonneg_right hbllo (by positivity)
    have h2 : (1 : ℝ) ≤ 1 / (8 * h + 12) * (3 * W) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hah3W : 1 ≤ ah * (3 * W) := by nlinarith
  -- the quotients
  set Qm := (pl / 2) / ah with hQm
  set Qp := (ph / 2) / bl with hQp
  have hQm0 : 0 ≤ Qm := by positivity
  have hQp_le : Qp ≤ 8 * W := by
    rw [hQp, div_le_iff₀ hbl0]
    calc ph / 2 ≤ 5 / 2 := by linarith
      _ ≤ 8 * W * (1 / (3 * W)) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
      _ ≤ 8 * W * bl := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [one_div, inv_le_iff_one_le_mul₀ (by positivity)]
          exact hbl3W
  have hQmp : Qm ≤ Qp := by
    rw [hQm, hQp, div_le_div_iff₀ hah0 hbl0]
    exact mul_le_mul (by linarith) (by linarith) hbl0.le (by linarith)
  have hQm_le : Qm ≤ 8 * W := hQmp.trans hQp_le
  have hqLo1 : qLo ≤ Qm := hfq.le
  have hqLo2 : Qm ≤ qLo + 2 * (8 * W) * u := hfq.ge_of_le hQm_le
  have hqLo0 : 0 ≤ qLo := hfq.nonneg
  have hqHi1 : Qp ≤ qHi := hcq.ge
  have hqHi2 : qHi ≤ Qp + 2 * (8 * W) * u := hcq.le_of_le hQp_le
  have hqHi_le : qHi ≤ 10 * W := by
    have : 2 * (8 * W) * u ≤ 2 * (8 * W) * (1 / 8) := mul_le_mul_of_nonneg_left hu8 (by positivity)
    linarith
  -- `Qp − Qm`
  have hQpm : Qp - Qm ≤ (piEps w + 2 * (ah - bl)) * (3 * W) ^ 2 := by
    have e : Qp - Qm = ((ph - pl) * ah + pl * (ah - bl)) / (2 * ah * bl) := by
      rw [hQp, hQm]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : (ph - pl) * ah ≤ piEps w * 2 := mul_le_mul hpw hah2 hah0.le hpeps0
    have h2 : pl * (ah - bl) ≤ 4 * (ah - bl) :=
      mul_le_mul_of_nonneg_right (by linarith) hahbl0
    have h3 : (piEps w + 2 * (ah - bl)) * (3 * W) ^ 2 * (2 * ah * bl)
        = 2 * (piEps w + 2 * (ah - bl)) * (ah * (3 * W)) * (bl * (3 * W)) := by ring
    rw [h3]
    have h4 : 0 ≤ 2 * (piEps w + 2 * (ah - bl)) := by positivity
    have h5 : 2 * (piEps w + 2 * (ah - bl)) * 1 * 1
        ≤ 2 * (piEps w + 2 * (ah - bl)) * (ah * (3 * W)) * (bl * (3 * W)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hah3W h4) hbl3W zero_le_one
      positivity
    linarith
  -- the pieces
  have hgap : 8 * (1 / 2 : ℝ) ^ (5 * h) ≤ u / 16 := by
    have : (1 / 2 : ℝ) ^ (5 * h) ≤ (1 / 2 : ℝ) ^ (w + 7) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have e : (1 / 2 : ℝ) ^ (w + 7) = u / 128 := by rw [pow_add, ← hu]; ring
    linarith
  have hahbl : ah - bl ≤ 300 * W * u := by
    have h1 : 8 * u * (S : ℝ) ≤ 8 * u * (w + 11) := mul_le_mul_of_nonneg_left hSw (by positivity)
    have h2 : (w : ℝ) * u ≤ W * u := mul_le_mul_of_nonneg_right hWw hu0.le
    have h3 : u ≤ W * u := by
      have := mul_le_mul_of_nonneg_right hW1 hu0.le; linarith
    linarith
  have hpiEps : piEps w ≤ 2 ^ 19 * W ^ 3 * u := by
    unfold piEps
    have : (w : ℝ) ^ 3 ≤ W ^ 3 := pow_le_pow_left₀ (by positivity) hWw 3
    have hu' : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    calc (2 : ℝ) ^ 19 * (w : ℝ) ^ 3 * (1 / 2 : ℝ) ^ w ≤ 2 ^ 19 * W ^ 3 * (1 / 2 : ℝ) ^ w := by
          gcongr
      _ = 2 ^ 19 * W ^ 3 * u := rfl
  have hW3 : W ^ 3 ≤ W ^ 5 := pow_le_pow_right₀ hW1 (by norm_num)
  have hW2 : W ^ 2 ≤ W ^ 5 := pow_le_pow_right₀ hW1 (by norm_num)
  have hW1' : W ≤ W ^ 5 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 5 := pow_le_pow_right₀ hW1 (by norm_num)
  have hP0 : 0 ≤ W ^ 5 * u := by positivity
  have hQpm' : Qp - Qm ≤ (9 * 2 ^ 19 + 5400) * (W ^ 5 * u) := by
    have h1 : (piEps w + 2 * (ah - bl)) * (3 * W) ^ 2
        ≤ (2 ^ 19 * W ^ 3 * u + 2 * (300 * W * u)) * (3 * W) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h2 : (2 ^ 19 * W ^ 3 * u + 2 * (300 * W * u)) * (3 * W) ^ 2
        = 9 * 2 ^ 19 * (W ^ 5 * u) + 5400 * (W ^ 3 * u) := by ring
    have h3 : W ^ 3 * u ≤ W ^ 5 * u := mul_le_mul_of_nonneg_right hW3 hu0.le
    linarith
  have hEv2 : 2 * Ev ≤ W ^ 5 * u := by
    have h1 : (1 / 2 : ℝ) ^ (4 * h) ≤ (1 / 2 : ℝ) ^ (w + 5) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have e : (1 / 2 : ℝ) ^ (w + 5) = u / 32 := by rw [pow_add, ← hu]; ring
    have h2 : (4 * (h : ℝ) + 4) * (1 / 2 : ℝ) ^ (4 * h) ≤ (w + 12) * (u / 32) := by
      apply mul_le_mul (by linarith) (e ▸ h1) (by positivity) (by positivity)
    have h3 : (w + 12 : ℝ) * (u / 32) ≤ W * u / 2 := by
      have : (w + 12 : ℝ) ≤ 16 * W := by linarith
      have := mul_le_mul_of_nonneg_right this hu0.le; linarith
    have h4 : W * u ≤ W ^ 5 * u := mul_le_mul_of_nonneg_right hW1' hu0.le
    linarith
  have hWu : W * u ≤ W ^ 5 * u := mul_le_mul_of_nonneg_right hW1' hu0.le
  have hLw' : LHi - LLo ≤ 12 * (W ^ 5 * u) := by
    have : 12 * |ℓz| * u ≤ 12 * W * u := by
      apply mul_le_mul_of_nonneg_right _ hu0.le
      linarith
    linarith
  -- magnitudes for the roundings
  have hEv1 : Ev ≤ 2 * W := by
    have : (4 * (h : ℝ) + 4) * (1 / 2 : ℝ) ^ (4 * h) ≤ 2 * W := by
      have h1 : (1 / 2 : ℝ) ^ (4 * h) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have : (4 * (h : ℝ) + 4) * (1 / 2 : ℝ) ^ (4 * h) ≤ (4 * h + 4) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    linarith
  have hqLo_le : qLo ≤ 8 * W := hqLo1.trans hQm_le
  have habs1 : |qLo - Ev| ≤ 10 * W := by
    rw [abs_le]; constructor <;> linarith
  have hlo1_abs : |lo1| ≤ 13 * W := by
    have h1 : 2 * |qLo - Ev| * u ≤ 2 * (10 * W) * (1 / 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left habs1 (by norm_num)) hu8 hu0.le (by positivity)
    rw [abs_le]; constructor <;> linarith
  have hLHi_abs' : |LHi| ≤ 2 * W := hLHi_abs.trans (by linarith)
  have hLLo_abs' : |LLo| ≤ 2 * W := hLLo_abs.trans (by linarith)
  have habs2 : |lo1 - LHi| ≤ 15 * W := by
    have := abs_le.mp hlo1_abs; have := abs_le.mp hLHi_abs'
    rw [abs_le]; constructor <;> linarith
  have habs3 : |qHi + Ev| ≤ 12 * W := by
    rw [abs_le]; constructor <;> linarith
  have hhi1_abs : |hi1| ≤ 15 * W := by
    have h1 : 2 * |qHi + Ev| * u ≤ 2 * (12 * W) * (1 / 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left habs3 (by norm_num)) hu8 hu0.le (by positivity)
    rw [abs_le]; constructor <;> linarith
  have habs4 : |hi1 - LLo| ≤ 17 * W := by
    have := abs_le.mp hhi1_abs; have := abs_le.mp hLLo_abs'
    rw [abs_le]; constructor <;> linarith
  have hr1 : 2 * |qLo - Ev| * u ≤ 20 * (W * u) := by
    have := mul_le_mul_of_nonneg_right habs1 hu0.le; linarith
  have hr2 : 2 * |lo1 - LHi| * u ≤ 30 * (W * u) := by
    have := mul_le_mul_of_nonneg_right habs2 hu0.le; linarith
  have hr3 : 2 * |qHi + Ev| * u ≤ 24 * (W * u) := by
    have := mul_le_mul_of_nonneg_right habs3 hu0.le; linarith
  have hr4 : 2 * |hi1 - LLo| * u ≤ 34 * (W * u) := by
    have := mul_le_mul_of_nonneg_right habs4 hu0.le; linarith
  have hqdiff : qHi - qLo ≤ (Qp - Qm) + 32 * (W * u) := by linarith
  -- assemble
  have htotal : hi - lo ≤ (Qp - Qm) + 32 * (W * u) + 2 * Ev + (LHi - LLo) + 108 * (W * u) := by
    linarith
  have hfin : (9 * 2 ^ 19 + 5400 : ℝ) * (W ^ 5 * u) + 140 * (W ^ 5 * u) + W ^ 5 * u
      + 12 * (W ^ 5 * u) ≤ 2 ^ 40 * (W ^ 5 * u) := by
    calc (9 * 2 ^ 19 + 5400 : ℝ) * (W ^ 5 * u) + 140 * (W ^ 5 * u) + W ^ 5 * u + 12 * (W ^ 5 * u)
        = (9 * 2 ^ 19 + 5400 + 140 + 1 + 12) * (W ^ 5 * u) := by ring
      _ ≤ 2 ^ 40 * (W ^ 5 * u) := mul_le_mul_of_nonneg_right (by norm_num) hP0
  unfold lnEps
  rw [← hW]
  have : hi - lo ≤ (9 * 2 ^ 19 + 5400 : ℝ) * (W ^ 5 * u) + 140 * (W ^ 5 * u) + W ^ 5 * u
      + 12 * (W ^ 5 * u) := by linarith
  calc hi - lo ≤ _ := this
    _ ≤ 2 ^ 40 * (W ^ 5 * u) := hfin
    _ = 2 ^ 40 * W ^ 5 * u := by ring

/-! ### The scaled argument and the AGM–logarithm bounds -/

/-- `y = x · 2^(2h+2−e)` lies in `[2^(2h+1), 2^(2h+2))`, so `k = 4/y ∈ [2^(−2h), 2 · 2^(−2h)]`. -/
theorem ln_scale {e : ℤ} {v : ℝ} (hv0 : 0 < v) (hlo : (2 : ℝ) ^ (e - 1) ≤ v) (hhi : v < (2 : ℝ) ^ e)
    (h : ℕ) (hh : 2 ≤ h) :
    (2 : ℝ) ^ (2 * h + 1) ≤ v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e) ∧
      v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e) < (2 : ℝ) ^ (2 * h + 2) ∧
      0 < v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e) ∧
      (1 / 2 : ℝ) ^ (2 * h) ≤ 4 / (v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e)) ∧
      4 / (v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e)) ≤ 2 * (1 / 2 : ℝ) ^ (2 * h) ∧
      4 / (v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e)) ≤ 1 := by
  set z : ℤ := ((2 * h + 2 : ℕ) : ℤ) - e with hz
  have hp : (0 : ℝ) < 2 ^ z := zpow_pos (by norm_num) _
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hlo' : (2 : ℝ) ^ (2 * h + 1) ≤ v * 2 ^ z := by
    have : (2 : ℝ) ^ (2 * h + 1) = 2 ^ (e - 1) * 2 ^ z := by
      rw [← zpow_add₀ h2, ← zpow_natCast]; congr 1; rw [hz]; push_cast; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hlo hp.le
  have hhi' : v * 2 ^ z < (2 : ℝ) ^ (2 * h + 2) := by
    have : (2 : ℝ) ^ (2 * h + 2) = 2 ^ e * 2 ^ z := by
      rw [← zpow_add₀ h2, ← zpow_natCast]; congr 1; rw [hz]; push_cast; ring
    rw [this]; exact mul_lt_mul_of_pos_right hhi hp
  have hy0 : 0 < v * 2 ^ z := mul_pos hv0 hp
  have hone : (1 / 2 : ℝ) ^ (2 * h) * 2 ^ (2 * h) = 1 := by
    rw [one_div_pow, one_div, inv_mul_cancel₀ (by positivity)]
  have hpow1 : (2 : ℝ) ^ (2 * h + 1) = 2 * 2 ^ (2 * h) := by rw [pow_succ]; ring
  have hpow2 : (2 : ℝ) ^ (2 * h + 2) = 4 * 2 ^ (2 * h) := by rw [pow_add]; ring
  have h32 : (32 : ℝ) ≤ 2 ^ (2 * h + 1) := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 * h + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨hlo', hhi', hy0, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hy0]
    calc (1 / 2 : ℝ) ^ (2 * h) * (v * 2 ^ z) ≤ (1 / 2 : ℝ) ^ (2 * h) * (4 * 2 ^ (2 * h)) :=
          mul_le_mul_of_nonneg_left (by rw [← hpow2]; exact hhi'.le) (by positivity)
      _ = 4 * ((1 / 2 : ℝ) ^ (2 * h) * 2 ^ (2 * h)) := by ring
      _ = 4 := by rw [hone, mul_one]
  · rw [div_le_iff₀ hy0]
    calc (4 : ℝ) = 4 * ((1 / 2 : ℝ) ^ (2 * h) * 2 ^ (2 * h)) := by rw [hone, mul_one]
      _ = 2 * (1 / 2 : ℝ) ^ (2 * h) * (2 * 2 ^ (2 * h)) := by ring
      _ ≤ 2 * (1 / 2 : ℝ) ^ (2 * h) * (v * 2 ^ z) :=
          mul_le_mul_of_nonneg_left (by rw [← hpow1]; exact hlo') (by positivity)
  · rw [div_le_iff₀ hy0, one_mul]
    linarith

/-- The AGM–logarithm bounds for `k ∈ [2^(−2h), 2 · 2^(−2h)]`, `h ≥ 2`. -/
theorem agmLog_bounds {k : ℝ} (h : ℕ) (hh : 2 ≤ h) (hk1 : (1 / 2 : ℝ) ^ (2 * h) ≤ k)
    (hk2 : k ≤ 2 * (1 / 2 : ℝ) ^ (2 * h)) (hk3 : k ≤ 1) :
    0 < k ∧ |(Real.pi / 2) / AGM 1 k - Real.log (4 / k)| ≤ (2 * h + 2) * (1 / 2 : ℝ) ^ (4 * h) ∧
      (2 * h + 2) * (1 / 2 : ℝ) ^ (4 * h) ≤ 1 ∧ (Real.pi / 2) / AGM 1 k ≤ 2 * h + 3 ∧
      1 / (2 * h + 3) ≤ AGM 1 k ∧ AGM 1 k ≤ 1 := by
  have hq0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * h) := by positivity
  have hk0 : 0 < k := lt_of_lt_of_le hq0 hk1
  have hM0 : 0 < AGM 1 k := AGM_one_pos hk0
  have herr := abs_pi_div_AGM_sub_log_le hk0 hk3
  have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogk : -(2 * h) ≤ Real.log k := by
    have h1 : Real.log ((1 / 2 : ℝ) ^ (2 * h)) ≤ Real.log k := Real.log_le_log hq0 hk1
    rw [Real.log_pow, one_div, Real.log_inv] at h1
    push_cast at h1
    nlinarith
  have hlogk0 : Real.log k ≤ 0 := Real.log_nonpos hk0.le hk3
  have hksq : k ^ 2 / 4 ≤ (1 / 2 : ℝ) ^ (4 * h) := by
    have : k ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ (2 * h)) ^ 2 := pow_le_pow_left₀ hk0.le hk2 2
    have e : (2 * (1 / 2 : ℝ) ^ (2 * h)) ^ 2 = 4 * (1 / 2 : ℝ) ^ (4 * h) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    linarith
  have hbound : k ^ 2 / 4 * (2 - Real.log k) ≤ (2 * h + 2) * (1 / 2 : ℝ) ^ (4 * h) := by
    calc k ^ 2 / 4 * (2 - Real.log k) ≤ (1 / 2 : ℝ) ^ (4 * h) * (2 * h + 2) :=
          mul_le_mul hksq (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  have herr' := herr.trans hbound
  have hsmall : (2 * h + 2) * (1 / 2 : ℝ) ^ (4 * h) ≤ 1 := by
    have h1 : (2 * h + 2 : ℕ) ≤ 2 ^ (4 * h) :=
      ((Nat.lt_two_pow_self (n := 2 * h + 2)).le).trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : ((2 * h + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * h) := by exact_mod_cast h1
    have h3 : (2 : ℝ) ^ (4 * h) * (1 / 2 : ℝ) ^ (4 * h) = 1 := by
      rw [one_div_pow, one_div, mul_inv_cancel₀ (by positivity)]
    push_cast at h2
    calc (2 * h + 2) * (1 / 2 : ℝ) ^ (4 * h) ≤ (2 : ℝ) ^ (4 * h) * (1 / 2 : ℝ) ^ (4 * h) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 1 := h3
  have hlog4k : Real.log (4 / k) ≤ 2 * h + 2 := by
    have h1 : 4 / k ≤ 4 * 2 ^ (2 * h) := by
      rw [div_le_iff₀ hk0]
      have : (1 / 2 : ℝ) ^ (2 * h) * 2 ^ (2 * h) = 1 := by
        rw [one_div_pow, one_div, inv_mul_cancel₀ (by positivity)]
      calc (4 : ℝ) = 4 * 2 ^ (2 * h) * (1 / 2 : ℝ) ^ (2 * h) := by
            rw [mul_assoc, mul_comm ((2 : ℝ) ^ (2 * h)), this, mul_one]
        _ ≤ 4 * 2 ^ (2 * h) * k := mul_le_mul_of_nonneg_left hk1 (by positivity)
    have h2 : Real.log (4 / k) ≤ Real.log (4 * 2 ^ (2 * h)) :=
      Real.log_le_log (by positivity) h1
    have h3 : (4 : ℝ) * 2 ^ (2 * h) = 2 ^ (2 * h + 2) := by rw [pow_add]; ring
    rw [h3, Real.log_pow] at h2
    push_cast at h2
    nlinarith
  have hq : (Real.pi / 2) / AGM 1 k ≤ 2 * h + 3 := by
    have := (abs_le.mp herr').2
    linarith
  refine ⟨hk0, herr', hsmall, hq, ?_, ?_⟩
  · have hpi := Real.pi_gt_three
    rw [div_le_iff₀ hM0] at hq
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have := AGM_le_max one_pos hk0
    rwa [max_eq_left hk3] at this

/-- `32 h + 48 ≤ 2^(5h)` for `h ≥ 2`. -/
theorem lin_le_two_pow_five {h : ℕ} (hh : 2 ≤ h) : 32 * h + 48 ≤ 2 ^ (5 * h) := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    calc 32 * (h + 1) + 48 ≤ 2 * (32 * h + 48) := by omega
      _ ≤ 2 * 2 ^ (5 * h) := by omega
      _ ≤ 2 ^ (5 * (h + 1)) := by
          rw [show 5 * (h + 1) = 5 * h + 5 by ring, pow_add, mul_comm]
          exact Nat.mul_le_mul_left (2 ^ (5 * h)) (by norm_num)

/-! ### The rounded-down AGM -/

/-- After `S = 2 ⌈lg 2h⌉ + 3` rounded-down steps from `(1, ⌊k⌋_w)`: with
`δ = (2 + 8 S) 2^(−w)`, `b_S ≤ AGM(1, k) ≤ a_S + δ`, `b_S ≥ 1/(8h + 12)`, `a_S ≤ 1` and
`a_S + δ − b_S ≤ 8 · 2^(−5h) + 2 δ`. -/
theorem lnAgm_spec {w : ℕ} (hw : 64 ≤ w) {k : ℝ} (h : ℕ) (hh : 2 ≤ h) (hh4 : w + 5 ≤ 4 * h)
    (hh4' : 4 * h ≤ w + 8) (hk1 : (1 / 2 : ℝ) ^ (2 * h) ≤ k)
    (hk2 : k ≤ 2 * (1 / 2 : ℝ) ^ (2 * h)) (hk3 : k ≤ 1)
    {kLo : AzFloat} {kl : ℝ} (hkl : kLo.toVal = some (kl : EReal)) (hfl : FloorOf w k kl) :
    ∃ aS bl : ℝ,
      (agmIterLoN w (2 * Nat.clog 2 (2 * h) + 3) (one, kLo)).1.toVal = some (aS : EReal) ∧
      (agmIterLoN w (2 * Nat.clog 2 (2 * h) + 3) (one, kLo)).2.toVal = some (bl : EReal) ∧
      bl ≤ AGM 1 k ∧
      AGM 1 k ≤ aS + (2 * (1 / 2 : ℝ) ^ w
        + 8 * (1 / 2 : ℝ) ^ w * ((2 * Nat.clog 2 (2 * h) + 3 : ℕ) : ℝ)) ∧
      1 / (8 * h + 12) ≤ bl ∧ 0 ≤ aS ∧ aS ≤ 1 ∧
      aS + (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * ((2 * Nat.clog 2 (2 * h) + 3 : ℕ) : ℝ))
        - bl ≤ 8 * (1 / 2 : ℝ) ^ (5 * h)
          + 2 * (2 * (1 / 2 : ℝ) ^ w
            + 8 * (1 / 2 : ℝ) ^ w * ((2 * Nat.clog 2 (2 * h) + 3 : ℕ) : ℝ)) := by
  have : NeZero w := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  have hu32 : (w : ℝ) * u ≤ (1 / 2 : ℝ) ^ 32 := mul_half_pow_le hw
  have hw64 : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hu38 : u ≤ (1 / 2 : ℝ) ^ 38 := by
    have : (64 : ℝ) * u ≤ (w : ℝ) * u := mul_le_mul_of_nonneg_right hw64 hu0.le
    have e : (1 / 2 : ℝ) ^ 32 = 64 * (1 / 2 : ℝ) ^ 38 := by norm_num
    linarith
  have hu8 : u ≤ 1 / 8 := hu38.trans (by norm_num)
  obtain ⟨hk0, -, -, hq, hMlo, hM1⟩ := agmLog_bounds h hh hk1 hk2 hk3
  set S := 2 * Nat.clog 2 (2 * h) + 3 with hS
  have hS1 : 1 ≤ S := by omega
  have hclog : Nat.clog 2 (2 * h) ≤ 2 * h := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hSw : S ≤ w + 11 := by omega
  have hSw' : (S : ℝ) ≤ w + 11 := by exact_mod_cast hSw
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  set δ := 2 * u + 8 * u * (S : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ_le : δ ≤ 1 / 2 := by
    have h1 : 8 * u * (S : ℝ) ≤ 8 * u * (w + 11) := mul_le_mul_of_nonneg_left hSw' (by positivity)
    have e : (1 / 2 : ℝ) ^ 32 = 64 * (1 / 2 : ℝ) ^ 38 := by norm_num
    nlinarith
  -- the initial pair
  have h0 : RelLower 1 k 0 (2 * u) (one, kLo) := by
    refine ⟨1, kl, toVal_one', hkl, ?_, ?_, ?_, ?_⟩
    · simp only [agmA_zero]; linarith
    · simp only [agmA_zero]; exact le_rfl
    · simp only [agmB_zero]; linarith [hfl.ge]
    · simp only [agmB_zero]; exact hfl.le
  have hiter := relLower_agmIterLoN one_pos hk0 w hu8 S 0 (δ := 2 * u) (by positivity)
    (by rw [← hδ]; exact hδ_le) h0
  rw [Nat.zero_add] at hiter
  obtain ⟨aS, bl, haS, hbl, haS1, haS2, hbl1, hbl2⟩ := hiter
  rw [← hδ] at haS1 hbl1
  -- the exact iterates
  have hgap := agm_log_gap hk0 hk3 h hk1
  rw [← hS] at hgap
  have hbM : agmB 1 k S ≤ AGM 1 k := agmB_le_AGM one_pos hk0 hS1
  have hMa : AGM 1 k ≤ agmA 1 k S := AGM_le_agmA one_pos hk0 hS1
  have haS1' : agmA 1 k S ≤ 1 := agmA_one_le hk0 hk3 hS1
  have hbS0 : 0 < agmB 1 k S := (agm_pos one_pos hk0 S).2
  have hba : agmB 1 k S ≤ agmA 1 k S := agmB_le_agmA one_pos hk0 hS1
  have hbSlo : 1 / (4 * h + 6) ≤ agmB 1 k S := by
    have h1 : 8 * (1 / 2 : ℝ) ^ (5 * h) ≤ 1 / (2 * (2 * h + 3)) := by
      have hn := lin_le_two_pow_five hh
      have hn' : ((32 * h + 48 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (5 * h) := by exact_mod_cast hn
      push_cast at hn'
      have hpow1 : (2 : ℝ) ^ (5 * h) * (1 / 2 : ℝ) ^ (5 * h) = 1 := by
        rw [one_div_pow, one_div, mul_inv_cancel₀ (by positivity)]
      have h1' : (32 * h + 48) * (1 / 2 : ℝ) ^ (5 * h) ≤ 1 := by
        calc (32 * h + 48) * (1 / 2 : ℝ) ^ (5 * h) ≤ 2 ^ (5 * h) * (1 / 2 : ℝ) ^ (5 * h) :=
              mul_le_mul_of_nonneg_right hn' (by positivity)
          _ = 1 := hpow1
      rw [le_div_iff₀ (by positivity)]
      calc 8 * (1 / 2 : ℝ) ^ (5 * h) * (2 * (2 * h + 3))
          = (32 * h + 48) * (1 / 2 : ℝ) ^ (5 * h) := by
            ring
        _ ≤ 1 := h1'
    have h2 : (1 : ℝ) / (2 * h + 3) - 1 / (2 * (2 * h + 3)) = 1 / (4 * h + 6) := by
      field_simp; ring
    linarith
  have hAδ : agmA 1 k S ≤ aS + δ := by
    have : agmA 1 k S * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right haS1' hδ0
    linarith
  have haS0 : 0 ≤ aS :=
    le_trans (mul_nonneg (agm_pos one_pos hk0 S).1.le (by linarith)) haS1
  refine ⟨aS, bl, haS, hbl, hbl2.trans hbM, hMa.trans hAδ, ?_, haS0, haS2.trans haS1', ?_⟩
  · have h1 : agmB 1 k S * (1 / 2) ≤ agmB 1 k S * (1 - δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hbS0.le
    have h2 : (1 : ℝ) / (8 * h + 12) = 1 / (4 * h + 6) * (1 / 2) := by field_simp; ring
    rw [h2]
    calc 1 / (4 * h + 6) * (1 / 2 : ℝ) ≤ agmB 1 k S * (1 / 2) :=
          mul_le_mul_of_nonneg_right hbSlo (by norm_num)
      _ ≤ agmB 1 k S * (1 - δ) := h1
      _ ≤ bl := hbl1
  · have h1 : δ * agmB 1 k S ≤ δ * 1 :=
      mul_le_mul_of_nonneg_left (hba.trans haS1') hδ0
    nlinarith

/-- The upper end `ah = ⌈a_S + δ⌉_w` of the AGM bracket: `M ≤ ah ≤ 2` and
`ah − b_S ≤ g + 3δ` from `a_S + δ − b_S ≤ g + 2δ` (pure real arithmetic). -/
theorem ln_agm_widen {w : ℕ} (hw : 64 ≤ w) {S : ℕ} (hS3 : 3 ≤ S) (hSw : (S : ℝ) ≤ w + 11)
    {aS bl M g ah : ℝ} (haS1 : aS ≤ 1)
    (hMaS : M ≤ aS + (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ)))
    (hwidth0 : aS + (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ)) - bl
      ≤ g + 2 * (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ)))
    (hcah : CeilOf w (aS + (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ))) ah) :
    M ≤ ah ∧ ah ≤ 2 ∧ ah - bl ≤ g + 3 * (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ)) := by
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hu32 : (w : ℝ) * u ≤ (1 / 2 : ℝ) ^ 32 := mul_half_pow_le hw
  have hw64 : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hu38 : u ≤ (1 / 2 : ℝ) ^ 38 := by
    have : (64 : ℝ) * u ≤ (w : ℝ) * u := mul_le_mul_of_nonneg_right hw64 hu0.le
    have e : (1 / 2 : ℝ) ^ 32 = 64 * (1 / 2 : ℝ) ^ 38 := by norm_num
    linarith
  have hu8 : u ≤ 1 / 8 := hu38.trans (by norm_num)
  set δ := 2 * u + 8 * u * (S : ℝ) with hδ
  have hS3' : (3 : ℝ) ≤ S := by exact_mod_cast hS3
  have hδ_le : δ ≤ 1 / 2 := by
    have h1 : 8 * u * (S : ℝ) ≤ 8 * u * (w + 11) := mul_le_mul_of_nonneg_left hSw (by positivity)
    have e : (1 / 2 : ℝ) ^ 32 = 64 * (1 / 2 : ℝ) ^ 38 := by norm_num
    nlinarith
  have h1 : aS + δ ≤ 3 / 2 := by linarith
  have h2 := hcah.le_of_le h1
  have h3 : 3 * u ≤ δ := by nlinarith
  refine ⟨hMaS.trans hcah.ge, ?_, ?_⟩
  · have : 2 * (3 / 2 : ℝ) * u ≤ 2 * (3 / 2) * (1 / 8) :=
      mul_le_mul_of_nonneg_left hu8 (by norm_num)
    linarith
  · linarith

/-! ### The term `ℓ ln 2` -/

/-- `pb` is a bracket of `π` fit for the working precision `w`: ends with values `0 ≤ pl < π ≤ ph`
and width at most `piEps w` (what `lnBracketCore` needs; `piBracket w` qualifies, and so does
`piBracket W` for any `W ≥ w`). -/
def PiBracketFor (w : ℕ) (pb : AzFloat × AzFloat) : Prop :=
  ∃ pl ph : ℝ, pb.1.toVal = some (pl : EReal) ∧ pb.2.toVal = some (ph : EReal) ∧
    0 ≤ pl ∧ pl < Real.pi ∧ Real.pi ≤ ph ∧ ph - pl ≤ piEps w

/-- `lb` is a bracket of `ln 2` fit for the working precision `w`: ends with values
`1/5 ≤ ll ≤ ln 2 ≤ lh` and width at most `8 · 2^(−w)`. -/
def Ln2BracketFor (w : ℕ) (lb : AzFloat × AzFloat) : Prop :=
  ∃ ll lh : ℝ, lb.1.toVal = some (ll : EReal) ∧ lb.2.toVal = some (lh : EReal) ∧
    ll ≤ Real.log 2 ∧ Real.log 2 ≤ lh ∧ lh - ll ≤ 8 * (1 / 2 : ℝ) ^ w ∧ 1 / 5 ≤ ll

theorem piBracketFor_piBracket {w : ℕ} (hw : 64 ≤ w) : PiBracketFor w (piBracket w) :=
  piBracket_spec hw

theorem ln2BracketFor_ln2Bracket {w : ℕ} (hw : 2 ≤ w) : Ln2BracketFor w (ln2Bracket w) := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨ll, lh, h1, h2, h3, h4, h5, h6⟩ := ln2Bracket_spec w
  exact ⟨ll, lh, h1, h2, h3, h4, h5, h6 hw⟩

/-- A bracket fit for a finer precision `W ≥ w` is fit for `w`. -/
theorem PiBracketFor.of_le {w W : ℕ} {pb : AzFloat × AzFloat} (hw : 4 ≤ w) (hW : w ≤ W)
    (h : PiBracketFor W pb) : PiBracketFor w pb := by
  obtain ⟨pl, ph, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨pl, ph, h1, h2, h3, h4, h5, h6.trans (piEps_antitone hw hW)⟩

/-- A bracket fit for a finer precision `W ≥ w` is fit for `w`. -/
theorem Ln2BracketFor.of_le {w W : ℕ} {lb : AzFloat × AzFloat} (hW : w ≤ W)
    (h : Ln2BracketFor W lb) : Ln2BracketFor w lb := by
  obtain ⟨ll, lh, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ll, lh, h1, h2, h3, h4, h5.trans ?_, h6⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hW)
    (by norm_num)

/-- The bracket of `ℓ ln 2`: `|ℓ|` times the float bracket of `ln 2`, rounded outward, the signs
restored by negation when `ℓ < 0`. -/
theorem ln_L_spec {w : ℕ} (hw : 64 ≤ w) {lb : AzFloat × AzFloat} (hlb : Ln2BracketFor w lb)
    (ℓ : AzInt) :
    ∃ LLo LHi : ℝ,
      (if ℓ.sign = true then (mulPrecRound (ofAzNat ℓ.abs) lb.1 w .Floor).1
        else -(mulPrecRound (ofAzNat ℓ.abs) lb.2 w .Ceiling).1).toVal
          = some (LLo : EReal) ∧
      (if ℓ.sign = true then (mulPrecRound (ofAzNat ℓ.abs) lb.2 w .Ceiling).1
        else -(mulPrecRound (ofAzNat ℓ.abs) lb.1 w .Floor).1).toVal
          = some (LHi : EReal) ∧
      LLo ≤ (ℓ.toInt : ℝ) * Real.log 2 ∧ (ℓ.toInt : ℝ) * Real.log 2 ≤ LHi ∧
      LHi - LLo ≤ 12 * |(ℓ.toInt : ℝ)| * (1 / 2 : ℝ) ^ w ∧
      |LLo| ≤ 2 * |(ℓ.toInt : ℝ)| ∧ |LHi| ≤ 2 * |(ℓ.toInt : ℝ)| := by
  have : NeZero w := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 1000 := by
    calc u ≤ (1 / 2 : ℝ) ^ 64 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
      _ ≤ 1 / 1000 := by norm_num
  obtain ⟨a, b, ha, hb, haL, hLb, hab, ha5⟩ := hlb
  rw [← hu_def] at hab
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hb1 : b ≤ 71 / 100 := by linarith
  set M : ℝ := (ℓ.abs.toNat : ℝ) with hM_def
  have hM0 : 0 ≤ M := by positivity
  have hM : (ofAzNat ℓ.abs).toVal = some (M : EReal) := toVal_ofAzNat _
  obtain ⟨A, hA, hfA⟩ := mulFloor_err hM ha w (mul_nonneg hM0 ha0.le)
  obtain ⟨B, hB, hcB⟩ := mulCeiling_err hM hb w (mul_nonneg hM0 hb0.le)
  have hA1 := hfA.le
  have hA2 := hfA.ge
  have hA0 := hfA.nonneg
  have hB1 := hcB.ge
  have hB2 := hcB.le
  rw [← hu_def] at hA2 hB2
  have hMa : M * a ≤ M * Real.log 2 := mul_le_mul_of_nonneg_left haL hM0
  have hMb : M * Real.log 2 ≤ M * b := mul_le_mul_of_nonneg_left hLb hM0
  have hMb7 : M * b ≤ M * (71 / 100) := mul_le_mul_of_nonneg_left hb1 hM0
  have hMa7 : M * a ≤ M * (71 / 100) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have hMab : M * (b - a) ≤ M * (8 * u) := mul_le_mul_of_nonneg_left hab hM0
  have hMbu : 2 * (M * b) * u ≤ 2 * (M * (71 / 100)) * u := by
    have := mul_le_mul_of_nonneg_right hMb7 hu0.le; linarith
  have hMau : 2 * (M * a) * u ≤ 2 * (M * (71 / 100)) * u := by
    have := mul_le_mul_of_nonneg_right hMa7 hu0.le; linarith
  have hMu : M * (71 / 100) * u ≤ M * (71 / 100) * (1 / 1000) :=
    mul_le_mul_of_nonneg_left hu1 (by positivity)
  have hwidth : B - A ≤ 12 * M * u := by linarith
  have hBle : B ≤ 2 * M := by linarith
  have hAle : A ≤ 2 * M := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hℓabs : |(ℓ.toInt : ℝ)| = M := by
    unfold AzInt.toInt
    split_ifs <;> push_cast <;> rw [← hM_def]
    · exact abs_of_nonneg hM0
    · rw [abs_neg]; exact abs_of_nonneg hM0
  rw [hℓabs]
  by_cases hs : ℓ.sign = true
  · have hℓ : (ℓ.toInt : ℝ) = M := by
      simp only [AzInt.toInt, hs, ↓reduceIte, Int.cast_natCast]
      rw [hM_def]
    simp only [hs, ↓reduceIte]
    rw [hℓ]
    refine ⟨A, B, hA, hB, hA1.trans hMa, hMb.trans hB1, hwidth, ?_, ?_⟩
    · rw [abs_of_nonneg hA0]; exact hAle
    · rw [abs_of_nonneg hB0]; exact hBle
  · have hs' : ℓ.sign = false := by simpa using hs
    have hℓ : (ℓ.toInt : ℝ) = -M := by
      simp only [AzInt.toInt, hs', Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      rw [hM_def]
    simp only [hs', Bool.false_eq_true, ↓reduceIte]
    rw [hℓ]
    refine ⟨-B, -A, by rw [toVal_neg, hB]; rfl, by rw [toVal_neg, hA]; rfl, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · rw [abs_neg, abs_of_nonneg hB0]; exact hBle
    · rw [abs_neg, abs_of_nonneg hA0]; exact hAle

/-! ### The bracket -/

set_option maxHeartbeats 400000 in
/-- `lnAgmBracket pb lb x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`), for
any brackets `pb` of `π` and `lb` of `ln 2` fit for `w`. -/
theorem lnAgmBracket_spec {w : ℕ} (hw : 64 ≤ w) {pb lb : AzFloat × AzFloat}
    (hpb : PiBracketFor w pb) (hlb : Ln2BracketFor w lb) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, (lnAgmBracket pb lb (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnAgmBracket pb lb (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  have : NeZero w := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  have hu32 : (w : ℝ) * u ≤ (1 / 2 : ℝ) ^ 32 := mul_half_pow_le hw
  have hw64 : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hu38 : u ≤ (1 / 2 : ℝ) ^ 38 := by
    have : (64 : ℝ) * u ≤ (w : ℝ) * u := mul_le_mul_of_nonneg_right hw64 hu0.le
    have e : (1 / 2 : ℝ) ^ 32 = 64 * (1 / 2 : ℝ) ^ 38 := by norm_num
    linarith
  have hu8 : u ≤ 1 / 8 := hu38.trans (by norm_num)
  -- the value of `x`
  set v := finiteVal true e m with hv_def
  have hx : (finite true e q m hv).toVal = some (v : EReal) := toVal_finite _ _ _ _ _
  have hv0 : 0 < v := finiteVal_true_pos e hv
  obtain ⟨hvlo, hvhi⟩ := abs_finiteVal_bounds true e hv
  rw [abs_of_pos hv0] at hvlo hvhi
  -- the parameters
  set h := lnH w with hh_def
  have hh2 : 2 ≤ h := by unfold lnH at hh_def; omega
  have hh4 : w + 5 ≤ 4 * h := by unfold lnH at hh_def; omega
  have hh4' : 4 * h ≤ w + 8 := by unfold lnH at hh_def; omega
  have hhw : 2 * h + 2 ≤ w := by unfold lnH at hh_def; omega
  have hS_eq : lnSteps w = 2 * Nat.clog 2 (2 * h) + 3 := rfl
  set S := 2 * Nat.clog 2 (2 * h) + 3 with hS
  have hclog : Nat.clog 2 (2 * h) ≤ 2 * h := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hSw : (S : ℝ) ≤ w + 11 := by
    have : S ≤ w + 11 := by omega
    exact_mod_cast this
  -- the scaled argument
  set ℓ : AzInt := (AzNat.ofNat (2 * h + 2)).toAzInt - e with hℓ
  have hℓ_int : ℓ.toInt = ((2 * h + 2 : ℕ) : ℤ) - e.toInt := by
    rw [hℓ, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  have hy : ((finite true e q m hv) <<< ℓ).toVal = some ((v * (2 : ℝ) ^ ℓ.toInt : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal hx ℓ
  rw [hℓ_int] at hy
  obtain ⟨hy1, hy2, hy0, hk1, hk2, hk3⟩ := ln_scale hv0 hvlo hvhi h hh2
  set yv := v * (2 : ℝ) ^ (((2 * h + 2 : ℕ) : ℤ) - e.toInt) with hyv
  set k := 4 / yv with hk
  obtain ⟨hk0, herr, hsmall, hq, hMlo, hM1⟩ := agmLog_bounds h hh2 hk1 hk2 hk3
  have hM0 : 0 < AGM 1 k := AGM_one_pos hk0
  have h4k : 4 / k = yv := by rw [hk]; field_simp
  rw [h4k] at herr
  -- `k` enclosed from below
  obtain ⟨kl, hkl, hfl⟩ := divFloor_err toVal_four hy hy0 (by norm_num) w
  rw [← hk] at hfl
  -- the AGM
  obtain ⟨aS, bl, haS, hbl, hblM, hMaS, hbllo, haS0, haS1, hwidth0⟩ :=
    lnAgm_spec hw h hh2 hh4 hh4' hk1 hk2 hk3 hkl hfl
  rw [← hS] at haS hbl hMaS hwidth0
  set δ := 2 * u + 8 * u * (S : ℝ) with hδ
  have hδ_eq : (((8 * S + 2 : ℕ) : ℝ) * u : ℝ) = δ := by push_cast; rw [hδ]; ring
  have hD : (lnAgmDelta w S).toVal = some ((δ : ℝ) : EReal) := by
    rw [toVal_lnAgmDelta, ← hu_def, hδ_eq]
  have hbl0 : 0 < bl := lt_of_lt_of_le (by positivity) hbllo
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨ah, hah, hcah⟩ := addCeiling_err haS hD w (by linarith)
  obtain ⟨hMah, hah2, hwidth⟩ := ln_agm_widen hw (S := S) (by omega) hSw haS1 hMaS hwidth0 hcah
  have hah0 : 0 < ah := lt_of_lt_of_le hM0 hMah
  -- `π`
  obtain ⟨pl, ph, hpl, hph, hpl0, hplπ, hπph, hpw⟩ := hpb
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hpeps : piEps w ≤ 1 / 16 := piEps_le hw
  obtain ⟨qLo, hqLo, hfq⟩ := divFloor_err (toVal_half hpl) hah hah0 (by linarith) w
  obtain ⟨qHi, hqHi, hcq⟩ := divCeiling_err (toVal_half hph) hbl hbl0 (by linarith) w
  -- `ε`
  set eps := powerOf2 ((AzNat.ofNat (Nat.size (2 * h + 2))).toAzInt
    - (AzNat.ofNat (4 * h)).toAzInt) with heps
  have hE : eps.toVal = some (((2 : ℝ) ^ (((Nat.size (2 * h + 2) : ℕ) : ℤ) - ((4 * h : ℕ) : ℤ)) : ℝ)
      : EReal) := by
    rw [heps, toVal_powerOf2, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]
  set Ev : ℝ := (2 : ℝ) ^ (((Nat.size (2 * h + 2) : ℕ) : ℤ) - ((4 * h : ℕ) : ℤ)) with hEv
  have hEv_eq : Ev = (2 : ℝ) ^ (Nat.size (2 * h + 2)) * (1 / 2 : ℝ) ^ (4 * h) := by
    rw [hEv, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow, one_div,
      div_eq_mul_inv]
  have hEv_ge : (2 * h + 2) * (1 / 2 : ℝ) ^ (4 * h) ≤ Ev := by
    rw [hEv_eq]
    have h1 : (2 * h + 2 : ℕ) < 2 ^ (Nat.size (2 * h + 2)) := Nat.lt_size_self _
    have h2 : ((2 * h + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.size (2 * h + 2)) := by exact_mod_cast h1.le
    push_cast at h2
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hEv_le : Ev ≤ (4 * h + 4) * (1 / 2 : ℝ) ^ (4 * h) := by
    rw [hEv_eq]
    have h1 := two_pow_size_le (2 * h + 2) (by omega)
    have h2 : (2 : ℝ) ^ (Nat.size (2 * h + 2)) ≤ 2 * (2 * h + 2 : ℕ) := by exact_mod_cast h1
    push_cast at h2
    have : (2 : ℝ) ^ (Nat.size (2 * h + 2)) ≤ 4 * h + 4 := by linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hEv0 : 0 ≤ Ev := by rw [hEv]; positivity
  have herrE : |(Real.pi / 2) / AGM 1 k - Real.log yv| ≤ Ev := herr.trans hEv_ge
  -- `ℓ ln 2`
  obtain ⟨LLo, LHi, hLLo, hLHi, hL1, hL2, hLw, hLLo_abs, hLHi_abs⟩ := ln_L_spec hw hlb ℓ
  -- the final combination
  simp only [lnAgmBracket]
  rw [← hh_def, hS_eq, ← hℓ, ← heps]
  obtain ⟨lo1, hlo1, hlo1a, hlo1b⟩ := subFloor_abs hqLo hE w
  obtain ⟨lo, hlo, hloa, hlob⟩ := subFloor_abs hlo1 hLHi w
  obtain ⟨hi1, hhi1, hhi1a, hhi1b⟩ := addCeiling_abs hqHi hE w
  obtain ⟨hi, hhi, hhia, hhib⟩ := subCeiling_abs hhi1 hLLo w
  -- `ln y = ln x + ℓ ln 2`
  have hlogy : Real.log yv = Real.log v + (ℓ.toInt : ℝ) * Real.log 2 := by
    rw [hyv, Real.log_mul hv0.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow, hℓ_int]
  have hQ : (pl / 2) / ah ≤ (Real.pi / 2) / AGM 1 k := by
    rw [div_le_div_iff₀ hah0 hM0]
    exact mul_le_mul (by linarith) hMah hM0.le (by linarith)
  have hQ' : (Real.pi / 2) / AGM 1 k ≤ (ph / 2) / bl := by
    rw [div_le_div_iff₀ hM0 hbl0]
    exact mul_le_mul (by linarith) hblM hbl0.le (by linarith)
  obtain ⟨herr1, herr2⟩ := abs_le.mp herrE
  refine ⟨lo, hi, hlo, hhi, ?_, ?_, ?_⟩
  · -- `lo ≤ ln x`
    have : lo ≤ qLo - Ev - LHi := by linarith
    have h1 : qLo ≤ (Real.pi / 2) / AGM 1 k := hfq.le.trans hQ
    linarith
  · -- `ln x ≤ hi`
    have : qHi + Ev - LLo ≤ hi := by linarith
    have h1 : (Real.pi / 2) / AGM 1 k ≤ qHi := hQ'.trans hcq.ge
    linarith
  · -- the width
    have hSw' : (S : ℝ) ≤ w + 11 := hSw
    exact ln_final_bounds hw hh2 hh4 hh4' hSw' (e := e.toInt) (ℓz := (ℓ.toInt : ℝ))
      (by rw [hℓ_int]; push_cast
          have h1 : 2 * (h : ℝ) + 2 ≤ w := by exact_mod_cast hhw
          calc _ ≤ |2 * (h : ℝ) + 2| + |(e.toInt : ℝ)| := abs_sub _ _
            _ ≤ (w : ℝ) + |(e.toInt : ℝ)| + 8 := by
                rw [abs_of_nonneg (by positivity)]; linarith)
      hblM hMah hbllo hah2 hwidth hpl0 hplπ hπph hpw hfq hcq hEv0 hEv_le hLw hLLo_abs
      hLHi_abs hlo1a hlo1b hlob hhi1a hhi1b hhib

/-! ### The series path -/

theorem one_sub_mul_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 1 - a - b ≤ (1 - a) * (1 - b) := by
  nlinarith [mul_nonneg ha hb]

theorem one_sub_mul_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    1 - a - b - c ≤ (1 - a) * (1 - b) * (1 - c) := by
  nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
    mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr hc1)]

/-- `(k + 1)(2J + 1) ≥ w + 1` for `J = lnSeriesTerms k w`. -/
theorem lnSeriesTerms_spec (k w : ℕ) : w + 1 ≤ (k + 1) * (2 * lnSeriesTerms k w + 1) := by
  unfold lnSeriesTerms
  have h1 := Nat.div_add_mod (w + 1) (2 * (k + 1))
  have h2 := Nat.mod_lt (w + 1) (show 0 < 2 * (k + 1) by omega)
  nlinarith

theorem lnSeriesTerms_le {k w : ℕ} (hw : 3 ≤ w) : lnSeriesTerms k w ≤ w := by
  unfold lnSeriesTerms
  have := Nat.div_le_div_left (a := w + 1) (show 2 ≤ 2 * (k + 1) by omega) two_pos
  omega

theorem two_pow_lnSeriesK_le {w : ℕ} (hw : 1 ≤ w) : 2 ^ lnSeriesK w ≤ w :=
  (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)).trans (Nat.pow_log_le_self 2 (by omega))

/-- The partial sums of the series `Σ t^(2j+1)/(2j+1)` (DLMF 4.6.4 without the factor `2`). -/
noncomputable def lnSeriesPartial (t : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, t ^ (2 * j + 1) / (2 * j + 1)

theorem lnSeriesPartial_zero (t : ℝ) : lnSeriesPartial t 0 = 0 := by simp [lnSeriesPartial]

theorem lnSeriesPartial_succ (t : ℝ) (j : ℕ) :
    lnSeriesPartial t (j + 1) = lnSeriesPartial t j + t ^ (2 * j + 1) / (2 * j + 1) := by
  unfold lnSeriesPartial; rw [Finset.sum_range_succ]

theorem lnSeriesPartial_nonneg {t : ℝ} (ht : 0 ≤ t) (J : ℕ) : 0 ≤ lnSeriesPartial t J :=
  Finset.sum_nonneg fun j _ => by positivity

/-- **DLMF 4.6.4** as needed here: `ln((1+t)/(1−t)) = 2 Σ t^(2j+1)/(2j+1)`; for `0 ≤ t ≤ 1/2`,
`J` terms give a lower bound and leave a tail of at most `(8/3) t^(2J+1)`. -/
theorem log_atanh_series_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (J : ℕ) :
    2 * lnSeriesPartial t J ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤ 2 * lnSeriesPartial t J + 8 / 3 * t ^ (2 * J + 1) := by
  have habs : |t| < 1 := by rw [abs_of_nonneg ht0]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hlog : Real.log ((1 + t) / (1 - t)) = Real.log (1 + t) - Real.log (1 - t) :=
    Real.log_div (by linarith) (by linarith)
  rw [hlog]
  have hf0 : ∀ k : ℕ, 0 ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1) := fun k => by positivity
  have hsum_eq : ∀ J, ∑ j ∈ Finset.range J, 2 * (1 / (2 * (j : ℝ) + 1)) * t ^ (2 * j + 1)
      = 2 * lnSeriesPartial t J := by
    intro J
    unfold lnSeriesPartial
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  constructor
  · rw [← hsum_eq]
    exact sum_le_hasSum (Finset.range J) (fun i _ => hf0 i) hs
  · rw [← hsum_eq, ← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add J]
    have ht2 : t ^ 2 < 1 := by nlinarith
    have hg : ∀ i : ℕ, 2 * (1 / (2 * ((i + J : ℕ) : ℝ) + 1)) * t ^ (2 * (i + J) + 1)
        ≤ 2 * t ^ (2 * J + 1) * (t ^ 2) ^ i := by
      intro i
      have h1 : (1 : ℝ) / (2 * ((i + J : ℕ) : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ ((i + J : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have h2 : t ^ (2 * (i + J) + 1) = t ^ (2 * J + 1) * (t ^ 2) ^ i := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [h2]
      have h3 : 0 ≤ t ^ (2 * J + 1) * (t ^ 2) ^ i := by positivity
      calc 2 * (1 / (2 * ((i + J : ℕ) : ℝ) + 1)) * (t ^ (2 * J + 1) * (t ^ 2) ^ i)
          ≤ 2 * 1 * (t ^ (2 * J + 1) * (t ^ 2) ^ i) := by gcongr
        _ = 2 * t ^ (2 * J + 1) * (t ^ 2) ^ i := by ring
    have hsumm : Summable fun i : ℕ =>
        2 * (1 / (2 * ((i + J : ℕ) : ℝ) + 1)) * t ^ (2 * (i + J) + 1) :=
      (summable_nat_add_iff J).mpr hs.summable
    have hgeo : Summable fun i : ℕ => 2 * t ^ (2 * J + 1) * (t ^ 2) ^ i :=
      (summable_geometric_of_lt_one (by positivity) ht2).mul_left _
    have htail : ∑' i : ℕ, 2 * (1 / (2 * ((i + J : ℕ) : ℝ) + 1)) * t ^ (2 * (i + J) + 1)
        ≤ 8 / 3 * t ^ (2 * J + 1) := by
      calc ∑' i : ℕ, 2 * (1 / (2 * ((i + J : ℕ) : ℝ) + 1)) * t ^ (2 * (i + J) + 1)
          ≤ ∑' i : ℕ, 2 * t ^ (2 * J + 1) * (t ^ 2) ^ i := Summable.tsum_le_tsum hg hsumm hgeo
        _ = 2 * t ^ (2 * J + 1) * (1 - t ^ 2)⁻¹ := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ht2]
        _ ≤ 8 / 3 * t ^ (2 * J + 1) := by
            have h34 : (1 - t ^ 2)⁻¹ ≤ 4 / 3 := by
              rw [inv_le_comm₀ (by nlinarith) (by norm_num)]; nlinarith
            have : 0 ≤ t ^ (2 * J + 1) := by positivity
            nlinarith
    linarith

/-- The square-root reduction: with `L = ln m₀`, after `k` further roots from a value `y` with
`1 ≤ y`, `L/2^i − 6u ≤ ln y ≤ L/2^i`, the result `z` has `1 ≤ z` and
`L/2^(i+k) − 6u ≤ ln z ≤ L/2^(i+k)` (`u = 2^(−w)`). -/
theorem lnSqrtIter_spec {w : ℕ} (hw : 64 ≤ w) (L : ℝ) (k : ℕ) :
    ∀ (i : ℕ) (y : AzFloat) (yv : ℝ), y.toVal = some (yv : EReal) → 1 ≤ yv →
      Real.log yv ≤ L / 2 ^ i → L / 2 ^ i - 6 * (1 / 2 : ℝ) ^ w ≤ Real.log yv →
      ∃ zv : ℝ, (lnSqrtIter w k y).toVal = some (zv : EReal) ∧ 1 ≤ zv ∧
        Real.log zv ≤ L / 2 ^ (i + k) ∧ L / 2 ^ (i + k) - 6 * (1 / 2 : ℝ) ^ w ≤ Real.log zv := by
  induction k with
  | zero =>
    intro i y yv hy h1 h2 h3
    exact ⟨yv, hy, h1, by simpa using h2, by simpa using h3⟩
  | succ k ih =>
    intro i y yv hy h1 h2 h3
    have : NeZero w := ⟨by omega⟩
    obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
    have hu0 : 0 < u := by rw [hu_def]; positivity
    have hu6 : 6 * u ≤ 1 / 2 := by
      have : u ≤ (1 / 2 : ℝ) ^ 64 := by
        rw [hu_def]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
      have : (1 / 2 : ℝ) ^ 64 ≤ 1 / 12 := by norm_num
      linarith
    rw [← hu_def] at h3
    have hy0 : 0 < yv := by linarith
    obtain ⟨r, hr, hfr⟩ := sqrtFloor_err hy hy0.le w
    have hsq1 : 1 ≤ Real.sqrt yv := Real.one_le_sqrt.mpr h1
    have hsq0 : 0 < Real.sqrt yv := by linarith
    have hz : (maxOf (sqrtPrecRound y w .Floor).1 one).toVal = some ((max r 1 : ℝ) : EReal) :=
      toVal_maxOf hr toVal_one'
    have hz1 : 1 ≤ max r 1 := le_max_right _ _
    have hzle : max r 1 ≤ Real.sqrt yv := max_le hfr.le hsq1
    have hpow : L / 2 ^ (i + 1) = L / 2 ^ i / 2 := by rw [pow_succ, div_div]
    have hlog_le : Real.log (max r 1) ≤ L / 2 ^ (i + 1) := by
      rw [hpow]
      calc Real.log (max r 1) ≤ Real.log (Real.sqrt yv) :=
            Real.log_le_log (by linarith) hzle
        _ = Real.log yv / 2 := Real.log_sqrt hy0.le
        _ ≤ L / 2 ^ i / 2 := by linarith
    have hr_ge : Real.sqrt yv * (1 - 2 * u) ≤ r := by
      have := hfr.ge
      rw [← hu_def] at this
      linarith
    have hlog_ge : L / 2 ^ (i + 1) - 6 * u ≤ Real.log (max r 1) := by
      have hpos : 0 < Real.sqrt yv * (1 - 2 * u) := by
        apply mul_pos hsq0; linarith
      have h1' : Real.log (Real.sqrt yv * (1 - 2 * u)) ≤ Real.log (max r 1) :=
        Real.log_le_log hpos (hr_ge.trans (le_max_left _ _))
      rw [Real.log_mul hsq0.ne' (by linarith), Real.log_sqrt hy0.le] at h1'
      have hl2 : -(3 * u) ≤ Real.log (1 - 2 * u) := by
        have h := Real.one_sub_inv_le_log_of_pos (x := 1 - 2 * u) (by linarith)
        have : (1 - 2 * u)⁻¹ ≤ 1 + 3 * u := by
          rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
        linarith
      rw [hpow]
      linarith
    obtain ⟨zv, hzv, hzv1, hzv2, hzv3⟩ := ih (i + 1) _ (max r 1) hz hz1 hlog_le (by
      rw [hu_def] at hlog_ge; exact hlog_ge)
    refine ⟨zv, ?_, hzv1, ?_, ?_⟩
    · simpa [lnSqrtIter] using hzv
    · rwa [show i + (k + 1) = i + 1 + k by omega]
    · rwa [show i + (k + 1) = i + 1 + k by omega]

/-- The invariant of `lnSeriesLoop`: with `S_j = Σ_{i<j} t^(2i+1)/(2i+1)` and `u = 2^(−w)`, the
computed sum `s` and power `p` satisfy `S_j (1 − (10 + 20j)u) ≤ s ≤ S_j` and
`t^(2j+1) (1 − (8 + 20j)u) ≤ p ≤ t^(2j+1)`. -/
theorem lnSeriesLoop_spec {w : ℕ} (hw : 64 ≤ w) {t : ℝ} (ht0 : 0 ≤ t)
    {t2 : AzFloat} {t2v : ℝ} (ht2 : t2.toVal = some (t2v : EReal)) (ht2le : t2v ≤ t ^ 2)
    (ht2ge : t ^ 2 * (1 - 18 * (1 / 2 : ℝ) ^ w) ≤ t2v)
    {tau : AzFloat} {tauv : ℝ} (htau : tau.toVal = some (tauv : EReal)) (n : ℕ) :
    ∀ (j : ℕ) (s p : AzFloat) (sv pv : ℝ), j + n ≤ w →
      s.toVal = some (sv : EReal) → p.toVal = some (pv : EReal) →
      0 ≤ sv → sv ≤ lnSeriesPartial t j →
      lnSeriesPartial t j * (1 - (10 + 20 * j) * (1 / 2 : ℝ) ^ w) ≤ sv →
      0 ≤ pv → pv ≤ t ^ (2 * j + 1) → t ^ (2 * j + 1) * (1 - (8 + 20 * j) * (1 / 2 : ℝ) ^ w) ≤ pv →
      ∃ (m : ℕ) (sv' pv' : ℝ), j ≤ m ∧ m ≤ j + n ∧ (m = j + n ∨ pv' < tauv) ∧
        (lnSeriesLoop w t2 tau n j (s, p)).1.toVal = some (sv' : EReal) ∧
        (lnSeriesLoop w t2 tau n j (s, p)).2.toVal = some (pv' : EReal) ∧
        0 ≤ sv' ∧ sv' ≤ lnSeriesPartial t m ∧
        lnSeriesPartial t m * (1 - (10 + 20 * (m : ℝ)) * (1 / 2 : ℝ) ^ w) ≤ sv' ∧
        0 ≤ pv' ∧ pv' ≤ t ^ (2 * m + 1) ∧
        t ^ (2 * m + 1) * (1 - (8 + 20 * (m : ℝ)) * (1 / 2 : ℝ) ^ w) ≤ pv' := by
  induction n with
  | zero =>
    intro j s p sv pv _ hs hp hs0 hs1 hs2 hp0 hp1 hp2
    exact ⟨j, sv, pv, le_rfl, by omega, Or.inl (by omega), hs, hp, hs0, hs1, hs2, hp0, hp1, hp2⟩
  | succ n ih =>
    intro j s p sv pv hjn hs hp hs0 hs1 hs2 hp0 hp1 hp2
    have : NeZero w := ⟨by omega⟩
    by_cases hlt : (partialCompare p tau == some Ordering.lt) = true
    · -- the power is already below `tau`: stop
      have hrec : lnSeriesLoop w t2 tau (n + 1) j (s, p) = (s, p) := by
        simp only [lnSeriesLoop, hlt, ↓reduceIte]
      have hpt : pv < tauv := by
        rw [partialCompare_eq, hp, htau] at hlt
        simpa [compare_coe_coe, compare_lt_iff_lt] using hlt
      rw [hrec]
      exact ⟨j, sv, pv, le_rfl, by omega, Or.inr hpt, hs, hp, hs0, hs1, hs2, hp0, hp1, hp2⟩
    obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
    have hu0 : 0 < u := by rw [hu_def]; positivity
    have hwu : (w : ℝ) * u ≤ (1 / 2 : ℝ) ^ 32 := by rw [hu_def]; exact mul_half_pow_le hw
    have hwu' : 28 * ((w : ℝ) * u) ≤ 1 := by
      have : (1 / 2 : ℝ) ^ 32 ≤ 1 / 28 := by norm_num
      linarith
    have hju : ((j : ℝ) + 1) * u ≤ (w : ℝ) * u := by
      have : ((j : ℝ) + 1) ≤ w := by exact_mod_cast (show j + 1 ≤ w by omega)
      exact mul_le_mul_of_nonneg_right this hu0.le
    rw [← hu_def] at hs2 hp2 ht2ge
    set α := (8 + 20 * (j : ℝ)) * u with hα
    set β := (10 + 20 * (j : ℝ)) * u with hβ
    have hα0 : 0 ≤ α := by positivity
    have hα1 : α ≤ 1 := by rw [hα]; nlinarith
    have hβα : β = α + 2 * u := by rw [hα, hβ]; ring
    have h2u : 0 ≤ 1 - 2 * u := by nlinarith
    have hT0 : 0 ≤ t ^ (2 * j + 1) / (2 * j + 1) := by positivity
    have hpow0 : 0 ≤ t ^ (2 * j + 1) := by positivity
    have ht2v0 : 0 ≤ t2v := by
      refine le_trans ?_ ht2ge
      apply mul_nonneg (by positivity); nlinarith
    -- the term
    have hd : (ofAzNat (AzNat.ofNat (2 * j + 1))).toVal = some ((((2 * j + 1 : ℕ) : ℝ)) : EReal) :=
      toVal_ofAzNat_ofNat _
    have hdpos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
    obtain ⟨termv, hterm, hfterm⟩ := divFloor_err hp hd hdpos hp0 w
    have hcast : (((2 * j + 1 : ℕ) : ℝ)) = 2 * (j : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hfterm
    have hterm_le : termv ≤ t ^ (2 * j + 1) / (2 * j + 1) :=
      hfterm.le.trans (div_le_div_of_nonneg_right hp1 (by positivity))
    have hterm_ge : t ^ (2 * j + 1) / (2 * j + 1) * (1 - α - 2 * u) ≤ termv := by
      have h1 : t ^ (2 * j + 1) * (1 - α) / (2 * j + 1) ≤ pv / (2 * j + 1) :=
        div_le_div_of_nonneg_right hp2 (by positivity)
      have h2 : pv / (2 * j + 1) * (1 - 2 * u) ≤ termv := by
        have := hfterm.ge; rw [← hu_def] at this; linarith
      have h3 : t ^ (2 * j + 1) * (1 - α) / (2 * j + 1)
          = t ^ (2 * j + 1) / (2 * j + 1) * (1 - α) := by
        ring
      rw [h3] at h1
      calc t ^ (2 * j + 1) / (2 * j + 1) * (1 - α - 2 * u)
          ≤ t ^ (2 * j + 1) / (2 * j + 1) * ((1 - α) * (1 - 2 * u)) :=
            mul_le_mul_of_nonneg_left (one_sub_mul_two hα0 (by linarith)) hT0
        _ = t ^ (2 * j + 1) / (2 * j + 1) * (1 - α) * (1 - 2 * u) := by ring
        _ ≤ pv / (2 * j + 1) * (1 - 2 * u) := mul_le_mul_of_nonneg_right h1 h2u
        _ ≤ termv := h2
    -- the new sum
    obtain ⟨sv', hs', hfs'⟩ := addFloor_err hs hterm w (by linarith [hfterm.nonneg])
    have hS := lnSeriesPartial_succ t j
    have hS0 := lnSeriesPartial_nonneg ht0 (j + 1)
    have hs'_le : sv' ≤ lnSeriesPartial t (j + 1) := by rw [hS]; linarith [hfs'.le]
    have hs'_ge : lnSeriesPartial t (j + 1) * (1 - (10 + 20 * ((j + 1 : ℕ) : ℝ)) * u) ≤ sv' := by
      have h1 : lnSeriesPartial t (j + 1) * (1 - β) ≤ sv + termv := by
        rw [hS, add_mul]
        have : t ^ (2 * j + 1) / (2 * j + 1) * (1 - β)
            = t ^ (2 * j + 1) / (2 * j + 1) * (1 - α - 2 * u) := by
          rw [hβα]; ring
        linarith
      have h2 : (sv + termv) * (1 - 2 * u) ≤ sv' := by
        have := hfs'.ge; rw [← hu_def] at this; linarith
      have h3 : lnSeriesPartial t (j + 1) * (1 - β - 2 * u)
          ≤ lnSeriesPartial t (j + 1) * ((1 - β) * (1 - 2 * u)) :=
        mul_le_mul_of_nonneg_left (one_sub_mul_two (by positivity) (by linarith)) hS0
      have h4 : (10 + 20 * ((j + 1 : ℕ) : ℝ)) * u = β + 20 * u := by rw [hβ]; push_cast; ring
      rw [h4]
      have h5 : lnSeriesPartial t (j + 1) * (1 - (β + 20 * u))
          ≤ lnSeriesPartial t (j + 1) * (1 - β - 2 * u) :=
        mul_le_mul_of_nonneg_left (by linarith) hS0
      calc lnSeriesPartial t (j + 1) * (1 - (β + 20 * u))
          ≤ lnSeriesPartial t (j + 1) * ((1 - β) * (1 - 2 * u)) := h5.trans h3
        _ = lnSeriesPartial t (j + 1) * (1 - β) * (1 - 2 * u) := by ring
        _ ≤ (sv + termv) * (1 - 2 * u) := mul_le_mul_of_nonneg_right h1 h2u
        _ ≤ sv' := h2
    -- the new power
    obtain ⟨pv', hp', hfp'⟩ := mulFloor_err hp ht2 w (mul_nonneg hp0 ht2v0)
    have hpow_eq : t ^ (2 * (j + 1) + 1) = t ^ (2 * j + 1) * t ^ 2 := by ring
    have hp'_le : pv' ≤ t ^ (2 * (j + 1) + 1) := by
      rw [hpow_eq]
      exact hfp'.le.trans (mul_le_mul hp1 ht2le ht2v0 hpow0)
    have hp'_ge : t ^ (2 * (j + 1) + 1) * (1 - (8 + 20 * ((j + 1 : ℕ) : ℝ)) * u) ≤ pv' := by
      have h1 : t ^ (2 * j + 1) * (1 - α) * (t ^ 2 * (1 - 18 * u)) ≤ pv * t2v :=
        mul_le_mul hp2 ht2ge (by apply mul_nonneg (by positivity); nlinarith)
          hp0
      have h2 : pv * t2v * (1 - 2 * u) ≤ pv' := by
        have := hfp'.ge; rw [← hu_def] at this; linarith
      have h4 : (8 + 20 * ((j + 1 : ℕ) : ℝ)) * u = α + 18 * u + 2 * u := by rw [hα]; push_cast; ring
      rw [h4, hpow_eq]
      have hX : 0 ≤ t ^ (2 * j + 1) * t ^ 2 := by positivity
      calc t ^ (2 * j + 1) * t ^ 2 * (1 - (α + 18 * u + 2 * u))
          ≤ t ^ (2 * j + 1) * t ^ 2 * ((1 - α) * (1 - 18 * u) * (1 - 2 * u)) := by
            apply mul_le_mul_of_nonneg_left _ hX
            have := one_sub_mul_three hα0 (by positivity : (0 : ℝ) ≤ 18 * u)
              (by positivity : (0 : ℝ) ≤ 2 * u) (by linarith)
            linarith
        _ = t ^ (2 * j + 1) * (1 - α) * (t ^ 2 * (1 - 18 * u)) * (1 - 2 * u) := by ring
        _ ≤ pv * t2v * (1 - 2 * u) := mul_le_mul_of_nonneg_right h1 h2u
        _ ≤ pv' := h2
    -- the recursive call
    have hrec : lnSeriesLoop w t2 tau (n + 1) j (s, p)
        = lnSeriesLoop w t2 tau n (j + 1) ((addPrecRound s
            (divPrecRound p (ofAzNat (AzNat.ofNat (2 * j + 1))) w .Floor).1 w .Floor).1,
          (mulPrecRound p t2 w .Floor).1) := by
      simp only [lnSeriesLoop, hlt, Bool.false_eq_true, ↓reduceIte]
    rw [hrec]
    have hsv'0 : 0 ≤ sv' := hfs'.nonneg
    have hpv'0 : 0 ≤ pv' := hfp'.nonneg
    rw [hu_def] at hs'_ge hp'_ge
    obtain ⟨m, sv'', pv'', hm1, hm2, hstop, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      ih (j + 1) _ _ sv' pv' (by omega) hs' hp' hsv'0 hs'_le hs'_ge hpv'0 hp'_le hp'_ge
    refine ⟨m, sv'', pv'', by omega, by omega, ?_, h1, h2, h3, h4, h5, h6, h7, h8⟩
    rcases hstop with hstop | hstop
    · exact Or.inl (by omega)
    · exact Or.inr hstop

/-- The pure-real width budget of the series bracket: all the slacks are `O(W²) u` with
`W = w + |e| + 8`, far below `lnEps = 2^40 W^5 u`. -/
theorem lnSeries_final_bounds {u W Av Ev LLo LHi lo hi1 hi : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hW : 72 ≤ W) (hAv0 : 0 ≤ Av) (hAv1 : Av ≤ 1) (hEv0 : 0 ≤ Ev) (hEv : Ev ≤ 38 * W ^ 2 * u)
    (hLw : LHi - LLo ≤ 12 * W * u) (hLLo : |LLo| ≤ 2 * W) (hLHi : |LHi| ≤ 2 * W)
    (hlo : Av + LLo ≤ lo + 2 * |Av + LLo| * u)
    (hhi1ge : Av + Ev ≤ hi1) (hhi1 : hi1 ≤ Av + Ev + 2 * (Av + Ev) * u)
    (hhi : hi ≤ hi1 + LHi + 2 * |hi1 + LHi| * u) :
    hi - lo ≤ 2 ^ 40 * W ^ 5 * u := by
  obtain ⟨hLLo1, hLLo2⟩ := abs_le.mp hLLo
  obtain ⟨hLHi1, hLHi2⟩ := abs_le.mp hLHi
  have hW2 : W ≤ W ^ 2 := by nlinarith
  have hEvu : Ev * u ≤ 38 * W ^ 2 * u := by nlinarith
  have hhi1' : hi1 ≤ 3 + 114 * W ^ 2 * u := by nlinarith
  have habs1 : |Av + LLo| ≤ 1 + 2 * W := abs_le.mpr ⟨by linarith, by linarith⟩
  have habs2 : |hi1 + LHi| ≤ 3 + 114 * W ^ 2 * u + 2 * W := by
    rw [abs_le]; constructor <;> nlinarith
  have hW2u : W ^ 2 * u ≤ W ^ 2 := by nlinarith
  have h1 : 2 * |Av + LLo| * u ≤ 2 * (1 + 2 * W) * u := by nlinarith
  have h2 : 2 * |hi1 + LHi| * u ≤ 2 * (3 + 114 * W ^ 2 + 2 * W) * u := by nlinarith
  have hW5 : 400 * W ^ 2 ≤ 2 ^ 40 * W ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 72) hW 3]
  nlinarith

/-- `lnSeriesLead y₁ = c` says `y₁ ≤ 2^(−c−1)`, unless `c = 0`. -/
theorem lnSeriesLead_spec {y₁ : AzFloat} {v : ℝ} (hy : y₁.toVal = some (v : EReal)) :
    lnSeriesLead y₁ = 0 ∨ v ≤ (1 / 2 : ℝ) ^ (lnSeriesLead y₁ + 1) := by
  cases y₁ with
  | finite s e' q' m' hv' =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hy
    simp only [lnSeriesLead, exponent?]
    by_cases hs : e'.sign = true
    · left; simp [hs]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      rcases Nat.eq_zero_or_pos e'.abs.toNat with h0 | h0
      · left; omega
      · right
        rw [show e'.abs.toNat - 1 + 1 = e'.abs.toNat by omega]
        have hb := (abs_finiteVal_bounds s e' hv').2
        have hint : e'.toInt = -(e'.abs.toNat : ℤ) := by
          unfold AzInt.toInt
          rw [ite_eq_right hs]
        rw [hint, zpow_neg, zpow_natCast] at hb
        rw [one_div_pow, one_div, ← hy]
        exact (le_abs_self _).trans hb.le
  | zero => left; rfl
  | nan => left; rfl
  | infinity s => left; rfl

set_option maxHeartbeats 800000 in
/-- `lnSeriesBracketK k lb x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`),
for any bracket `lb` of `ln 2` fit for `w` and any `k` with `2^k ≤ w`. -/
theorem lnSeriesBracketK_spec {w k : ℕ} (hw : 64 ≤ w) (hk : 2 ^ k ≤ w) {lb : AzFloat × AzFloat}
    (hlb : Ln2BracketFor w lb) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ,
      (lnSeriesBracketK k lb (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnSeriesBracketK k lb (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu_def]; positivity
  have hu64 : u ≤ (1 / 2 : ℝ) ^ 64 := by
    rw [hu_def]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
  have hu1 : u ≤ 1 / 1000 := hu64.trans (by norm_num)
  have hwu : (w : ℝ) * u ≤ (1 / 2 : ℝ) ^ 32 := by rw [hu_def]; exact mul_half_pow_le hw
  have hw64 : (64 : ℝ) ≤ w := by exact_mod_cast hw
  -- the value of `x`
  set v := finiteVal true e m with hv_def
  have hx : (finite true e q m hv).toVal = some (v : EReal) := toVal_finite _ _ _ _ _
  have hv0 : 0 < v := finiteVal_true_pos e hv
  obtain ⟨hvlo, hvhi⟩ := abs_finiteVal_bounds true e hv
  rw [abs_of_pos hv0] at hvlo hvhi
  -- the parameters: the leading zeros of `m₀ − 1` decide how many roots are taken
  have h2k_orig : (2 : ℝ) ^ k ≤ w := by exact_mod_cast hk
  -- `ℓ = e − 1` and `m₀ = x 2^(−ℓ) ∈ [1, 2)`
  set ℓ : AzInt := e - 1 with hℓ
  have hℓ_int : ℓ.toInt = e.toInt - 1 := by rw [hℓ, AzInt.toInt_sub]; rfl
  have hm0 : ((finite true e q m hv) <<< (-ℓ)).toVal
      = some ((v * (2 : ℝ) ^ (1 - e.toInt) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal hx, AzInt.toInt_neg, hℓ_int, neg_sub]
  set m0v : ℝ := v * (2 : ℝ) ^ (1 - e.toInt) with hm0v
  have h2e : (0 : ℝ) < (2 : ℝ) ^ (1 - e.toInt) := zpow_pos (by norm_num) _
  have hm01 : 1 ≤ m0v := by
    have := mul_le_mul_of_nonneg_right hvlo h2e.le
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show e.toInt - 1 + (1 - e.toInt) = 0 by ring,
      zpow_zero] at this
    exact this
  have hm02 : m0v < 2 := by
    have := mul_lt_mul_of_pos_right hvhi h2e
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show e.toInt + (1 - e.toInt) = 1 by ring,
      zpow_one] at this
    exact this
  have hm00 : 0 < m0v := by linarith
  set L := Real.log m0v with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hm01
  have hL1 : L ≤ Real.log 2 := Real.log_le_log hm00 hm02.le
  have hlog2 := Real.log_two_lt_d9
  have hlogv : Real.log v = L + (ℓ.toInt : ℝ) * Real.log 2 := by
    rw [hL, hm0v, Real.log_mul hv0.ne' h2e.ne', Real.log_zpow, hℓ_int]; push_cast; ring
  -- the leading zeros of `m₀ − 1`, the roots actually taken, the number of terms
  obtain ⟨d0v, hd0, hfd0⟩ := subFloor_err hm0 toVal_one' w (by linarith)
  set c0 := lnSeriesLead (subPrecRound ((finite true e q m hv) <<< (-ℓ)) one w .Floor).1
    with hc0
  set kr := k - min k c0 with hkr
  have hkr_le : kr ≤ k := by omega
  set J := lnSeriesTerms (kr + c0) w with hJ_def
  have hJw : J ≤ w := lnSeriesTerms_le (by omega)
  have hkJ := lnSeriesTerms_spec (kr + c0) w
  have h2k : (2 : ℝ) ^ kr ≤ w := (pow_le_pow_right₀ one_le_two hkr_le).trans h2k_orig
  have h2k0 : (0 : ℝ) < 2 ^ kr := by positivity
  have hLc0 : L ≤ (1 / 2 : ℝ) ^ c0 := by
    rcases lnSeriesLead_spec hd0 with hlead | hlead <;> rw [← hc0] at hlead
    · rw [hlead, pow_zero]; linarith
    · have h1 : (m0v - 1) * (1 - 2 * u) ≤ d0v := by
        have := hfd0.ge; rw [← hu_def] at this; linarith
      have h2 : m0v - 1 ≤ 2 * (1 / 2 : ℝ) ^ (c0 + 1) := by
        have hu4 : 2 * u ≤ 1 / 2 := by linarith
        nlinarith
      have h3 : 2 * (1 / 2 : ℝ) ^ (c0 + 1) = (1 / 2 : ℝ) ^ c0 := by rw [pow_succ]; ring
      have h4 : L ≤ m0v - 1 := Real.log_le_sub_one_of_pos hm00
      linarith
  -- the square roots
  obtain ⟨yv, hy, hy1, hylog_le, hylog_ge⟩ := lnSqrtIter_spec hw L kr 0 _ m0v hm0 hm01
    (by rw [pow_zero, div_one]) (by rw [pow_zero, div_one, ← hu_def]; linarith)
  rw [zero_add] at hylog_le hylog_ge
  rw [← hu_def] at hylog_ge
  have hy0 : 0 < yv := by linarith
  have hy2 : yv ≤ 2 := by
    have h1 : Real.log yv ≤ Real.log 2 := by
      calc Real.log yv ≤ L / 2 ^ kr := hylog_le
        _ ≤ L := div_le_self hL0 (one_le_pow₀ one_le_two)
        _ ≤ Real.log 2 := hL1
    exact (Real.log_le_log_iff hy0 two_pos).mp h1
  -- `t = (y − 1)/(y + 1)`
  set tv : ℝ := (yv - 1) / (yv + 1) with htv
  have hyp1 : 0 < yv + 1 := by linarith
  have htv0 : 0 ≤ tv := div_nonneg (by linarith) hyp1.le
  have htv3 : tv ≤ 1 / 3 := by rw [htv, div_le_iff₀ hyp1]; linarith
  have htv_half : tv ≤ 1 / 2 := htv3.trans (by norm_num)
  have hy_eq : (1 + tv) / (1 - tv) = yv := by
    rw [htv]; field_simp; ring
  have ht_le : 2 * tv ≤ Real.log yv := by
    have := (log_atanh_series_bounds htv0 htv_half 1).1
    rw [hy_eq] at this
    simpa [lnSeriesPartial] using this
  have htk : tv ≤ (1 / 2 : ℝ) ^ (kr + c0 + 1) := by
    have h1 : Real.log yv ≤ (1 / 2 : ℝ) ^ c0 / 2 ^ kr := by
      calc Real.log yv ≤ L / 2 ^ kr := hylog_le
        _ ≤ (1 / 2 : ℝ) ^ c0 / 2 ^ kr := div_le_div_of_nonneg_right hLc0 h2k0.le
    have h2 : (1 / 2 : ℝ) ^ (kr + c0 + 1) = (1 / 2 : ℝ) ^ c0 / 2 ^ kr / 2 := by
      rw [pow_add, pow_add, pow_one, one_div_pow (2 : ℝ) kr]
      ring
    rw [h2]
    linarith
  -- the tail
  have htail : 8 / 3 * tv ^ (2 * J + 1) ≤ 2 * u := by
    have h1 : tv ^ (2 * J + 1) ≤ ((1 / 2 : ℝ) ^ (kr + c0 + 1)) ^ (2 * J + 1) :=
      pow_le_pow_left₀ htv0 htk _
    rw [← pow_mul] at h1
    have h2 : ((1 / 2 : ℝ)) ^ ((kr + c0 + 1) * (2 * J + 1)) ≤ (1 / 2 : ℝ) ^ (w + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkJ
    rw [pow_succ, ← hu_def] at h2
    linarith
  -- the computed `t`
  obtain ⟨numv, hnum, hfnum⟩ := subFloor_err hy toVal_one' w (by linarith)
  obtain ⟨denv, hden, hcden⟩ := addCeiling_err hy toVal_one' w (by linarith)
  have hdenv0 : 0 < denv := lt_of_lt_of_le hyp1 hcden.ge
  obtain ⟨tcv, htc, hftc⟩ := divFloor_err hnum hden hdenv0 hfnum.nonneg w
  have htcv0 : 0 ≤ tcv := hftc.nonneg
  have htc_le : tcv ≤ tv := by
    refine hftc.le.trans ?_
    rw [htv, div_le_div_iff₀ hdenv0 hyp1]
    exact mul_le_mul hfnum.le hcden.ge hyp1.le (by linarith)
  have htc_ge : tv * (1 - 8 * u) ≤ tcv := by
    have hA : (yv - 1) * (1 - 2 * u) ≤ numv := by
      have := hfnum.ge; rw [← hu_def] at this; linarith
    have hB : denv ≤ (yv + 1) * (1 + 2 * u) := by
      have := hcden.le; rw [← hu_def] at this; linarith
    have hB0 : (0 : ℝ) < (yv + 1) * (1 + 2 * u) := by positivity
    have h1 : (yv - 1) * (1 - 2 * u) / ((yv + 1) * (1 + 2 * u)) ≤ numv / denv := by
      rw [div_le_div_iff₀ hB0 hdenv0]
      exact mul_le_mul hA hB hdenv0.le hfnum.nonneg
    have h2 : numv / denv * (1 - 2 * u) ≤ tcv := by
      have := hftc.ge; rw [← hu_def] at this; linarith
    have h3 : (yv - 1) * (1 - 2 * u) / ((yv + 1) * (1 + 2 * u)) * (1 - 2 * u)
        = tv * ((1 - 2 * u) ^ 2 / (1 + 2 * u)) := by
      rw [htv]; field_simp
    have h4 : 1 - 8 * u ≤ (1 - 2 * u) ^ 2 / (1 + 2 * u) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    calc tv * (1 - 8 * u) ≤ tv * ((1 - 2 * u) ^ 2 / (1 + 2 * u)) :=
          mul_le_mul_of_nonneg_left h4 htv0
      _ = (yv - 1) * (1 - 2 * u) / ((yv + 1) * (1 + 2 * u)) * (1 - 2 * u) := h3.symm
      _ ≤ numv / denv * (1 - 2 * u) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ tcv := h2
  -- `t²`
  obtain ⟨t2v, ht2, hft2⟩ := sqrFloor_err htc w
  have ht2le : t2v ≤ tv ^ 2 := by
    rw [pow_two]; exact hft2.le.trans (mul_le_mul htc_le htc_le htcv0 htv0)
  have ht2ge : tv ^ 2 * (1 - 18 * (1 / 2 : ℝ) ^ w) ≤ t2v := by
    rw [← hu_def]
    have h1 : tv * (1 - 8 * u) * (tv * (1 - 8 * u)) ≤ tcv * tcv :=
      mul_le_mul htc_ge htc_ge (mul_nonneg htv0 (by linarith)) htcv0
    have h2 : tcv * tcv * (1 - 2 * u) ≤ t2v := by
      have := hft2.ge; rw [← hu_def] at this; linarith
    have h3 := one_sub_mul_three (by positivity : (0 : ℝ) ≤ 8 * u) (by positivity : (0 : ℝ) ≤ 8 * u)
      (by positivity : (0 : ℝ) ≤ 2 * u) (by linarith)
    have hX : 0 ≤ tv ^ 2 := by positivity
    calc tv ^ 2 * (1 - 18 * u) ≤ tv ^ 2 * ((1 - 8 * u) * (1 - 8 * u) * (1 - 2 * u)) := by
          apply mul_le_mul_of_nonneg_left _ hX; linarith
      _ = tv * (1 - 8 * u) * (tv * (1 - 8 * u)) * (1 - 2 * u) := by ring
      _ ≤ tcv * tcv * (1 - 2 * u) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ t2v := h2
  -- the series, stopped after `jf ≤ J` terms
  have hz : (zero : AzFloat).toVal = some ((0 : ℝ) : EReal) := by simp
  have htau : (powerOf2 (-(AzNat.ofNat (w + 3)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (w + 3) : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_neg, toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
      zpow_natCast, one_div_pow, one_div]
  obtain ⟨jf, sv, pv, -, hmJ, hstop, hs, -, hs0, hs_le, hs_ge, -, -, hp_ge⟩ :=
    lnSeriesLoop_spec hw htv0 ht2 ht2le ht2ge htau J 0 zero _ 0 tcv (by omega) hz htc le_rfl
      (by rw [lnSeriesPartial_zero]) (by rw [lnSeriesPartial_zero, zero_mul]) htcv0
      (by simpa using htc_le) (by rw [← hu_def]; simpa using htc_ge)
  rw [zero_add] at hmJ hstop
  rw [← hu_def] at hs_ge hp_ge
  have hmJ' : (jf : ℝ) ≤ J := by exact_mod_cast hmJ
  have hS0 := lnSeriesPartial_nonneg htv0 jf
  obtain ⟨hser1, hser2⟩ := log_atanh_series_bounds htv0 htv_half jf
  rw [hy_eq] at hser1 hser2
  -- the tail after `jf` terms
  have htail_m : 8 / 3 * tv ^ (2 * jf + 1) ≤ 2 * u := by
    rcases hstop with hstop | hstop
    · rw [hstop]; exact htail
    · have hα : (8 + 20 * (jf : ℝ)) * u ≤ 1 / 2 := by
        have : (8 + 20 * (jf : ℝ)) * u ≤ 28 * ((w : ℝ) * u) := by
          have hmw : (jf : ℝ) ≤ w := by exact_mod_cast (hmJ.trans hJw)
          nlinarith
        have : (1 / 2 : ℝ) ^ 32 ≤ 1 / 56 := by norm_num
        linarith
      have h1 : tv ^ (2 * jf + 1) ≤ 2 * pv := by
        have hX : 0 ≤ tv ^ (2 * jf + 1) := by positivity
        nlinarith
      have h2 : (1 / 2 : ℝ) ^ (w + 3) = u / 8 := by rw [hu_def, pow_add]; ring
      rw [h2] at hstop
      linarith
  -- `A = 2^(k+1) s`, `E = (20J + 18) 2^k u`
  have hA : ((lnSeriesLoop w (sqrPrecRound (divPrecRound (subPrecRound
        (lnSqrtIter w kr ((finite true e q m hv) <<< (-ℓ))) one w .Floor).1
        (addPrecRound (lnSqrtIter w kr ((finite true e q m hv) <<< (-ℓ))) one w .Ceiling).1
        w .Floor).1 w .Floor).1 (powerOf2 (-(AzNat.ofNat (w + 3)).toAzInt)) J 0 (zero,
        (divPrecRound (subPrecRound
        (lnSqrtIter w kr ((finite true e q m hv) <<< (-ℓ))) one w .Floor).1
        (addPrecRound (lnSqrtIter w kr ((finite true e q m hv) <<< (-ℓ))) one w .Ceiling).1
        w .Floor).1)).1 <<< ((kr + 1 : ℕ) : AzInt)).toVal
      = some ((sv * 2 ^ (kr + 1) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal hs, AzInt.toInt_natCast, zpow_natCast]
  set Av : ℝ := sv * 2 ^ (kr + 1) with hAv
  have hE : (ofAzNat (AzNat.ofNat (20 * J + 18)) <<< ((kr : AzInt) - (w : AzInt))).toVal
      = some ((((20 * J + 18 : ℕ) : ℝ) * 2 ^ kr * u : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal (toVal_ofAzNat_ofNat _), AzInt.toInt_sub, AzInt.toInt_natCast,
      AzInt.toInt_natCast, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, hu_def,
      one_div_pow, div_eq_mul_inv, one_div, mul_assoc]
  set Ev : ℝ := ((20 * J + 18 : ℕ) : ℝ) * 2 ^ kr * u with hEv
  have hEv0 : 0 ≤ Ev := by positivity
  -- `A ≤ L ≤ A + E`
  have hlogy_lo : 2 * lnSeriesPartial tv jf ≤ Real.log yv := hser1
  have hA_le : Av ≤ L := by
    have h1 : Av ≤ 2 ^ kr * (2 * lnSeriesPartial tv jf) := by
      rw [hAv, pow_succ]
      have := mul_le_mul_of_nonneg_right hs_le (by positivity : (0 : ℝ) ≤ 2 ^ kr * 2)
      linarith
    have h2 : 2 ^ kr * Real.log yv ≤ L := by
      have := mul_le_mul_of_nonneg_left hylog_le h2k0.le
      rwa [mul_div_cancel₀ _ h2k0.ne'] at this
    have h3 : 2 ^ kr * (2 * lnSeriesPartial tv jf) ≤ 2 ^ kr * Real.log yv :=
      mul_le_mul_of_nonneg_left hlogy_lo h2k0.le
    linarith
  have hA_ge : L ≤ Av + Ev := by
    have hβ : 2 * lnSeriesPartial tv jf - 2 * sv ≤ (10 + 20 * (J : ℝ)) * u := by
      have h1 : lnSeriesPartial tv jf - sv
          ≤ lnSeriesPartial tv jf * ((10 + 20 * (jf : ℝ)) * u) := by
        linarith
      have h2 : 2 * lnSeriesPartial tv jf ≤ 1 := by
        have := hylog_le
        have h3 : L / 2 ^ kr ≤ 1 := by
          rw [div_le_one h2k0]; linarith [one_le_pow₀ (M₀ := ℝ) one_le_two (n := kr)]
        linarith
      have h4 : (10 + 20 * (jf : ℝ)) * u ≤ (10 + 20 * (J : ℝ)) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have h5 : (0 : ℝ) ≤ (10 + 20 * (jf : ℝ)) * u := by positivity
      have h6 : lnSeriesPartial tv jf * ((10 + 20 * (jf : ℝ)) * u)
          ≤ 1 / 2 * ((10 + 20 * (jf : ℝ)) * u) :=
        mul_le_mul_of_nonneg_right (by linarith) h5
      linarith only [h1, h4, h6]
    have h1 : L ≤ 2 ^ kr * Real.log yv + 2 ^ kr * (6 * u) := by
      have := mul_le_mul_of_nonneg_left hylog_ge h2k0.le
      rw [mul_sub, mul_div_cancel₀ _ h2k0.ne'] at this
      linarith
    have h2 : Real.log yv ≤ 2 * sv + (10 + 20 * (J : ℝ)) * u + 2 * u := by linarith
    have h3 : 2 ^ kr * Real.log yv ≤ 2 ^ kr * (2 * sv + (10 + 20 * (J : ℝ)) * u + 2 * u) :=
      mul_le_mul_of_nonneg_left h2 h2k0.le
    have h4 : Ev = 2 ^ kr * ((20 * (J : ℝ) + 18) * u) := by rw [hEv]; push_cast; ring
    have h5 : Av = 2 ^ kr * (2 * sv) := by rw [hAv, pow_succ]; ring
    have h6 : 2 ^ kr * (2 * sv + (10 + 20 * (J : ℝ)) * u + 2 * u) + 2 ^ kr * (6 * u)
        = 2 ^ kr * (2 * sv) + 2 ^ kr * ((20 * (J : ℝ) + 18) * u) := by ring
    rw [h4, h5]
    linarith only [h1, h3, h6]
  -- `ℓ ln 2`
  obtain ⟨LLo, LHi, hLLo, hLHi, hL1, hL2, hLw, hLLo_abs, hLHi_abs⟩ := ln_L_spec hw hlb ℓ
  rw [← hu_def] at hLw
  -- the final combination
  simp only [lnSeriesBracketK]
  rw [← hℓ, ← hc0, ← hkr, ← hJ_def]
  obtain ⟨lo, hlo, hloa, hlob⟩ := addFloor_abs hA hLLo w
  obtain ⟨hi1, hhi1, hchi1⟩ := addCeiling_err hA hE w (by positivity)
  obtain ⟨hi, hhi, hhia, hhib⟩ := addCeiling_abs hhi1 hLHi w
  rw [← hu_def] at hlob hhib
  refine ⟨lo, hi, hlo, hhi, ?_, ?_, ?_⟩
  · rw [hlogv]; linarith
  · rw [hlogv]; linarith [hchi1.ge]
  · -- the width
    have hℓe : |(ℓ.toInt : ℝ)| ≤ |(e.toInt : ℝ)| + 1 := by
      rw [hℓ_int]; push_cast
      calc |(e.toInt : ℝ) - 1| ≤ |(e.toInt : ℝ)| + |(1 : ℝ)| := abs_sub _ _
        _ = |(e.toInt : ℝ)| + 1 := by rw [abs_one]
    set W : ℝ := (w : ℝ) + |(e.toInt : ℝ)| + 8 with hW
    have hW72 : 72 ≤ W := by rw [hW]; linarith [abs_nonneg (e.toInt : ℝ)]
    have hJW : (J : ℝ) ≤ W := by
      have : (J : ℝ) ≤ w := by exact_mod_cast hJw
      rw [hW]; linarith [abs_nonneg (e.toInt : ℝ)]
    have h2kW : (2 : ℝ) ^ kr ≤ W := by rw [hW]; linarith [abs_nonneg (e.toInt : ℝ)]
    have hℓW : |(ℓ.toInt : ℝ)| ≤ W := by rw [hW]; linarith
    have hEvW : Ev ≤ 38 * W ^ 2 * u := by
      rw [hEv]; push_cast
      have h1 : 20 * (J : ℝ) + 18 ≤ 38 * W := by linarith
      have h2 : (20 * (J : ℝ) + 18) * 2 ^ kr ≤ 38 * W * W := by
        apply mul_le_mul h1 h2kW (by positivity) (by linarith)
      have : (20 * (J : ℝ) + 18) * 2 ^ kr * u ≤ 38 * W * W * u :=
        mul_le_mul_of_nonneg_right h2 hu0.le
      linarith [this]
    have hAv0 : 0 ≤ Av := by positivity
    have hAv1 : Av ≤ 1 := by linarith
    have hLw' : LHi - LLo ≤ 12 * W * u := by
      have : 12 * |(ℓ.toInt : ℝ)| * u ≤ 12 * W * u := by
        apply mul_le_mul_of_nonneg_right _ hu0.le; linarith
      linarith
    have hLLoW : |LLo| ≤ 2 * W := by linarith
    have hLHiW : |LHi| ≤ 2 * W := by linarith
    have hhi1' : hi1 ≤ Av + Ev + 2 * (Av + Ev) * u := by
      have := hchi1.le; rw [← hu_def] at this; exact this
    have := lnSeries_final_bounds hu0 (by linarith) hW72 hAv0 hAv1 hEv0 hEvW hLw' hLLoW hLHiW
      hlob hchi1.ge hhi1' hhib
    unfold lnEps
    rw [← hu_def]
    exact this

/-- `lnSeriesBracket lb x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`), for
any bracket `lb` of `ln 2` fit for `w`. -/
theorem lnSeriesBracket_spec {w : ℕ} (hw : 64 ≤ w) {lb : AzFloat × AzFloat}
    (hlb : Ln2BracketFor w lb) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, (lnSeriesBracket lb (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnSeriesBracket lb (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w :=
  lnSeriesBracketK_spec hw (two_pow_lnSeriesK_le (by omega)) hlb e hv

/-! ### The dispatcher -/

/-- `lnBracketCore pb lb x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`), for
any bracket `lb` of `ln 2` fit for `w` and, above `lnSeriesThreshold`, any bracket `pb` of `π`
fit for `w`. -/
theorem lnBracketCore_spec {w : ℕ} (hw : 64 ≤ w) {pb lb : AzFloat × AzFloat}
    (hpb : lnSeriesThreshold < w → PiBracketFor w pb) (hlb : Ln2BracketFor w lb) (e : AzInt)
    {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, (lnBracketCore pb lb (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnBracketCore pb lb (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  unfold lnBracketCore
  split_ifs with hT
  · exact lnSeriesBracket_spec hw hlb e hv
  · exact lnAgmBracket_spec hw (hpb (by omega)) hlb e hv

theorem lnBracket_eq_core (x : AzFloat) (e : AzInt) (w : ℕ) :
    lnBracket x e w = lnBracketCore (piBracket w) (ln2Bracket w) x e w := by
  unfold lnBracket lnBracketCore
  split_ifs <;> rfl

/-- `lnBracket x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`). -/
theorem lnBracket_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, (lnBracket (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnBracket (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  rw [lnBracket_eq_core]
  exact lnBracketCore_spec hw (fun _ => piBracketFor_piBracket hw)
    (ln2BracketFor_ln2Bracket (by omega)) e hv

/-- `lnBracketWith c x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`), for
any constants `c`. -/
theorem lnBracketWith_spec (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, (lnBracketWith c (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnBracketWith c (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  unfold lnBracketWith
  split_ifs with hW
  · have hpb : lnSeriesThreshold < w → PiBracketFor w c.pi := fun hT => by
      rw [c.pi_eq (by omega)]
      exact (piBracketFor_piBracket (by omega)).of_le (by omega) hW
    have hlb : Ln2BracketFor w c.ln2 := by
      rw [c.ln2_eq]
      exact (ln2BracketFor_ln2Bracket (by omega)).of_le hW
    exact lnBracketCore_spec hw hpb hlb e hv
  · exact lnBracket_spec hw e hv

/-! ### The Ziv interface -/

/-- The logarithm of a finite positive float other than `1` is irrational. -/
theorem irrational_log_finiteVal (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hne : finiteVal true e m ≠ 1) : Irrational (Real.log (finiteVal true e m)) := by
  obtain ⟨r, hr⟩ := exists_rat_of_toVal (toVal_finite true e q m hv)
  have hv0 := finiteVal_true_pos e hv
  rw [hr] at hv0 hne ⊢
  exact irrational_log_rat (by exact_mod_cast hv0) (by exact_mod_cast hne)

/-- A positive float that is not IEEE-equal to `one` has value `≠ 1`. -/
theorem finiteVal_ne_one_of_not_eqIEEE (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h : ¬ eqIEEE (finite true e q m hv) one = true) : finiteVal true e m ≠ 1 := by
  intro h1
  apply h
  rw [eqIEEE_iff]
  exact ⟨((1 : ℝ) : EReal), by rw [toVal_finite, h1], toVal_one'⟩

/-- `lnApprox x e w` encloses `ln x` strictly, with width at most `lnEps e w` (`w ≥ 64`). -/
theorem lnApprox_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hne : finiteVal true e m ≠ 1) :
    ∃ lv hv' : ℝ, Rounds (lnApprox (finite true e q m hv) e w).1 lv ∧
      Rounds (lnApprox (finite true e q m hv) e w).2 hv' ∧
      lv < Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) < hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  obtain ⟨lv, hv', hlv, hhv, hlo, hhi, hwidth⟩ := lnBracket_spec hw e hv
  have hirr := irrational_log_finiteVal e hv hne
  refine ⟨lv, hv', ?_, ?_, ?_, ?_, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo fun h => hirr.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi fun h => hirr.ne_rat r (h.trans hr)

/-- The Ziv certificate: at some working precision `w₀ · 2^f`, rounding is possible. -/
theorem lnApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (e : AzInt) {q : ℕ}
    {m : AzNat} (hv : FiniteValid q m) (hne : ¬ eqIEEE (finite true e q m hv) one = true)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnApprox (finite true e q m hv) e (w₀ * 2 ^ f)).1
      (lnApprox (finite true e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  have hne' := finiteVal_ne_one_of_not_eqIEEE e hv hne
  exists_isSome_of_irrational_threshold p mode (lnApprox (finite true e q m hv) e)
    (irrational_log_finiteVal e hv hne') (lnEps e.toInt) (tendsto_lnEps e.toInt) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := lnApprox_spec hw e hv hne'
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-- `lnApproxWith c x e w` encloses `ln x` strictly, with width at most `lnEps e w` (`w ≥ 64`). -/
theorem lnApproxWith_spec (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hne : finiteVal true e m ≠ 1) :
    ∃ lv hv' : ℝ, Rounds (lnApproxWith c (finite true e q m hv) e w).1 lv ∧
      Rounds (lnApproxWith c (finite true e q m hv) e w).2 hv' ∧
      lv < Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) < hv' ∧
      hv' - lv ≤ lnEps e.toInt w := by
  obtain ⟨lv, hv', hlv, hhv, hlo, hhi, hwidth⟩ := lnBracketWith_spec c hw e hv
  have hirr := irrational_log_finiteVal e hv hne
  refine ⟨lv, hv', ?_, ?_, ?_, ?_, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo (hr ▸ fun h => hirr ⟨r, h⟩)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi (hr ▸ fun h => hirr ⟨r, h.symm⟩)

/-- The Ziv certificate for `lnApproxWith`. -/
theorem lnApproxWith_isSome_exists (c : LnConsts) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hne : ¬ eqIEEE (finite true e q m hv) one = true) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnApproxWith c (finite true e q m hv) e (w₀ * 2 ^ f)).1
      (lnApproxWith c (finite true e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  have hne' := finiteVal_ne_one_of_not_eqIEEE e hv hne
  exists_isSome_of_irrational_threshold p mode (lnApproxWith c (finite true e q m hv) e)
    (irrational_log_finiteVal e hv hne') (lnEps e.toInt) (tendsto_lnEps e.toInt) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := lnApproxWith_spec c hw e hv hne'
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### The logarithm of a rational -/

/-- `lnEps e` is decreasing in the working precision: `(X + 1)^5 ≤ 2 X^5` for `X ≥ 8`. -/
theorem lnEps_succ_le (e : ℤ) (w : ℕ) : lnEps e (w + 1) ≤ lnEps e w := by
  unfold lnEps
  set X : ℝ := (w : ℝ) + |(e : ℝ)| + 8 with hX
  have hX8 : 8 ≤ X := by
    rw [hX]; linarith [abs_nonneg (e : ℝ), (Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  have hX0 : 0 ≤ X := by linarith
  have h1 : ((w + 1 : ℕ) : ℝ) + |(e : ℝ)| + 8 = X + 1 := by rw [hX]; push_cast; ring
  rw [h1]
  have h2 : X + 1 ≤ 9 / 8 * X := by linarith
  have h3 : (X + 1) ^ 5 ≤ (9 / 8 * X) ^ 5 := pow_le_pow_left₀ (by linarith) h2 5
  have h4 : (9 / 8 * X) ^ 5 ≤ 2 * X ^ 5 := by
    rw [mul_pow]; nlinarith [pow_nonneg hX0 5]
  have hu : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have h5 := mul_le_mul_of_nonneg_right (h3.trans h4) hu.le
  rw [pow_succ (1 / 2 : ℝ) w]
  nlinarith [h5]

theorem lnEps_antitone {e : ℤ} {w W : ℕ} (hW : w ≤ W) : lnEps e W ≤ lnEps e w := by
  induction W, hW using Nat.le_induction with
  | base => exact le_rfl
  | succ W _ ih => exact (lnEps_succ_le e W).trans ih

/-- `lnEps` is monotone in `|e|`. -/
theorem lnEps_mono {e e' : ℤ} (h : |e| ≤ |e'|) (w : ℕ) : lnEps e w ≤ lnEps e' w := by
  unfold lnEps
  have h' : |(e : ℝ)| ≤ |(e' : ℝ)| := by rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast h
  gcongr

theorem toVal_powerOf2_two_sub (w : ℕ) :
    (powerOf2 (((2 : ℕ) : AzInt) - (w : AzInt))).toVal
      = some ((4 * (1 / 2 : ℝ) ^ w : ℝ) : EReal) := by
  rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_natCast, AzInt.toInt_natCast, Nat.cast_ofNat,
    zpow_sub₀ (by norm_num), zpow_natCast, one_div_pow, one_div, div_eq_mul_inv]
  norm_num

/-- A float with a positive value is `finite true …`. -/
theorem eq_finite_true_of_toVal_pos {x : AzFloat} {r : ℝ} (hx : x.toVal = some (r : EReal))
    (hr : 0 < r) :
    ∃ (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
      x = finite true e q m hv ∧ finiteVal true e m = r := by
  cases x with
  | nan => rw [toVal_nan] at hx; cases hx
  | infinity s => rw [toVal_infinity] at hx; cases s <;> simp at hx
  | zero =>
    rw [toVal_zero, ← EReal.coe_zero, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    linarith
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    cases s with
    | false => rw [finiteVal_false] at hx; have := finiteVal_true_pos e hv; linarith
    | true => exact ⟨e, q, m, hv, rfl, hx⟩

theorem toRat_pos_of_sign (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) :
    (0 : ℚ) < AzRat.toRat q := by
  have hnum : (0 : ℝ) < q.num.toNat := by exact_mod_cast AzRat.num_toNat_pos q h0
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have : (0 : ℝ) < (AzRat.toRat q : ℝ) := by
    rw [coe_toRat_eq, hs]
    simp only [↓reduceIte, Int.cast_natCast]
    exact div_pos hnum hden
  exact_mod_cast this

theorem toRat_neg_of_sign (q : AzRat) (hs : q.sign = false) (h0 : q.num ≠ 0) :
    (AzRat.toRat q : ℝ) < 0 := by
  have hnum : (0 : ℝ) < q.num.toNat := by exact_mod_cast AzRat.num_toNat_pos q h0
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  rw [coe_toRat_eq, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

theorem toRat_eq_one_of_num_eq_den (q : AzRat) (hs : q.sign = true) (h : q.num = q.den) :
    AzRat.toRat q = 1 := by
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have : (AzRat.toRat q : ℝ) = 1 := by
    rw [coe_toRat_eq, hs]
    simp only [↓reduceIte, Int.cast_natCast]
    rw [h]; exact div_self hden.ne'
  exact_mod_cast this

theorem toRat_ne_one_of_num_ne_den (q : AzRat) (hs : q.sign = true) (h : q.num ≠ q.den) :
    AzRat.toRat q ≠ 1 := by
  intro h1
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have h1' : (AzRat.toRat q : ℝ) = 1 := by exact_mod_cast h1
  rw [coe_toRat_eq, hs] at h1'
  simp only [↓reduceIte, Int.cast_natCast] at h1'
  rw [div_eq_one_iff_eq hden.ne'] at h1'
  exact h (AzNat.toNat_injective (by exact_mod_cast h1'))

/-- The width bound of `lnRatApprox`: `lnEps` at an exponent bound `E`, the widening `4·2^(−w)`
and the rounding of the widened end (`A` bounds `|ln q|`). -/
noncomputable def lnRatEps (E : ℕ) (A : ℝ) (w : ℕ) : ℝ :=
  lnEps E w + 4 * (1 / 2 : ℝ) ^ w + 2 * (A + (lnEps E w + 8 * (1 / 2 : ℝ) ^ w)) * (1 / 2 : ℝ) ^ w

theorem tendsto_lnRatEps (E : ℕ) (A : ℝ) :
    Filter.Tendsto (lnRatEps E A) Filter.atTop (nhds 0) := by
  have hL := tendsto_lnEps (E : ℤ)
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (hL.add (hu.const_mul 4)).add (((hA.add (hL.add (hu.const_mul 8))).const_mul 2).mul hu)
  simp only [mul_zero, add_zero] at this
  exact this

/-- A bracket function for `ln` of a positive float with the conclusion of `lnBracket_spec`
(`lnBracket`, `lnBracketWith c`). -/
def LnBracketFn (L : AzFloat → AzInt → ℕ → AzFloat × AzFloat) : Prop :=
  ∀ {w : ℕ}, 64 ≤ w → ∀ (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m),
    ∃ lv hv' : ℝ, (L (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (L (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
      lv ≤ Real.log (finiteVal true e m) ∧ Real.log (finiteVal true e m) ≤ hv' ∧
      hv' - lv ≤ lnEps e.toInt w

theorem lnBracketFn_lnBracket : LnBracketFn lnBracket := fun hw e _ _ hv => lnBracket_spec hw e hv

theorem lnBracketFn_lnBracketWith (c : LnConsts) : LnBracketFn (lnBracketWith c) :=
  fun hw e _ _ hv => lnBracketWith_spec c hw e hv

/-- `lnFloorBracketBy L y w` for a float `y` with `y ≤ q ≤ y (1 + 2·2^(−w))` encloses `ln q`,
with width at most `lnRatEps E |ln q| w`, `E = ⌊2 |ln q|⌋ + 2` (`w ≥ 64`), for any bracket
function `L` with the conclusion of `lnBracket_spec`. -/
theorem lnFloorBracketBy_spec {L : AzFloat → AzInt → ℕ → AzFloat × AzFloat} (hL : LnBracketFn L)
    {w : ℕ} (hw : 64 ≤ w) {y : AzFloat} {r qv : ℝ}
    (hr : y.toVal = some (r : EReal)) (hqv0 : 0 < qv) (hr1 : r ≤ qv)
    (hr2 : qv ≤ r + 2 * qv * (1 / 2 : ℝ) ^ w) :
    ∃ lv hv : ℝ, (lnFloorBracketBy L y w).1.toVal = some (lv : EReal) ∧
      (lnFloorBracketBy L y w).2.toVal = some (hv : EReal) ∧
      lv ≤ Real.log qv ∧ Real.log qv ≤ hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log qv|⌋₊ + 2) |Real.log qv| w := by
  have : NeZero w := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hu4 : u ≤ 1 / 16 := by
    calc u ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have hqu : 2 * qv * u ≤ 2 * qv * (1 / 16) := mul_le_mul_of_nonneg_left hu4 (by positivity)
  have hrhalf : qv / 2 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨e, q', m, hv, hx, hrv⟩ := eq_finite_true_of_toVal_pos hr hr0
  subst hx
  simp only [lnFloorBracketBy]
  obtain ⟨lv, hv', hlv, hhv, hlo, hhi, hwid⟩ := hL hw e hv
  rw [hrv] at hlo hhi
  obtain ⟨hlow, hhigh⟩ := abs_finiteVal_bounds true e hv
  rw [hrv, abs_of_pos hr0] at hlow hhigh
  -- the logarithms
  have hlog2 := Real.log_two_gt_d9
  have hlogr_lo : ((e.toInt : ℝ) - 1) * Real.log 2 ≤ Real.log r := by
    have := Real.log_le_log (by positivity) hlow
    rwa [Real.log_zpow, Int.cast_sub, Int.cast_one] at this
  have hlogr_hi : Real.log r < (e.toInt : ℝ) * Real.log 2 := by
    have := Real.log_lt_log hr0 hhigh
    rwa [Real.log_zpow] at this
  have hlogq_lo : Real.log r ≤ Real.log qv := Real.log_le_log hr0 hr1
  have hlogq_hi : Real.log qv ≤ Real.log r + 4 * u := by
    have h1 : Real.log qv - Real.log r = Real.log (qv / r) := (Real.log_div hqv0.ne' hr0.ne').symm
    have h2 : Real.log (qv / r) ≤ qv / r - 1 := Real.log_le_sub_one_of_pos (div_pos hqv0 hr0)
    have h3 : qv / r - 1 ≤ 4 * u := by
      rw [div_sub_one hr0.ne', div_le_iff₀ hr0]
      have : 4 * u * (qv / 2) ≤ 4 * u * r := mul_le_mul_of_nonneg_left hrhalf (by positivity)
      linarith
    linarith
  set L := Real.log qv with hL
  have hL1 : L ≤ |L| := le_abs_self L
  have hL2 : -|L| ≤ L := neg_abs_le L
  have hLabs0 : 0 ≤ |L| := abs_nonneg L
  -- the exponent bound `|e| ≤ 2 |L| + 1`
  have habs_e : |(e.toInt : ℝ)| ≤ 2 * |L| + 1 := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith
    have hlog2pos : 0 < Real.log 2 := by linarith
    have hup : (e.toInt : ℝ) - 1 ≤ 2 * |L| := by
      have h1 : (e.toInt : ℝ) - 1 ≤ |L| / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; linarith
      have h2 : |L| / Real.log 2 ≤ 2 * |L| := by
        rw [div_le_iff₀ hlog2pos]
        have := mul_le_mul_of_nonneg_left hhalf hLabs0
        linarith
      linarith
    have hdown : -(2 * |L| + 1) ≤ (e.toInt : ℝ) := by
      have h1 : -(|L| + 4 * u) / Real.log 2 ≤ (e.toInt : ℝ) := by
        rw [div_le_iff₀ hlog2pos]; linarith
      have h2 : -(2 * (|L| + 4 * u)) ≤ -(|L| + 4 * u) / Real.log 2 := by
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ hlog2pos]
        have := mul_le_mul_of_nonneg_left hhalf (by positivity : (0 : ℝ) ≤ |L| + 4 * u)
        linarith
      linarith
    rw [abs_le]; constructor <;> linarith
  set E : ℕ := ⌊2 * |L|⌋₊ + 2 with hE
  have hEe : |e.toInt| ≤ ((E : ℕ) : ℤ) := by
    have h1 : 2 * |L| < ⌊2 * |L|⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : |(e.toInt : ℝ)| ≤ ((E : ℕ) : ℝ) := by rw [hE]; push_cast; linarith
    rw [← Int.cast_abs] at h2
    exact_mod_cast h2
  have hwid' : hv' - lv ≤ lnEps (E : ℤ) w :=
    hwid.trans (lnEps_mono (by rw [Nat.abs_cast]; exact hEe) w)
  have hEps0 : 0 ≤ lnEps (E : ℤ) w := by unfold lnEps; positivity
  -- the widened upper end
  obtain ⟨hv2, hhv2, h21, h22⟩ := addCeiling_abs hhv (toVal_powerOf2_two_sub w) w
  rw [← hu] at h21 h22
  have hbound : |hv' + 4 * u| ≤ |L| + (lnEps (E : ℤ) w + 8 * u) := by
    rw [abs_le]; constructor <;> linarith
  have hprod : 2 * |hv' + 4 * u| * u ≤ 2 * (|L| + (lnEps (E : ℤ) w + 8 * u)) * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by norm_num)) hu0.le
  refine ⟨lv, hv2, hlv, hhv2, hlo.trans hlogq_lo, by linarith, ?_⟩
  unfold lnRatEps
  linarith

theorem lnFloorBracket_spec {w : ℕ} (hw : 64 ≤ w) {y : AzFloat} {r qv : ℝ}
    (hr : y.toVal = some (r : EReal)) (hqv0 : 0 < qv) (hr1 : r ≤ qv)
    (hr2 : qv ≤ r + 2 * qv * (1 / 2 : ℝ) ^ w) :
    ∃ lv hv : ℝ, (lnFloorBracket y w).1.toVal = some (lv : EReal) ∧
      (lnFloorBracket y w).2.toVal = some (hv : EReal) ∧
      lv ≤ Real.log qv ∧ Real.log qv ≤ hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log qv|⌋₊ + 2) |Real.log qv| w :=
  lnFloorBracketBy_spec lnBracketFn_lnBracket hw hr hqv0 hr1 hr2

theorem lnFloorBracketWith_spec (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) {y : AzFloat} {r qv : ℝ}
    (hr : y.toVal = some (r : EReal)) (hqv0 : 0 < qv) (hr1 : r ≤ qv)
    (hr2 : qv ≤ r + 2 * qv * (1 / 2 : ℝ) ^ w) :
    ∃ lv hv : ℝ, (lnFloorBracketWith c y w).1.toVal = some (lv : EReal) ∧
      (lnFloorBracketWith c y w).2.toVal = some (hv : EReal) ∧
      lv ≤ Real.log qv ∧ Real.log qv ≤ hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log qv|⌋₊ + 2) |Real.log qv| w :=
  lnFloorBracketBy_spec (lnBracketFn_lnBracketWith c) hw hr hqv0 hr1 hr2

/-- `x − 2x² ≤ ln (1 + x)` for `x ≥ −1/2`. -/
theorem sub_two_mul_sq_le_log_one_add {x : ℝ} (hx : -1 / 2 ≤ x) :
    x - 2 * x ^ 2 ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [e] at h
  refine le_trans ?_ h
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 + 2 * x)]

/-- The tiny-argument facts: for a float of exponent `e ≤ −(w + 8)`, `|x| < 2^(−w−8)`. -/
theorem abs_finiteVal_lt_of_tiny (s : Bool) {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) {w : ℕ} (hs : e.sign = false) (he : w + 8 ≤ e.abs.toNat) :
    |finiteVal s e m| < (2 : ℝ) ^ e.toInt ∧ (2 : ℝ) ^ e.toInt ≤ (1 / 2 : ℝ) ^ (w + 8) := by
  refine ⟨(abs_finiteVal_bounds s e hv).2, ?_⟩
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [htoInt, hs]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) he

/-- `lnP1BracketOf F x w` encloses `ln (1 + x)` with the width bound of `lnFloorBracket`, for
every bracket function `F` with the conclusion of `lnFloorBracket_spec` at `w`. -/
theorem lnP1BracketOf_spec {F : AzFloat → ℕ → AzFloat × AzFloat} {w : ℕ} (hw : 64 ≤ w)
    (hF : ∀ {y : AzFloat} {r qv : ℝ}, y.toVal = some (r : EReal) → 0 < qv → r ≤ qv →
      qv ≤ r + 2 * qv * (1 / 2 : ℝ) ^ w →
      ∃ lv hv : ℝ, (F y w).1.toVal = some (lv : EReal) ∧ (F y w).2.toVal = some (hv : EReal) ∧
        lv ≤ Real.log qv ∧ Real.log qv ≤ hv ∧
        hv - lv ≤ lnRatEps (⌊2 * |Real.log qv|⌋₊ + 2) |Real.log qv| w)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) :
    ∃ lv hv : ℝ, (lnP1BracketOf F x w).1.toVal = some (lv : EReal) ∧
      (lnP1BracketOf F x w).2.toVal = some (hv : EReal) ∧
      lv ≤ Real.log (1 + xv) ∧ Real.log (1 + xv) ≤ hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  have hgen : ∃ lv hv : ℝ, (F (addPrecRound one x w .Floor).1 w).1.toVal = some (lv : EReal) ∧
      (F (addPrecRound one x w .Floor).1 w).2.toVal = some (hv : EReal) ∧
      lv ≤ Real.log (1 + xv) ∧ Real.log (1 + xv) ≤ hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w := by
    obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
    exact hF hr hpos hf.le hf.ge
  cases x with
  | nan => exact hgen
  | infinity s => exact hgen
  | zero => exact hgen
  | finite s e q m hv =>
    simp only [lnP1BracketOf]
    split_ifs with hc
    · obtain ⟨hs, he⟩ := hc
      have : NeZero (w + 8) := ⟨by omega⟩
      rw [toVal_finite] at hx
      have hxv : xv = finiteVal s e m := by
        rw [Option.some.injEq, EReal.coe_eq_coe_iff] at hx; exact hx.symm
      obtain ⟨hlt, h2e⟩ := abs_finiteVal_lt_of_tiny s hv hs he
      rw [← hxv] at hlt
      set u := (1 / 2 : ℝ) ^ w with hu
      have hu0 : 0 < u := by positivity
      have hus : u ≤ 1 / 16 := by
        calc u ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 16 := by norm_num
      have hu8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by rw [hu, pow_add]; norm_num; ring
      rw [hu8] at h2e
      set t := (2 : ℝ) ^ e.toInt with ht
      have ht0 : 0 < t := by positivity
      have hx' : (finite s e q m hv).toVal = some (xv : EReal) := by rw [toVal_finite, hxv]
      have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
        rw [toVal_abs, hx', Option.map_some, ← EReal.coe_neg]
        congr 1
      have hd : ((((finite s e q m hv).abs <<< e) <<< AzInt.ofInt 1)).toVal
          = some ((2 * (|xv| * t) : ℝ) : EReal) := by
        rw [toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs e), AzInt.toInt_ofInt,
          zpow_one, mul_comm]
      obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hx' hd (w + 8)
      rw [hu8] at hlo2
      have hax := abs_nonneg xv
      have hsq : xv ^ 2 ≤ |xv| * t := by
        rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left hlt.le hax
      have hxhalf : -1 / 2 ≤ xv := by
        have := neg_abs_le xv; linarith
      have hlow := sub_two_mul_sq_le_log_one_add hxhalf
      have hup : Real.log (1 + xv) ≤ xv := by
        have := Real.log_le_sub_one_of_pos hpos; linarith
      have hd0 : 0 ≤ |xv| * t := mul_nonneg hax ht0.le
      have hdle : |xv| * t ≤ u / 256 * (u / 256) :=
        mul_le_mul (hlt.le.trans h2e) h2e ht0.le (by positivity)
      have habsd : |xv - 2 * (|xv| * t)| ≤ u := by
        rw [abs_le]
        constructor
        · have := neg_abs_le xv; nlinarith
        · have := le_abs_self xv; nlinarith
      refine ⟨lo, xv, hlo, hx', by linarith, hup, ?_⟩
      have hE : (0 : ℝ) ≤ lnEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2 : ℕ) w := by
        unfold lnEps; positivity
      have hA := abs_nonneg (Real.log (1 + xv))
      unfold lnRatEps
      have h1 : xv - lo ≤ 4 * u := by nlinarith [mul_le_mul_of_nonneg_right habsd hu0.le]
      nlinarith [mul_nonneg (add_nonneg hA (add_nonneg hE (by positivity : (0 : ℝ) ≤ 8 * u)))
        hu0.le]
    · exact hgen

/-- The ends of a bracket as `Roundable`s round to themselves and inherit strict enclosure. -/
theorem rounds_pair_of_bracket {b : AzFloat × AzFloat} {lv hv v : ℝ}
    (hlv : b.1.toVal = some (lv : EReal)) (hhv : b.2.toVal = some (hv : EReal))
    (hlo : lv ≤ v) (hhi : v ≤ hv) (hirr : Irrational v) :
    Rounds (fun p mode => setPrecRound b.1 p mode) lv ∧
      Rounds (fun p mode => setPrecRound b.2 p mode) hv ∧ lv < v ∧ v < hv := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r', hr'⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo fun h => hirr.ne_rat r' (h.symm.trans hr')
  · obtain ⟨r', hr'⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi fun h => hirr.ne_rat r' (h.trans hr')

/-- `lnFloorApprox y w` encloses `ln q` strictly when `ln q` is irrational. -/
theorem lnFloorApprox_spec {w : ℕ} (hw : 64 ≤ w) {y : AzFloat} {r qv : ℝ}
    (hr : y.toVal = some (r : EReal)) (hqv0 : 0 < qv) (hr1 : r ≤ qv)
    (hr2 : qv ≤ r + 2 * qv * (1 / 2 : ℝ) ^ w) (hirr : Irrational (Real.log qv)) :
    ∃ lv hv : ℝ, Rounds (lnFloorApprox y w).1 lv ∧ Rounds (lnFloorApprox y w).2 hv ∧
      lv < Real.log qv ∧ Real.log qv < hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log qv|⌋₊ + 2) |Real.log qv| w := by
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hr hqv0 hr1 hr2
  refine ⟨lv, hv, ?_, ?_, ?_, ?_, hwid⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r', hr'⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo fun h => hirr.ne_rat r' (h.symm.trans hr')
  · obtain ⟨r', hr'⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi fun h => hirr.ne_rat r' (h.trans hr')

/-- `lnRatApprox q w` encloses `ln q` strictly, with width at most `lnRatEps E |ln q| w`
(`w ≥ 64`, `q > 0`, `q ≠ 1`). -/
theorem lnRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hq1 : AzRat.toRat q ≠ 1) :
    ∃ lv hv : ℝ, Rounds (lnRatApprox q w).1 lv ∧ Rounds (lnRatApprox q w).2 hv ∧
      lv < Real.log (AzRat.toRat q : ℝ) ∧ Real.log (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
        |Real.log (AzRat.toRat q : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  exact lnFloorApprox_spec hw hr hqv0 hr1 hr2 (irrational_log_rat hq hq1)

/-- The Ziv certificate for `ln q`: at some working precision `w₀ · 2^f`, rounding is possible. -/
theorem lnRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (hq1 : AzRat.toRat q ≠ 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnRatApprox q (w₀ * 2 ^ f)).1 (lnRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (lnRatApprox q) (irrational_log_rat hq hq1)
    (lnRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2) |Real.log (AzRat.toRat q : ℝ)|)
    (tendsto_lnRatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := lnRatApprox_spec hw q hq hq1
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The logarithm of `1 + x` -/

/-- `ln (1 + x)` is irrational for a float `x ≠ 0` with `1 + x > 0`. -/
theorem irrational_log_one_add_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hpos : 0 < 1 + xv) (hx0 : xv ≠ 0) : Irrational (Real.log (1 + xv)) := by
  obtain ⟨rx, hrx⟩ := exists_rat_of_toVal hx
  have e : (1 + xv) = ((1 + rx : ℚ) : ℝ) := by push_cast; rw [hrx]
  rw [e]
  have hrx0 : rx ≠ 0 := fun h => hx0 (by rw [hrx, h, Rat.cast_zero])
  have hpos' : (0 : ℚ) < 1 + rx := by
    have : (0 : ℝ) < ((1 + rx : ℚ) : ℝ) := by rw [← e]; exact hpos
    exact_mod_cast this
  exact irrational_log_rat hpos' fun h => hrx0 (by linarith)

/-- `lnP1Approx x w` encloses `ln (1 + x)` strictly, with width at most
`lnRatEps E |ln (1 + x)| w` (`w ≥ 64`, `x > −1`, `x ≠ 0`). -/
theorem lnP1Approx_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (hx0 : xv ≠ 0) :
    ∃ lv hv : ℝ, Rounds (lnP1Approx x w).1 lv ∧ Rounds (lnP1Approx x w).2 hv ∧
      lv < Real.log (1 + xv) ∧ Real.log (1 + xv) < hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  exact lnFloorApprox_spec hw hr hpos hf.le hf.ge (irrational_log_one_add_of_toVal hx hpos hx0)

/-- The Ziv certificate for `ln (1 + x)`. -/
theorem lnP1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (hx0 : xv ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnP1Approx x (w₀ * 2 ^ f)).1 (lnP1Approx x (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (lnP1Approx x)
    (irrational_log_one_add_of_toVal hx (by linarith) hx0)
    (lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)|) (tendsto_lnRatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := lnP1Approx_spec hw hx hx1 hx0
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The same with precomputed constants -/

theorem lnFloorApproxWith_spec (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) {y : AzFloat} {r qv : ℝ}
    (hr : y.toVal = some (r : EReal)) (hqv0 : 0 < qv) (hr1 : r ≤ qv)
    (hr2 : qv ≤ r + 2 * qv * (1 / 2 : ℝ) ^ w) (hirr : Irrational (Real.log qv)) :
    ∃ lv hv : ℝ, Rounds (lnFloorApproxWith c y w).1 lv ∧ Rounds (lnFloorApproxWith c y w).2 hv ∧
      lv < Real.log qv ∧ Real.log qv < hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log qv|⌋₊ + 2) |Real.log qv| w := by
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracketWith_spec c hw hr hqv0 hr1 hr2
  obtain ⟨h1, h2, h3, h4⟩ := rounds_pair_of_bracket hlv hhv hlo hhi hirr
  exact ⟨lv, hv, h1, h2, h3, h4, hwid⟩

theorem lnRatApproxWith_spec (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (hq1 : AzRat.toRat q ≠ 1) :
    ∃ lv hv : ℝ, Rounds (lnRatApproxWith c q w).1 lv ∧ Rounds (lnRatApproxWith c q w).2 hv ∧
      lv < Real.log (AzRat.toRat q : ℝ) ∧ Real.log (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
        |Real.log (AzRat.toRat q : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  exact lnFloorApproxWith_spec c hw hr hqv0 hr1 hr2 (irrational_log_rat hq hq1)

theorem lnRatApproxWith_isSome_exists (c : LnConsts) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q) (hq1 : AzRat.toRat q ≠ 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnRatApproxWith c q (w₀ * 2 ^ f)).1
      (lnRatApproxWith c q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (lnRatApproxWith c q) (irrational_log_rat hq hq1)
    (lnRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2) |Real.log (AzRat.toRat q : ℝ)|)
    (tendsto_lnRatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := lnRatApproxWith_spec c hw q hq hq1
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

theorem lnP1ApproxWith_spec (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (hx0 : xv ≠ 0) :
    ∃ lv hv : ℝ, Rounds (lnP1ApproxWith c x w).1 lv ∧ Rounds (lnP1ApproxWith c x w).2 hv ∧
      lv < Real.log (1 + xv) ∧ Real.log (1 + xv) < hv ∧
      hv - lv ≤ lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  exact lnFloorApproxWith_spec c hw hr hpos hf.le hf.ge
    (irrational_log_one_add_of_toVal hx hpos hx0)

theorem lnP1ApproxWith_isSome_exists (c : LnConsts) (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (hx0 : xv ≠ 0)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnP1ApproxWith c x (w₀ * 2 ^ f)).1
      (lnP1ApproxWith c x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (lnP1ApproxWith c x)
    (irrational_log_one_add_of_toVal hx (by linarith) hx0)
    (lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)|) (tendsto_lnRatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := lnP1ApproxWith_spec c hw hx hx1 hx0
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-- The bracket of `ln 2` that `c` supplies for `w` is fit for `w`. -/
theorem LnConsts.ln2At_fit (c : LnConsts) {w : ℕ} (hw : 64 ≤ w) : Ln2BracketFor w (c.ln2At w) := by
  unfold LnConsts.ln2At
  split_ifs with hW
  · rw [c.ln2_eq]
    exact (ln2BracketFor_ln2Bracket (by omega)).of_le hW
  · exact ln2BracketFor_ln2Bracket (by omega)

/-! ### Facts about the exponent for `lnP1PrecRound` -/

theorem toVal_neg_one : (-one).toVal = some ((-1 : ℝ) : EReal) := by
  rw [toVal_neg, toVal_one']; rfl

/-- A negative float with exponent `e ≤ 0` (`¬ (e.sign ∧ e.abs ≠ 0)`) lies in `(−1, 0)`. -/
theorem finiteVal_false_gt_neg_one (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h : ¬ (e.sign = true ∧ e.abs ≠ 0)) : -1 < finiteVal false e m := by
  have he : e.toInt ≤ 0 := by
    unfold AzInt.toInt
    split_ifs with hs
    · have h0 : e.abs = 0 := by
        by_contra hne; exact h ⟨hs, hne⟩
      rw [h0, AzNat.toNat_zero]; rfl
    · omega
  have hb := (abs_finiteVal_bounds true e hv).2
  have hpos := finiteVal_true_pos e hv
  rw [abs_of_pos hpos] at hb
  have h1 : (2 : ℝ) ^ e.toInt ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) he
  rw [finiteVal_false]
  linarith

/-- A negative float with exponent `e ≥ 1` (`e.sign ∧ e.abs ≠ 0`) is `≤ −1`. -/
theorem finiteVal_false_le_neg_one (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h : e.sign = true ∧ e.abs ≠ 0) : finiteVal false e m ≤ -1 := by
  have he : 1 ≤ e.toInt := by
    unfold AzInt.toInt
    rw [h.1]
    simp only [↓reduceIte]
    have := toNat_ne_zero_of_ne_zero h.2
    omega
  have hb := (abs_finiteVal_bounds true e hv).1
  have hpos := finiteVal_true_pos e hv
  rw [abs_of_pos hpos] at hb
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (e.toInt - 1) := one_le_zpow₀ (by norm_num) (by omega)
  rw [finiteVal_false]
  linarith

theorem finiteVal_false_ne_zero (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal false e m ≠ 0 := by
  rw [finiteVal_false]; exact neg_ne_zero.mpr (finiteVal_true_pos e hv).ne'

end Azurite.AzFloat
