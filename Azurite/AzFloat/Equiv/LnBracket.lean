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
import Azurite.AzRat.Equiv.Order
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Mul
import Azurite.BrentZimmermann.Chapter4.AGMLogBound
import Azurite.Transcendental.Exp

/-!
# Equivalence: the bracket of `ln x`

* `RelEncloses`: the interval AGM keeps the iterates within a *relative* error `δ`, and one
  step adds at most `8 · 2^(−w)` to `δ` (`relEncloses_agmStep`): the AGM is homogeneous, so the
  roundings — each within a factor `1 ± 2 · 2^(−w)` — compose multiplicatively.
* `agm_log_gap`: after `lnSteps w` steps from `(1, k)`, `k ≥ 2^(−2h)`, the gap is at most
  `8 · 2^(−5h)` (`agm_log_iterations`, then two quadratic steps).
* `lnBracket_spec`: for a positive float `x` with exponent `e`, `lnBracket x e w` encloses
  `ln x` with width at most `lnEps e w = 2^40 (w + |e| + 8)^5 2^(−w)` (`w ≥ 64`), using
  `abs_pi_div_AGM_sub_log_le` (MCA's AGM–logarithm error), `piBracket_spec` and `ln2Bracket_spec`
  (the term `ℓ ln 2`, `ln_L_spec`).
* `lnApprox_isSome_exists`: the Ziv certificate, from `irrational_log_rat`.
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

/-! ### The relative enclosure of the AGM iterates -/

/-- The ends of `s` enclose `(a_n, b_n)` and lie within the relative error `δ`. -/
def RelEncloses (a b : ℝ) (n : ℕ) (δ : ℝ) (s : AgmBounds) : Prop :=
  ∃ al ah bl bh : ℝ, s.aLo.toVal = some (al : EReal) ∧ s.aHi.toVal = some (ah : EReal) ∧
    s.bLo.toVal = some (bl : EReal) ∧ s.bHi.toVal = some (bh : EReal) ∧
    agmA a b n * (1 - δ) ≤ al ∧ al ≤ agmA a b n ∧ agmA a b n ≤ ah ∧ ah ≤ agmA a b n * (1 + δ) ∧
    agmB a b n * (1 - δ) ≤ bl ∧ bl ≤ agmB a b n ∧ agmB a b n ≤ bh ∧ bh ≤ agmB a b n * (1 + δ)

variable {a b : ℝ}

/-- One step adds `8 · 2^(−w)` to the relative error. -/
theorem relEncloses_agmStep (ha : 0 < a) (hb : 0 < b) {n : ℕ} {δ : ℝ} {s : AgmBounds} (w : ℕ)
    [NeZero w] (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8)
    (h : RelEncloses a b n δ s) :
    RelEncloses a b (n + 1) (δ + 8 * (1 / 2 : ℝ) ^ w) (agmStep w s) := by
  obtain ⟨al, ah, bl, bh, hal, hah, hbl, hbh, hal1, hal2, hah1, hah2, hbl1, hbl2, hbh1, hbh2⟩ := h
  set u := (1 / 2 : ℝ) ^ w with hu_def
  have hu0 : 0 < u := by positivity
  obtain ⟨hA, hB⟩ := agm_pos ha hb n
  set A := agmA a b n with hA_def
  set B := agmB a b n with hB_def
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hal0 : 0 ≤ al := le_trans (mul_nonneg hA.le h1δ) hal1
  have hbl0 : 0 ≤ bl := le_trans (mul_nonneg hB.le h1δ) hbl1
  have hah0 : 0 ≤ ah := le_trans hA.le hah1
  have hbh0 : 0 ≤ bh := le_trans hB.le hbh1
  simp only [agmStep]
  -- the arithmetic mean
  obtain ⟨r1, hr1, hf1⟩ := addFloor_err hal hbl w (by linarith)
  obtain ⟨r2, hr2, hc2⟩ := addCeiling_err hah hbh w (by linarith)
  -- the geometric mean
  obtain ⟨m1, hm1, hfm1⟩ := mulFloor_err hal hbl w (mul_nonneg hal0 hbl0)
  obtain ⟨m2, hm2, hcm2⟩ := mulCeiling_err hah hbh w (mul_nonneg hah0 hbh0)
  obtain ⟨q1, hq1, hfq1⟩ := sqrtFloor_err hm1 hfm1.nonneg w
  have hm2nn : 0 ≤ m2 := le_trans (mul_nonneg hah0 hbh0) hcm2.ge
  obtain ⟨q2, hq2, hcq2⟩ := sqrtCeiling_err hm2 hm2nn w
  have hAB0 : 0 ≤ A * B := mul_nonneg hA.le hB.le
  have hS0 : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  refine ⟨r1 / 2, r2 / 2, q1, q2, toVal_half hr1, toVal_half hr2, hq1, hq2, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
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
  · rw [agmA_succ]; linarith [hc2.ge]
  · rw [agmA_succ]
    have h3 : ah + bh ≤ (A + B) * (1 + δ) := by linarith
    have h4 : r2 ≤ (ah + bh) * (1 + 2 * u) := by linarith [hc2.le]
    have h5 : (ah + bh) * (1 + 2 * u) ≤ (A + B) * (1 + δ) * (1 + 2 * u) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    have h6 : (A + B) * (1 + δ) * (1 + 2 * u) ≤ (A + B) * (1 + (δ + 8 * u)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
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
  · rw [agmB_succ]
    have h1 : A * B ≤ ah * bh := mul_le_mul hah1 hbh1 hB.le hah0
    exact (Real.sqrt_le_sqrt (h1.trans hcm2.ge)).trans hcq2.ge
  · rw [agmB_succ]
    have hm2le : m2 ≤ ah * bh * (1 + 2 * u) := by linarith [hcm2.le]
    have hprod : ah * bh ≤ A * (1 + δ) * (B * (1 + δ)) :=
      mul_le_mul hah2 hbh2 hbh0 (mul_nonneg hA.le (by linarith))
    have hm2hi : m2 ≤ A * B * ((1 + δ) ^ 2 * (1 + 2 * u)) := by
      calc m2 ≤ ah * bh * (1 + 2 * u) := hm2le
        _ ≤ A * (1 + δ) * (B * (1 + δ)) * (1 + 2 * u) :=
            mul_le_mul_of_nonneg_right hprod (by linarith)
        _ = A * B * ((1 + δ) ^ 2 * (1 + 2 * u)) := by ring
    have hsq : Real.sqrt m2 ≤ Real.sqrt (A * B * ((1 + δ) ^ 2 * (1 + 2 * u))) :=
      Real.sqrt_le_sqrt hm2hi
    rw [Real.sqrt_mul hAB0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)] at hsq
    have hs2u : Real.sqrt (1 + 2 * u) ≤ 1 + u := sqrt_one_add_le hu0.le
    have h7 : Real.sqrt m2 ≤ Real.sqrt (A * B) * (1 + δ) * (1 + u) := by
      calc Real.sqrt m2 ≤ Real.sqrt (A * B) * ((1 + δ) * Real.sqrt (1 + 2 * u)) := hsq
        _ ≤ Real.sqrt (A * B) * ((1 + δ) * (1 + u)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2u (by linarith)) hS0
        _ = _ := by ring
    have h8 : q2 ≤ Real.sqrt m2 * (1 + 2 * u) := by linarith [hcq2.le]
    have h9 : Real.sqrt m2 * (1 + 2 * u) ≤ Real.sqrt (A * B) * (1 + δ) * (1 + u) * (1 + 2 * u) :=
      mul_le_mul_of_nonneg_right h7 (by linarith)
    have h10 : Real.sqrt (A * B) * (1 + δ) * (1 + u) * (1 + 2 * u)
        ≤ Real.sqrt (A * B) * (1 + (δ + 8 * u)) := by
      have huu : u * u ≤ u / 8 := by
        have := mul_le_mul_of_nonneg_left hu hu0.le; linarith
      have hdu : δ * u ≤ u / 2 := by
        have := mul_le_mul_of_nonneg_right hδ hu0.le; linarith
      have hduu : δ * (u * u) ≤ u / 16 := by
        have := mul_le_mul_of_nonneg_left huu hδ0
        have := mul_le_mul_of_nonneg_right hδ (by positivity : (0 : ℝ) ≤ u / 8)
        nlinarith
      have e : (1 + δ) * (1 + u) * (1 + 2 * u)
          = 1 + δ + 3 * u + 2 * (u * u) + 3 * (δ * u) + 2 * (δ * (u * u)) := by ring
      have : (1 + δ) * (1 + u) * (1 + 2 * u) ≤ 1 + (δ + 8 * u) := by
        rw [e]
        linarith
      calc Real.sqrt (A * B) * (1 + δ) * (1 + u) * (1 + 2 * u)
          = Real.sqrt (A * B) * ((1 + δ) * (1 + u) * (1 + 2 * u)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hS0
    linarith

theorem relEncloses_agmIterN (ha : 0 < a) (hb : 0 < b) (w : ℕ) [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) :
    ∀ (n m : ℕ) {δ : ℝ} {s : AgmBounds}, 0 ≤ δ → δ + 8 * (1 / 2 : ℝ) ^ w * n ≤ 1 / 2 →
      RelEncloses a b m δ s →
      RelEncloses a b (m + n) (δ + 8 * (1 / 2 : ℝ) ^ w * n) (agmIterN w n s)
  | 0, m, δ, s, _, _, h => by
    simp only [agmIterN, Nat.cast_zero, mul_zero, add_zero]
    exact h
  | n + 1, m, δ, s, hδ0, hδ, h => by
    have hu0 : 0 < (1 / 2 : ℝ) ^ w := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep := relEncloses_agmStep ha hb w hδ0 (by push_cast at hδ; nlinarith) hu h
    have hrec := relEncloses_agmIterN ha hb w hu n (m + 1) (δ := δ + 8 * (1 / 2 : ℝ) ^ w)
      (by positivity) (by push_cast at hδ ⊢; linarith) hstep
    have e1 : m + (n + 1) = m + 1 + n := by omega
    have e2 : δ + 8 * (1 / 2 : ℝ) ^ w * ((n + 1 : ℕ) : ℝ)
        = δ + 8 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (n : ℝ) := by push_cast; ring
    simp only [agmIterN]
    rw [e1, e2]
    exact hrec

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
      + 2 * (2 * (1 / 2 : ℝ) ^ w + 8 * (1 / 2 : ℝ) ^ w * (S : ℝ)))
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
  have hahbl : ah - bl ≤ 200 * W * u := by
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
  have hQpm' : Qp - Qm ≤ (9 * 2 ^ 19 + 3600) * (W ^ 5 * u) := by
    have h1 : (piEps w + 2 * (ah - bl)) * (3 * W) ^ 2
        ≤ (2 ^ 19 * W ^ 3 * u + 2 * (200 * W * u)) * (3 * W) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h2 : (2 ^ 19 * W ^ 3 * u + 2 * (200 * W * u)) * (3 * W) ^ 2
        = 9 * 2 ^ 19 * (W ^ 5 * u) + 3600 * (W ^ 3 * u) := by ring
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
  have hfin : (9 * 2 ^ 19 + 3600 : ℝ) * (W ^ 5 * u) + 140 * (W ^ 5 * u) + W ^ 5 * u
      + 12 * (W ^ 5 * u) ≤ 2 ^ 40 * (W ^ 5 * u) := by
    calc (9 * 2 ^ 19 + 3600 : ℝ) * (W ^ 5 * u) + 140 * (W ^ 5 * u) + W ^ 5 * u + 12 * (W ^ 5 * u)
        = (9 * 2 ^ 19 + 3600 + 140 + 1 + 12) * (W ^ 5 * u) := by ring
      _ ≤ 2 ^ 40 * (W ^ 5 * u) := mul_le_mul_of_nonneg_right (by norm_num) hP0
  unfold lnEps
  rw [← hW]
  have : hi - lo ≤ (9 * 2 ^ 19 + 3600 : ℝ) * (W ^ 5 * u) + 140 * (W ^ 5 * u) + W ^ 5 * u
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

/-! ### The interval AGM -/

/-- After `2 ⌈lg 2h⌉ + 3` interval steps from `(1, [k⁻, k⁺])`: `b⁻ ≤ AGM(1, k) ≤ a⁺`, with
`b⁻ ≥ 1/(8h + 12)`, `a⁺ ≤ 2` and `a⁺ − b⁻ ≤ 8 · 2^(−5h) + 2 δ`, `δ = (2 + 8 S) 2^(−w)`. -/
theorem lnAgm_spec {w : ℕ} (hw : 64 ≤ w) {k : ℝ} (h : ℕ) (hh : 2 ≤ h) (hh4 : w + 5 ≤ 4 * h)
    (hh4' : 4 * h ≤ w + 8) (hk1 : (1 / 2 : ℝ) ^ (2 * h) ≤ k)
    (hk2 : k ≤ 2 * (1 / 2 : ℝ) ^ (2 * h)) (hk3 : k ≤ 1)
    {kLo kHi : AzFloat} {kl kh : ℝ} (hkl : kLo.toVal = some (kl : EReal))
    (hkh : kHi.toVal = some (kh : EReal)) (hfl : FloorOf w k kl) (hch : CeilOf w k kh) :
    ∃ ah bl : ℝ,
      (agmIterN w (2 * Nat.clog 2 (2 * h) + 3) ⟨one, one, kLo, kHi⟩).aHi.toVal = some (ah : EReal) ∧
      (agmIterN w (2 * Nat.clog 2 (2 * h) + 3) ⟨one, one, kLo, kHi⟩).bLo.toVal = some (bl : EReal) ∧
      bl ≤ AGM 1 k ∧ AGM 1 k ≤ ah ∧ 1 / (8 * h + 12) ≤ bl ∧ ah ≤ 2 ∧
      ah - bl ≤ 8 * (1 / 2 : ℝ) ^ (5 * h)
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
  -- the initial relative enclosure
  have h0 : RelEncloses 1 k 0 (2 * u) ⟨one, one, kLo, kHi⟩ := by
    refine ⟨1, 1, kl, kh, toVal_one', toVal_one', hkl, hkh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [agmA_zero]; linarith
    · simp only [agmA_zero]; exact le_rfl
    · simp only [agmA_zero]; exact le_rfl
    · simp only [agmA_zero]; linarith
    · simp only [agmB_zero]; linarith [hfl.ge]
    · simp only [agmB_zero]; exact hfl.le
    · simp only [agmB_zero]; exact hch.ge
    · simp only [agmB_zero]; linarith [hch.le]
  have hiter := relEncloses_agmIterN one_pos hk0 w hu8 S 0 (δ := 2 * u) (by positivity)
    (by rw [← hδ]; exact hδ_le) h0
  rw [Nat.zero_add] at hiter
  obtain ⟨al, ah, bl, bh, -, hah, hbl, -, -, -, hah1, hah2, hbl1, hbl2, -, -⟩ := hiter
  rw [← hδ] at hah2 hbl1
  -- the exact iterates
  have hgap := agm_log_gap hk0 hk3 h hk1
  rw [← hS] at hgap
  have hbM : agmB 1 k S ≤ AGM 1 k := agmB_le_AGM one_pos hk0 hS1
  have hMa : AGM 1 k ≤ agmA 1 k S := AGM_le_agmA one_pos hk0 hS1
  have haS1 : agmA 1 k S ≤ 1 := agmA_one_le hk0 hk3 hS1
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
  refine ⟨ah, bl, hah, hbl, hbl2.trans hbM, hMa.trans hah1, ?_, ?_, ?_⟩
  · have h1 : agmB 1 k S * (1 / 2) ≤ agmB 1 k S * (1 - δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hbS0.le
    have h2 : (1 : ℝ) / (8 * h + 12) = 1 / (4 * h + 6) * (1 / 2) := by field_simp; ring
    rw [h2]
    calc 1 / (4 * h + 6) * (1 / 2 : ℝ) ≤ agmB 1 k S * (1 / 2) :=
          mul_le_mul_of_nonneg_right hbSlo (by norm_num)
      _ ≤ agmB 1 k S * (1 - δ) := h1
      _ ≤ bl := hbl1
  · have : agmA 1 k S * (1 + δ) ≤ 1 * (3 / 2) :=
      mul_le_mul haS1 (by linarith) (by linarith) zero_le_one
    linarith
  · have e : agmA 1 k S * (1 + δ) - agmB 1 k S * (1 - δ)
        = (agmA 1 k S - agmB 1 k S) + δ * (agmA 1 k S + agmB 1 k S) := by ring
    have h1 : δ * (agmA 1 k S + agmB 1 k S) ≤ δ * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0
    linarith

/-! ### The term `ℓ ln 2` -/

/-- The bracket of `ℓ ln 2`: `|ℓ|` times the float bracket of `ln 2`, rounded outward, the signs
restored by negation when `ℓ < 0`. -/
theorem ln_L_spec {w : ℕ} (hw : 64 ≤ w) (ℓ : AzInt) :
    ∃ LLo LHi : ℝ,
      (if ℓ.sign = true then (mulPrecRound (ofAzNat ℓ.abs) (ln2Bracket w).1 w .Floor).1
        else -(mulPrecRound (ofAzNat ℓ.abs) (ln2Bracket w).2 w .Ceiling).1).toVal
          = some (LLo : EReal) ∧
      (if ℓ.sign = true then (mulPrecRound (ofAzNat ℓ.abs) (ln2Bracket w).2 w .Ceiling).1
        else -(mulPrecRound (ofAzNat ℓ.abs) (ln2Bracket w).1 w .Floor).1).toVal
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
  obtain ⟨a, b, ha, hb, haL, hLb, hab, hapos⟩ := ln2Bracket_spec w
  rw [← hu_def] at hab
  have ha5 : 1 / 5 ≤ a := hapos (by omega)
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

/-- `lnBracket x e w` encloses `ln x`, with width at most `lnEps e w` (`w ≥ 64`). -/
theorem lnBracket_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, (lnBracket (finite true e q m hv) e w).1.toVal = some (lv : EReal) ∧
      (lnBracket (finite true e q m hv) e w).2.toVal = some (hv' : EReal) ∧
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
  -- `k` enclosed
  obtain ⟨kl, hkl, hfl⟩ := divFloor_err toVal_four hy hy0 (by norm_num) w
  obtain ⟨kh, hkh, hch⟩ := divCeiling_err toVal_four hy hy0 (by norm_num) w
  rw [← hk] at hfl hch
  -- the AGM
  obtain ⟨ah, bl, hah, hbl, hblM, hMah, hbllo, hah2, hwidth⟩ :=
    lnAgm_spec hw h hh2 hh4 hh4' hk1 hk2 hk3 hkl hkh hfl hch
  rw [← hS] at hah hbl hwidth
  have hbl0 : 0 < bl := lt_of_lt_of_le (by positivity) hbllo
  have hah0 : 0 < ah := lt_of_lt_of_le hM0 hMah
  -- `π`
  obtain ⟨pl, ph, hpl, hph, hpl0, hplπ, hπph, hpw⟩ := piBracket_spec hw
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
  obtain ⟨LLo, LHi, hLLo, hLHi, hL1, hL2, hLw, hLLo_abs, hLHi_abs⟩ := ln_L_spec hw ℓ
  -- the final combination
  simp only [lnBracket]
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

end Azurite.AzFloat
