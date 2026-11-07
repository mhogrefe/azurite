/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section23Gudermannian
import Azurite.DLMF.Chapter4.Section6

/-!
# DLMF §4.24 Inverse Trigonometric Functions: Further Properties

## §4.24(i) Power Series

All principal values are the 4.23(i) integrals (`arcsinD`, `arccosD`, `arctanD`).

* 4.24.1 (`|z| ≤ 1`, absolutely convergent): `dlmf_4_24_1`. Inside the disc the binomial series
  of `(1 − (sz)²)^{−1/2}` (`hasSum_one_sub_cpow_neg_half`, from 4.6.7 via
  `choose_neg_half_mul_neg_one_pow`) is integrated term by term (`hasSum_arcsinD`). The
  coefficients are summable because their partial sums are bounded by `arcsin 1 = ½π`
  (`summable_arcsinCoeff`). The boundary follows by
  continuity (`continuousOn_arcsinD_closedBall`, using 4.23.19 at `±1`).
* 4.24.2 (`|1 − z| ≤ 2`, absolutely convergent): `dlmf_4_24_2`, from 4.24.1 and the half-angle
  relation `arccos z = 2 arcsin(((1 − z)/2)^{1/2})` (`arccosD_eq_two_mul_arcsinD`). On the cut
  `1 < z ≤ 3` this uses the values of the integrals `arcsin x = ½π − i arccosh x`
  (`arcsinD_of_one_lt`) and `arcsin(iy) = i arcsinh y` (`arcsinD_I_mul`).
* 4.24.3 (`|z| ≤ 1`, `z ≠ ±i`): `dlmf_4_24_3` (partial sums; conditionally convergent on
  `|z| = 1`, via `tendsto_oddLogSeries` of §4.6), `dlmf_4_24_3_hasSum` (`|z| < 1`).
* 4.24.4 (`ℜz ≷ 0`, `|z| ≥ 1`): `dlmf_4_24_4`, via 4.23.18.
* 4.24.5 (`ℜ(z²) > −½`): `dlmf_4_24_5`. The 4.23.3 integrand is expanded as a geometric series
  in `t(1 − s²)`, `t = z²/(1 + z²)`, and integrated term by term with
  `∫₀¹ (1 − s²)ⁿ ds = 2·4⋯(2n)/(3·5⋯(2n + 1))` (`integral_one_sub_sq_pow`). The condition is
  exactly `|t| < 1` (`norm_div_one_add_lt_one_iff`).
* 4.24.6: `dlmf_4_24_6`.

## §4.24(ii) Derivatives

Each formula holds where the principal value is analytic (off its cuts).

* 4.24.7–4.24.9, 4.24.12: `dlmf_4_24_7`, `dlmf_4_24_8`, `dlmf_4_24_9`, `dlmf_4_24_12`.
* 4.24.10–4.24.11 (`ℜz ≷ 0`): `dlmf_4_24_10`, `dlmf_4_24_11`. The two signs come from
  `z(1 − z⁻²)^{1/2} = ±(z² − 1)^{1/2}` for `ℜz ≷ 0` (`mul_cpow_half_one_sub_inv_sq`; the
  principal `(z² − 1)^{1/2}` changes branch across the imaginary axis).

## §4.24(iii) Addition Formulas

DLMF: "every value of the left-hand side is a value of the right-hand side and vice versa. All
square roots have either possible value." The general values are the 4.23(i) sets `arcsinGen`,
`arccosGen`, `arctanGen`, `arccotGen`. The 4.23.1 paths avoid `±1`, so the arguments `±1` are
excluded. The sign `±` is `σ = ±1`.

* 4.24.14, 4.24.15, the first equality of 4.24.16, 4.24.17: set equalities `dlmf_4_24_14`,
  `dlmf_4_24_15`, `dlmf_4_24_16`, `dlmf_4_24_17`.
* 4.24.13 and the second equality of 4.24.16 (**errata**): only "every value of the left-hand
  side is a value of the right-hand side" holds (`dlmf_4_24_13`, `dlmf_4_24_16_arccos`).
  Counterexamples to the converse, already with principal roots: `dlmf_4_24_13_converse_fails`
  (`⅔π ∈ Arcsin(√3/2)`, `∉ Arcsin ½ + Arcsin ½`) and `dlmf_4_24_16_arccos_converse_fails`
  (`−½π ∈ Arccos 0`, `∉ Arcsin ½ + Arccos ½`).
-/

open Set Filter Topology Complex MeasureTheory Finset Polynomial
open scoped Real Interval

namespace Azurite.DLMF

theorem complex_ring_choose_succ_mul (a : ℂ) (n : ℕ) :
    Ring.choose a (n + 1) * (n + 1) = Ring.choose a n * (a - n) := by
  have h : ∀ m : ℕ, (descPochhammer ℤ m).smeval a = (descPochhammer ℂ m).eval a := by
    intro m
    rw [← aeval_eq_smeval, aeval_def, eval₂_eq_eval_map, descPochhammer_map]
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, h, h, descPochhammer_succ_eval,
    Nat.factorial_succ, smul_eq_mul, smul_eq_mul]
  push_cast
  have := Nat.cast_ne_zero (R := ℂ) |>.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- The coefficient `1·3·5⋯(2n − 1)/(2·4·6⋯(2n))` of 4.24.1. -/
noncomputable def arcsinCoeff (n : ℕ) : ℝ := ∏ i ∈ range n, ((2 * i + 1 : ℝ) / (2 * i + 2))

theorem arcsinCoeff_succ (n : ℕ) :
    arcsinCoeff (n + 1) = arcsinCoeff n * ((2 * n + 1) / (2 * n + 2)) := prod_range_succ _ _

theorem arcsinCoeff_nonneg (n : ℕ) : 0 ≤ arcsinCoeff n :=
  prod_nonneg fun i _ => by positivity

theorem arcsinCoeff_le_one (n : ℕ) : arcsinCoeff n ≤ 1 :=
  prod_le_one₀ (fun i _ => by positivity) fun i _ => by
    rw [div_le_one (by positivity)]; linarith

/-- `C(−1/2, n)(−1)ⁿ = 1·3⋯(2n − 1)/(2·4⋯(2n))`. -/
theorem choose_neg_half_mul_neg_one_pow (n : ℕ) :
    Ring.choose (-1 / 2 : ℂ) n * (-1) ^ n = arcsinCoeff n := by
  induction n with
  | zero => simp [arcsinCoeff]
  | succ n ih =>
    have h1 := complex_ring_choose_succ_mul (-1 / 2) n
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hr : Ring.choose (-1 / 2 : ℂ) (n + 1) =
        Ring.choose (-1 / 2 : ℂ) n * (-1 / 2 - n) / (n + 1) := by
      rw [eq_div_iff hn]; exact h1
    rw [hr, arcsinCoeff_succ, pow_succ]
    push_cast
    rw [← ih]
    have : (2 * (n : ℂ) + 2) ≠ 0 := by
      rw [show (2 * (n : ℂ) + 2) = 2 * (n + 1) by ring]; exact mul_ne_zero two_ne_zero hn
    field_simp
    ring

/-- The binomial series `(1 − w)^{−1/2} = ∑ (1·3⋯(2n − 1))/(2·4⋯(2n)) wⁿ`, `|w| < 1`. -/
theorem hasSum_one_sub_cpow_neg_half {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (arcsinCoeff n : ℂ) * w ^ n) ((1 - w) ^ (-1 / 2 : ℂ)) := by
  have h := dlmf_4_6_7 (-1 / 2) (z := -w) (by rwa [norm_neg])
  rw [← sub_eq_add_neg] at h
  refine h.congr_fun fun n => ?_
  rw [← choose_neg_half_mul_neg_one_pow]; ring

theorem integral_ofReal_pow_mul (c : ℂ) (m : ℕ) :
    ∫ s in (0 : ℝ)..1, c * (s : ℂ) ^ m = c / (m + 1) := by
  rw [intervalIntegral.integral_const_mul]
  have : ∫ s in (0 : ℝ)..1, (s : ℂ) ^ m = ((∫ s in (0 : ℝ)..1, s ^ m : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [this, integral_pow]
  push_cast
  ring

/-- **DLMF 4.24.1** inside the unit disc: the binomial series of the 4.23.1 integrand, integrated
term by term. -/
theorem hasSum_arcsinD {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) / (2 * n + 1)) (arcsinD z) := by
  have hint : ∀ n : ℕ, ∫ s in (0 : ℝ)..1, (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) * (s : ℂ) ^ (2 * n)
      = (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) / (2 * n + 1) := by
    intro n
    rw [integral_ofReal_pow_mul]; push_cast; ring
  rw [show (fun n : ℕ => (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) / (2 * n + 1)) = fun n =>
    ∫ s in (0 : ℝ)..1, (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) * (s : ℂ) ^ (2 * n) from
    funext fun n => (hint n).symm, arcsinD]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => ‖z‖ ^ (2 * n + 1)) (fun n => by fun_prop) ?_ ?_ ?_ ?_
  · intro n
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (arcsinCoeff_nonneg n), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs.1]
    have h1 := arcsinCoeff_le_one n
    have h2 : s ^ (2 * n) ≤ 1 := pow_le_one₀ hs.1.le hs.2
    have h3 : 0 ≤ ‖z‖ ^ (2 * n + 1) := by positivity
    calc arcsinCoeff n * ‖z‖ ^ (2 * n + 1) * s ^ (2 * n) ≤ 1 * ‖z‖ ^ (2 * n + 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) h2 (pow_nonneg hs.1.le _) (by positivity)
      _ = _ := by ring
  · refine Eventually.of_forall fun s _ => ?_
    have hq : ‖z‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg z) hz two_ne_zero
    exact ((summable_geometric_of_lt_one (by positivity) hq).mul_left ‖z‖).congr fun n => by
      ring
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hw : ‖(s * z) ^ 2‖ < 1 := by
      rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      have : s * ‖z‖ < 1 := by nlinarith [norm_nonneg z, hs.2]
      exact pow_lt_one₀ (mul_nonneg hs.1.le (norm_nonneg z)) this two_ne_zero
    have h := (hasSum_one_sub_cpow_neg_half hw).mul_left z
    convert h using 1
    · funext n; ring
    · rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg, div_eq_mul_inv]

/-- The coefficients of 4.24.1 are summable (their sum is `arcsin 1 = π/2`). -/
theorem summable_arcsinCoeff :
    Summable fun n : ℕ => arcsinCoeff n / (2 * n + 1) := by
  have hreal : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasSum (fun n : ℕ => arcsinCoeff n * r ^ (2 * n + 1) / (2 * n + 1)) (Real.arcsin r) := by
    intro r hr
    have h := hasSum_arcsinD (z := r) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]; exact hr.2)
    rw [arcsinD_ofReal ⟨by linarith [hr.1], hr.2⟩] at h
    exact Complex.hasSum_ofReal.mp (by push_cast; exact h)
  refine summable_of_sum_range_le (c := π / 2)
    (fun n => div_nonneg (arcsinCoeff_nonneg n) (by positivity)) fun N => ?_
  have hc : Continuous fun r : ℝ => ∑ n ∈ range N, arcsinCoeff n * r ^ (2 * n + 1) / (2 * n + 1) :=
    by fun_prop
  have hlim := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  simp only [one_pow, mul_one] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  refine (sum_le_hasSum (range N) (fun n _ => ?_) (hreal r hr)).trans (Real.arcsin_le_pi_div_two r)
  exact div_nonneg (mul_nonneg (arcsinCoeff_nonneg n) (pow_nonneg hr.1.le _)) (by positivity)

theorem continuousAt_arcsin_log {z₀ : ℂ} (h : z₀ ^ 2 = 1) :
    ContinuousAt (fun z : ℂ => -I * log ((1 - z ^ 2) ^ (1 / 2 : ℂ) + I * z)) z₀ := by
  have h1 : ContinuousAt (fun z : ℂ => (1 - z ^ 2) ^ (1 / 2 : ℂ)) z₀ := by
    have hc := continuousAt_cpow_zero_of_re_pos (z := 1 / 2) (by norm_num)
    refine ContinuousAt.comp_of_eq (f := fun z : ℂ => (1 - z ^ 2, (1 / 2 : ℂ))) hc
      (by fun_prop) ?_
    simp [h]
  refine continuousAt_const.mul ((continuousAt_clog ?_).comp (h1.add (by fun_prop)))
  rw [h, sub_self, zero_cpow (by norm_num), zero_add]
  refine mem_slitPlane_of_im_ne ?_
  simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  intro hre
  have : z₀ = (z₀.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [this, mul_pow, I_sq, mul_neg_one, ← ofReal_pow, ← ofReal_neg, ← ofReal_one, ofReal_inj] at h
  nlinarith [sq_nonneg z₀.im]

theorem mem_arcsinCut_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : z ∈ arcsinCut ∨ z = 1 ∨ z = -1 := by
  by_cases h : z.im ≠ 0
  · exact Or.inl (Or.inl h)
  push Not at h
  have hre : |z.re| ≤ 1 := (abs_re_le_norm z).trans hz
  rcases hre.lt_or_eq with h' | h'
  · exact Or.inl (Or.inr h')
  · right
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])
    rcases abs_eq (zero_le_one' ℝ) |>.mp h' with h'' | h''
    · left; rw [hz', h'']; simp
    · right; rw [hz', h'']; simp

theorem continuousOn_arcsinD_closedBall : ContinuousOn arcsinD (Metric.closedBall 0 1) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rcases mem_arcsinCut_of_norm_le hz with h | h
  · exact (hasStrictDerivAt_arcsinD h).hasDerivAt.continuousAt.continuousWithinAt
  · have h2 : z ^ 2 = 1 := by rcases h with rfl | rfl <;> norm_num
    refine (continuousAt_arcsin_log h2).continuousWithinAt.congr (fun w hw => ?_) ?_
    · rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact dlmf_4_23_19 (mem_arcsinCut_of_norm_le hw)
    · exact dlmf_4_23_19 (Or.inr h)

/-- **DLMF 4.24.1**: `arcsin z = z + (1/2)(z³/3) + (1·3)/(2·4)(z⁵/5) + ⋯`, `|z| ≤ 1`
(absolutely convergent). -/
theorem dlmf_4_24_1 {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) / (2 * n + 1)) (arcsinD z) := by
  set T : ℕ → ℂ → ℂ := fun n w => (arcsinCoeff n : ℂ) * w ^ (2 * n + 1) / (2 * n + 1) with hT
  have hb : ∀ n (w : ℂ), ‖w‖ ≤ 1 → ‖T n w‖ ≤ arcsinCoeff n / (2 * n + 1) := by
    intro n w hw
    have hn : ‖(2 * (n : ℂ) + 1)‖ = 2 * n + 1 := by
      rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    simp only [hT, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (arcsinCoeff_nonneg n), hn]
    gcongr
    calc arcsinCoeff n * ‖w‖ ^ (2 * n + 1) ≤ arcsinCoeff n * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg w) hw) (arcsinCoeff_nonneg n)
      _ = _ := mul_one _
  have hcont : ContinuousOn (fun w => ∑' n, T n w) (Metric.closedBall 0 1) :=
    continuousOn_tsum (fun n => by fun_prop) summable_arcsinCoeff fun n w hw => hb n w (by
      rwa [Metric.mem_closedBall, dist_zero_right] at hw)
  have heq : EqOn (fun w => ∑' n, T n w) arcsinD (Metric.closedBall 0 1) :=
    Set.EqOn.of_subset_closure (s := Metric.ball 0 1)
      (fun w hw => (hasSum_arcsinD (by rwa [Metric.mem_ball, dist_zero_right] at hw)).tsum_eq)
      hcont continuousOn_arcsinD_closedBall Metric.ball_subset_closedBall
      (by rw [closure_ball 0 one_ne_zero])
  have hs : Summable fun n => T n z := Summable.of_norm_bounded summable_arcsinCoeff
    fun n => hb n z hz
  have heq' : ∑' n, T n z = arcsinD z := heq (by rwa [Metric.mem_closedBall, dist_zero_right])
  have := hs.hasSum
  rwa [heq'] at this

theorem mem_arctanCut_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ I) (h2 : z ≠ -I) :
    z ∈ arctanCut := by
  by_cases hre : z.re ≠ 0
  · exact Or.inl hre
  push Not at hre
  right
  have him : |z.im| ≤ 1 := (abs_im_le_norm z).trans hz
  refine lt_of_le_of_ne him fun h => ?_
  rcases abs_eq (zero_le_one' ℝ) |>.mp h with h' | h'
  · exact h1 (Complex.ext (by simp [hre]) (by simp [h']))
  · exact h2 (Complex.ext (by simp [hre]) (by simp [h']))

/-- **DLMF 4.24.3**: `arctan z = z − z³/3 + z⁵/5 − z⁷/7 + ⋯`, `|z| ≤ 1`, `z ≠ ±i` (conditionally
convergent on `|z| = 1`, so stated for the partial sums). -/
theorem dlmf_4_24_3 {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ I) (h2 : z ≠ -I) :
    Tendsto (fun K => ∑ k ∈ range K, (-1) ^ k * z ^ (2 * k + 1) / (2 * k + 1)) atTop
      (𝓝 (arctanD z)) := by
  have hu : ‖z * I‖ ≤ 1 := by rwa [norm_mul, norm_I, mul_one]
  have hu1 : z * I ≠ 1 := fun h => h2 (by linear_combination -I * h + z * I_sq)
  have hu2 : z * I ≠ -1 := fun h => h1 (by linear_combination -I * h + z * I_sq)
  have h := (tendsto_oddLogSeries hu hu1 hu2).const_mul (-I / 2)
  rw [arctanD_eq (mem_arctanCut_of_norm_le hz h1 h2), Complex.arctan]
  refine h.congr fun K => ?_
  rw [oddLogPartial, mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hI : I ^ (2 * k + 1) = (-1) ^ k * I := by rw [pow_succ, pow_mul, I_sq]
  rw [mul_pow, hI]
  linear_combination (-((-1) ^ k * z ^ (2 * k + 1) / (2 * k + 1))) * I_sq

/-- **DLMF 4.24.3** inside the unit disc (absolutely convergent). -/
theorem dlmf_4_24_3_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (-1) ^ k * z ^ (2 * k + 1) / (2 * k + 1)) (arctanD z) := by
  have h1 : z ≠ I := fun h => by rw [h, norm_I] at hz; exact lt_irrefl _ hz
  have h2 : z ≠ -I := fun h => by rw [h, norm_neg, norm_I] at hz; exact lt_irrefl _ hz
  rw [arctanD_eq (mem_arctanCut_of_norm_le hz.le h1 h2)]
  convert Complex.hasSum_arctan hz using 2 with k
  push_cast; ring

theorem arctanD_eq_sub_arctanD_inv {z : ℂ} {σ : ℝ} (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    arctanD z = σ * (π / 2) - arctanD (1 / z) := by
  have h := dlmf_4_23_18 (z := z)
  rcases hσ with ⟨hr, rfl⟩ | ⟨hr, rfl⟩
  · rw [← arccotD, h.1 hr]; push_cast; ring
  · rw [← arccotD, h.2 hr]; push_cast; ring

/-- **DLMF 4.24.4**: `arctan z = ±½π − 1/z + 1/(3z³) − 1/(5z⁵) + ⋯`, `ℜz ≷ 0`, `|z| ≥ 1`. -/
theorem dlmf_4_24_4 {z : ℂ} (hz : 1 ≤ ‖z‖) {σ : ℝ}
    (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    Tendsto (fun K => σ * (π / 2) + ∑ k ∈ range K, (-1) ^ (k + 1) / ((2 * k + 1) * z ^ (2 * k + 1)))
      atTop (𝓝 (arctanD z)) := by
  have hre : z.re ≠ 0 := by rcases hσ with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  have hz0 : z ≠ 0 := fun h => hre (by rw [h]; simp)
  have hwre : (1 / z).re ≠ 0 := by
    rw [one_div, inv_re]
    exact div_ne_zero hre (normSq_pos.mpr hz0).ne'
  have hw : ‖1 / z‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact div_le_one_of_le₀ hz (norm_nonneg _)
  have h := (dlmf_4_24_3 hw (fun h => hwre (by rw [h]; simp))
    (fun h => hwre (by rw [h]; simp))).const_sub ((σ : ℂ) * (π / 2))
  rw [← arctanD_eq_sub_arctanD_inv hσ] at h
  refine h.congr fun K => ?_
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [one_div_pow]
  have : z ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hz0
  have : (2 * (k : ℂ) + 1) ≠ 0 := by
    rw [show (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring]
    exact_mod_cast (show (2 * k + 1 : ℕ) ≠ 0 by omega)
  field_simp
  ring

/-! ### 4.24.5–4.24.6 -/

/-- The coefficient `2·4⋯(2n)/(3·5⋯(2n + 1))` of 4.24.5. -/
noncomputable def arctanEulerCoeff (n : ℕ) : ℝ := ∏ i ∈ range n, ((2 * i + 2 : ℝ) / (2 * i + 3))

theorem integral_one_sub_sq_pow_succ (n : ℕ) :
    (2 * (n : ℝ) + 3) * ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ (n + 1) =
      (2 * (n : ℝ) + 2) * ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ n := by
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (1 - s ^ 2) ^ (n + 1))
      (((n : ℝ) + 1) * (1 - x ^ 2) ^ n * (-2 * x)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).const_sub 1).pow (n + 1)
    convert this using 1
    simp
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s) 1 x := fun x _ => hasDerivAt_id' x
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [mul_one, one_pow, sub_self, zero_pow (Nat.succ_ne_zero n), mul_zero] at hparts
  rw [show (fun x : ℝ => ((n : ℝ) + 1) * (1 - x ^ 2) ^ n * (-2 * x) * x) = fun x =>
      -(2 * ((n : ℝ) + 1)) * ((1 - x ^ 2) ^ n - (1 - x ^ 2) ^ (n + 1)) from
      funext fun x => by ring, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)] at hparts
  linear_combination hparts

/-- `∫₀¹ (1 − s²)ⁿ ds = 2·4⋯(2n)/(3·5⋯(2n + 1))`. -/
theorem integral_one_sub_sq_pow (n : ℕ) :
    ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ n = arctanEulerCoeff n := by
  induction n with
  | zero => simp [arctanEulerCoeff]
  | succ n ih =>
    have h := integral_one_sub_sq_pow_succ n
    rw [ih] at h
    rw [arctanEulerCoeff, prod_range_succ, ← arctanEulerCoeff]
    have : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    linear_combination h

theorem norm_div_one_add_lt_one_iff {w : ℂ} (hw : w ≠ -1) :
    ‖w / (1 + w)‖ < 1 ↔ -(1 / 2) < w.re := by
  have h0 : 1 + w ≠ 0 := fun h => hw (by linear_combination h)
  have hp : 0 < ‖1 + w‖ := norm_pos_iff.mpr h0
  rw [norm_div, div_lt_one hp, ← sq_lt_sq₀ (norm_nonneg _) hp.le, Complex.sq_norm,
    Complex.sq_norm, normSq_add, normSq_one, one_mul, conj_re]
  constructor <;> intro h <;> linarith

/-- **DLMF 4.24.6**: `ℜ(z²) > −½` iff `x² − y² > −½`, i.e. `z = x + iy` lies between the two
branches of the rectangular hyperbola `x² − y² = −½` (asymptotes `y = ±x`). -/
theorem dlmf_4_24_6 (z : ℂ) : -(1 / 2) < (z ^ 2).re ↔ -(1 / 2) < z.re ^ 2 - z.im ^ 2 := by
  rw [sq z, mul_re, ← sq, ← sq]

/-- **DLMF 4.24.5**: `arctan z = z/(z² + 1)(1 + (2/3)(z²/(1 + z²))
+ (2·4)/(3·5)(z²/(1 + z²))² + ⋯)`, `ℜ(z²) > −½`. -/
theorem dlmf_4_24_5 {z : ℂ} (hz : -(1 / 2) < (z ^ 2).re) :
    HasSum (fun n : ℕ => z / (z ^ 2 + 1) * ((arctanEulerCoeff n : ℂ) * (z ^ 2 / (1 + z ^ 2)) ^ n))
      (arctanD z) := by
  have hw1 : z ^ 2 ≠ -1 := fun h => by rw [h] at hz; norm_num at hz
  have h0 : 1 + z ^ 2 ≠ 0 := fun h => hw1 (by linear_combination h)
  set t := z ^ 2 / (1 + z ^ 2) with ht
  have htn : ‖t‖ < 1 := (norm_div_one_add_lt_one_iff hw1).mpr hz
  set c := z / (z ^ 2 + 1) with hc
  have hint : ∀ n : ℕ, ∫ s in (0 : ℝ)..1, c * (t ^ n * ((((1 - s ^ 2) ^ n : ℝ)) : ℂ)) =
      c * ((arctanEulerCoeff n : ℂ) * t ^ n) := by
    intro n
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, integral_one_sub_sq_pow]
    ring
  rw [show (fun n : ℕ => c * ((arctanEulerCoeff n : ℂ) * t ^ n)) = fun n =>
    ∫ s in (0 : ℝ)..1, c * (t ^ n * ((((1 - s ^ 2) ^ n : ℝ)) : ℂ)) from
    funext fun n => (hint n).symm, arctanD]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => ‖c‖ * ‖t‖ ^ n) (fun n => by fun_prop) ?_ ?_ ?_ ?_
  · intro n
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have h2 : 1 - s ^ 2 ≤ 1 := by nlinarith [hs.1]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg h1 n)]
    have : (1 - s ^ 2) ^ n ≤ 1 := pow_le_one₀ h1 h2
    have : ‖t‖ ^ n * (1 - s ^ 2) ^ n ≤ ‖t‖ ^ n := by
      calc ‖t‖ ^ n * (1 - s ^ 2) ^ n ≤ ‖t‖ ^ n * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := mul_one _
    exact mul_le_mul_of_nonneg_left this (norm_nonneg c)
  · exact Eventually.of_forall fun s _ =>
      (summable_geometric_of_lt_one (norm_nonneg t) htn).mul_left ‖c‖
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have h2 : 1 - s ^ 2 ≤ 1 := by nlinarith [hs.1]
    have hq : ‖t * ((1 - s ^ 2 : ℝ) : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
      calc ‖t‖ * (1 - s ^ 2) ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg t)
        _ < 1 := by rw [mul_one]; exact htn
    have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left c
    have hne : 1 - t * ((1 - s ^ 2 : ℝ) : ℂ) ≠ 0 := by
      intro h
      have : t * ((1 - s ^ 2 : ℝ) : ℂ) = 1 := by linear_combination -h
      rw [this, norm_one] at hq; exact lt_irrefl _ hq
    have hkey : (1 + z ^ 2) * (1 - t * ((1 - s ^ 2 : ℝ) : ℂ)) = 1 + (s * z) ^ 2 := by
      rw [ht]; push_cast; field_simp; ring
    have hne2 : 1 + ((s : ℂ) * z) ^ 2 ≠ 0 := by rw [← hkey]; exact mul_ne_zero h0 hne
    convert hg using 1
    · funext n; rw [mul_pow, ofReal_pow]
    · have h0' : z ^ 2 + 1 ≠ 0 := by rw [add_comm]; exact h0
      rw [← hkey, hc]
      field_simp
      ring

/-! ### 4.24.2 -/

theorem ofReal_mul_cpow_half {r : ℝ} (hr : 0 < r) (y : ℂ) :
    ((r : ℂ) * y) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) * y ^ (1 / 2 : ℂ) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hy), cpow_def_of_ne_zero hy, log_ofReal_mul hr hy,
    add_mul, exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, ofReal_exp]
  push_cast
  ring_nf

theorem cpow_half_ofReal_neg {a : ℝ} (ha : 0 < a) :
    ((-a : ℝ) : ℂ) ^ (1 / 2 : ℂ) = I * ((√a : ℝ) : ℂ) := by
  rw [ofReal_cpow_of_nonpos (by linarith), show (π : ℂ) * I * (1 / 2) = π / 2 * I by ring,
    exp_pi_div_two_mul_I, ofReal_neg, neg_neg,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow ha.le, Real.sqrt_eq_rpow]
  ring

/-- An integral over `[a, b]` of a function equal on `[a, b]` to `c` times a real function. -/
theorem integral_eq_const_mul_ofReal {f : ℝ → ℂ} {g : ℝ → ℝ} {c : ℂ} {a b : ℝ} (hab : a ≤ b)
    (heq : EqOn f (fun s => c * g s) (Icc a b)) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable f volume a b ∧ ∫ s in a..b, f s = c * ∫ s in a..b, g s := by
  have hg' : IntervalIntegrable (fun s => c * (g s : ℂ)) volume a b :=
    (show IntervalIntegrable (fun s => (g s : ℂ)) volume a b from
      ⟨hg.1.ofReal, hg.2.ofReal⟩).const_mul c
  refine ⟨(intervalIntegrable_congr fun s hs => ?_).mpr hg', ?_⟩
  · rw [uIoc_of_le hab] at hs; exact heq ⟨hs.1.le, hs.2⟩
  · rw [intervalIntegral.integral_congr (by rwa [uIcc_of_le hab]),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal]

/-- On the cut `x > 1`: `arcsin x = ½π − i arccosh x` (the value of the 4.23.1 integral). -/
theorem arcsinD_of_one_lt {x : ℝ} (hx : 1 < x) :
    arcsinD x = π / 2 - I * Real.arcosh x := by
  have hx0 : 0 < x := by linarith
  have hb : 1 / x ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hx0).mpr hx.le⟩
  set f : ℝ → ℂ := fun s => (x : ℂ) / (1 - (s * x) ^ 2) ^ (1 / 2 : ℂ) with hf
  -- the first piece `[0, 1/x]`
  have hd1 : ∀ s ∈ Ioo 0 (1 / x), HasDerivAt (fun s => Real.arcsin (s * x))
      (x / √(1 - (s * x) ^ 2)) s := by
    intro s hs
    have h1 : s * x < 1 := by have := hs.2; rw [lt_div_iff₀ hx0] at this; linarith
    have h2 : -1 < s * x := by nlinarith [hs.1]
    have := (Real.hasDerivAt_arcsin h2.ne' h1.ne).comp s (hasDerivAt_mul_const x)
    rw [show x / √(1 - (s * x) ^ 2) = 1 / √(1 - (s * x) ^ 2) * x by ring]; exact this
  have hc1 : ContinuousOn (fun s => Real.arcsin (s * x)) (Icc 0 (1 / x)) := by fun_prop
  have hi1 : IntervalIntegrable (fun s => x / √(1 - (s * x) ^ 2)) volume 0 (1 / x) :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun s => Real.arcsin (s * x))
      (by rwa [uIcc_of_le hb.1]) (fun s hs => hd1 s (by rwa [min_eq_left hb.1, max_eq_right hb.1]
        at hs)) (fun s _ => by positivity)
  have hv1 : ∫ s in (0 : ℝ)..(1 / x), x / √(1 - (s * x) ^ 2) = π / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.1 hc1 hd1 hi1,
      one_div_mul_cancel hx0.ne', zero_mul, Real.arcsin_one, Real.arcsin_zero, sub_zero]
  have he1 : EqOn f (fun s => (1 : ℂ) * ((x / √(1 - (s * x) ^ 2) : ℝ))) (Icc 0 (1 / x)) := by
    intro s hs
    have h : 0 ≤ 1 - (s * x) ^ 2 := by
      have : s * x ≤ 1 := by have := hs.2; rw [le_div_iff₀ hx0] at this; linarith
      nlinarith [mul_nonneg hs.1 hx0.le]
    simp only [hf, one_mul]
    rw [show (1 : ℂ) - (s * x) ^ 2 = ((1 - (s * x) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow h,
      ← Real.sqrt_eq_rpow]
    push_cast; ring
  -- the second piece `[1/x, 1]`
  have hd2 : ∀ s ∈ Ioo (1 / x) 1, HasDerivAt (fun s => Real.arcosh (s * x))
      (x / √((s * x) ^ 2 - 1)) s := by
    intro s hs
    have h1 : 1 < s * x := by have := hs.1; rw [div_lt_iff₀ hx0] at this; linarith
    have := (Real.hasDerivAt_arcosh h1).comp s (hasDerivAt_mul_const x)
    rw [show x / √((s * x) ^ 2 - 1) = (√((s * x) ^ 2 - 1))⁻¹ * x by ring]; exact this
  have hc2 : ContinuousOn (fun s => Real.arcosh (s * x)) (Icc (1 / x) 1) := by
    refine Real.continuousOn_arcosh.comp (by fun_prop) fun s hs => ?_
    show 1 ≤ s * x
    have := hs.1; rw [div_le_iff₀ hx0] at this; linarith
  have hi2 : IntervalIntegrable (fun s => x / √((s * x) ^ 2 - 1)) volume (1 / x) 1 :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun s => Real.arcosh (s * x))
      (by rwa [uIcc_of_le hb.2]) (fun s hs => hd2 s (by rwa [min_eq_left hb.2, max_eq_right hb.2]
        at hs)) (fun s _ => by positivity)
  have hv2 : ∫ s in (1 / x)..1, x / √((s * x) ^ 2 - 1) = Real.arcosh x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.2 hc2 hd2 hi2, one_mul,
      one_div_mul_cancel hx0.ne', Real.arcosh_zero, sub_zero]
  have he2 : EqOn f (fun s => (-I) * ((x / √((s * x) ^ 2 - 1) : ℝ))) (Icc (1 / x) 1) := by
    intro s hs
    have h1 : 1 ≤ s * x := by have := hs.1; rw [div_le_iff₀ hx0] at this; linarith
    simp only [hf]
    rcases h1.lt_or_eq with h1 | h1
    · have hpos : 0 < (s * x) ^ 2 - 1 := by nlinarith
      rw [show (1 : ℂ) - (s * x) ^ 2 = ((-((s * x) ^ 2 - 1) : ℝ) : ℂ) by push_cast; ring,
        cpow_half_ofReal_neg hpos]
      have : ((√((s * x) ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
      push_cast
      field_simp
      rw [I_sq]; ring
    · have h0 : (1 : ℂ) - ((s : ℂ) * x) ^ 2 = 0 := by
        rw [← ofReal_mul, ← h1]; norm_num
      rw [h0, zero_cpow (show (1 / 2 : ℂ) ≠ 0 by norm_num), div_zero, ← h1]
      norm_num
  obtain ⟨hf1, hF1⟩ := integral_eq_const_mul_ofReal hb.1 he1 hi1
  obtain ⟨hf2, hF2⟩ := integral_eq_const_mul_ofReal hb.2 he2 hi2
  rw [arcsinD, ← intervalIntegral.integral_add_adjacent_intervals hf1 hf2, hF1, hF2, hv1, hv2]
  push_cast
  ring

/-- `arcsin(iy) = i arcsinh y` (the value of the 4.23.1 integral). -/
theorem arcsinD_I_mul (y : ℝ) : arcsinD (I * y) = I * arcsinhR y := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => Real.arsinh (s * y))
      (y / √(1 + (s * y) ^ 2)) s := by
    intro s _
    have := (Real.hasDerivAt_arsinh (s * y)).comp s (hasDerivAt_mul_const y)
    rw [show y / √(1 + (s * y) ^ 2) = (√(1 + (s * y) ^ 2))⁻¹ * y by ring]; exact this
  have hc : Continuous fun s : ℝ => y / √(1 + (s * y) ^ 2) :=
    continuous_const.div (by fun_prop) fun s => (Real.sqrt_pos.mpr (by positivity)).ne'
  have hv : ∫ s in (0 : ℝ)..1, y / √(1 + (s * y) ^ 2) = Real.arsinh y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
    simp
  have he : EqOn (fun s : ℝ => I * y / (1 - (s * (I * y)) ^ 2) ^ (1 / 2 : ℂ))
      (fun s => I * ((y / √(1 + (s * y) ^ 2) : ℝ))) (Icc 0 1) := by
    intro s _
    simp only
    rw [show (1 : ℂ) - (s * (I * y)) ^ 2 = ((1 + (s * y) ^ 2 : ℝ) : ℂ) by
      push_cast; rw [mul_pow, mul_pow, I_sq]; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity : (0 : ℝ) ≤ 1 + (s * y) ^ 2), ← Real.sqrt_eq_rpow]
    push_cast; ring
  obtain ⟨-, hF⟩ := integral_eq_const_mul_ofReal zero_le_one he (hc.intervalIntegrable _ _)
  rw [arcsinD, hF, hv, arcsinhR_eq]

theorem arcosh_eq_two_mul_arsinh {x : ℝ} (hx : 1 ≤ x) :
    Real.arcosh x = 2 * Real.arsinh √((x - 1) / 2) := by
  set u := Real.arsinh √((x - 1) / 2)
  have hu : 0 ≤ u := Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _)
  have hs : Real.sinh u = √((x - 1) / 2) := Real.sinh_arsinh _
  have hc : Real.cosh (2 * u) = x := by
    rw [Real.cosh_two_mul, Real.cosh_sq, hs, Real.sq_sqrt (by linarith)]
    ring
  rw [← hc, Real.arcosh_cosh (by linarith)]

/-- The half-angle relation `arccos z = 2 arcsin(((1 − z)/2)^{1/2})`, `|1 − z| ≤ 2`. -/
theorem arccosD_eq_two_mul_arcsinD {z : ℂ} (hz : ‖1 - z‖ ≤ 2) :
    arccosD z = 2 * arcsinD (((1 - z) / 2) ^ (1 / 2 : ℂ)) := by
  set w := ((1 - z) / 2) ^ (1 / 2 : ℂ) with hw
  have hw2 : w ^ 2 = (1 - z) / 2 := by
    rw [hw, one_div, cpow_ofNat_inv_pow]
  by_cases hcut : ∃ x : ℝ, 1 ≤ x ∧ z = x
  · obtain ⟨x, hx1, rfl⟩ := hcut
    rcases hx1.lt_or_eq with hx1 | rfl
    · have hq : 0 < (x - 1) / 2 := by linarith
      have hwI : w = I * ((√((x - 1) / 2) : ℝ) : ℂ) := by
        rw [hw, show (1 - (x : ℂ)) / 2 = ((-((x - 1) / 2) : ℝ) : ℂ) by push_cast; ring,
          cpow_half_ofReal_neg hq]
      rw [hwI, arcsinD_I_mul, arcsinhR_eq, dlmf_4_23_16, arcsinD_of_one_lt hx1,
        arcosh_eq_two_mul_arsinh hx1.le]
      push_cast; ring
    · have : w = 0 := by rw [hw]; simp
      rw [this, (dlmf_table_4_23_1_zero).1, ofReal_one, (dlmf_table_4_23_1_one).2.1]; ring
  push Not at hcut
  by_cases hm1 : z = -1
  · subst hm1
    have : w = 1 := by rw [hw]; norm_num
    rw [this, dlmf_table_4_23_1_one.1, dlmf_table_4_23_1_neg_one.2.1]; ring
  -- `z` is off the cuts
  have hre1 : -1 ≤ z.re := by
    have := (re_le_norm (1 - z)).trans hz
    simp at this; linarith
  have hzc : z ∈ arcsinCut := by
    by_cases him : z.im ≠ 0
    · exact Or.inl him
    push Not at him
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt : z.re < 1 := by
      by_contra h; push Not at h; exact hcut z.re h hz'
    have hne : z.re ≠ -1 := fun h => hm1 (by rw [hz', h]; push_cast; ring)
    exact Or.inr (abs_lt.mpr ⟨lt_of_le_of_ne hre1 (Ne.symm hne), hlt⟩)
  have hslit : (1 - z) / 2 ∈ slitPlane := by
    rcases hzc with h | h
    · refine mem_slitPlane_of_im_ne ?_
      simpa using h
    · rw [mem_slitPlane_iff]; left
      have := (abs_lt.mp h).2
      simp; linarith
  have hwre : 0 < w.re := re_cpow_half_pos_of_mem_slitPlane hslit
  have hwn : ‖w‖ ≤ 1 := by
    have h1 : ‖w‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hw2, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      linarith
    nlinarith [norm_nonneg w]
  have hwc : w ∈ arcsinCut := by
    by_cases him : w.im ≠ 0
    · exact Or.inl him
    push Not at him
    right
    have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have h1 : |w.re| ≤ 1 := (abs_re_le_norm w).trans hwn
    refine lt_of_le_of_ne h1 fun h => hm1 ?_
    have : w.re = 1 := by rw [abs_of_pos hwre] at h; exact h
    have : w = 1 := by rw [hwr, this]; simp
    rw [this] at hw2
    linear_combination 2 * hw2
  obtain ⟨-, hvs, hvsin, -⟩ := arcsinD_props hwc
  set v := arcsinD w with hv
  have hvre : 0 < v.re := by
    have h := re_sin v
    rw [hvsin] at h
    by_contra hle
    push Not at hle
    have : Real.sin v.re ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hle (by linarith [hvs.1, Real.pi_pos])
    nlinarith [Real.cosh_pos v.im]
  have hus : (π / 2 - 2 * v : ℂ) ∈ sinStrip := by
    have := hvs.2
    constructor <;> simp <;> linarith
  have husin : sin (π / 2 - 2 * v) = z := by
    rw [sin_pi_div_two_sub, cos_two_mul, cos_sq', hvsin, hw2]
    ring
  obtain ⟨-, hzs, hzsin, -⟩ := arcsinD_props hzc
  have := injOn_sin_sinStrip hzs hus (by rw [hzsin, husin])
  rw [dlmf_4_23_16, this]
  ring

/-- `1·3⋯(2n − 1)/(2·4⋯(2n)) = 1·3⋯(2n − 1)/(2ⁿ n!)`. -/
theorem arcsinCoeff_eq (n : ℕ) :
    arcsinCoeff n = (∏ i ∈ range n, (2 * i + 1 : ℝ)) / (2 ^ n * n.factorial) := by
  induction n with
  | zero => simp [arcsinCoeff]
  | succ n ih =>
    rw [arcsinCoeff_succ, ih, prod_range_succ, Nat.factorial_succ, pow_succ]
    push_cast
    have : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp

/-- The coefficient `1·3·5⋯(2n − 1)/(2^{2n}(2n + 1)n!)` of 4.24.2 (`= 1` for `n = 0`). -/
noncomputable def arccosCoeff (n : ℕ) : ℝ :=
  (∏ i ∈ range n, (2 * i + 1 : ℝ)) / (2 ^ (2 * n) * (2 * n + 1) * n.factorial)

theorem arccosCoeff_eq (n : ℕ) : arccosCoeff n = arcsinCoeff n / (2 ^ n * (2 * n + 1)) := by
  rw [arccosCoeff, arcsinCoeff_eq, pow_mul']
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **DLMF 4.24.2**: `arccos z = (2(1 − z))^{1/2}(1 + ∑_{n≥1} 1·3·5⋯(2n − 1)/(2^{2n}(2n + 1)n!)
(1 − z)ⁿ)`, `|1 − z| ≤ 2` (the `n = 0` term of the sum is the `1`; absolutely convergent). -/
theorem dlmf_4_24_2 {z : ℂ} (hz : ‖1 - z‖ ≤ 2) :
    Summable (fun n : ℕ => (arccosCoeff n : ℂ) * (1 - z) ^ n) ∧
      arccosD z = (2 * (1 - z)) ^ (1 / 2 : ℂ) * ∑' n : ℕ, (arccosCoeff n : ℂ) * (1 - z) ^ n := by
  set w := ((1 - z) / 2) ^ (1 / 2 : ℂ) with hw
  have hw2 : w ^ 2 = (1 - z) / 2 := by rw [hw, one_div, cpow_ofNat_inv_pow]
  have hwn : ‖w‖ ≤ 1 := by
    have h1 : ‖w‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hw2, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      linarith
    nlinarith [norm_nonneg w]
  have h2w : (2 * (1 - z)) ^ (1 / 2 : ℂ) = 2 * w := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show 2 * (1 - z) = ((4 : ℝ) : ℂ) * ((1 - z) / 2) by push_cast; ring,
      ofReal_mul_cpow_half (by norm_num), h4]
    push_cast; rfl
  have hsum : Summable (fun n : ℕ => (arccosCoeff n : ℂ) * (1 - z) ^ n) := by
    refine Summable.of_norm_bounded summable_arcsinCoeff fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, arccosCoeff_eq,
      abs_of_nonneg (div_nonneg (arcsinCoeff_nonneg n) (by positivity))]
    calc arcsinCoeff n / (2 ^ n * (2 * n + 1)) * ‖1 - z‖ ^ n
        ≤ arcsinCoeff n / (2 ^ n * (2 * n + 1)) * 2 ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz n)
            (div_nonneg (arcsinCoeff_nonneg n) (by positivity))
      _ = arcsinCoeff n / (2 * n + 1) := by
          have : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp
  refine ⟨hsum, ?_⟩
  have h := (dlmf_4_24_1 hwn).mul_left 2
  rw [← arccosD_eq_two_mul_arcsinD hz] at h
  rw [h2w, ← tsum_mul_left, ← h.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [arccosCoeff_eq, pow_succ, pow_mul, hw2, div_pow]
  push_cast
  have : (2 * (n : ℂ) + 1) ≠ 0 := by
    rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring]
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  field_simp

/-! ### §4.24(ii) Derivatives -/

/-- **DLMF 4.24.7**: `d/dz arcsin z = (1 − z²)^{−1/2}`. -/
theorem dlmf_4_24_7 {z : ℂ} (hz : z ∈ arcsinCut) :
    HasDerivAt arcsinD ((1 - z ^ 2) ^ (-1 / 2 : ℂ)) z := by
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  exact (hasStrictDerivAt_arcsinD hz).hasDerivAt

/-- **DLMF 4.24.8**: `d/dz arccos z = −(1 − z²)^{−1/2}`. -/
theorem dlmf_4_24_8 {z : ℂ} (hz : z ∈ arcsinCut) :
    HasDerivAt arccosD (-(1 - z ^ 2) ^ (-1 / 2 : ℂ)) z := by
  rw [show arccosD = fun w => (π / 2 : ℂ) - arcsinD w from funext dlmf_4_23_16]
  exact (dlmf_4_24_7 hz).const_sub _

/-- **DLMF 4.24.9**: `d/dz arctan z = 1/(1 + z²)`. -/
theorem dlmf_4_24_9 {z : ℂ} (hz : z ∈ arctanCut) : HasDerivAt arctanD (1 / (1 + z ^ 2)) z := by
  refine (hasDerivAt_arctan_of_mem hz).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_arctanCut.mem_nhds hz] with w hw using arctanD_eq hw

theorem neg_mem_arcsinCut {z : ℂ} (hz : z ∈ arcsinCut) : -z ∈ arcsinCut := by
  rcases hz with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

/-- `z(1 − z⁻²)^{1/2} = (z² − 1)^{1/2}` for `ℜz > 0` off the cut of `arccsc`. -/
theorem mul_cpow_half_one_sub_inv_sq_of_re_pos {z : ℂ} (hz : 0 < z.re) (hc : 1 / z ∈ arcsinCut) :
    z * (1 - (1 / z) ^ 2) ^ (1 / 2 : ℂ) = (z ^ 2 - 1) ^ (1 / 2 : ℂ) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  set w := (1 - (1 / z) ^ 2) ^ (1 / 2 : ℂ) with hw
  set v := (z ^ 2 - 1) ^ (1 / 2 : ℂ) with hv
  have hw2 : w ^ 2 = 1 - (1 / z) ^ 2 := by rw [hw, one_div (2 : ℂ), cpow_ofNat_inv_pow]
  have hv2 : v ^ 2 = z ^ 2 - 1 := by rw [hv, one_div (2 : ℂ), cpow_ofNat_inv_pow]
  have hws : 1 - (1 / z) ^ 2 ∈ slitPlane := by
    simpa using one_sub_sq_mem_slitPlane hc (s := 1) ⟨zero_le_one, le_rfl⟩
  have hwre : 0 < w.re := re_cpow_half_pos_of_mem_slitPlane hws
  -- `z² − 1` is off the negative axis
  have hvs : z ^ 2 - 1 ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_cases hy : z.im = 0
    · left
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hy])
      have h1 : 1 < z.re := by
        by_contra h; push Not at h
        rcases hc with hc | hc
        · apply hc; rw [hzr]; simp
        · rw [hzr, ← ofReal_one, ← ofReal_div, ofReal_re, abs_of_pos (by positivity),
            div_lt_one hz] at hc
          linarith
      simp [sq, hy]; nlinarith
    · right
      have : z.re * z.im ≠ 0 := mul_ne_zero hz.ne' hy
      simp [sq]; intro h; apply this; linarith
  have hvre : 0 < v.re := re_cpow_half_pos_of_mem_slitPlane hvs
  -- `Re(u conj z) > 0` and `Re(v conj z) > 0` for the two square roots of `z² − 1`
  have hu : 0 < (z * w * (starRingEnd ℂ) z).re := by
    rw [mul_right_comm, mul_conj, re_ofReal_mul]
    exact mul_pos (normSq_pos.mpr hz0) hwre
  have hvim : v.re * v.im = z.re * z.im := by
    have := congrArg im hv2
    simp [sq] at this
    linarith
  have hvp : 0 < (v * (starRingEnd ℂ) z).re := by
    simp only [mul_re, conj_re, conj_im]
    have : 0 < v.re * (v.re * z.re + v.im * z.im) := by
      rw [show v.re * (v.re * z.re + v.im * z.im) = z.re * (v.re ^ 2 + z.im ^ 2) by
        linear_combination z.im * hvim]
      exact mul_pos hz (by positivity)
    nlinarith
  have hsq : (z * w - v) * (z * w + v) = 0 := by
    rw [show (z * w - v) * (z * w + v) = z ^ 2 * w ^ 2 - v ^ 2 by ring, hw2, hv2]
    field_simp
    ring
  rcases mul_eq_zero.mp hsq with h | h
  · linear_combination h
  · exfalso
    have : ((z * w + v) * (starRingEnd ℂ) z).re = 0 := by rw [h, zero_mul, zero_re]
    rw [add_mul, add_re] at this
    linarith

/-- `z(1 − z⁻²)^{1/2} = ±(z² − 1)^{1/2}` for `ℜz ≷ 0` (DLMF's remark after 4.24.12). -/
theorem mul_cpow_half_one_sub_inv_sq {z : ℂ} {σ : ℂ} (hc : 1 / z ∈ arcsinCut)
    (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    z * (1 - (1 / z) ^ 2) ^ (1 / 2 : ℂ) = σ * (z ^ 2 - 1) ^ (1 / 2 : ℂ) := by
  rcases hσ with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [one_mul, mul_cpow_half_one_sub_inv_sq_of_re_pos h hc]
  · have h' := mul_cpow_half_one_sub_inv_sq_of_re_pos (z := -z) (by simpa using h)
      (by rw [one_div_neg_eq_neg_one_div]; exact neg_mem_arcsinCut hc)
    rw [neg_sq, one_div_neg_eq_neg_one_div, neg_sq] at h'
    linear_combination -h'

theorem hasDerivAt_arccscD {z : ℂ} (hz0 : z ≠ 0) (hc : 1 / z ∈ arcsinCut) :
    HasDerivAt arccscD (((1 - (1 / z) ^ 2) ^ (1 / 2 : ℂ))⁻¹ * -(z ^ 2)⁻¹) z := by
  have hc' : z⁻¹ ∈ arcsinCut := by rwa [one_div] at hc
  have h := (hasStrictDerivAt_arcsinD hc').hasDerivAt.comp z (hasDerivAt_inv hz0)
  convert h using 1
  · funext w; simp [arccscD, Function.comp, one_div]
  · rw [one_div]

/-- **DLMF 4.24.10**: `d/dz arccsc z = ∓1/(z(z² − 1)^{1/2})`, `ℜz ≷ 0`. -/
theorem dlmf_4_24_10 {z : ℂ} {σ : ℂ} (hc : 1 / z ∈ arcsinCut)
    (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    HasDerivAt arccscD (-σ * (1 / (z * (z ^ 2 - 1) ^ (1 / 2 : ℂ)))) z := by
  have hz0 : z ≠ 0 := fun h => by
    rcases hσ with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] at h' <;> simp at h'
  have hσ2 : σ * σ = 1 := by rcases hσ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hk := mul_cpow_half_one_sub_inv_sq hc hσ
  have hw : (1 - (1 / z) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    have hs := one_sub_sq_mem_slitPlane hc (s := 1) ⟨zero_le_one, le_rfl⟩
    rw [ofReal_one, one_mul] at hs
    have := re_cpow_half_pos_of_mem_slitPlane hs
    exact fun h => by rw [h, zero_re] at this; exact lt_irrefl _ this
  convert hasDerivAt_arccscD hz0 hc using 1
  have hv : (z ^ 2 - 1) ^ (1 / 2 : ℂ) = σ * (z * (1 - (1 / z) ^ 2) ^ (1 / 2 : ℂ)) := by
    rw [hk, ← mul_assoc, hσ2, one_mul]
  rw [hv]
  have hσ0 : σ ≠ 0 := fun h => by rw [h, zero_mul] at hσ2; exact zero_ne_one hσ2
  field_simp

/-- **DLMF 4.24.11**: `d/dz arcsec z = ±1/(z(z² − 1)^{1/2})`, `ℜz ≷ 0`. -/
theorem dlmf_4_24_11 {z : ℂ} {σ : ℂ} (hc : 1 / z ∈ arcsinCut)
    (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    HasDerivAt arcsecD (σ * (1 / (z * (z ^ 2 - 1) ^ (1 / 2 : ℂ)))) z := by
  rw [show arcsecD = fun w => (π / 2 : ℂ) - arccscD w from funext dlmf_4_23_17]
  convert (dlmf_4_24_10 hc hσ).const_sub (π / 2 : ℂ) using 1
  ring

/-- **DLMF 4.24.12**: `d/dz arccot z = −1/(1 + z²)`. -/
theorem dlmf_4_24_12 {z : ℂ} (hz0 : z ≠ 0) (hc : 1 / z ∈ arctanCut) :
    HasDerivAt arccotD (-(1 / (1 + z ^ 2))) z := by
  have hc' : z⁻¹ ∈ arctanCut := by rwa [one_div] at hc
  have h := (dlmf_4_24_9 hc').comp z (hasDerivAt_inv hz0)
  have h1 := one_add_sq_ne_zero_of_mem_arctanCut hc
  have h2 : 1 + z ^ 2 ≠ 0 := by
    intro h; apply h1; field_simp; linear_combination h
  convert h using 1
  · funext w; simp [arccotD, Function.comp, one_div]
  · have h1' : 1 + z⁻¹ ^ 2 ≠ 0 := by rwa [one_div] at h1
    rw [show 1 + z⁻¹ ^ 2 = (1 + z ^ 2) / z ^ 2 by field_simp; ring] at h1' ⊢
    field_simp

/-! ### §4.24(iii) Addition Formulas -/

theorem sign_trig {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (b : ℂ) :
    sin (σ * b) = σ * sin b ∧ cos (σ * b) = cos b ∧ σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> simp [sin_neg, cos_neg]

/-- A second argument with prescribed cosine and a prescribed value of `p · sin`. -/
theorem exists_cos_eq_mul_sin_eq {v p R b₀ : ℂ} (hb₀ : cos b₀ = v) (h : (p * sin b₀) ^ 2 = R ^ 2) :
    ∃ b, cos b = v ∧ p * sin b = R := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · exact ⟨b₀, hb₀, h'⟩
  · exact ⟨-b₀, by rw [cos_neg, hb₀], by rw [sin_neg, mul_neg, h', neg_neg]⟩

/-- **DLMF 4.24.13** (one inclusion): every value of `Arcsin u ± Arcsin v` is a value of
`Arcsin(u(1 − v²)^{1/2} ± v(1 − u²)^{1/2})` for some choice of the square roots. The converse
fails (`dlmf_4_24_13_converse_fails`, erratum). -/
theorem dlmf_4_24_13 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ 1) (hu2 : u ≠ -1)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ r s : ℂ, r ^ 2 = 1 - v ^ 2 → s ^ 2 = 1 - u ^ 2 →
      u * r + σ * v * s ≠ 1 ∧ u * r + σ * v * s ≠ -1) :
    ∀ a ∈ arcsinGen u, ∀ b ∈ arcsinGen v, ∃ r s : ℂ, r ^ 2 = 1 - v ^ 2 ∧ s ^ 2 = 1 - u ^ 2 ∧
      a + σ * b ∈ arcsinGen (u * r + σ * v * s) := by
  intro a ha b hb
  rw [mem_arcsinGen_iff hu1 hu2] at ha
  rw [mem_arcsinGen_iff hv1 hv2] at hb
  have hr : cos b ^ 2 = 1 - v ^ 2 := by rw [cos_sq', hb]
  have hs : cos a ^ 2 = 1 - u ^ 2 := by rw [cos_sq', ha]
  obtain ⟨h1, h2⟩ := hR _ _ hr hs
  refine ⟨cos b, cos a, hr, hs, ?_⟩
  obtain ⟨hsn, hcs, -⟩ := sign_trig hσ b
  rw [mem_arcsinGen_iff h1 h2, sin_add, hsn, hcs, ha, hb]
  ring

theorem real_sin_two_pi_div_three : Real.sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem real_cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

/-- **Erratum to 4.24.13**: with `u = v = ½` and the principal roots `(1 − u²)^{1/2} = √3/2`,
`w = ⅔π` is a value of `Arcsin(u(1 − v²)^{1/2} + v(1 − u²)^{1/2}) = Arcsin(√3/2)` but not a
value of `Arcsin ½ + Arcsin ½`. -/
theorem dlmf_4_24_13_converse_fails :
    ((√3 / 2 : ℝ) : ℂ) ^ 2 = 1 - (1 / 2 : ℂ) ^ 2 ∧
      ((2 * π / 3 : ℝ) : ℂ) ∈ arcsinGen ((1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ) +
        (1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ)) ∧
      ¬ ∃ a ∈ arcsinGen (1 / 2 : ℂ), ∃ b ∈ arcsinGen (1 / 2 : ℂ),
        ((2 * π / 3 : ℝ) : ℂ) = a + b := by
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hc : (1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ) =
      ((√3 / 2 : ℝ) : ℂ) := by ring
  have hlt : √3 / 2 < 1 := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have : √3 < 2 := h4 ▸ Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hpos : 0 < √3 / 2 := by positivity
  refine ⟨by push_cast; rw [div_pow, h3]; norm_num, ?_, ?_⟩
  · rw [hc, mem_arcsinGen_iff (fun h => by
        have := congrArg re h; simp at this; linarith)
      (fun h => by have := congrArg re h; simp at this; linarith), ← ofReal_sin,
      real_sin_two_pi_div_three]
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [mem_arcsinGen_iff (by norm_num) (by norm_num)] at ha hb
    have hb' : b = ((2 * π / 3 : ℝ) : ℂ) - a := by rw [hab]; ring
    rw [hb', sin_sub, ← ofReal_sin, ← ofReal_cos, real_sin_two_pi_div_three,
      real_cos_two_pi_div_three, ha] at hb
    have hca : cos a ^ 2 = 3 / 4 := by rw [cos_sq', ha]; norm_num
    have hlin : ((√3 : ℝ) : ℂ) * cos a = 1 / 2 := by push_cast at hb; linear_combination 2 * hb
    have : ((√3 : ℝ) : ℂ) ^ 2 * cos a ^ 2 = 1 / 4 := by
      rw [← mul_pow, hlin]; norm_num
    rw [h3, hca] at this
    norm_num at this

/-- **DLMF 4.24.14**: `Arccos u ± Arccos v = Arccos(uv ∓ ((1 − u²)(1 − v²))^{1/2})` (as sets of
values, the square root taking either value). -/
theorem dlmf_4_24_14 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ 1) (hu2 : u ≠ -1)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ R : ℂ, R ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) → u * v - σ * R ≠ 1 ∧ u * v - σ * R ≠ -1) :
    {w | ∃ a ∈ arccosGen u, ∃ b ∈ arccosGen v, w = a + σ * b} =
      {w | ∃ R : ℂ, R ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) ∧ w ∈ arccosGen (u * v - σ * R)} := by
  ext w
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_arccosGen_iff hu1 hu2] at ha
    rw [mem_arccosGen_iff hv1 hv2] at hb
    have hR2 : (sin a * sin b) ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) := by
      rw [mul_pow, sin_sq, sin_sq, ha, hb]
    obtain ⟨h1, h2⟩ := hR _ hR2
    refine ⟨_, hR2, ?_⟩
    obtain ⟨hsn, hcs, -⟩ := sign_trig hσ b
    rw [mem_arccosGen_iff h1 h2, cos_add, hsn, hcs, ha, hb]
    ring
  · rintro ⟨R, hR2, hw⟩
    obtain ⟨h1, h2⟩ := hR _ hR2
    rw [mem_arccosGen_iff h1 h2] at hw
    obtain ⟨a₀, ha₀⟩ := cos_surjective u
    obtain ⟨b₀, hb₀⟩ := cos_surjective v
    have hsq : (sin a₀ * sin b₀) ^ 2 = R ^ 2 := by rw [mul_pow, sin_sq, sin_sq, ha₀, hb₀, hR2]
    obtain ⟨b, hb, hab⟩ := exists_cos_eq_mul_sin_eq hb₀ hsq
    obtain ⟨hsn, hcs, -⟩ := sign_trig hσ b
    have hc : cos (a₀ + σ * b) = cos w := by
      rw [cos_add, hsn, hcs, ha₀, hb, hw, ← hab]; ring
    obtain ⟨k, hk | hk⟩ := cos_eq_cos_iff.mp hc
    · refine ⟨a₀ + k * (2 * π), ?_, b, ?_, ?_⟩
      · rw [mem_arccosGen_iff hu1 hu2, cos_add_int_mul_two_pi, ha₀]
      · rwa [mem_arccosGen_iff hv1 hv2]
      · rw [hk]; ring
    · refine ⟨-a₀ + k * (2 * π), ?_, -b, ?_, ?_⟩
      · rw [mem_arccosGen_iff hu1 hu2, cos_add_int_mul_two_pi, cos_neg, ha₀]
      · rw [mem_arccosGen_iff hv1 hv2, cos_neg, hb]
      · rw [hk]; ring

/-- **DLMF 4.24.15**: `Arctan u ± Arctan v = Arctan((u ± v)/(1 ∓ uv))` (as sets of values). -/
theorem dlmf_4_24_15 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hv1 : v ≠ I) (hv2 : v ≠ -I)
    (hd : 1 - σ * u * v ≠ 0) :
    {w | ∃ a ∈ arctanGen u, ∃ b ∈ arctanGen v, w = a + σ * b} =
      arctanGen ((u + σ * v) / (1 - σ * u * v)) := by
  ext w
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_arctanGen_iff] at ha hb ⊢
    obtain ⟨hca, hta⟩ := ha
    obtain ⟨hcb, htb⟩ := hb
    obtain ⟨hsn, hcs, hσ2⟩ := sign_trig hσ b
    have hsa : sin a = u * cos a := by rw [← hta, tan_eq_sin_div_cos]; field_simp
    have hsb : sin b = v * cos b := by rw [← htb, tan_eq_sin_div_cos]; field_simp
    have hc : cos (a + σ * b) = cos a * cos b * (1 - σ * u * v) := by
      rw [cos_add, hsn, hcs, hsa, hsb]; ring
    have hc0 : cos (a + σ * b) ≠ 0 := by
      rw [hc]; exact mul_ne_zero (mul_ne_zero hca hcb) hd
    refine ⟨hc0, ?_⟩
    rw [tan_eq_sin_div_cos, hc, sin_add, hsn, hcs, hsa, hsb]
    field_simp
  · intro hw
    rw [mem_arctanGen_iff] at hw
    obtain ⟨hcw, htw⟩ := hw
    set t := (u + σ * v) / (1 - σ * u * v) with ht
    have ht' : t * (1 - σ * u * v) = u + σ * v := div_mul_cancel₀ _ hd
    set b := arctan v with hbdef
    have hcb : cos b ≠ 0 := cos_arctan_ne_zero v hv1 hv2
    have htb : tan b = v := tan_arctan hv1 hv2
    obtain ⟨hsn, hcs, hσ2⟩ := sign_trig hσ b
    have hsb : sin b = v * cos b := by rw [← htb, tan_eq_sin_div_cos]; field_simp
    have hsw : sin w = t * cos w := by rw [← htw, tan_eq_sin_div_cos]; field_simp
    have hv0 : 1 + v ^ 2 ≠ 0 := by
      intro h
      have : (v - I) * (v + I) = 0 := by rw [show (v - I) * (v + I) = v ^ 2 - I ^ 2 by ring, I_sq]
                                         linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact hv1 (by linear_combination h')
      · exact hv2 (by linear_combination h')
    have hca : cos (w - σ * b) = cos w * cos b * (1 + σ * t * v) := by
      rw [cos_sub, hsn, hcs, hsw, hsb]; ring
    have hk : (1 + σ * t * v) * (1 - σ * u * v) = 1 + v ^ 2 := by
      linear_combination (σ * v) * ht' + v ^ 2 * hσ2
    have hk0 : 1 + σ * t * v ≠ 0 := fun h => hv0 (by rw [← hk, h, zero_mul])
    refine ⟨w - σ * b, ?_, b, ?_, by ring⟩
    · rw [mem_arctanGen_iff]
      have hc0 : cos (w - σ * b) ≠ 0 := by
        rw [hca]; exact mul_ne_zero (mul_ne_zero hcw hcb) hk0
      refine ⟨hc0, ?_⟩
      rw [tan_eq_sin_div_cos, div_eq_iff hc0, hca, sin_sub, hsn, hcs, hsw, hsb]
      linear_combination (cos w * cos b) * ht'
    · exact (mem_arctanGen_iff).mpr ⟨hcb, htb⟩

/-- **DLMF 4.24.16** (first equality): `Arcsin u ± Arccos v = Arcsin(uv ± ((1 − u²)(1 − v²))^{1/2})`
(as sets of values, the square root taking either value). -/
theorem dlmf_4_24_16 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ 1) (hu2 : u ≠ -1)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ R : ℂ, R ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) → u * v + σ * R ≠ 1 ∧ u * v + σ * R ≠ -1) :
    {w | ∃ a ∈ arcsinGen u, ∃ b ∈ arccosGen v, w = a + σ * b} =
      {w | ∃ R : ℂ, R ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) ∧ w ∈ arcsinGen (u * v + σ * R)} := by
  ext w
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_arcsinGen_iff hu1 hu2] at ha
    rw [mem_arccosGen_iff hv1 hv2] at hb
    have hR2 : (cos a * sin b) ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) := by
      rw [mul_pow, cos_sq', ha, sin_sq, hb]
    obtain ⟨h1, h2⟩ := hR _ hR2
    refine ⟨_, hR2, ?_⟩
    obtain ⟨hsn, hcs, -⟩ := sign_trig hσ b
    rw [mem_arcsinGen_iff h1 h2, sin_add, hsn, hcs, ha, hb]
    ring
  · rintro ⟨R, hR2, hw⟩
    obtain ⟨h1, h2⟩ := hR _ hR2
    rw [mem_arcsinGen_iff h1 h2] at hw
    obtain ⟨a₀, ha₀⟩ := sin_surjective u
    obtain ⟨b₀, hb₀⟩ := cos_surjective v
    have hsq : (cos a₀ * sin b₀) ^ 2 = R ^ 2 := by
      rw [mul_pow, cos_sq', ha₀, sin_sq, hb₀, hR2]
    obtain ⟨b, hb, hab⟩ := exists_cos_eq_mul_sin_eq hb₀ hsq
    obtain ⟨hsn, hcs, -⟩ := sign_trig hσ b
    have hs : sin (a₀ + σ * b) = sin w := by
      rw [sin_add, hsn, hcs, ha₀, hb, hw, ← hab]; ring
    obtain ⟨k, hk | hk⟩ := sin_eq_sin_iff.mp hs
    · refine ⟨a₀ + k * (2 * π), ?_, b, ?_, ?_⟩
      · rw [mem_arcsinGen_iff hu1 hu2, sin_add_int_mul_two_pi, ha₀]
      · rwa [mem_arccosGen_iff hv1 hv2]
      · rw [hk]; ring
    · refine ⟨(π - a₀) + k * (2 * π), ?_, -b, ?_, ?_⟩
      · rw [mem_arcsinGen_iff hu1 hu2, sin_add_int_mul_two_pi, sin_pi_sub, ha₀]
      · rw [mem_arccosGen_iff hv1 hv2, cos_neg, hb]
      · rw [hk]; ring

/-- **DLMF 4.24.16** (second equality, one inclusion): every value of `Arcsin u ± Arccos v` is a
value of `Arccos(v(1 − u²)^{1/2} ∓ u(1 − v²)^{1/2})` for some choice of the square roots. The
converse fails (`dlmf_4_24_16_arccos_converse_fails`, erratum). -/
theorem dlmf_4_24_16_arccos {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ 1) (hu2 : u ≠ -1)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ s r : ℂ, s ^ 2 = 1 - u ^ 2 → r ^ 2 = 1 - v ^ 2 →
      v * s - σ * u * r ≠ 1 ∧ v * s - σ * u * r ≠ -1) :
    ∀ a ∈ arcsinGen u, ∀ b ∈ arccosGen v, ∃ s r : ℂ, s ^ 2 = 1 - u ^ 2 ∧ r ^ 2 = 1 - v ^ 2 ∧
      a + σ * b ∈ arccosGen (v * s - σ * u * r) := by
  intro a ha b hb
  rw [mem_arcsinGen_iff hu1 hu2] at ha
  rw [mem_arccosGen_iff hv1 hv2] at hb
  have hs : cos a ^ 2 = 1 - u ^ 2 := by rw [cos_sq', ha]
  have hr : sin b ^ 2 = 1 - v ^ 2 := by rw [sin_sq, hb]
  obtain ⟨h1, h2⟩ := hR _ _ hs hr
  refine ⟨cos a, sin b, hs, hr, ?_⟩
  obtain ⟨hsn, hcs, -⟩ := sign_trig hσ b
  rw [mem_arccosGen_iff h1 h2, cos_add, hsn, hcs, ha, hb]
  ring

/-- **Erratum to 4.24.16**: with `u = v = ½` and the principal roots `√3/2`, `w = −½π` is a value
of `Arccos(v(1 − u²)^{1/2} − u(1 − v²)^{1/2}) = Arccos 0` but not a value of
`Arcsin ½ + Arccos ½`. -/
theorem dlmf_4_24_16_arccos_converse_fails :
    ((√3 / 2 : ℝ) : ℂ) ^ 2 = 1 - (1 / 2 : ℂ) ^ 2 ∧
      (-(π / 2 : ℂ)) ∈ arccosGen ((1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ) -
        (1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ)) ∧
      ¬ ∃ a ∈ arcsinGen (1 / 2 : ℂ), ∃ b ∈ arccosGen (1 / 2 : ℂ), -(π / 2 : ℂ) = a + b := by
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨by push_cast; rw [div_pow, h3]; norm_num, ?_, ?_⟩
  · rw [sub_self, mem_arccosGen_iff (by norm_num) (by norm_num), cos_neg, cos_pi_div_two]
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [mem_arcsinGen_iff (by norm_num) (by norm_num)] at ha
    rw [mem_arccosGen_iff (by norm_num) (by norm_num)] at hb
    have hb' : b = -(a + π / 2) := by linear_combination -hab
    rw [hb', cos_neg, cos_add_pi_div_two, ha] at hb
    norm_num at hb

/-- **DLMF 4.24.17**: `Arctan u ± Arccot v = Arctan((uv ± 1)/(v ∓ u)) = Arccot((v ∓ u)/(uv ± 1))`
(as sets of values). -/
theorem dlmf_4_24_17 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hv0 : v ≠ 0) (hv1 : v ≠ I)
    (hv2 : v ≠ -I) (hd : v - σ * u ≠ 0) :
    {w | ∃ a ∈ arctanGen u, ∃ b ∈ arccotGen v, w = a + σ * b} =
        arctanGen ((u * v + σ) / (v - σ * u)) ∧
      arctanGen ((u * v + σ) / (v - σ * u)) = arccotGen ((v - σ * u) / (u * v + σ)) := by
  have hI : (1 / v) ≠ I := fun h => hv2 (by
    have : v = 1 / I := by rw [← h, one_div_one_div]
    rw [this, one_div, inv_I])
  have hI' : (1 / v) ≠ -I := fun h => hv1 (by
    have : v = 1 / (-I) := by rw [← h, one_div_one_div]
    rw [this, one_div, inv_neg, inv_I, neg_neg])
  have hd' : 1 - σ * u * (1 / v) ≠ 0 := by
    rw [show 1 - σ * u * (1 / v) = (v - σ * u) / v by field_simp]
    exact div_ne_zero hd hv0
  refine ⟨?_, by rw [arccotGen, one_div_div]⟩
  rw [show arccotGen v = arctanGen (1 / v) from rfl, dlmf_4_24_15 hσ hI hI' hd']
  congr 1
  field_simp

end Azurite.DLMF
