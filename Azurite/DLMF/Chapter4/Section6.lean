/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2Exp
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# DLMF §4.6: Power series

Formalizations of <https://dlmf.nist.gov/4.6>. The logarithmic series converge only conditionally
on the boundary of their regions, so they are stated as limits of partial sums.

* Key lemma `tendsto_logSeries`: `∑_{n≥1} wⁿ/n = −ln(1 − w)` for `|w| ≤ 1`, `w ≠ 1` (on `|w| = 1`
  by Dirichlet's test for the convergence and Abel's limit theorem for the value), and its odd
  part `tendsto_oddLogSeries`: `2∑ u^{2k+1}/(2k+1) = ln((1 + u)/(1 − u))` for `|u| ≤ 1`,
  `u ≠ ±1`.
* 4.6.1–4.6.6: `dlmf_4_6_1` … `dlmf_4_6_6`, with the DLMF's (closed) regions of validity.
* 4.6.7: the binomial expansion for `|z| < 1` with the binomial coefficients 1.2.6
  (`Ring.choose`, `dlmf_4_6_7`); for `a = 0, 1, 2, …` the series terminates and `z` is unrestricted
  (`dlmf_4_6_7_nat`, a generalization of 1.2.2).
-/

open Complex Set Filter Topology Finset
open scoped Real

namespace Azurite.DLMF

/-! ### The logarithmic series -/

/-- The partial sums `∑_{n<N} w^{n+1}/(n+1)`. -/
noncomputable def logPartial (w : ℂ) (N : ℕ) : ℂ := ∑ n ∈ range N, w ^ (n + 1) / (n + 1)

theorem logPartial_cauchy {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) : CauchySeq (logPartial w) := by
  have hb : ∀ n, ‖∑ i ∈ range n, w ^ (i + 1)‖ ≤ 2 / ‖w - 1‖ := by
    intro n
    have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    have e : ∑ i ∈ range n, w ^ (i + 1) = w * ((w ^ n - 1) / (w - 1)) := by
      rw [← geom_sum_eq hw1, Finset.mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [e, norm_mul, hw, one_mul, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc ‖w ^ n - 1‖ ≤ ‖w ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num
  have hanti : Antitone fun n : ℕ => 1 / ((n : ℝ) + 1) := fun a b h =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
  have := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    tendsto_one_div_add_atTop_nhds_zero_nat hb
  convert this using 1
  funext N
  simp only [logPartial, Complex.real_smul]
  refine sum_congr rfl fun n _ => ?_
  push_cast
  field_simp

/-- `∑_n w^{n+1} rⁿ/(n+1) = −ln(1 − wr)/r` for `0 < r < 1`, `|w| ≤ 1`. -/
theorem hasSum_logSeries_mul {w : ℂ} (hw : ‖w‖ ≤ 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => w ^ (n + 1) / (n + 1) * (r : ℂ) ^ n) (-log (1 - w * r) / r) := by
  have hwr : ‖w * r‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    nlinarith [norm_nonneg w]
  have h := (hasSum_taylorSeries_neg_log' hwr).div_const (r : ℂ)
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  convert h using 1
  funext n
  rw [mul_pow, pow_succ (r : ℂ)]
  field_simp

/-- **Key lemma**: `∑_{n≥1} wⁿ/n = −ln(1 − w)` for `|w| ≤ 1`, `w ≠ 1` (conditionally convergent
on `|w| = 1`). -/
theorem tendsto_logSeries {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    Tendsto (logPartial w) atTop (𝓝 (-log (1 - w))) := by
  rcases lt_or_eq_of_le hw with hlt | heq
  · exact (hasSum_taylorSeries_neg_log' hlt).tendsto_sum_nat
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (logPartial_cauchy heq hw1)
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n : ℕ => w ^ (n + 1) / (n + 1)) hl
  rw [tendsto_map'_iff] at habel
  -- the same limit computed from the closed form
  have hslit : 1 - w ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    rw [sub_re, one_re]
    have hre : w.re ≤ 1 := (re_le_norm w).trans heq.le
    rcases lt_or_eq_of_le hre with h | h
    · linarith
    · exfalso; apply hw1
      have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        rw [← normSq_eq_norm_sq, normSq_apply]; ring
      rw [heq, h] at hn
      have him : w.im = 0 := by nlinarith
      exact Complex.ext (by simpa using h) (by simpa using him)
  have hcont : ContinuousAt (fun r : ℝ => -log (1 - w * r) / r) 1 := by
    have h1 : ContinuousAt (fun r : ℝ => 1 - w * (r : ℂ)) 1 := by fun_prop
    have h2 : ContinuousAt (fun r : ℝ => log (1 - w * (r : ℂ))) 1 :=
      (continuousAt_clog (by simpa using hslit)).comp h1
    exact (h2.neg).div (by fun_prop) (by norm_num)
  have hlim : Tendsto (fun r : ℝ => -log (1 - w * r) / r) (𝓝[<] 1) (𝓝 (-log (1 - w))) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using this
  have heqf : ((fun z : ℂ => ∑' n : ℕ, w ^ (n + 1) / ((n : ℂ) + 1) * z ^ n) ∘ ofReal)
      =ᶠ[𝓝[<] 1] fun r : ℝ => -log (1 - w * r) / r := by
    have : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with r hr
    exact (hasSum_logSeries_mul hw hr.1 hr.2).tsum_eq
  have := tendsto_nhds_unique (habel.congr' heqf) hlim
  rwa [this] at hl

/-- The odd partial sums `∑_{k<K} u^{2k+1}/(2k+1)`. -/
noncomputable def oddLogPartial (u : ℂ) (K : ℕ) : ℂ :=
  ∑ k ∈ range K, u ^ (2 * k + 1) / (2 * k + 1)

theorem logPartial_sub_neg (u : ℂ) (K : ℕ) :
    logPartial u (2 * K) - logPartial (-u) (2 * K) = 2 * oddLogPartial u K := by
  induction K with
  | zero => simp [logPartial, oddLogPartial]
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring]
    simp only [logPartial, oddLogPartial, sum_range_succ] at ih ⊢
    have h1 : (-u) ^ (2 * K + 1) = -u ^ (2 * K + 1) := Odd.neg_pow ⟨K, rfl⟩ u
    have h2 : (-u) ^ (2 * K + 1 + 1) = u ^ (2 * K + 1 + 1) :=
      Even.neg_pow ⟨K + 1, by ring⟩ u
    rw [h1, h2]
    push_cast at ih ⊢
    linear_combination ih

/-- `ln((1 + u)/(1 − u)) = ln(1 + u) − ln(1 − u)` for `|u| ≤ 1`, `u ≠ ±1`. -/
theorem log_div_one_add_sub {u : ℂ} (hu : ‖u‖ ≤ 1) (hu1 : u ≠ 1) (hu2 : u ≠ -1) :
    log ((1 + u) / (1 - u)) = log (1 + u) - log (1 - u) := by
  have hp : 1 + u ≠ 0 := fun h => hu2 (by linear_combination h)
  have hm : 1 - u ≠ 0 := fun h => hu1 (by linear_combination -h)
  have hre : |u.re| ≤ 1 := (abs_re_le_norm u).trans hu
  have h1 : 0 ≤ (1 + u).re := by simp; linarith [(abs_le.mp hre).1]
  have h2 : 0 ≤ (1 - u).re := by simp; linarith [(abs_le.mp hre).2]
  have a1 := abs_arg_le_pi_div_two_iff.mpr h1
  have a2 := abs_arg_le_pi_div_two_iff.mpr h2
  -- one of the two real parts is positive, so one of the arguments is strictly inside
  have hstrict : |arg (1 + u)| < π / 2 ∨ |arg (1 - u)| < π / 2 := by
    by_cases hr : 0 < (1 + u).re
    · exact Or.inl (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
    · refine Or.inr (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_))
      simp at hr ⊢; linarith
  have him : (log (1 + u) - log (1 - u)).im = arg (1 + u) - arg (1 - u) := by
    simp [log_im]
  have hexp : exp (log (1 + u) - log (1 - u)) = (1 + u) / (1 - u) := by
    rw [exp_sub, exp_log hp, exp_log hm]
  rw [← hexp, log_exp]
  · rw [him]
    obtain ⟨b1, b2⟩ := abs_le.mp a1
    obtain ⟨c1, c2⟩ := abs_le.mp a2
    rcases hstrict with h | h <;> obtain ⟨d1, d2⟩ := abs_lt.mp h <;> linarith
  · rw [him]
    obtain ⟨b1, b2⟩ := abs_le.mp a1
    obtain ⟨c1, c2⟩ := abs_le.mp a2
    linarith

/-- `2∑_{k≥0} u^{2k+1}/(2k+1) = ln((1 + u)/(1 − u))` for `|u| ≤ 1`, `u ≠ ±1`. -/
theorem tendsto_oddLogSeries {u : ℂ} (hu : ‖u‖ ≤ 1) (hu1 : u ≠ 1) (hu2 : u ≠ -1) :
    Tendsto (fun K => 2 * oddLogPartial u K) atTop (𝓝 (log ((1 + u) / (1 - u)))) := by
  have hA := (tendsto_logSeries hu hu1).comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have hB := (tendsto_logSeries (w := -u) (by rwa [norm_neg])
    (fun h => hu2 (by linear_combination -h))).comp
    (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have := hA.sub hB
  have e : -log (1 - u) - -log (1 - -u) = log (1 + u) - log (1 - u) := by
    rw [sub_neg_eq_add]; ring_nf
  rw [e] at this
  rw [log_div_one_add_sub hu hu1 hu2]
  refine this.congr fun K => ?_
  simp only [Function.comp, id]
  exact logPartial_sub_neg u K

/-! ### 4.6.1–4.6.6 -/

/-- **DLMF 4.6.1**: `ln(1 + z) = z − ½z² + ⅓z³ − ⋯`, `|z| ≤ 1`, `z ≠ −1`. -/
theorem dlmf_4_6_1 {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ -1) :
    Tendsto (fun N => ∑ n ∈ range N, (-1) ^ n * z ^ (n + 1) / (n + 1)) atTop
      (𝓝 (log (1 + z))) := by
  have h := (tendsto_logSeries (w := -z) (by rwa [norm_neg])
    (fun h => hz1 (by linear_combination -h))).neg
  rw [sub_neg_eq_add, neg_neg] at h
  refine h.congr fun N => ?_
  simp only [logPartial, ← sum_neg_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [neg_pow, pow_succ (-1 : ℂ)]
  ring

/-- **DLMF 4.6.2**: `ln z = ∑ (1/n)((z − 1)/z)ⁿ`, `Re z ≥ ½`. -/
theorem dlmf_4_6_2 {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    Tendsto (fun N => ∑ n ∈ range N, ((z - 1) / z) ^ (n + 1) / (n + 1)) atTop (𝓝 (log z)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; norm_num at hz
  have hw : ‖(z - 1) / z‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hz0)]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
      ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  have hw1 : (z - 1) / z ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hz0]; intro h
    exact absurd (by linear_combination h : (-1 : ℂ) = 0) (by norm_num)
  have h := tendsto_logSeries hw hw1
  have e : 1 - (z - 1) / z = z⁻¹ := by field_simp; ring
  rw [e, log_inv, neg_neg] at h
  · exact h
  · intro ha
    have := (arg_eq_pi_iff.mp ha).1
    linarith

/-- **DLMF 4.6.3**: `ln z = (z − 1) − ½(z − 1)² + ⅓(z − 1)³ − ⋯`, `|z − 1| ≤ 1`, `z ≠ 0`. -/
theorem dlmf_4_6_3 {z : ℂ} (hz : ‖z - 1‖ ≤ 1) (hz0 : z ≠ 0) :
    Tendsto (fun N => ∑ n ∈ range N, (-1) ^ n * (z - 1) ^ (n + 1) / (n + 1)) atTop
      (𝓝 (log z)) := by
  have := dlmf_4_6_1 hz (fun h => hz0 (by linear_combination h))
  rwa [add_sub_cancel] at this

/-- **DLMF 4.6.4**: `ln z = 2((z−1)/(z+1) + ⅓((z−1)/(z+1))³ + ⋯)`, `Re z ≥ 0`, `z ≠ 0`. -/
theorem dlmf_4_6_4 {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun K => 2 * oddLogPartial ((z - 1) / (z + 1)) K) atTop (𝓝 (log z)) := by
  have hp : z + 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hu : ‖(z - 1) / (z + 1)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hp)]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
      ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  have hu1 : (z - 1) / (z + 1) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact absurd (by linear_combination h / 2 : (-1 : ℂ) = 0) (by norm_num)
  have hu2 : (z - 1) / (z + 1) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h; apply hz0; linear_combination h / 2
  have h := tendsto_oddLogSeries hu hu1 hu2
  have e : (1 + (z - 1) / (z + 1)) / (1 - (z - 1) / (z + 1)) = z := by field_simp; ring
  rwa [e] at h

/-- **DLMF 4.6.5**: `ln((z + 1)/(z − 1)) = 2(1/z + 1/(3z³) + 1/(5z⁵) + ⋯)`, `|z| ≥ 1`,
`z ≠ ±1`. -/
theorem dlmf_4_6_5 {z : ℂ} (hz : 1 ≤ ‖z‖) (hz1 : z ≠ 1) (hz2 : z ≠ -1) :
    Tendsto (fun K => 2 * ∑ k ∈ range K, 1 / ((2 * k + 1) * z ^ (2 * k + 1))) atTop
      (𝓝 (log ((z + 1) / (z - 1)))) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; norm_num at hz
  have hu : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz
  have hu1 : z⁻¹ ≠ 1 := fun h => hz1 (by rw [← inv_inv z, h, inv_one])
  have hu2 : z⁻¹ ≠ -1 := fun h => hz2 (by rw [← inv_inv z, h, inv_neg, inv_one])
  have h := tendsto_oddLogSeries hu hu1 hu2
  have e : (1 + z⁻¹) / (1 - z⁻¹) = (z + 1) / (z - 1) := by
    have : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    field_simp
  rw [e] at h
  refine h.congr fun K => ?_
  simp only [oddLogPartial]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [inv_pow]
  field_simp

/-- **DLMF 4.6.6**: `ln(z + a) = ln a + 2((z/(2a+z)) + ⅓(z/(2a+z))³ + ⋯)`, `a > 0`, `Re z ≥ −a`,
`z ≠ −a`. -/
theorem dlmf_4_6_6 {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : -a ≤ z.re) (hza : z ≠ -a) :
    Tendsto (fun K => (Real.log a : ℂ) + 2 * oddLogPartial (z / (2 * a + z)) K) atTop
      (𝓝 (log (z + a))) := by
  have hd : (2 * a + z : ℂ) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hu : ‖z / (2 * a + z)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hd)]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
      ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  have hu1 : z / (2 * a + z) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hd]; intro h
    have := congrArg re h; simp at this; linarith
  have hu2 : z / (2 * a + z) ≠ -1 := by
    rw [Ne, div_eq_iff hd]; intro h; apply hza; linear_combination h / 2
  have h := (tendsto_oddLogSeries hu hu1 hu2).const_add (Real.log a : ℂ)
  have hza' : (z + a : ℂ) ≠ 0 := fun h => hza (by linear_combination h)
  have e : (1 + z / (2 * a + z)) / (1 - z / (2 * a + z)) = (z + a) * ((a⁻¹ : ℝ) : ℂ) := by
    have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp; ring
  rw [e, log_mul_ofReal _ (inv_pos.mpr ha) _ hza', Real.log_inv] at h
  convert h using 2
  push_cast; ring

/-! ### 4.6.7 Binomial expansion -/

/-- **DLMF 4.6.7**: `(1 + z)^a = ∑ C(a, n) zⁿ` (binomial coefficients 1.2.6) for any complex `a`
and `|z| < 1`. -/
theorem dlmf_4_6_7 (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * z ^ n) ((1 + z) ^ a) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hz
  have h := (one_add_cpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum hz'
  rw [zero_add] at h
  convert h using 1
  funext n
  rw [binomialSeries_apply]
  simp [smul_eq_mul]

/-- **DLMF §4.6(ii)**: "If `a = 0, 1, 2, …`, then the series terminates and `z` is unrestricted"
(the binomial theorem 1.2.2). -/
theorem dlmf_4_6_7_nat (m : ℕ) (z : ℂ) :
    (∀ n, m < n → Ring.choose (m : ℂ) n = 0) ∧
      HasSum (fun n : ℕ => Ring.choose (m : ℂ) n * z ^ n) ((1 + z) ^ (m : ℂ)) := by
  have hz : ∀ n, m < n → Ring.choose (m : ℂ) n = 0 := fun n h => by
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
  refine ⟨hz, ?_⟩
  have hs : HasSum (fun n : ℕ => Ring.choose (m : ℂ) n * z ^ n)
      (∑ n ∈ range (m + 1), Ring.choose (m : ℂ) n * z ^ n) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by
      rw [Finset.mem_range, not_lt] at hn; rw [hz n (by omega), zero_mul]
  convert hs using 1
  rw [cpow_natCast, add_comm, add_pow]
  refine sum_congr rfl fun n _ => ?_
  rw [Ring.choose_natCast, one_pow, mul_one, mul_comm]

end Azurite.DLMF
