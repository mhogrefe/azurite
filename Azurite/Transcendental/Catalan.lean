/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.EulerGamma
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Nat.Choose.Central
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Catalan's constant

`G = ∑_{j≥0} (−1)^j/(2j+1)²` (`catalanConstant`), and the formula used to compute it:

  `G = (π/8) ln(2 + √3) + (3/8) ∑_{k≥0} 1/((2k+1)² C(2k,k))`  (`catalanConstant_eq_log_add_tsum`,
  Ramanujan), and with `ln(2 + √3) = 2√3 ∑_{k≥0} 1/((2k+1) 3^{k+1})`
  (`hasSum_atanhSqrtThreeTerm`, the series of `2 artanh(1/√3)`),

  `G = (√3 π/4) ∑ 1/((2k+1) 3^{k+1}) + (3/8) ∑ 1/((2k+1)² C(2k,k))`  (`catalanConstant_eq`):

two series of positive rational terms with ratios at most `1/3` and `1/4`, with the tails
`tsum_atanhSqrtThreeTerm_sub_sum` (`≤ (1/2) 3^{−N}`) and `tsum_catalanTerm_sub_sum`
(`≤ (4/3) 4^{−N}`).  They are summed by binary splitting in `Azurite/AzNat/HypSplit.lean` and
combined in `Azurite/AzFloat/CatalanBracket.lean`.

The proof of Ramanujan's formula, from first principles:

1. `∫₀¹ ln t/(1 + t²) dt = −G` (`integral_log_div_one_add_sq`): the geometric series with an
   explicit remainder, `|remainder| ≤ ∫₀¹ t^{2N} |ln t| dt = 1/(2N+1)²`.
2. `∫₀^{π/4} ln tan x dx = −G` (`integral_logTan_pi_div_four`): the substitution `t = tan x`.
3. `∫₀^{π/12} ln tan = (2/3) ∫₀^{π/4} ln tan` (`integral_logTan_pi_div_twelve`): integrate the
   triplication formula `ln tan 3x = ln tan x + ln tan(π/3 − x) + ln tan(π/3 + x)`
   (`logTan_three_mul`) over `[0, π/12]` and use `ln tan(π/2 − x) = −ln tan x`.
4. `∫₀^{π/6} φ/sin φ dφ = −(π/6) ln(2 + √3) − 2 ∫₀^{π/12} ln tan` (`integral_inv_sinc_eq_logTan`):
   integration by parts with `d/dφ ln tan(φ/2) = 1/sin φ` and `tan(π/12) = 2 − √3`
   (`logTan_pi_div_twelve`); hence `= (4/3) G − (π/6) ln(2 + √3)` (`integral_inv_sinc`).
5. The generating function `∑ w_k (2 sin φ)^{2k+1} = 2φ/cos φ`, `w_k = 1/((2k+1) C(2k,k))`
   (`hasSum_wallisCoeff_mul_pow`): Wallis' integrals `∫₀^π sin^{2k+1} = 2·4^k w_k`
   (`integral_sin_pow_odd_eq`), a geometric series under the integral, and
   `∫₀^π s sin θ/(1 − s² sin² θ) dθ = 2φ/cos φ` (`integral_sin_div_one_sub`).
6. Dividing by `sin φ`, multiplying by `cos φ` and integrating term by term over `[0, π/6]`
   (`hasSum_catalanTerm_integral`): `∑ 1/((2k+1)² C(2k,k)) = 2 ∫₀^{π/6} φ/sin φ dφ`.

The irrationality of `G` is in `Azurite/Transcendental/CatalanIrrational.lean`.
-/

namespace Azurite

open MeasureTheory Set Filter Topology Finset
open scoped Real Interval

/-- **Catalan's constant** `G = ∑_{j≥0} (−1)^j/(2j+1)² = 0.9159655941…`. -/
noncomputable def catalanConstant : ℝ := ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2

theorem summable_catalanTerm :
    Summable fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  have hs : Summable fun j : ℕ => 1 / (((j + 1 : ℕ) : ℝ)) ^ 2 :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine Summable.of_norm_bounded hs fun j => ?_
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  refine one_div_le_one_div_of_le (by positivity) ?_
  push_cast
  have : (0 : ℝ) ≤ j := j.cast_nonneg
  nlinarith

theorem hasSum_catalanConstant :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) catalanConstant :=
  summable_catalanTerm.hasSum

/-! ### `∫₀¹ ln t/(1 + t²) dt = −G` -/

/-- `1/(1 + t²) = ∑_{k<N} (−1)^k t^{2k} + (−1)^N t^{2N}/(1 + t²)`. -/
theorem inv_one_add_sq_eq_sum (t : ℝ) (N : ℕ) :
    1 / (1 + t ^ 2) = ∑ k ∈ range N, (-1) ^ k * t ^ (2 * k) +
      (-1) ^ N * (t ^ (2 * N) / (1 + t ^ 2)) := by
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, sum_range_succ, add_assoc]
    congr 1
    field_simp
    ring

theorem intervalIntegrable_log_div_one_add_sq (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log t / (1 + t ^ 2)) volume a b := by
  have hc : Continuous fun t : ℝ => 1 / (1 + t ^ 2) :=
    continuous_const.div (by fun_prop) fun t => by positivity
  refine (intervalIntegral.intervalIntegrable_log'.mul_continuousOn hc.continuousOn).congr ?_
  exact fun t _ => by ring

theorem intervalIntegrable_pow_mul_log (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ k * Real.log t) volume a b :=
  intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_pow k).continuousOn

/-- `∫₀¹ t^k ln t dt = −1/(k+1)²`. -/
theorem integral_pow_mul_log_zero_one (k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ k * Real.log t = -(1 / ((k : ℝ) + 1) ^ 2) := by
  rw [integral_pow_mul_log_Icc_zero zero_le_one k]
  simp

/-- **`∫₀¹ ln t/(1 + t²) dt = −G`**, by expanding `1/(1 + t²)` with an explicit remainder. -/
theorem integral_log_div_one_add_sq :
    ∫ t in (0 : ℝ)..1, Real.log t / (1 + t ^ 2) = -catalanConstant := by
  set I := ∫ t in (0 : ℝ)..1, Real.log t / (1 + t ^ 2) with hI
  -- the remainder after `N` terms
  have hrem : ∀ N : ℕ, |I + ∑ k ∈ range N, (-1 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ) ^ 2| ≤
      1 / ((2 * N + 1 : ℕ) : ℝ) ^ 2 := by
    intro N
    have hR : IntervalIntegrable (fun t : ℝ => (-1 : ℝ) ^ N *
        (t ^ (2 * N) * Real.log t * (1 / (1 + t ^ 2)))) volume 0 1 := by
      have hc : Continuous fun t : ℝ => 1 / (1 + t ^ 2) :=
        continuous_const.div (by fun_prop) fun t => by positivity
      exact ((intervalIntegrable_pow_mul_log (2 * N) 0 1).mul_continuousOn
        hc.continuousOn).const_mul _
    have hsplit : I = (∑ k ∈ range N, (-1 : ℝ) ^ k *
        (∫ t in (0 : ℝ)..1, t ^ (2 * k) * Real.log t)) +
        ∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ N * (t ^ (2 * N) * Real.log t * (1 / (1 + t ^ 2))) := by
      have e : ∑ k ∈ range N, (-1 : ℝ) ^ k * ∫ t in (0 : ℝ)..1, t ^ (2 * k) * Real.log t =
          ∫ t in (0 : ℝ)..1, ∑ k ∈ range N, (-1 : ℝ) ^ k * (t ^ (2 * k) * Real.log t) := by
        rw [intervalIntegral.integral_finsetSum fun k _ =>
          (intervalIntegrable_pow_mul_log (2 * k) 0 1).const_mul _]
        exact sum_congr rfl fun k _ => (intervalIntegral.integral_const_mul _ _).symm
      have hS : IntervalIntegrable (fun t : ℝ =>
          ∑ k ∈ range N, (-1 : ℝ) ^ k * (t ^ (2 * k) * Real.log t)) volume 0 1 := by
        have := IntervalIntegrable.sum (range N)
          (f := fun k t => (-1 : ℝ) ^ k * (t ^ (2 * k) * Real.log t)) fun k _ =>
            (intervalIntegrable_pow_mul_log (2 * k) 0 1).const_mul _
        exact this.congr fun t _ => Finset.sum_apply _ _ _
      rw [hI, e, ← intervalIntegral.integral_add hS hR]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have h := inv_one_add_sq_eq_sum t N
      rw [div_eq_mul_one_div]
      conv_lhs => rw [h]
      rw [mul_add, mul_sum]
      congr 1
      · exact sum_congr rfl fun k _ => by ring
      · ring
    have hsum : ∑ k ∈ range N, (-1 : ℝ) ^ k * ∫ t in (0 : ℝ)..1, t ^ (2 * k) * Real.log t
        = -∑ k ∈ range N, (-1 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [integral_pow_mul_log_zero_one]
      push_cast
      ring
    rw [hsplit, hsum, add_comm (-_) _, add_assoc, neg_add_cancel, add_zero]
    -- bound the remainder by `∫₀¹ t^{2N} (−ln t) dt`
    have hb : ‖∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ N * (t ^ (2 * N) * Real.log t * (1 / (1 + t ^ 2)))‖
        ≤ ∫ t in (0 : ℝ)..1, -(t ^ (2 * N) * Real.log t) := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Eventually.of_forall fun t ht => ?_) (intervalIntegrable_pow_mul_log (2 * N) 0 1).neg
      have hl : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
      have hp : 0 ≤ t ^ (2 * N) := pow_nonneg ht.1.le _
      have h1 : 1 / (1 + t ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg t]
      have h0 : 0 ≤ 1 / (1 + t ^ 2) := by positivity
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_mul,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp,
        abs_of_nonpos hl, abs_of_nonneg h0]
      nlinarith [mul_nonneg hp (neg_nonneg.2 hl)]
    rw [intervalIntegral.integral_neg, integral_pow_mul_log_zero_one, neg_neg,
      Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq ?_)
    push_cast
    ring
  -- pass to the limit
  have hlim : Tendsto (fun N : ℕ => I + ∑ k ∈ range N, (-1 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_atTop_mono (fun N : ℕ => (by omega : N ≤ 2 * N + 1)) tendsto_id)
    have h2 : Tendsto (fun N : ℕ => 1 / ((2 * N + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp h1)
    exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hrem N) h2
  have hlim2 := (tendsto_const_nhds (x := I)).add hasSum_catalanConstant.tendsto_sum_nat
  have := tendsto_nhds_unique hlim hlim2
  linarith

/-! ### The log-tangent integral -/

/-- `ln tan x`, written as `ln sin x − ln cos x`. -/
noncomputable def logTan (x : ℝ) : ℝ := Real.log (Real.sin x) - Real.log (Real.cos x)

theorem intervalIntegrable_logTan (a b : ℝ) : IntervalIntegrable logTan volume a b :=
  intervalIntegrable_log_sin.sub intervalIntegrable_log_cos

theorem logTan_pi_div_two_sub (x : ℝ) : logTan (π / 2 - x) = -logTan x := by
  rw [logTan, logTan, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]; ring

theorem logTan_pi_div_four : logTan (π / 4) = 0 := by
  rw [logTan, Real.sin_pi_div_four, Real.cos_pi_div_four, sub_self]

/-- `ln tan x = ln(tan x)` where the sine and the cosine are positive. -/
theorem logTan_eq_log_tan {x : ℝ} (hs : 0 < Real.sin x) (hc : 0 < Real.cos x) :
    logTan x = Real.log (Real.tan x) := by
  rw [logTan, Real.tan_eq_sin_div_cos, Real.log_div hs.ne' hc.ne']

/-- **Triplication**: `ln tan 3x = ln tan x + ln tan(π/3 − x) + ln tan(π/3 + x)`, `0 < x < π/6`
(from `sin 3x = 4 sin x sin(π/3 − x) sin(π/3 + x)` and the same for the cosine). -/
theorem logTan_three_mul {x : ℝ} (h0 : 0 < x) (h1 : x < π / 6) :
    logTan (3 * x) = logTan x + logTan (π / 3 - x) + logTan (π / 3 + x) := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : 0 < Real.sin (π / 3 - x) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc1 : 0 < Real.cos (π / 3 - x) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs2 : 0 < Real.sin (π / 3 + x) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc2 : 0 < Real.cos (π / 3 + x) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsc := Real.sin_sq_add_cos_sq x
  have es : Real.sin (3 * x) = 4 * (Real.sin x * Real.sin (π / 3 - x) * Real.sin (π / 3 + x)) := by
    rw [Real.sin_three_mul, Real.sin_sub, Real.sin_add, Real.sin_pi_div_three,
      Real.cos_pi_div_three]
    linear_combination (-(Real.sin x * Real.cos x ^ 2)) * h3 - 3 * Real.sin x * hsc
  have ec : Real.cos (3 * x) = 4 * (Real.cos x * Real.cos (π / 3 - x) * Real.cos (π / 3 + x)) := by
    rw [Real.cos_three_mul, Real.cos_sub, Real.cos_add, Real.sin_pi_div_three,
      Real.cos_pi_div_three]
    linear_combination (Real.cos x * Real.sin x ^ 2) * h3 + 3 * Real.cos x * hsc
  simp only [logTan]
  rw [es, ec, Real.log_mul four_ne_zero (mul_pos (mul_pos hs hs1) hs2).ne',
    Real.log_mul (mul_pos hs hs1).ne' hs2.ne', Real.log_mul hs.ne' hs1.ne',
    Real.log_mul four_ne_zero (mul_pos (mul_pos hc hc1) hc2).ne',
    Real.log_mul (mul_pos hc hc1).ne' hc2.ne', Real.log_mul hc.ne' hc1.ne']
  ring

/-- `∫₀^{π/12} ln tan = (2/3) ∫₀^{π/4} ln tan`, by integrating the triplication formula. -/
theorem integral_logTan_pi_div_twelve :
    ∫ x in (0 : ℝ)..π / 12, logTan x = 2 / 3 * ∫ x in (0 : ℝ)..π / 4, logTan x := by
  have hπ := Real.pi_pos
  have hI := intervalIntegrable_logTan
  -- the left side of the triplication formula
  have h3 : ∫ x in (0 : ℝ)..π / 12, logTan (3 * x) = 1 / 3 * ∫ x in (0 : ℝ)..π / 4, logTan x := by
    rw [intervalIntegral.integral_comp_mul_left (f := logTan) (by norm_num : (3 : ℝ) ≠ 0),
      mul_zero, show 3 * (π / 12) = π / 4 by ring, smul_eq_mul]
    norm_num
  -- the right side
  have hsub : ∫ x in (0 : ℝ)..π / 12, logTan (π / 3 - x) = ∫ x in π / 4..π / 3, logTan x := by
    rw [intervalIntegral.integral_comp_sub_left (f := logTan), sub_zero,
      show π / 3 - π / 12 = π / 4 by ring]
  have hadd : ∫ x in (0 : ℝ)..π / 12, logTan (π / 3 + x) = ∫ x in π / 3..5 * π / 12, logTan x := by
    rw [intervalIntegral.integral_comp_add_left (f := logTan), add_zero,
      show π / 3 + π / 12 = 5 * π / 12 by ring]
  have hrefl : ∫ x in π / 4..5 * π / 12, logTan x = -∫ x in π / 12..π / 4, logTan x := by
    rw [← intervalIntegral.integral_neg]
    have := intervalIntegral.integral_comp_sub_left (f := logTan) (a := π / 12) (b := π / 4)
      (π / 2)
    rw [show π / 2 - π / 4 = π / 4 by ring, show π / 2 - π / 12 = 5 * π / 12 by ring] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun x _ => logTan_pi_div_two_sub x
  have hcongr : ∫ x in (0 : ℝ)..π / 12, logTan (3 * x) =
      ∫ x in (0 : ℝ)..π / 12, (logTan x + logTan (π / 3 - x) + logTan (π / 3 + x)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le (by positivity)] at hx
    exact logTan_three_mul hx.1 (by linarith [hx.2])
  have i1 : IntervalIntegrable (fun x => logTan (π / 3 - x)) volume 0 (π / 12) := by
    have := (hI (π / 3 - 0) (π / 3 - π / 12)).comp_sub_left (π / 3)
    simpa using this
  have i2 : IntervalIntegrable (fun x => logTan (π / 3 + x)) volume 0 (π / 12) := by
    have := (hI (π / 3 + 0) (π / 3 + π / 12)).comp_add_left (π / 3)
    simpa using this
  rw [intervalIntegral.integral_add ((hI _ _).add i1) i2,
    intervalIntegral.integral_add (hI _ _) i1, hsub, hadd, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _), hrefl, h3] at hcongr
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hI 0 (π / 12))
    (hI (π / 12) (π / 4))
  linarith

/-- `tan` maps `(0, π/4)` onto `(0, 1)`. -/
theorem tan_image_Ioo : Real.tan '' Set.Ioo 0 (π / 4) = Set.Ioo 0 1 := by
  have hπ := Real.pi_pos
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : ∀ y ∈ Set.Icc (0 : ℝ) (π / 4), y ∈ Set.Ioo (-(π / 2)) (π / 2) := fun y hy =>
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    constructor
    · have := Real.strictMonoOn_tan (hmem 0 ⟨le_rfl, by positivity⟩)
        (hmem x ⟨hx.1.le, hx.2.le⟩) hx.1
      rwa [Real.tan_zero] at this
    · have := Real.strictMonoOn_tan (hmem x ⟨hx.1.le, hx.2.le⟩)
        (hmem (π / 4) ⟨by positivity, le_rfl⟩) hx.2
      rwa [Real.tan_pi_div_four] at this
  · intro ht
    refine ⟨Real.arctan t, ⟨?_, ?_⟩, Real.tan_arctan t⟩
    · have := Real.arctan_strictMono ht.1
      rwa [Real.arctan_zero] at this
    · have := Real.arctan_strictMono ht.2
      rwa [Real.arctan_one] at this

/-- **`∫₀^{π/4} ln tan x dx = −G`** (the substitution `t = tan x`). -/
theorem integral_logTan_pi_div_four : ∫ x in (0 : ℝ)..π / 4, logTan x = -catalanConstant := by
  have hπ := Real.pi_pos
  rw [← integral_log_div_one_add_sq, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo, ← tan_image_Ioo]
  have hcos : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 4), 0 < Real.cos x := fun x hx =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsin : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 4), 0 < Real.sin x := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (Real.hasDerivAt_tan (hcos x hx).ne').hasDerivWithinAt)
    (fun x hx y hy h => Real.strictMonoOn_tan.injOn
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩ h)]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hc := hcos x hx
  have h1 : 1 + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    have := Real.sin_sq_add_cos_sq x
    field_simp
    linarith
  rw [logTan_eq_log_tan (hsin x hx) hc, smul_eq_mul, abs_of_pos (by positivity), h1]
  field_simp

/-! ### `∫₀^{π/6} φ/sin φ dφ` -/

/-- `ln tan(π/12) = −ln(2 + √3)`. -/
theorem logTan_pi_div_twelve : logTan (π / 12) = -Real.log (2 + Real.sqrt 3) := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sin (π / 12) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hc : 0 < Real.cos (π / 12) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h2 : Real.sin (π / 6) = 2 * Real.sin (π / 12) * Real.cos (π / 12) := by
    rw [show π / 6 = 2 * (π / 12) by ring, Real.sin_two_mul]
  have h3 : Real.cos (π / 6) = 2 * Real.cos (π / 12) ^ 2 - 1 := by
    rw [show π / 6 = 2 * (π / 12) by ring, Real.cos_two_mul]
  rw [Real.sin_pi_div_six] at h2
  rw [Real.cos_pi_div_six] at h3
  have hr : (0 : ℝ) < 2 + Real.sqrt 3 := by positivity
  have hq : Real.sin (π / 12) / Real.cos (π / 12) = (2 + Real.sqrt 3)⁻¹ := by
    rw [div_eq_iff hc.ne', eq_comm, inv_mul_eq_iff_eq_mul₀ hr.ne']
    linear_combination (-2 * Real.sin (π / 12)) * h3 + 2 * Real.cos (π / 12) * h2
  rw [logTan_eq_log_tan hs hc, Real.tan_eq_sin_div_cos, hq, Real.log_inv]

/-- `φ ln tan(φ/2) → 0` as `φ → 0+`. -/
theorem tendsto_mul_logTan_half :
    Tendsto (fun φ : ℝ => φ * logTan (1 / 2 * φ)) (𝓝[>] 0) (𝓝 0) := by
  have hπ := Real.pi_pos
  -- the cosine part is continuous at `0`
  have hcos : Tendsto (fun φ : ℝ => φ * Real.log (Real.cos (1 / 2 * φ))) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun φ : ℝ => φ * Real.log (Real.cos (1 / 2 * φ))) 0 :=
      continuousAt_id.mul ((Real.continuousAt_log (by simp)).comp
        (by fun_prop : Continuous fun φ : ℝ => Real.cos (1 / 2 * φ)).continuousAt)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  -- the sine part, squeezed between `φ ln(φ/π)` and `0`
  have hlog : Tendsto (fun φ : ℝ => Real.log φ * φ) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
  have hid : Tendsto (fun φ : ℝ => φ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  have hlow : Tendsto (fun φ : ℝ => Real.log φ * φ - φ * Real.log π) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlog.sub (hid.mul_const (Real.log π))
  have hsin : Tendsto (fun φ : ℝ => φ * Real.log (Real.sin (1 / 2 * φ))) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with φ hφ
      have hj := Real.mul_le_sin (x := 1 / 2 * φ) (by linarith [hφ.1])
        (by linarith [hφ.2, Real.pi_gt_three])
      have hpos : 0 < φ / π := div_pos hφ.1 hπ
      have e : φ / π = 2 / π * (1 / 2 * φ) := by field_simp
      have hle : Real.log (φ / π) ≤ Real.log (Real.sin (1 / 2 * φ)) :=
        Real.log_le_log hpos (by rw [e]; exact hj)
      rw [Real.log_div hφ.1.ne' hπ.ne'] at hle
      linarith [mul_le_mul_of_nonneg_left hle hφ.1.le]
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with φ hφ
      have h1 : Real.log (Real.sin (1 / 2 * φ)) ≤ 0 :=
        Real.log_nonpos (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1])
          (by linarith [hφ.2, Real.pi_gt_three])) (Real.sin_le_one _)
      exact mul_nonpos_of_nonneg_of_nonpos hφ.1.le h1
  have := hsin.sub hcos
  rw [sub_zero] at this
  exact this.congr fun φ => by rw [logTan]; ring

/-- `d/dφ [φ ln tan(φ/2)] = ln tan(φ/2) + φ/sin φ` on `(0, π)`. -/
theorem hasDerivAt_mul_logTan_half {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π) :
    HasDerivAt (fun φ : ℝ => φ * logTan (1 / 2 * φ))
      (logTan (1 / 2 * φ) + (Real.sinc φ)⁻¹) φ := by
  have hs : 0 < Real.sin (1 / 2 * φ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < Real.cos (1 / 2 * φ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hh : HasDerivAt (fun φ : ℝ => 1 / 2 * φ) (1 / 2) φ := by
    simpa using (hasDerivAt_id φ).const_mul (1 / 2 : ℝ)
  have hsin : HasDerivAt (fun φ : ℝ => Real.log (Real.sin (1 / 2 * φ)))
      (Real.cos (1 / 2 * φ) * (1 / 2) / Real.sin (1 / 2 * φ)) φ :=
    ((Real.hasDerivAt_sin (1 / 2 * φ)).comp φ hh).log hs.ne'
  have hcos : HasDerivAt (fun φ : ℝ => Real.log (Real.cos (1 / 2 * φ)))
      (-Real.sin (1 / 2 * φ) * (1 / 2) / Real.cos (1 / 2 * φ)) φ :=
    ((Real.hasDerivAt_cos (1 / 2 * φ)).comp φ hh).log hc.ne'
  have key : HasDerivAt (fun φ : ℝ => φ * (Real.log (Real.sin (1 / 2 * φ)) -
      Real.log (Real.cos (1 / 2 * φ)))) _ φ := (hasDerivAt_id' φ).mul (hsin.sub hcos)
  refine key.congr_deriv ?_
  have hsinφ : Real.sin φ = 2 * Real.sin (1 / 2 * φ) * Real.cos (1 / 2 * φ) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  have hsc := Real.sin_sq_add_cos_sq (1 / 2 * φ)
  have e : ∀ S C : ℝ, S ≠ 0 → C ≠ 0 → S ^ 2 + C ^ 2 = 1 →
      C * (1 / 2) / S - -S * (1 / 2) / C = 1 / (2 * S * C) := by
    intro S C hS hC h
    field_simp
    linarith
  rw [Real.sinc_of_ne_zero h0.ne', hsinφ, logTan, e _ _ hs.ne' hc.ne' hsc, inv_div]
  ring

theorem continuousOn_inv_sinc : ContinuousOn (fun φ : ℝ => (Real.sinc φ)⁻¹) (Set.Icc 0 (π / 6)) :=
  Real.continuous_sinc.continuousOn.inv₀ fun φ hφ =>
    (Real.sinc_pos (by rw [abs_of_nonneg hφ.1]; linarith [hφ.2, Real.pi_pos])).ne'

/-- `∫₀^{π/6} φ/sin φ dφ = −(π/6) ln(2 + √3) − 2 ∫₀^{π/12} ln tan` (integration by parts; the
integrand is `1/sinc φ`, continuous at `0`). -/
theorem integral_inv_sinc_eq_logTan :
    ∫ φ in (0 : ℝ)..π / 6, (Real.sinc φ)⁻¹ =
      -(π / 6) * Real.log (2 + Real.sqrt 3) - 2 * ∫ x in (0 : ℝ)..π / 12, logTan x := by
  have hπ := Real.pi_pos
  have h6 : (0 : ℝ) < π / 6 := by positivity
  have hI1 : IntervalIntegrable (fun φ : ℝ => logTan (1 / 2 * φ)) volume 0 (π / 6) := by
    have := (intervalIntegrable_logTan 0 (π / 12)).comp_mul_left (c := 1 / 2)
    rw [zero_div, show π / 12 / (1 / 2) = π / 6 by ring] at this
    exact this
  have hI2 : IntervalIntegrable (fun φ : ℝ => (Real.sinc φ)⁻¹) volume 0 (π / 6) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h6.le]
    exact continuousOn_inv_sinc
  have hb : Tendsto (fun φ : ℝ => φ * logTan (1 / 2 * φ)) (𝓝[<] (π / 6))
      (𝓝 (π / 6 * logTan (1 / 2 * (π / 6)))) :=
    ((hasDerivAt_mul_logTan_half h6 (by linarith)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto h6
    (fun φ hφ => hasDerivAt_mul_logTan_half hφ.1 (by linarith [hφ.2])) (hI1.add hI2)
    tendsto_mul_logTan_half hb
  rw [intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_comp_mul_left (f := logTan) (by norm_num : (1 / 2 : ℝ) ≠ 0),
    mul_zero, show 1 / 2 * (π / 6) = π / 12 by ring, logTan_pi_div_twelve, smul_eq_mul] at hftc
  linarith

/-- **`∫₀^{π/6} φ/sin φ dφ = (4/3) G − (π/6) ln(2 + √3)`**. -/
theorem integral_inv_sinc :
    ∫ φ in (0 : ℝ)..π / 6, (Real.sinc φ)⁻¹ =
      4 / 3 * catalanConstant - π / 6 * Real.log (2 + Real.sqrt 3) := by
  rw [integral_inv_sinc_eq_logTan, integral_logTan_pi_div_twelve, integral_logTan_pi_div_four]
  ring

/-! ### The Wallis coefficients `1/((2k+1) C(2k,k))` and their generating function -/

/-- `w_k = 1/((2k+1) C(2k,k))`. -/
noncomputable def wallisCoeff (k : ℕ) : ℝ :=
  1 / (((2 * k + 1 : ℕ) : ℝ) * (Nat.centralBinom k : ℝ))

theorem centralBinom_cast_pos (k : ℕ) : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
  exact_mod_cast Nat.centralBinom_pos k

theorem wallisCoeff_pos (k : ℕ) : 0 < wallisCoeff k := by
  have := centralBinom_cast_pos k
  unfold wallisCoeff; positivity

/-- `w_{k+1} = w_k (k+1)/(2(2k+3))`. -/
theorem wallisCoeff_succ (k : ℕ) :
    wallisCoeff (k + 1) = wallisCoeff k * (((k : ℝ) + 1) / (2 * (2 * k + 3))) := by
  have hR : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hC := centralBinom_cast_pos k
  have hC1 := centralBinom_cast_pos (k + 1)
  unfold wallisCoeff
  push_cast
  rw [div_mul_div_comm, one_mul, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(2 * (k : ℝ) + 3)) * hR

theorem wallisCoeff_succ_le (k : ℕ) : wallisCoeff (k + 1) ≤ 1 / 4 * wallisCoeff k := by
  rw [wallisCoeff_succ, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (wallisCoeff_pos k).le
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  linarith

theorem wallisCoeff_le (k : ℕ) : wallisCoeff k ≤ (1 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simp [wallisCoeff]
  | succ k ih =>
    calc wallisCoeff (k + 1) ≤ 1 / 4 * wallisCoeff k := wallisCoeff_succ_le k
      _ ≤ 1 / 4 * (1 / 4 : ℝ) ^ k := by gcongr
      _ = (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- Wallis: `∫₀^π sin^{2k+1} θ dθ = 2 · 4^k · w_k`. -/
theorem integral_sin_pow_odd_eq (k : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.sin θ ^ (2 * k + 1) = 2 * 4 ^ k * wallisCoeff k := by
  rw [integral_sin_pow_odd, mul_assoc]
  congr 1
  induction k with
  | zero => simp [wallisCoeff]
  | succ k ih =>
    rw [prod_range_succ, ih, wallisCoeff_succ, pow_succ]
    have : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

/-- Term-by-term integration under a summable uniform bound. -/
theorem hasSum_intervalIntegral_of_summable_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    {M : ℕ → ℝ} (hc : ∀ n, Continuous (F n)) (hM : Summable M)
    (hb : ∀ n, ∀ t ∈ Ι a b, |F n t| ≤ M n) (hlim : ∀ t ∈ Ι a b, HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in a..b, F n t) (∫ t in a..b, f t) :=
  intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => M n)
    (fun n => (hc n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact hb n t ht)
    (Eventually.of_forall fun _ _ => hM) intervalIntegrable_const (Eventually.of_forall hlim)

/-- `∫₀^π s sin θ/(1 − s² sin² θ) dθ = 2φ/cos φ` for `s = sin φ`, `0 < φ < π/2`. -/
theorem integral_sin_div_one_sub {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    ∫ θ in (0 : ℝ)..π,
      Real.sin φ * Real.sin θ / (1 - Real.sin φ ^ 2 * Real.sin θ ^ 2) = 2 * φ / Real.cos φ := by
  set s := Real.sin φ with hs
  set c := Real.cos φ with hc
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have hden : ∀ θ : ℝ, 0 < 1 - s ^ 2 * Real.sin θ ^ 2 := fun θ => by
    have := Real.sin_sq_le_one θ
    nlinarith [sq_nonneg s, sq_nonneg (Real.sin θ), sq_pos_of_pos hc0]
  have hd : ∀ θ : ℝ, HasDerivAt (fun θ => -(Real.arctan (s * Real.cos θ / c) / c))
      (s * Real.sin θ / (1 - s ^ 2 * Real.sin θ ^ 2)) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => s * Real.cos θ / c) (s * -Real.sin θ / c) θ :=
      ((Real.hasDerivAt_cos θ).const_mul s).div_const c
    have h2 := ((Real.hasDerivAt_arctan (s * Real.cos θ / c)).comp θ h1).div_const c |>.neg
    refine h2.congr_deriv ?_
    have hsc' := Real.sin_sq_add_cos_sq θ
    have e : 1 + (s * Real.cos θ / c) ^ 2 = (1 - s ^ 2 * Real.sin θ ^ 2) / c ^ 2 := by
      field_simp
      nlinarith [hsc, hsc']
    have := (hden θ).ne'
    rw [e]
    field_simp
  have hcont : Continuous fun θ => s * Real.sin θ / (1 - s ^ 2 * Real.sin θ ^ 2) :=
    (by fun_prop : Continuous fun θ => s * Real.sin θ).div (by fun_prop) fun θ => (hden θ).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hcont.intervalIntegrable _ _), Real.cos_pi, Real.cos_zero, mul_neg, mul_one, neg_div,
    Real.arctan_neg]
  have ht : Real.arctan (s / c) = φ := by
    rw [hs, hc, ← Real.tan_eq_sin_div_cos, Real.arctan_tan (by linarith) h1]
  rw [ht]
  field_simp
  ring

/-- **The generating function** `∑ w_k (2 sin φ)^{2k+1} = 2φ/cos φ`, `0 < φ < π/2`. -/
theorem hasSum_wallisCoeff_mul_pow {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    HasSum (fun k : ℕ => wallisCoeff k * (2 * Real.sin φ) ^ (2 * k + 1))
      (2 * φ / Real.cos φ) := by
  have hπ := Real.pi_pos
  set s := Real.sin φ with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hs1 : s < 1 := by
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl h1
    rwa [Real.sin_pi_div_two] at this
  have hs2 : s ^ 2 < 1 := by nlinarith
  have h := hasSum_intervalIntegral_of_summable_bound (a := 0) (b := π)
    (F := fun k θ => s * (s * Real.sin θ) ^ (2 * k) * Real.sin θ)
    (f := fun θ => s * Real.sin θ / (1 - s ^ 2 * Real.sin θ ^ 2)) (M := fun k => (s ^ 2) ^ k)
    (fun k => by fun_prop) (summable_geometric_of_lt_one (sq_nonneg s) hs2)
    (fun k θ _ => by
      have hθ := Real.abs_sin_le_one θ
      rw [abs_mul, abs_mul, abs_pow, abs_mul, abs_of_pos hs0, pow_mul, mul_pow]
      have ha2 : |Real.sin θ| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hθ
      have h1 : (s ^ 2 * |Real.sin θ| ^ 2) ^ k ≤ (s ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (sq_nonneg s) ha2) k
      have h2 : 0 ≤ (s ^ 2 * |Real.sin θ| ^ 2) ^ k := by positivity
      calc s * (s ^ 2 * |Real.sin θ| ^ 2) ^ k * |Real.sin θ|
          ≤ 1 * (s ^ 2 * |Real.sin θ| ^ 2) ^ k * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hs1.le h2) hθ (abs_nonneg _) (by positivity)
        _ ≤ (s ^ 2) ^ k := by rw [one_mul, mul_one]; exact h1)
    (fun θ _ => by
      have hr0 : 0 ≤ (s * Real.sin θ) ^ 2 := sq_nonneg _
      have hr1 : (s * Real.sin θ) ^ 2 < 1 := by
        have := Real.sin_sq_le_one θ
        rw [mul_pow]; nlinarith [sq_nonneg s, sq_nonneg (Real.sin θ)]
      have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (s * Real.sin θ)
      have e1 : (fun k : ℕ => s * (s * Real.sin θ) ^ (2 * k) * Real.sin θ) =
          fun k => s * Real.sin θ * ((s * Real.sin θ) ^ 2) ^ k :=
        funext fun k => by rw [pow_mul]; ring
      rw [e1, div_eq_mul_inv, show s ^ 2 * Real.sin θ ^ 2 = (s * Real.sin θ) ^ 2 by ring]
      exact hg)
  rw [integral_sin_div_one_sub h0 h1] at h
  refine h.congr_fun fun k => ?_
  have e : ∀ θ : ℝ, s * (s * Real.sin θ) ^ (2 * k) * Real.sin θ =
      s ^ (2 * k + 1) * Real.sin θ ^ (2 * k + 1) := fun θ => by ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_sin_pow_odd_eq, mul_pow, pow_succ 2 (2 * k),
    pow_mul]
  norm_num
  ring

/-! ### The series `∑ 1/((2k+1)² C(2k,k))` -/

/-- The terms `1/((2k+1)² C(2k,k))` of the accelerated series for Catalan's constant. -/
noncomputable def catalanTerm (k : ℕ) : ℝ :=
  1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2 * (Nat.centralBinom k : ℝ))

theorem catalanTerm_eq (k : ℕ) : catalanTerm k = wallisCoeff k / ((2 * k + 1 : ℕ) : ℝ) := by
  have := centralBinom_cast_pos k
  unfold catalanTerm wallisCoeff
  field_simp

theorem catalanTerm_zero : catalanTerm 0 = 1 := by simp [catalanTerm]

/-- `t_{k+1} = t_k (k+1)(2k+1)/(2(2k+3)²)`. -/
theorem catalanTerm_succ (k : ℕ) :
    catalanTerm (k + 1) =
      catalanTerm k * (((k : ℝ) + 1) * (2 * k + 1) / (2 * (2 * k + 3) ^ 2)) := by
  rw [catalanTerm_eq, catalanTerm_eq, wallisCoeff_succ]
  push_cast
  field_simp
  ring

theorem catalanTerm_pos (k : ℕ) : 0 < catalanTerm k := by
  have := centralBinom_cast_pos k
  unfold catalanTerm; positivity

/-- `∑ 1/((2k+1)² C(2k,k)) = 2 ∫₀^{π/6} φ/sin φ dφ`, by integrating the generating function. -/
theorem hasSum_catalanTerm_integral :
    HasSum catalanTerm (2 * ∫ φ in (0 : ℝ)..π / 6, (Real.sinc φ)⁻¹) := by
  have hπ := Real.pi_pos
  have h6 : (0 : ℝ) < π / 6 := by positivity
  have hsin : ∀ φ ∈ Ι (0 : ℝ) (π / 6), 0 < Real.sin φ ∧ 2 * Real.sin φ ≤ 1 := fun φ hφ => by
    rw [Set.uIoc_of_le h6.le] at hφ
    refine ⟨Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2]), ?_⟩
    have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hφ.1]) (by linarith) hφ.2
    rw [Real.sin_pi_div_six] at this
    linarith
  have h := hasSum_intervalIntegral_of_summable_bound (a := 0) (b := π / 6)
    (F := fun k φ => wallisCoeff k * ((2 * Real.sin φ) ^ (2 * k) * (2 * Real.cos φ)))
    (f := fun φ => 2 * (Real.sinc φ)⁻¹) (M := fun k => 2 * (1 / 4 : ℝ) ^ k)
    (fun k => by fun_prop) ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)
    (fun k φ hφ => by
      obtain ⟨hs0, hs1⟩ := hsin φ hφ
      have hp : (2 * Real.sin φ) ^ (2 * k) ≤ 1 := pow_le_one₀ (by linarith) hs1
      have hp0 : 0 ≤ (2 * Real.sin φ) ^ (2 * k) := by positivity
      have hc := Real.abs_cos_le_one φ
      rw [abs_mul, abs_of_pos (wallisCoeff_pos k), abs_mul, abs_of_nonneg hp0, abs_mul,
        abs_two]
      calc wallisCoeff k * ((2 * Real.sin φ) ^ (2 * k) * (2 * |Real.cos φ|))
          ≤ (1 / 4 : ℝ) ^ k * (1 * (2 * 1)) :=
            mul_le_mul (wallisCoeff_le k) (mul_le_mul hp (by linarith) (by positivity)
              zero_le_one) (by positivity) (by positivity)
        _ = 2 * (1 / 4 : ℝ) ^ k := by ring)
    (fun φ hφ => by
      obtain ⟨hs0, -⟩ := hsin φ hφ
      rw [Set.uIoc_of_le h6.le] at hφ
      have hc0 : 0 < Real.cos φ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
      have hg := (hasSum_wallisCoeff_mul_pow hφ.1 (by linarith [hφ.2])).mul_left
        (Real.cos φ / Real.sin φ)
      have e : Real.cos φ / Real.sin φ * (2 * φ / Real.cos φ) = 2 * (Real.sin φ / φ)⁻¹ := by
        field_simp
      rw [e] at hg
      rw [Real.sinc_of_ne_zero hφ.1.ne']
      refine hg.congr_fun fun k => ?_
      rw [pow_succ]
      field_simp)
  rw [intervalIntegral.integral_const_mul] at h
  refine h.congr_fun fun k => ?_
  have hd : ∀ φ : ℝ, HasDerivAt
      (fun φ => wallisCoeff k * ((2 * Real.sin φ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)))
      (wallisCoeff k * ((2 * Real.sin φ) ^ (2 * k) * (2 * Real.cos φ))) φ := by
    intro φ
    have h1 : HasDerivAt (fun φ => 2 * Real.sin φ) (2 * Real.cos φ) φ :=
      (Real.hasDerivAt_sin φ).const_mul 2
    have h2 := ((h1.pow (2 * k + 1)).div_const ((2 * k + 1 : ℕ) : ℝ)).const_mul (wallisCoeff k)
    refine h2.congr_deriv ?_
    have : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel]
    field_simp
  have hcont : Continuous fun φ : ℝ =>
      wallisCoeff k * ((2 * Real.sin φ) ^ (2 * k) * (2 * Real.cos φ)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun φ _ => hd φ)
    (hcont.intervalIntegrable _ _), Real.sin_pi_div_six, Real.sin_zero, catalanTerm_eq]
  norm_num [div_eq_mul_inv]

/-- `∑ 1/((2k+1)² C(2k,k)) = (8/3) G − (π/3) ln(2 + √3)`. -/
theorem hasSum_catalanTerm :
    HasSum catalanTerm (8 / 3 * catalanConstant - π / 3 * Real.log (2 + Real.sqrt 3)) := by
  have h := hasSum_catalanTerm_integral
  rw [integral_inv_sinc] at h
  convert h using 1
  ring

/-- **Ramanujan's formula** `G = (π/8) ln(2 + √3) + (3/8) ∑_{k≥0} 1/((2k+1)² C(2k,k))`. -/
theorem catalanConstant_eq_log_add_tsum :
    catalanConstant = π / 8 * Real.log (2 + Real.sqrt 3) + 3 / 8 * ∑' k, catalanTerm k := by
  rw [hasSum_catalanTerm.tsum_eq]
  ring

/-! ### `ln(2 + √3)` as a series: `2√3 ∑ 1/((2k+1) 3^{k+1})` -/

/-- The terms `1/((2k+1) 3^{k+1})` of `artanh(1/√3)/√3 = ln(2 + √3)/(2√3)`. -/
noncomputable def atanhSqrtThreeTerm (k : ℕ) : ℝ := 1 / (((2 * k + 1 : ℕ) : ℝ) * 3 ^ (k + 1))

theorem atanhSqrtThreeTerm_pos (k : ℕ) : 0 < atanhSqrtThreeTerm k := by
  unfold atanhSqrtThreeTerm; positivity

/-- `ln(2 + √3) = 2√3 ∑_{k≥0} 1/((2k+1) 3^{k+1})`. -/
theorem hasSum_atanhSqrtThreeTerm :
    HasSum (fun k => 2 * Real.sqrt 3 * atanhSqrtThreeTerm k) (Real.log (2 + Real.sqrt 3)) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 3 := by positivity
  have hr1 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set x : ℝ := (Real.sqrt 3)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hr0
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hr1
  have hxsq : x ^ 2 = 1 / 3 := by rw [hx, inv_pow, h3, one_div]
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := x) (by rw [abs_of_pos hx0]; exact hx1)
  have hval : Real.log (1 + x) - Real.log (1 - x) = Real.log (2 + Real.sqrt 3) := by
    rw [← Real.log_div (by positivity) (by linarith)]
    congr 1
    rw [div_eq_iff (by linarith), hx]
    field_simp
    nlinarith [h3]
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  have hxk : x ^ (2 * k + 1) = Real.sqrt 3 * (1 / 3) ^ (k + 1) := by
    rw [pow_succ, pow_mul, hxsq, pow_succ, hx]
    field_simp
    nlinarith [h3]
  rw [hxk, atanhSqrtThreeTerm]
  push_cast
  rw [one_div_pow]
  field_simp

/-- **Catalan's constant from two rational series**:
`G = (√3 π/4) ∑ 1/((2k+1) 3^{k+1}) + (3/8) ∑ 1/((2k+1)² C(2k,k))`. -/
theorem catalanConstant_eq :
    catalanConstant = Real.sqrt 3 * π / 4 * ∑' k, atanhSqrtThreeTerm k
      + 3 / 8 * ∑' k, catalanTerm k := by
  have h := hasSum_atanhSqrtThreeTerm.tsum_eq
  rw [tsum_mul_left] at h
  rw [catalanConstant_eq_log_add_tsum, ← h]
  ring

/-! ### Tails -/

/-- A nonnegative series with term ratio at most `r < 1`: the tail after `N` terms lies in
`[0, t_N/(1 − r)]`. -/
theorem tail_le_of_ratio {t : ℕ → ℝ} {S r : ℝ} (hS : HasSum t S) (ht : ∀ k, 0 ≤ t k)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hratio : ∀ k, t (k + 1) ≤ r * t k) (N : ℕ) :
    0 ≤ S - ∑ k ∈ range N, t k ∧ S - ∑ k ∈ range N, t k ≤ t N / (1 - r) := by
  have htail := (hasSum_nat_add_iff' N).2 hS
  have hb : ∀ k : ℕ, t (k + N) ≤ t N * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show k + 1 + N = (k + N) + 1 by ring, pow_succ]
      calc t (k + N + 1) ≤ r * t (k + N) := hratio _
        _ ≤ r * (t N * r ^ k) := by gcongr
        _ = t N * (r ^ k * r) := by ring
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (t N)
  rw [← div_eq_mul_inv] at hg
  exact ⟨htail.nonneg fun k => ht _, hasSum_le hb htail hg⟩

theorem catalanTerm_succ_le (k : ℕ) : catalanTerm (k + 1) ≤ 1 / 4 * catalanTerm k := by
  rw [catalanTerm_eq, catalanTerm_eq]
  have h := wallisCoeff_succ_le k
  have hw := (wallisCoeff_pos k).le
  have h1 : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have h2 : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1)
  calc wallisCoeff (k + 1) / ((2 * (k + 1) + 1 : ℕ) : ℝ)
      ≤ 1 / 4 * wallisCoeff k / ((2 * k + 1 : ℕ) : ℝ) :=
        div_le_div₀ (by positivity) h h1 h2
    _ = 1 / 4 * (wallisCoeff k / ((2 * k + 1 : ℕ) : ℝ)) := by ring

theorem catalanTerm_le (k : ℕ) : catalanTerm k ≤ (1 / 4 : ℝ) ^ k := by
  rw [catalanTerm_eq]
  refine (div_le_self (wallisCoeff_pos k).le ?_).trans (wallisCoeff_le k)
  exact_mod_cast (by omega : 1 ≤ 2 * k + 1)

/-- The tail of `∑ 1/((2k+1)² C(2k,k))` after `N` terms lies in `[0, (4/3) 4^{−N}]`. -/
theorem tsum_catalanTerm_sub_sum (N : ℕ) :
    0 ≤ ∑' k, catalanTerm k - ∑ k ∈ range N, catalanTerm k ∧
      ∑' k, catalanTerm k - ∑ k ∈ range N, catalanTerm k ≤ 4 / 3 * (1 / 4 : ℝ) ^ N := by
  have h := tail_le_of_ratio hasSum_catalanTerm.summable.hasSum (fun k => (catalanTerm_pos k).le)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) catalanTerm_succ_le N
  refine ⟨h.1, h.2.trans ?_⟩
  have := catalanTerm_le N
  norm_num
  linarith

theorem atanhSqrtThreeTerm_succ_le (k : ℕ) :
    atanhSqrtThreeTerm (k + 1) ≤ 1 / 3 * atanhSqrtThreeTerm k := by
  unfold atanhSqrtThreeTerm
  rw [pow_succ 3 (k + 1), ← div_eq_mul_one_div, div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have h2 : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1)
  have hp : (0 : ℝ) < 3 ^ (k + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hp.le]

theorem atanhSqrtThreeTerm_le (k : ℕ) : atanhSqrtThreeTerm k ≤ (1 / 3 : ℝ) ^ (k + 1) := by
  unfold atanhSqrtThreeTerm
  rw [one_div_pow]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have h1 : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  exact le_mul_of_one_le_left (by positivity) h1

theorem summable_atanhSqrtThreeTerm : Summable atanhSqrtThreeTerm := by
  have h := hasSum_atanhSqrtThreeTerm.summable
  have h3 : (2 * Real.sqrt 3) ≠ 0 := by positivity
  exact (summable_mul_left_iff h3).1 h

/-- The tail of `∑ 1/((2k+1) 3^{k+1})` after `N` terms lies in `[0, (1/2) 3^{−N}]`. -/
theorem tsum_atanhSqrtThreeTerm_sub_sum (N : ℕ) :
    0 ≤ ∑' k, atanhSqrtThreeTerm k - ∑ k ∈ range N, atanhSqrtThreeTerm k ∧
      ∑' k, atanhSqrtThreeTerm k - ∑ k ∈ range N, atanhSqrtThreeTerm k ≤
        1 / 2 * (1 / 3 : ℝ) ^ N := by
  have h := tail_le_of_ratio summable_atanhSqrtThreeTerm.hasSum
    (fun k => (atanhSqrtThreeTerm_pos k).le) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
    atanhSqrtThreeTerm_succ_le N
  refine ⟨h.1, h.2.trans ?_⟩
  have := atanhSqrtThreeTerm_le N
  rw [pow_succ] at this
  norm_num
  linarith

end Azurite
