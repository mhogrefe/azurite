/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Euler's constant by Sweeney's method

`γ = ∑_{k≥0} (−1)^k n^(k+1)/((k+1)·(k+1)!) − ln n − E₁(n)` for every `n > 0`, with
`E₁(n) = ∫ₙ^∞ e^{−t}/t dt ∈ [0, e^{−n}/n]` (`eulerMascheroni_eq_sweeney`, `expIntegralE1_nonneg`,
`expIntegralE1_le`), and the tail of the series after `N ≥ 4n` terms is at most `2^(4n−N)`
(`abs_tsum_sweeneyTerm_sub_sum_le`).  Choosing `n ≈ 0.7 w` and `N = 4n + w + O(1)` therefore gives
`γ` to `w` bits from an exact rational (summed by binary splitting, `Azurite/AzNat/SweeneySplit`),
one logarithm and two explicit tails (`Azurite/AzFloat/EulerGammaBracket`).

The starting point is Mathlib's `γ = −∫₀^∞ ln t · e^{−t} dt`
(`Real.eulerMascheroniConstant_eq_neg_integral_log`, from `Γ'(1) = −γ`).  The integral is split at
`n`; on `(n, ∞)` integration by parts gives `e^{−n} ln n + E₁(n)`; on `(0, n]` the exponential is
expanded and `∫₀ⁿ tᵏ ln t dt = n^(k+1) ln n/(k+1) − n^(k+1)/(k+1)²` is integrated term by term,
which regroups into `ln n (1 − e^{−n}) − ∑ sweeneyTerm`.
-/

namespace Azurite

open MeasureTheory Set Filter Topology Finset

/-- The terms of Sweeney's series: `(−1)^k n^(k+1)/((k+1)·(k+1)!)`. -/
noncomputable def sweeneyTerm (n : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ k * n ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))

/-- The exponential integral `E₁(n) = ∫ₙ^∞ e^{−t}/t dt`. -/
noncomputable def expIntegralE1 (n : ℝ) : ℝ := ∫ t in Ioi n, Real.exp (-t) / t

/-! ### Integrability -/

theorem integrableOn_log_mul_exp_neg_Ioc {n : ℝ} (hn : 0 ≤ n) :
    IntegrableOn (fun t => Real.log t * Real.exp (-t)) (Ioc 0 n) := by
  have h : IntervalIntegrable (fun t => Real.log t * Real.exp (-t)) volume 0 n :=
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn).mp h

/-- `t e^{−t}` is integrable on `(n, ∞)` for `n ≥ 0`. -/
theorem integrableOn_id_mul_exp_neg_Ioi {n : ℝ} (hn : 0 ≤ n) :
    IntegrableOn (fun t => t * Real.exp (-t)) (Ioi n) := by
  have hG : ∀ x : ℝ, HasDerivAt (fun t => -((t + 1) * Real.exp (-t))) (x * Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    have := (h1.mul h2).neg
    convert this using 1
    ring
  have hlim : Tendsto (fun t => -((t + 1) * Real.exp (-t))) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    simp only [pow_one, pow_zero, one_mul] at h1 h2
    have := (h1.add h2).neg
    simp only [add_zero, neg_zero] at this
    refine this.congr fun t => ?_
    ring
  exact integrableOn_Ioi_deriv_of_nonneg ((hG n).continuousAt.continuousWithinAt)
    (fun x _ => hG x) (fun x hx => mul_nonneg (by linarith [mem_Ioi.mp hx]) (Real.exp_pos _).le)
    hlim

theorem integrableOn_log_mul_exp_neg_Ioi {n : ℝ} (hn : 1 ≤ n) :
    IntegrableOn (fun t => Real.log t * Real.exp (-t)) (Ioi n) := by
  have hg := integrableOn_id_mul_exp_neg_Ioi (by linarith : (0 : ℝ) ≤ n)
  refine Integrable.mono hg.integrable ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    exact (Real.continuousOn_log.mono fun x hx => ne_of_gt (by linarith [mem_Ioi.mp hx])).mul
      (by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).continuousOn
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : 1 ≤ x := by linarith [mem_Ioi.mp hx]
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hl0,
      abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith : (0 : ℝ) < x)]
    exact mul_le_mul_of_nonneg_right (Real.log_le_self (by linarith)) (Real.exp_pos _).le

theorem integrableOn_exp_neg_div_Ioi {n : ℝ} (hn : 0 < n) :
    IntegrableOn (fun t => Real.exp (-t) / t) (Ioi n) := by
  have hg : IntegrableOn (fun t => Real.exp (-t) / n) (Ioi n) :=
    (integrableOn_exp_neg_Ioi (c := n)).div_const n
  refine Integrable.mono hg.integrable ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).continuousOn.div
      continuousOn_id (fun x hx => ne_of_gt (by linarith [mem_Ioi.mp hx]))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx : n < x := mem_Ioi.mp hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (by linarith)),
      abs_of_pos (div_pos (Real.exp_pos _) hn)]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hn hx.le

/-! ### The exponential integral -/

theorem expIntegralE1_nonneg {n : ℝ} (hn : 0 < n) : 0 ≤ expIntegralE1 n :=
  setIntegral_nonneg measurableSet_Ioi fun x hx =>
    div_nonneg (Real.exp_pos _).le (by linarith [mem_Ioi.mp hx])

theorem expIntegralE1_le {n : ℝ} (hn : 0 < n) : expIntegralE1 n ≤ Real.exp (-n) / n := by
  unfold expIntegralE1
  calc ∫ t in Ioi n, Real.exp (-t) / t ≤ ∫ t in Ioi n, Real.exp (-t) / n := by
        refine setIntegral_mono_on (integrableOn_exp_neg_div_Ioi hn)
          ((integrableOn_exp_neg_Ioi (c := n)).div_const n) measurableSet_Ioi fun x hx => ?_
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le hn (mem_Ioi.mp hx).le
    _ = Real.exp (-n) / n := by rw [integral_div, integral_exp_neg_Ioi]

/-! ### The two pieces of `∫₀^∞ ln t · e^{−t} dt` -/

/-- Integration by parts on `(n, ∞)`: `∫ₙ^∞ ln t e^{−t} dt = e^{−n} ln n + E₁(n)`. -/
theorem integral_log_mul_exp_neg_Ioi {n : ℝ} (hn : 1 ≤ n) :
    ∫ t in Ioi n, Real.log t * Real.exp (-t) = Real.exp (-n) * Real.log n + expIntegralE1 n := by
  have hn0 : 0 < n := by linarith
  have hu : ∀ x ∈ Ioi n, HasDerivAt Real.log x⁻¹ x :=
    fun x hx => Real.hasDerivAt_log (ne_of_gt (by linarith [mem_Ioi.mp hx]))
  have hv : ∀ x ∈ Ioi n, HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-x)) x := by
    intro x _
    have := ((hasDerivAt_neg x).exp).neg
    convert this using 1
    ring
  have huv' : IntegrableOn (Real.log * fun t : ℝ => Real.exp (-t)) (Ioi n) :=
    integrableOn_log_mul_exp_neg_Ioi hn
  have hu'v : IntegrableOn ((fun x : ℝ => x⁻¹) * fun t : ℝ => -Real.exp (-t)) (Ioi n) := by
    have := (integrableOn_exp_neg_div_Ioi hn0).neg
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.neg_apply]
    rw [div_eq_mul_inv]; ring
  have h_zero : Tendsto (Real.log * fun t : ℝ => -Real.exp (-t)) (𝓝[>] n)
      (𝓝 (Real.log n * -Real.exp (-n))) := by
    have hc : ContinuousAt (Real.log * fun t : ℝ => -Real.exp (-t)) n :=
      (Real.continuousAt_log hn0.ne').mul
        (by fun_prop : Continuous fun t : ℝ => -Real.exp (-t)).continuousAt
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (Real.log * fun t : ℝ => -Real.exp (-t)) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simp only [pow_one] at h1
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.log_nonneg hx)]
    exact mul_le_mul_of_nonneg_right (Real.log_le_self (by linarith)) (Real.exp_pos _).le
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [h]
  unfold expIntegralE1
  have : ∫ x in Ioi n, x⁻¹ * -Real.exp (-x) = -∫ t in Ioi n, Real.exp (-t) / t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [div_eq_mul_inv]; ring
  rw [this]
  ring

/-- `∫₀ⁿ tᵏ ln t dt = n^(k+1) ln n/(k+1) − n^(k+1)/(k+1)²`. -/
theorem integral_pow_mul_log_Icc_zero {n : ℝ} (hn : 0 ≤ n) (k : ℕ) :
    ∫ t in (0 : ℝ)..n, t ^ k * Real.log t
      = n ^ (k + 1) * Real.log n / (k + 1) - n ^ (k + 1) / ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set F : ℝ → ℝ := fun t => t ^ (k + 1) * Real.log t / (k + 1) - t ^ (k + 1) / ((k : ℝ) + 1) ^ 2
    with hF
  have hcont : Continuous F := by
    have e : (fun t : ℝ => t ^ (k + 1) * Real.log t) = fun t => t ^ k * (t * Real.log t) := by
      funext t; ring
    rw [hF]
    refine ((?_ : Continuous fun t : ℝ => t ^ (k + 1) * Real.log t).div_const _).sub
      ((continuous_pow (k + 1)).div_const _)
    rw [e]
    exact (continuous_pow k).mul Real.continuous_mul_log
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) n, HasDerivAt F (x ^ k * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun t : ℝ => t ^ (k + 1) * Real.log t)
        (((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1) * Real.log x + x ^ (k + 1) * x⁻¹) x :=
      (hasDerivAt_pow (k + 1) x).mul (Real.hasDerivAt_log hx0)
    have h2 : HasDerivAt (fun t : ℝ => t ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1)) x :=
      hasDerivAt_pow (k + 1) x
    have := (h1.div_const ((k : ℝ) + 1)).sub (h2.div_const (((k : ℝ) + 1) ^ 2))
    convert this using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t ^ k * Real.log t) volume 0 n :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_pow k).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hn hcont.continuousOn hderiv hint]
  simp only [hF, Real.log_zero, mul_zero, zero_div, zero_pow (Nat.succ_ne_zero k), sub_zero]

/-- Term-by-term integration of `ln t · e^{−t}` on `[0, n]`. -/
theorem hasSum_integral_log_mul_exp_neg {n : ℝ} (hn : 0 ≤ n) :
    HasSum (fun k : ℕ => ∫ t in (0 : ℝ)..n, Real.log t * ((-t) ^ k / (k.factorial : ℝ)))
      (∫ t in (0 : ℝ)..n, Real.log t * Real.exp (-t)) := by
  have hexp : ∀ x : ℝ, HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
    intro x
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun k t => |Real.log t| * (n ^ k / (k.factorial : ℝ))) ?_ ?_ ?_ ?_ ?_
  · intro k
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine (Real.continuousOn_log.mono ?_).mul
      (by fun_prop : Continuous fun t : ℝ => (-t) ^ k / (k.factorial : ℝ)).continuousOn
    intro x hx
    rw [uIoc_of_le hn] at hx
    exact ne_of_gt hx.1
  · intro k
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hn] at ht
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, Nat.abs_cast, abs_of_pos ht.1]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ ht.1.le ht.2 k) (by positivity)) (abs_nonneg _)
  · exact Filter.Eventually.of_forall fun t _ => (hexp n).summable.mul_left _
  · have e : (fun t => ∑' k : ℕ, |Real.log t| * (n ^ k / (k.factorial : ℝ)))
        = fun t => ‖Real.log t‖ * Real.exp n := by
      funext t
      rw [tsum_mul_left, (hexp n).tsum_eq, Real.norm_eq_abs]
    rw [e]
    exact intervalIntegral.intervalIntegrable_log'.norm.mul_const _
  · exact Filter.Eventually.of_forall fun t _ => (hexp (-t)).mul_left (Real.log t)

/-- The `k`-th integral of the expansion. -/
theorem integral_log_mul_neg_pow_div {n : ℝ} (hn : 0 ≤ n) (k : ℕ) :
    ∫ t in (0 : ℝ)..n, Real.log t * ((-t) ^ k / (k.factorial : ℝ))
      = (-1) ^ k / (k.factorial : ℝ) *
        (n ^ (k + 1) * Real.log n / (k + 1) - n ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
  have e : (fun t : ℝ => Real.log t * ((-t) ^ k / (k.factorial : ℝ)))
      = fun t => (-1) ^ k / (k.factorial : ℝ) * (t ^ k * Real.log t) := by
    funext t; rw [neg_pow]; ring
  rw [e, intervalIntegral.integral_const_mul, integral_pow_mul_log_Icc_zero hn k]

/-- `∑_k (−1)^k n^(k+1)/(k+1)! = 1 − e^{−n}`. -/
theorem hasSum_neg_one_pow_mul_pow_succ_div_factorial (n : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * n ^ (k + 1) / ((k + 1).factorial : ℝ)) (1 - Real.exp (-n)) := by
  have hexp : HasSum (fun k : ℕ => (-n) ^ k / (k.factorial : ℝ)) (Real.exp (-n)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-n)
  have h := (hasSum_nat_add_iff' 1).mpr hexp
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  have h' := h.neg
  have e : (fun k : ℕ => (-1) ^ k * n ^ (k + 1) / ((k + 1).factorial : ℝ))
      = fun k => -((-n) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    funext k
    rw [neg_pow, pow_succ]
    ring
  rw [e, show (1 : ℝ) - Real.exp (-n) = -(Real.exp (-n) - 1) by ring]
  exact h'

/-- `∫₀ⁿ ln t · e^{−t} dt = ln n (1 − e^{−n}) − ∑ sweeneyTerm n k`, and the series converges. -/
theorem hasSum_sweeneyTerm_of_integral {n : ℝ} (hn : 0 < n) :
    HasSum (sweeneyTerm n)
      (Real.log n * (1 - Real.exp (-n)) - ∫ t in (0 : ℝ)..n, Real.log t * Real.exp (-t)) := by
  have hI := hasSum_integral_log_mul_exp_neg hn.le
  have hI' := hI.congr_fun (fun k => (integral_log_mul_neg_pow_div hn.le k).symm)
  have hu := (hasSum_neg_one_pow_mul_pow_succ_div_factorial n).mul_left (Real.log n)
  have h := hu.sub hI'
  refine h.congr_fun fun k => ?_
  unfold sweeneyTerm
  have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hf : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hf0 : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [hk, hf]
  field_simp
  ring

/-- **Sweeney's formula**: `γ = ∑_{k≥0} (−1)^k n^(k+1)/((k+1)(k+1)!) − ln n − E₁(n)` (`n ≥ 1`). -/
theorem eulerMascheroni_eq_sweeney {n : ℝ} (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant = ∑' k, sweeneyTerm n k - Real.log n - expIntegralE1 n := by
  have hn0 : 0 < n := by linarith
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
  have hsplit : ∫ t in Ioi 0, Real.log t * Real.exp (-t)
      = (∫ t in Ioc 0 n, Real.log t * Real.exp (-t))
        + ∫ t in Ioi n, Real.log t * Real.exp (-t) := by
    rw [← Ioc_union_Ioi_eq_Ioi hn0.le]
    refine setIntegral_union ?_ measurableSet_Ioi (integrableOn_log_mul_exp_neg_Ioc hn0.le)
      (integrableOn_log_mul_exp_neg_Ioi hn)
    exact Set.disjoint_left.mpr fun x hx hx' => absurd (mem_Ioi.mp hx') (not_lt.mpr hx.2)
  have hsum := (hasSum_sweeneyTerm_of_integral hn0).tsum_eq
  rw [hsplit, ← intervalIntegral.integral_of_le hn0.le, integral_log_mul_exp_neg_Ioi hn, hsum]
  ring

theorem summable_sweeneyTerm {n : ℝ} (hn : 0 < n) : Summable (sweeneyTerm n) :=
  (hasSum_sweeneyTerm_of_integral hn).summable

/-! ### The tail of the series -/

theorem abs_sweeneyTerm {n : ℝ} (hn : 0 ≤ n) (k : ℕ) :
    |sweeneyTerm n k| = n ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)) := by
  unfold sweeneyTerm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg hn,
    abs_of_pos (by positivity)]

/-- From index `k` with `2n ≤ k + 2` on, each term is at most half the previous one. -/
theorem abs_sweeneyTerm_succ_le {n k : ℕ} (hk : 2 * n ≤ k + 2) :
    |sweeneyTerm (n : ℝ) (k + 1)| ≤ |sweeneyTerm (n : ℝ) k| / 2 := by
  rw [abs_sweeneyTerm (Nat.cast_nonneg n), abs_sweeneyTerm (Nat.cast_nonneg n)]
  have hf : ((k + 1 + 1).factorial : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk2 : (2 * (n : ℝ)) ≤ (k : ℝ) + 2 := by exact_mod_cast hk
  have hpos1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) * ((k + 1 + 1).factorial : ℝ) := by positivity
  rw [div_div, div_le_div_iff₀ hpos2 (by positivity), hf]
  push_cast
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hX : (0 : ℝ) ≤ (n : ℝ) ^ (k + 1) := by positivity
  have hF : (0 : ℝ) ≤ ((k + 1).factorial : ℝ) := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : 2 * (n : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2) := by nlinarith
  have hpk : (n : ℝ) ^ (k + 1 + 1) = (n : ℝ) ^ (k + 1) * n := pow_succ _ _
  rw [hpk]
  nlinarith [mul_nonneg (mul_nonneg hX hF) (sub_nonneg.mpr key)]

theorem abs_sweeneyTerm_add_le {n N : ℕ} (hN : 2 * n ≤ N + 2) (i : ℕ) :
    |sweeneyTerm (n : ℝ) (N + i)| ≤ |sweeneyTerm (n : ℝ) N| * (1 / 2 : ℝ) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := abs_sweeneyTerm_succ_le (n := n) (k := N + i) (by omega)
    rw [show N + (i + 1) = N + i + 1 by ring, pow_succ]
    calc |sweeneyTerm (n : ℝ) (N + i + 1)| ≤ |sweeneyTerm (n : ℝ) (N + i)| / 2 := h
      _ ≤ |sweeneyTerm (n : ℝ) N| * (1 / 2 : ℝ) ^ i / 2 := by gcongr
      _ = |sweeneyTerm (n : ℝ) N| * ((1 / 2 : ℝ) ^ i * (1 / 2)) := by ring

/-- `nᵐ/m! ≤ eⁿ (1/2)^(m − 2n)` for `m ≥ 2n`. -/
theorem pow_div_factorial_le_exp_mul {n m : ℕ} (hm : 2 * n ≤ m) :
    (n : ℝ) ^ m / (m.factorial : ℝ) ≤ Real.exp n * (1 / 2 : ℝ) ^ (m - 2 * n) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, pow_zero, mul_one]
    exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg n) _
  | succ m hm ih =>
    have hf : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hhalf : (n : ℝ) / ((m : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hm1 two_pos]
      have : (2 * (n : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have e : (n : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)
        = (n : ℝ) ^ m / (m.factorial : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) := by
      rw [hf, pow_succ]
      field_simp
    rw [e, show m + 1 - 2 * n = (m - 2 * n) + 1 by omega, pow_succ, ← mul_assoc]
    exact mul_le_mul ih hhalf (by positivity) (by positivity)

theorem exp_nat_le_four_pow (n : ℕ) : Real.exp n ≤ (4 : ℝ) ^ n := by
  have h := Real.exp_one_lt_d9
  have : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [this]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le (by norm_num at h ⊢; linarith) n

/-- The tail of Sweeney's series after `N` terms, `2n ≤ N + 2`, is at most twice the first
omitted term. -/
theorem abs_tsum_sweeneyTerm_sub_sum_le_two_mul {n N : ℕ} (hn : 1 ≤ n) (hN2 : 2 * n ≤ N + 2) :
    |∑' k, sweeneyTerm (n : ℝ) k - ∑ k ∈ range N, sweeneyTerm (n : ℝ) k|
      ≤ 2 * |sweeneyTerm (n : ℝ) N| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum := summable_sweeneyTerm hn0
  -- the tail as a sum over `i`
  rw [← hsum.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hgeo : Summable fun i : ℕ => |sweeneyTerm (n : ℝ) N| * (1 / 2 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hnorm : Summable fun i : ℕ => ‖sweeneyTerm (n : ℝ) (i + N)‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hgeo
    rw [Real.norm_eq_abs, add_comm]
    exact abs_sweeneyTerm_add_le hN2 i
  have h1 : |∑' i, sweeneyTerm (n : ℝ) (i + N)| ≤ ∑' i, |sweeneyTerm (n : ℝ) (i + N)| := by
    have := norm_tsum_le_tsum_norm hnorm
    simpa [Real.norm_eq_abs] using this
  have h2 : ∑' i, |sweeneyTerm (n : ℝ) (i + N)|
      ≤ ∑' i, |sweeneyTerm (n : ℝ) N| * (1 / 2 : ℝ) ^ i := by
    refine Summable.tsum_le_tsum (fun i => ?_) (by simpa [Real.norm_eq_abs] using hnorm) hgeo
    rw [add_comm]
    exact abs_sweeneyTerm_add_le hN2 i
  have h3 : ∑' i, |sweeneyTerm (n : ℝ) N| * (1 / 2 : ℝ) ^ i = |sweeneyTerm (n : ℝ) N| * 2 := by
    rw [tsum_mul_left, tsum_geometric_two]
  linarith

/-- A term is at most `n^(k+1)/(k+1)!`. -/
theorem abs_sweeneyTerm_le {n : ℕ} (N : ℕ) :
    |sweeneyTerm (n : ℝ) N| ≤ (n : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  rw [abs_sweeneyTerm (Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  nlinarith [(Nat.cast_pos.mpr (Nat.factorial_pos (N + 1)) : (0 : ℝ) < ((N + 1).factorial : ℝ))]

/-- The tail of Sweeney's series after `N ≥ 4n` terms is at most `2^(4n − N)`. -/
theorem abs_tsum_sweeneyTerm_sub_sum_le {n N : ℕ} (hn : 1 ≤ n) (hN : 4 * n ≤ N) :
    |∑' k, sweeneyTerm (n : ℝ) k - ∑ k ∈ range N, sweeneyTerm (n : ℝ) k|
      ≤ (1 / 2 : ℝ) ^ (N - 4 * n) := by
  have h := abs_tsum_sweeneyTerm_sub_sum_le_two_mul hn (N := N) (by omega)
  have h4 := abs_sweeneyTerm_le (n := n) N
  have h5 := pow_div_factorial_le_exp_mul (n := n) (m := N + 1) (by omega)
  have h6 := exp_nat_le_four_pow n
  have h7 : (4 : ℝ) ^ n * (1 / 2 : ℝ) ^ (N + 1 - 2 * n) * 2 = (1 / 2 : ℝ) ^ (N - 4 * n) := by
    have e1 : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]; norm_num
    have e2 : N + 1 - 2 * n = (N - 4 * n) + (2 * n + 1) := by omega
    rw [e1, e2, pow_add, one_div_pow (2 : ℝ) (2 * n + 1), pow_succ (2 : ℝ) (2 * n)]
    field_simp
  have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N + 1 - 2 * n) := by positivity
  calc |∑' k, sweeneyTerm (n : ℝ) k - ∑ k ∈ range N, sweeneyTerm (n : ℝ) k|
      ≤ |sweeneyTerm (n : ℝ) N| * 2 := by linarith
    _ ≤ (n : ℝ) ^ (N + 1) / ((N + 1).factorial : ℝ) * 2 := by linarith
    _ ≤ Real.exp n * (1 / 2 : ℝ) ^ (N + 1 - 2 * n) * 2 := by linarith
    _ ≤ (4 : ℝ) ^ n * (1 / 2 : ℝ) ^ (N + 1 - 2 * n) * 2 := by
        have := mul_le_mul_of_nonneg_right h6 hpow0
        linarith
    _ = (1 / 2 : ℝ) ^ (N - 4 * n) := h7

/-- `nᵐ/m! ≤ (e n/m)ᵐ` for `m ≥ 1` (from `mᵐ/m! ≤ eᵐ`). -/
theorem pow_div_factorial_le_exp_mul_div_pow {n : ℝ} (hn : 0 ≤ n) {m : ℕ} (hm : 1 ≤ m) :
    n ^ m / (m.factorial : ℝ) ≤ (Real.exp 1 * n / m) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  rw [← Real.exp_one_pow] at h
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  calc n ^ m / (m.factorial : ℝ) = (n / m) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) := by
        rw [div_pow]; field_simp
    _ ≤ (n / m) ^ m * Real.exp 1 ^ m := by gcongr
    _ = (Real.exp 1 * n / m) ^ m := by rw [← mul_pow]; congr 1; ring

/-- `(10e/37)^37 ≤ 2^(−16)`, via `e < 2.72`. -/
theorem ten_exp_one_div_37_pow_le : ((10 : ℝ) * Real.exp 1 / 37) ^ 37 ≤ (1 / 2 : ℝ) ^ 16 := by
  have he : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  calc ((10 : ℝ) * Real.exp 1 / 37) ^ 37 ≤ ((10 : ℝ) * 2.72 / 37) ^ 37 := by gcongr
    _ ≤ (1 / 2 : ℝ) ^ 16 := by norm_num

/-- **The sharper tail bound**: with `N + 1 = 37 q` terms and `n ≤ 10 q`, the tail of Sweeney's
series is at most `2 · 2^(−16 q)` (the first omitted term is at most `(e n/(N+1))^(N+1) ≤
(10e/37)^(37q)`). -/
theorem abs_tsum_sweeneyTerm_sub_sum_le_of_le {n q : ℕ} (hn : 1 ≤ n) (hq : n ≤ 10 * q) :
    |∑' k, sweeneyTerm (n : ℝ) k - ∑ k ∈ range (37 * q - 1), sweeneyTerm (n : ℝ) k|
      ≤ 2 * (1 / 2 : ℝ) ^ (16 * q) := by
  have hq1 : 1 ≤ q := by omega
  have hN1 : 37 * q - 1 + 1 = 37 * q := by omega
  have h := abs_tsum_sweeneyTerm_sub_sum_le_two_mul hn (N := 37 * q - 1) (by omega)
  refine h.trans ?_
  gcongr
  have h4 := abs_sweeneyTerm_le (n := n) (37 * q - 1)
  have h5 := pow_div_factorial_le_exp_mul_div_pow (Nat.cast_nonneg n) (m := 37 * q - 1 + 1)
    (by omega)
  have h6 : (Real.exp 1 * n / ((37 * q - 1 + 1 : ℕ) : ℝ)) ^ (37 * q - 1 + 1)
      ≤ ((10 : ℝ) * Real.exp 1 / 37) ^ (37 * q - 1 + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    rw [hN1]
    push_cast
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hnq : (n : ℝ) ≤ 10 * q := by exact_mod_cast hq
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.exp_pos 1]
  have h7 : ((10 : ℝ) * Real.exp 1 / 37) ^ (37 * q - 1 + 1) ≤ (1 / 2 : ℝ) ^ (16 * q) := by
    rw [hN1, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by positivity) ten_exp_one_div_37_pow_le q
  rw [hN1] at h4 h5 h6 h7
  linarith

end Azurite
