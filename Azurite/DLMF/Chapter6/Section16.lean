/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section15

/-!
# DLMF §6.16(i): the Gibbs phenomenon

Formalizations of <https://dlmf.nist.gov/6.16.i>.

## Main results

* `gibbsS`, `gibbsR`, `dlmf_6_16_2`: `S_n(x) = ½ ∫_0^x sin(2nt)/sin t dt = ½ Si(2nx) + R_n(x)`
  (6.16.2, 6.16.3; `∑_{k<n} cos((2k+1)t) = sin(2nt)/(2 sin t)`, `sum_cos_odd`).
* `dlmf_6_16_4`: `R_n(x) = O(1/n)` uniformly on `[−a, a]` for every `a < π`, by integration by
  parts with `h(t) = 1/sin t − 1/t` (`|h′| ≤ 4` on `(0, 1]` by Taylor bounds, `gibbsH_small`).
* `dlmf_6_16_4_endpoint` (**erratum**): DLMF claims uniformity on `[−π, π]`, but
  `R_n(π) = −½ Si(2nπ) → −π/4` (as `S_n(π) = 0`); `h` is unbounded at `±π`.
* `dlmf_6_16_1`: the partial sums tend to `π/4`, `0`, `−π/4` (6.16.1; the series is only
  conditionally convergent, so it is stated through `S_n`).
* `dlmf_6_16_gibbs`, `dlmf_6_16_not_uniform`: `S_n(π/(2n)) → ½ Si(π) > π/4` (overshoot) and
  `S_n(π/n) → ½ Si(2π) < π/4` (undershoot); the convergence on `(0, π)` is not uniform.
  The decimals (`1.1789…`, 18%, 10%) and Figure 6.16.1 are not formalized.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat Interval

namespace Azurite.DLMF

/-! ### 6.16.2, 6.16.3 -/

/-- **DLMF 6.16.2**: the partial sum `S_n(x) = ∑_{k<n} sin((2k+1)x)/(2k+1)` of 6.16.1. -/
noncomputable def gibbsS (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.sin ((2 * k + 1) * x) / (2 * k + 1)

/-- **DLMF 6.16.3**: `R_n(x) = ½ ∫_0^x (1/sin t − 1/t) sin(2nt) dt`. -/
noncomputable def gibbsR (n : ℕ) (x : ℝ) : ℝ :=
  1 / 2 * ∫ t in (0 : ℝ)..x, (1 / Real.sin t - 1 / t) * Real.sin (2 * n * t)

/-- `∑_{k<n} cos((2k+1)t) = sin(2nt)/(2 sin t)` for `sin t ≠ 0`. -/
theorem sum_cos_odd (n : ℕ) {t : ℝ} (ht : Real.sin t ≠ 0) :
    ∑ k ∈ Finset.range n, Real.cos ((2 * k + 1) * t) = Real.sin (2 * n * t) / (2 * Real.sin t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : Real.sin (2 * ((n + 1 : ℕ) : ℝ) * t) = Real.sin ((2 * n + 1) * t + t) := by
      push_cast; ring_nf
    have h2 : Real.sin (2 * (n : ℝ) * t) = Real.sin ((2 * n + 1) * t - t) := by ring_nf
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    field_simp
    ring

theorem hasDerivAt_gibbsS (n : ℕ) (x : ℝ) :
    HasDerivAt (gibbsS n) (∑ k ∈ Finset.range n, Real.cos ((2 * k + 1) * x)) x := by
  unfold gibbsS
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((Real.hasDerivAt_sin _).comp x
    ((hasDerivAt_id x).const_mul (2 * (k : ℝ) + 1))).div_const (2 * (k : ℝ) + 1)
  refine h.congr_deriv ?_
  have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  simp only [mul_one, id]
  field_simp

theorem gibbsS_zero_left (x : ℝ) : gibbsS 0 x = 0 := by simp [gibbsS]

theorem gibbsS_at_zero (n : ℕ) : gibbsS n 0 = 0 := by simp [gibbsS]

/-- `sin t ≠ 0` almost everywhere. -/
theorem ae_sin_ne_zero : ∀ᵐ t : ℝ, Real.sin t ≠ 0 := by
  have hc : {t : ℝ | Real.sin t = 0}.Countable := by
    refine (Set.countable_range fun k : ℤ => (k : ℝ) * π).mono fun t ht => ?_
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 ht
    exact ⟨k, hk⟩
  have := hc.measure_zero volume
  rw [ae_iff]
  simpa using this

/-- **DLMF 6.16.2** (first equality): `S_n(x) = ½ ∫_0^x sin(2nt)/sin t dt`. -/
theorem dlmf_6_16_2_integral (n : ℕ) (x : ℝ) :
    gibbsS n x = 1 / 2 * ∫ t in (0 : ℝ)..x, Real.sin (2 * n * t) / Real.sin t := by
  have hc : Continuous fun t => ∑ k ∈ Finset.range n, Real.cos ((2 * k + 1) * t) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun t _ => hasDerivAt_gibbsS n t) (hc.intervalIntegrable _ _)
  rw [gibbsS_at_zero, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_sin_ne_zero] with t ht _
  rw [sum_cos_odd n ht]
  field_simp

/-- The real sine integral as an integral of `sinc`: `Si(y) = ∫_0^y sin u/u du`. -/
theorem SiR_eq_integral (y : ℝ) : SiR y = ∫ u in (0 : ℝ)..y, sincR u := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_SiR u)
    (continuous_sincR.intervalIntegrable _ _), SiR_zero, sub_zero]

/-- `∫_0^x sin(2nt)/t dt = Si(2nx)`. -/
theorem integral_sin_div_eq_SiR (n : ℕ) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, Real.sin (2 * n * t) / t = SiR (2 * n * x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [SiR_zero]
  have hn' : (0 : ℝ) < 2 * n := by positivity
  have e : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) x →
      Real.sin (2 * n * t) / t = (2 * n) * sincR (2 * n * t) := by
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [h0] with t ht _
    rw [sincR_of_ne (mul_ne_zero hn'.ne' ht)]
    field_simp
  rw [intervalIntegral.integral_congr_ae e, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun u => sincR u) hn'.ne', mul_zero,
    ← SiR_eq_integral, smul_eq_mul]
  field_simp

theorem intervalIntegrable_sin_div_sin (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.sin (2 * n * t) / Real.sin t) volume a b := by
  have hc : Continuous fun t => 2 * ∑ k ∈ Finset.range n, Real.cos ((2 * k + 1) * t) := by
    fun_prop
  refine (hc.intervalIntegrable a b).congr_ae ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
  filter_upwards [ae_sin_ne_zero] with t ht _
  rw [sum_cos_odd n ht]
  field_simp

theorem intervalIntegrable_sin_two_mul_div (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.sin (2 * n * t) / t) volume a b := by
  have hc : Continuous fun t => (2 * n) * sincR (2 * n * t) := by
    exact continuous_const.mul (continuous_sincR.comp (continuous_const.mul continuous_id))
  refine (hc.intervalIntegrable a b).congr_ae ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [ae_iff]; simp [measure_singleton]
  filter_upwards [h0] with t ht _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < 2 * n := by positivity
  rw [sincR_of_ne (mul_ne_zero hn'.ne' ht)]
  field_simp

/-- **DLMF 6.16.2**: `S_n(x) = ½ ∫_0^x sin(2nt)/sin t dt = ½ Si(2nx) + R_n(x)`. -/
theorem dlmf_6_16_2 (n : ℕ) (x : ℝ) :
    gibbsS n x = 1 / 2 * ∫ t in (0 : ℝ)..x, Real.sin (2 * n * t) / Real.sin t ∧
      1 / 2 * ∫ t in (0 : ℝ)..x, Real.sin (2 * n * t) / Real.sin t =
        1 / 2 * SiR (2 * n * x) + gibbsR n x := by
  refine ⟨dlmf_6_16_2_integral n x, ?_⟩
  rw [gibbsR, ← integral_sin_div_eq_SiR, ← mul_add, ← intervalIntegral.integral_add
    (intervalIntegrable_sin_two_mul_div n 0 x) ((intervalIntegrable_sin_div_sin n 0 x).sub
      (intervalIntegrable_sin_two_mul_div n 0 x) |>.congr ?_)]
  · congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  · exact fun t _ => by ring

/-! ### 6.16.4 -/

/-- `h(t) = 1/sin t − 1/t`, the factor in 6.16.3 (with value `0` at `t = 0`). -/
noncomputable def gibbsH (t : ℝ) : ℝ := 1 / Real.sin t - 1 / t

/-- `h′(t) = 1/t² − cos t/sin² t`. -/
noncomputable def gibbsH' (t : ℝ) : ℝ := 1 / t ^ 2 - Real.cos t / Real.sin t ^ 2

theorem gibbsH_zero : gibbsH 0 = 0 := by simp [gibbsH]

theorem hasDerivAt_gibbsH {t : ℝ} (ht : t ≠ 0) (hs : Real.sin t ≠ 0) :
    HasDerivAt gibbsH (gibbsH' t) t := by
  have h := ((Real.hasDerivAt_sin t).inv hs).sub ((hasDerivAt_id t).inv ht)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => by
    simp [gibbsH, one_div])
  simp only [gibbsH', id, one_div]
  ring

theorem sin_pos_of_mem {t a : ℝ} (ha : a < π) (ht : t ∈ Ioc (0 : ℝ) a) : 0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_of_le_of_lt ht.2 ha)

/-- Taylor bounds on `(0, 1]`: `sin t ≥ t/2`, `|h(t)| ≤ t`, `|h′(t)| ≤ 4`. -/
theorem gibbsH_small {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    t / 2 ≤ Real.sin t ∧ |gibbsH t| ≤ t ∧ |gibbsH' t| ≤ 4 := by
  obtain ⟨ht0, ht1⟩ := ht
  have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
  have hs := Real.sin_bound hta
  have hc := Real.cos_bound hta
  rw [abs_of_pos ht0] at hs hc
  set e₁ := Real.sin t - (t - t ^ 3 / 6) with he₁
  set e₂ := Real.cos t - (1 - t ^ 2 / 2) with he₂
  have hS : Real.sin t = t - t ^ 3 / 6 + e₁ := by rw [he₁]; ring
  have hC : Real.cos t = 1 - t ^ 2 / 2 + e₂ := by rw [he₂]; ring
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs
  obtain ⟨hc1, hc2⟩ := abs_le.1 hc
  have t2 : t ^ 2 ≤ t := by nlinarith
  have t3 : t ^ 3 ≤ t ^ 2 := by nlinarith
  have t4 : t ^ 4 ≤ t ^ 3 := by nlinarith
  have t5 : t ^ 5 ≤ t ^ 4 := by nlinarith
  have t6 : t ^ 6 ≤ t ^ 5 := by nlinarith
  have t7 : t ^ 7 ≤ t ^ 6 := by nlinarith [pow_pos ht0 6]
  have t8 : t ^ 8 ≤ t ^ 7 := by nlinarith [pow_pos ht0 7]
  have hsin : t / 2 ≤ Real.sin t := by rw [hS]; linarith
  have hsin0 : 0 < Real.sin t := by linarith
  refine ⟨hsin, ?_, ?_⟩
  · -- `h = (t − sin t)/(t sin t)`
    have e : gibbsH t = (t - Real.sin t) / (t * Real.sin t) := by
      rw [gibbsH]; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos ht0 hsin0), div_le_iff₀ (mul_pos ht0 hsin0)]
    have hn : |t - Real.sin t| ≤ t ^ 3 / 4 := by
      rw [hS, abs_le]; constructor <;> linarith
    have : t ^ 3 / 4 ≤ t * (t * Real.sin t) := by
      have := mul_le_mul_of_nonneg_left hsin (by positivity : (0 : ℝ) ≤ t * t)
      nlinarith
    linarith
  · -- `h′ = (sin² t − t² cos t)/(t² sin² t)`
    have e : gibbsH' t = (Real.sin t ^ 2 - t ^ 2 * Real.cos t) / (t ^ 2 * Real.sin t ^ 2) := by
      rw [gibbsH']; field_simp
    have hN : Real.sin t ^ 2 - t ^ 2 * Real.cos t = t ^ 4 / 6 + t ^ 6 / 36 +
        2 * (t - t ^ 3 / 6) * e₁ + e₁ ^ 2 - t ^ 2 * e₂ := by rw [hS, hC]; ring
    have ha1 : |e₁| ≤ t ^ 4 * (5 / 96) := abs_le.2 ⟨by linarith, by linarith⟩
    have ha2 : |e₂| ≤ t ^ 4 * (5 / 96) := abs_le.2 ⟨hc1, hc2⟩
    have b1 : |2 * (t - t ^ 3 / 6) * e₁| ≤ t ^ 4 / 8 := by
      rw [abs_mul, abs_of_pos (by nlinarith)]
      calc 2 * (t - t ^ 3 / 6) * |e₁| ≤ 2 * t * (t ^ 4 * (5 / 96)) :=
            mul_le_mul (by nlinarith) ha1 (abs_nonneg _) (by positivity)
        _ ≤ t ^ 4 / 8 := by linarith
    have b2 : e₁ ^ 2 ≤ t ^ 4 / 8 := by
      have h := pow_le_pow_left₀ (abs_nonneg e₁) ha1 2
      rw [sq_abs] at h
      linarith
    have b3 : |t ^ 2 * e₂| ≤ t ^ 4 / 8 := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc t ^ 2 * |e₂| ≤ t ^ 2 * (t ^ 4 * (5 / 96)) :=
            mul_le_mul_of_nonneg_left ha2 (by positivity)
        _ ≤ t ^ 4 / 8 := by linarith
    have hNb : |Real.sin t ^ 2 - t ^ 2 * Real.cos t| ≤ t ^ 4 := by
      rw [hN, abs_le]
      obtain ⟨b11, b12⟩ := abs_le.1 b1
      obtain ⟨b31, b32⟩ := abs_le.1 b3
      have := sq_nonneg e₁
      have := pow_pos ht0 4
      have := pow_pos ht0 6
      constructor <;> linarith
    have hpos : 0 < t ^ 2 * Real.sin t ^ 2 := by positivity
    rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h1 : t ^ 2 / 4 ≤ Real.sin t ^ 2 := by nlinarith
    have h2 : t ^ 2 * (t ^ 2 / 4) ≤ t ^ 2 * Real.sin t ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith

/-- For `a < π`: `h` is continuous on `[0, a]`, `|h′| ≤ L` on `(0, a]`, `|h| ≤ M` on `[0, a]`. -/
theorem gibbsH_bounds {a : ℝ} (ha : a < π) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧ ContinuousOn gibbsH (Icc 0 a) ∧
      (∀ t ∈ Ioc (0 : ℝ) a, |gibbsH' t| ≤ L) ∧ ∀ t ∈ Icc (0 : ℝ) a, |gibbsH t| ≤ M := by
  have hsin : ∀ t ∈ Icc (1 : ℝ) a, Real.sin t ≠ 0 := fun t ht =>
    (sin_pos_of_mem ha ⟨by linarith [ht.1], ht.2⟩).ne'
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := a)).exists_bound_of_continuousOn
    (f := gibbsH') (fun t ht => ((continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (by simp; linarith [ht.1]))).sub (Real.continuous_cos.continuousAt.div
        (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 (hsin t ht)))).continuousWithinAt)
  -- continuity of `h` on `[0, a]`
  have hcont : ContinuousOn gibbsH (Icc 0 a) := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      refine Metric.continuousWithinAt_iff.2 fun ε hε => ⟨min ε 1, by positivity, fun s hs hd => ?_⟩
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hs.1] at hd
      rw [gibbsH_zero, dist_zero_right, Real.norm_eq_abs]
      rcases hs.1.eq_or_lt with h | h
      · rw [← h, gibbsH_zero, abs_zero]; exact hε
      · exact lt_of_le_of_lt (gibbsH_small ⟨h, by linarith [min_le_right ε 1]⟩).2.1
          (lt_of_lt_of_le hd (min_le_left _ _))
    · exact (hasDerivAt_gibbsH h0.ne' (sin_pos_of_mem ha ⟨h0, ht.2⟩).ne').continuousAt
        |>.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a)).exists_bound_of_continuousOn hcont
  refine ⟨max 4 B, max M 0, le_max_of_le_left (by norm_num), le_max_right _ _, hcont,
    fun t ht => ?_, fun t ht => ?_⟩
  · rcases le_or_gt t 1 with h1 | h1
    · exact (gibbsH_small ⟨ht.1, h1⟩).2.2.trans (le_max_left _ _)
    · have := hB t ⟨h1.le, ht.2⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _)
  · have := hM t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- `R_n` is odd. -/
theorem gibbsR_neg (n : ℕ) (x : ℝ) : gibbsR n (-x) = -gibbsR n x := by
  rw [gibbsR, gibbsR]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
    (fun t => (1 / Real.sin t - 1 / t) * Real.sin (2 * n * t))
  simp only [neg_zero] at h
  have e : ∀ t : ℝ, (1 / Real.sin (-t) - 1 / -t) * Real.sin (2 * n * -t) =
      (1 / Real.sin t - 1 / t) * Real.sin (2 * n * t) := fun t => by
    rw [Real.sin_neg, show 2 * (n : ℝ) * -t = -(2 * n * t) by ring, Real.sin_neg]
    field_simp
    ring
  simp only [e] at h
  rw [intervalIntegral.integral_symm (-x) 0, ← h]
  ring

/-- The integration-by-parts bound: `|R_n(x)| ≤ (M + L a)/(4n)` for `x ∈ [0, a]`. -/
theorem abs_gibbsR_le {a : ℝ} (ha : a < π) {L M : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hcont : ContinuousOn gibbsH (Icc 0 a)) (hL : ∀ t ∈ Ioc (0 : ℝ) a, |gibbsH' t| ≤ L)
    (hM : ∀ t ∈ Icc (0 : ℝ) a, |gibbsH t| ≤ M) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) a) : |gibbsR n x| ≤ (M + L * a) / (4 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (2 * n : ℝ) ≠ 0 := by positivity
  set v : ℝ → ℝ := fun t => -(Real.cos (2 * n * t) / (2 * n))
  have hv : ∀ t, HasDerivAt v (Real.sin (2 * n * t)) t := fun t => by
    have h := (((Real.hasDerivAt_cos _).comp t
      ((hasDerivAt_id t).const_mul (2 * (n : ℝ)))).div_const (2 * (n : ℝ))).neg
    refine h.congr_deriv ?_
    simp only [mul_one, id]
    field_simp
  have hsub : Icc 0 x ⊆ Icc 0 a := Icc_subset_Icc_right hx.2
  have huc : ContinuousOn gibbsH [[0, x]] := by rw [uIcc_of_le hx.1]; exact hcont.mono hsub
  have hu' : IntervalIntegrable gibbsH' volume 0 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
    refine Measure.integrableOn_of_bounded (M := L) (by simp : volume (Ioc (0 : ℝ) x) ≠ ⊤)
      ?_ ?_
    · exact (by unfold gibbsH'; fun_prop : Measurable gibbsH').aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]; exact hL t ⟨ht.1, ht.2.trans hx.2⟩
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right huc
    (fun t _ => (hv t).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [min_eq_left hx.1, max_eq_right hx.1] at ht
      exact (hasDerivAt_gibbsH ht.1.ne' (sin_pos_of_mem ha ⟨ht.1, ht.2.le.trans hx.2⟩).ne'
        ).hasDerivWithinAt)
    (fun t _ => (hv t).hasDerivWithinAt) hu'
    ((by fun_prop : Continuous fun t : ℝ => Real.sin (2 * n * t)).intervalIntegrable _ _)
  have hR : gibbsR n x = 1 / 2 * ∫ t in (0 : ℝ)..x, gibbsH t * Real.sin (2 * n * t) := rfl
  rw [hR, hibp, gibbsH_zero, zero_mul, sub_zero]
  have hb1 : |gibbsH x * v x| ≤ M / (2 * n) := by
    rw [abs_mul]
    simp only [v, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
    calc |gibbsH x| * (|Real.cos (2 * n * x)| / (2 * n)) ≤ M * (1 / (2 * n)) :=
          mul_le_mul (hM x hx) (div_le_div_of_nonneg_right (Real.abs_cos_le_one _)
            (by positivity)) (by positivity) hM0
      _ = _ := by ring
  have hb2 : ‖∫ t in (0 : ℝ)..x, gibbsH' t * v t‖ ≤ L / (2 * n) * |x - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hx.1] at ht
    rw [Real.norm_eq_abs, abs_mul]
    simp only [v, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
    calc |gibbsH' t| * (|Real.cos (2 * n * t)| / (2 * n)) ≤ L * (1 / (2 * n)) :=
          mul_le_mul (hL t ⟨ht.1, ht.2.trans hx.2⟩) (div_le_div_of_nonneg_right
            (Real.abs_cos_le_one _) (by positivity)) (by positivity) hL0
      _ = _ := by ring
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] at hb2
  have hxa : L / (2 * n) * x ≤ L / (2 * n) * a := by
    gcongr; exact hx.2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc 1 / 2 * |gibbsH x * v x - ∫ t in (0 : ℝ)..x, gibbsH' t * v t|
      ≤ 1 / 2 * (M / (2 * n) + L / (2 * n) * a) := by
        gcongr
        exact (abs_sub _ _).trans (by linarith)
    _ = _ := by field_simp; ring

/-- **DLMF 6.16.4** (corrected range): `R_n(x) = O(1/n)` uniformly for `x ∈ [−a, a]`, any
`a < π`.  (Uniformity on all of `[−π, π]` fails: `dlmf_6_16_4_endpoint`.) -/
theorem dlmf_6_16_4 {a : ℝ} (ha : a < π) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (-a) a, |gibbsR n x| ≤ C / n := by
  obtain ⟨L, M, hL0, hM0, hcont, hL, hM⟩ := gibbsH_bounds ha
  refine ⟨(M + L * |a|) / 4, fun n hn x hx => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ y ∈ Icc (0 : ℝ) a, |gibbsR n y| ≤ (M + L * |a|) / 4 / n := fun y hy => by
    refine (abs_gibbsR_le ha hL0 hM0 hcont hL hM hn hy).trans ?_
    rw [div_div]
    gcongr
    exact le_abs_self a
  rcases le_total 0 x with h | h
  · exact key x ⟨h, hx.2⟩
  · rw [show x = -(-x) by ring, gibbsR_neg, abs_neg]
    exact key (-x) ⟨by linarith, by linarith [hx.1]⟩

/-! ### Consequences: the limits 6.16.1 and the Gibbs phenomenon -/

theorem gibbsS_neg (n : ℕ) (x : ℝ) : gibbsS n (-x) = -gibbsS n x := by
  simp only [gibbsS, mul_neg, Real.sin_neg, neg_div, Finset.sum_neg_distrib]

theorem gibbsS_eq (n : ℕ) (x : ℝ) : gibbsS n x = 1 / 2 * SiR (2 * n * x) + gibbsR n x :=
  (dlmf_6_16_2 n x).1.trans (dlmf_6_16_2 n x).2

theorem tendsto_gibbsR {a : ℝ} (ha : a < π) {x : ℕ → ℝ} (hx : ∀ᶠ n in atTop, x n ∈ Icc (-a) a) :
    Tendsto (fun n => gibbsR n (x n)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := dlmf_6_16_4 ha
  have hl : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [hx, eventually_ge_atTop 1] with n h hn
  rw [Real.norm_eq_abs]; exact hC n hn _ h

/-- **DLMF 6.16.1**: `sin x + ⅓ sin 3x + ⅕ sin 5x + ⋯ = π/4, 0, −π/4` for `0 < x < π`, `x = 0`,
`−π < x < 0` (a conditionally convergent series, stated through its partial sums `S_n`). -/
theorem dlmf_6_16_1 :
    (∀ x ∈ Ioo (0 : ℝ) π, Tendsto (fun n => gibbsS n x) atTop (𝓝 (π / 4))) ∧
      (∀ n, gibbsS n 0 = 0) ∧
      ∀ x ∈ Ioo (-π) (0 : ℝ), Tendsto (fun n => gibbsS n x) atTop (𝓝 (-(π / 4))) := by
  have hpos : ∀ x ∈ Ioo (0 : ℝ) π, Tendsto (fun n => gibbsS n x) atTop (𝓝 (π / 4)) := by
    intro x hx
    have hSi : Tendsto (fun n : ℕ => SiR (2 * n * x)) atTop (𝓝 (π / 2)) := by
      refine tendsto_SiR.comp ?_
      have : Tendsto (fun n : ℕ => (n : ℝ) * (2 * x)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith [hx.1])
      exact this.congr fun n => by ring
    have hR := tendsto_gibbsR hx.2 (x := fun _ => x)
      (Eventually.of_forall fun _ => ⟨by linarith [hx.1], le_rfl⟩)
    have := (hSi.const_mul (1 / 2)).add hR
    rw [add_zero, show 1 / 2 * (π / 2) = π / 4 by ring] at this
    exact this.congr fun n => (gibbsS_eq n x).symm
  refine ⟨hpos, gibbsS_at_zero, fun x hx => ?_⟩
  have := (hpos (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).neg
  simp only [gibbsS_neg, neg_neg] at this
  exact this

/-- **§6.16(i), the Gibbs phenomenon**: at `x = π/(2n)` the partial sums tend to `½ Si(π)`, which
exceeds `π/4` (the overshoot of about 18%); at `x = π/n` they tend to `½ Si(2π) < π/4` (the
undershoot of about 10%).  (The decimals are not formalized.) -/
theorem dlmf_6_16_gibbs :
    Tendsto (fun n : ℕ => gibbsS n (π / (2 * n))) atTop (𝓝 (SiR π / 2)) ∧ π / 4 < SiR π / 2 ∧
      Tendsto (fun n : ℕ => gibbsS n (π / n)) atTop (𝓝 (SiR (2 * π) / 2)) ∧
        SiR (2 * π) / 2 < π / 4 := by
  have hπ := Real.pi_pos
  have hcl : ∀ (k : ℝ) (y : ℕ → ℝ), 0 < k → (∀ n : ℕ, 1 ≤ n → y n = k / n) →
      Tendsto (fun n : ℕ => gibbsS n (y n)) atTop (𝓝 (SiR (2 * k) / 2)) := by
    intro k y hk hy
    have hR := tendsto_gibbsR (a := π / 2) (by linarith) (x := y) (by
      filter_upwards [eventually_ge_atTop (⌈2 * k / π⌉₊ + 1)] with n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (by omega) hn
      have hn2 : 2 * k / π ≤ n := by
        have := Nat.le_ceil (2 * k / π)
        have : (⌈2 * k / π⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
        linarith
      rw [hy n (by exact_mod_cast hn1)]
      have hpos : 0 < k / n := by positivity
      constructor
      · linarith
      · rw [div_le_iff₀ (by linarith)]
        rw [div_le_iff₀ hπ] at hn2
        linarith)
    have := (tendsto_const_nhds (x := SiR (2 * k) / 2)).add hR
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [gibbsS_eq, hy n hn, show 2 * (n : ℝ) * (k / n) = 2 * k by field_simp]
    ring
  obtain ⟨h1, h2, -, -⟩ := dlmf_6_3_F2_Si_extrema 0
  obtain ⟨h3, -, -, -⟩ := dlmf_6_3_F2_Si_extrema 1
  simp only [CharP.cast_eq_zero, mul_zero, zero_mul, zero_add, one_mul, Nat.cast_one,
    mul_one] at h1 h2 h3
  refine ⟨?_, by linarith, ?_, by linarith⟩
  · have := hcl (π / 2) (fun n => π / (2 * n)) (by positivity) fun n _ => by ring
    rwa [show 2 * (π / 2) = π by ring] at this
  · exact hcl π (fun n => π / n) hπ fun n _ => rfl

/-- **§6.16(i)**: the limits of 6.16.1 are not approached uniformly on `(0, π)`. -/
theorem dlmf_6_16_not_uniform :
    ¬ TendstoUniformlyOn (fun n x => gibbsS n x) (fun _ => π / 4) atTop (Ioo 0 π) := by
  intro hu
  obtain ⟨hlim, hgt, -, -⟩ := dlmf_6_16_gibbs
  set ε := (SiR π / 2 - π / 4) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have h1 := (Metric.tendstoUniformlyOn_iff.1 hu) ε hε
  have h2 := hlim.eventually (lt_mem_nhds (show π / 4 + ε < SiR π / 2 by simp only [ε]; linarith))
  obtain ⟨n, hn1, hn2, hn⟩ := (h1.and (h2.and (eventually_ge_atTop 1))).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : π / (2 * n) ∈ Ioo 0 π := ⟨by positivity, by
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]⟩
  have := hn1 _ hx
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

/-! ### The endpoints `x = ±π` (DLMF erratum) -/

theorem gibbsS_pi (n : ℕ) : gibbsS n π = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show (2 * (k : ℝ) + 1) * π = ((2 * k + 1 : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi, zero_div]

/-- **DLMF erratum (6.16.4)**: `R_n(π) = −½ Si(2nπ) → −π/4`, so `R_n(x) = O(1/n)` does not hold
uniformly for `x ∈ [−π, π]` as DLMF states; it holds uniformly on every `[−a, a]`, `a < π`
(`dlmf_6_16_4`). -/
theorem dlmf_6_16_4_endpoint :
    Tendsto (fun n : ℕ => gibbsR n π) atTop (𝓝 (-(π / 4))) ∧
      ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (-π) π, |gibbsR n x| ≤ C / n := by
  have hR : ∀ n : ℕ, gibbsR n π = -(1 / 2 * SiR (2 * n * π)) := fun n => by
    have := gibbsS_eq n π
    rw [gibbsS_pi] at this
    linarith
  have hlim : Tendsto (fun n : ℕ => gibbsR n π) atTop (𝓝 (-(π / 4))) := by
    have hSi : Tendsto (fun n : ℕ => SiR (2 * n * π)) atTop (𝓝 (π / 2)) := by
      refine tendsto_SiR.comp ?_
      have : Tendsto (fun n : ℕ => (n : ℝ) * (2 * π)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      exact this.congr fun n => by ring
    have := (hSi.const_mul (1 / 2)).neg
    rw [show -(1 / 2 * (π / 2)) = -(π / 4) by ring] at this
    exact this.congr fun n => (hR n).symm
  refine ⟨hlim, fun ⟨C, hC⟩ => ?_⟩
  have h0 : Tendsto (fun n : ℕ => gibbsR n π) atTop (𝓝 0) := by
    have hl : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hC n hn π ⟨by linarith [Real.pi_pos], le_rfl⟩
  have := tendsto_nhds_unique hlim h0
  linarith [Real.pi_pos]

end Azurite.DLMF
