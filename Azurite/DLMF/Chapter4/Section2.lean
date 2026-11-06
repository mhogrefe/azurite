/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# DLMF §4.2(i): The logarithm

Formalizations of <https://dlmf.nist.gov/4.2.i>. The principal branch `ln z` is Mathlib's
`Complex.log` (with `Complex.log 0 = 0`), and `ph z` is `Complex.arg` (§1.9).

Integration paths are `C¹` maps `γ : ℝ → ℂ` traversed over `[0, 1]`, and `∫₁^z dt/t` along `γ` is
`pathLogIntegral γ = ∫₀¹ γ′(s)/γ(s) ds`.

* 4.2.1 (the general logarithm `Ln z`): `exp ∫_γ dt/t = z` for every path from `1` to `z` avoiding
  the origin (`exp_pathLogIntegral`); its values are exactly `ln z + 2kπi`, `k ∈ ℤ`, i.e. 4.2.6
  (`dlmf_4_2_1`, `dlmf_4_2_6`: every path gives one of them, and every `k` occurs).
* 4.2.2: along a path not meeting `(−∞, 0]` the integral is `ln z` (`dlmf_4_2_2`); "`ln z` is a
  single-valued analytic function on `ℂ ∖ (−∞, 0]` and real-valued when `z` ranges over the positive
  real numbers" (`dlmf_4_2_i_analytic`, `dlmf_4_2_i_real`).
* 4.2.3: `ln z = ln |z| + i ph z`, `−π < ph z < π` off the cut (`dlmf_4_2_3`); "The only zero of
  `ln z` is at `z = 1`" (`dlmf_4_2_i_zero`).
* 4.2.4, 4.2.5: the extension to the cut `z = x < 0`, `−π < ph z ≤ π` (`dlmf_4_2_5`,
  `dlmf_4_2_5_cut`).
* 4.2.7 (the closed definition): `ln(x ± i0) = ln |x| ± iπ`, `x < 0`, as limits from the upper
  and lower half-planes (`dlmf_4_2_7`); "`ln z` is … discontinuous across the cut"
  (`dlmf_4_2_i_discontinuous`).

Not formalized: the description of `k` in 4.2.6 as the signed number of crossings of the negative
real axis, and the remarks on the regions of validity of 4.8.7 and 4.2.37 (later sections).
-/

open Complex Set Filter Topology intervalIntegral
open scoped Real

namespace Azurite.DLMF

/-- `∫₁^z dt/t` along the path `γ` (`s ∈ [0, 1]`). -/
noncomputable def pathLogIntegral (γ : ℝ → ℂ) : ℂ := ∫ s in (0 : ℝ)..1, deriv γ s / γ s

theorem pathLog_integrand_continuousOn {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s : Set ℝ} (h0 : ∀ t ∈ s, γ t ≠ 0) : ContinuousOn (fun t => deriv γ t / γ t) s :=
  ((hγ.continuous_deriv le_rfl).continuousOn).div hγ.continuous.continuousOn h0

/-- **DLMF 4.2.1**: along any path from `1` to `z` that does not meet the origin,
`exp ∫₁^z dt/t = z`. -/
theorem exp_pathLogIntegral {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 0) (h1 : γ 0 = 1) : exp (pathLogIntegral γ) = γ 1 := by
  set G : ℝ → ℂ := fun s => ∫ t in (0 : ℝ)..s, deriv γ t / γ t
  set U : Set ℝ := {t | γ t ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hγ.continuous continuous_const
  have hcont : ContinuousOn (fun t => deriv γ t / γ t) U :=
    pathLog_integrand_continuousOn hγ fun t ht => ht
  have hsub : Icc (0 : ℝ) 1 ⊆ U := fun t ht => h0 t ht
  have hint : ∀ s ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (fun t => deriv γ t / γ t) MeasureTheory.volume 0 s := fun s hs =>
    (hcont.mono ((uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ hs).trans hsub)).intervalIntegrable
  have hG : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt G (deriv γ s / γ s) s := fun s hs =>
    integral_hasDerivAt_right (hint s hs)
      ((hcont.stronglyMeasurableAtFilter hU) s (hsub hs))
      ((hcont s (hsub hs)).continuousAt (hU.mem_nhds (hsub hs)))
  set F : ℝ → ℂ := fun s => γ s * exp (-G s)
  have hF : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F 0 s := by
    intro s hs
    have hd := ((hγ.differentiable one_ne_zero) s).hasDerivAt
    have := hd.mul ((hG s hs).neg.cexp)
    convert this using 1
    field_simp [h0 s hs]
    ring
  have hFc : ContinuousOn F (Icc 0 1) := fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hFc
    (fun s hs => (hF s (Ico_subset_Icc_self hs)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simp only [F, G, integral_same, neg_zero, exp_zero, mul_one, h1] at hconst
  change γ 1 * exp (-pathLogIntegral γ) = 1 at hconst
  have e : exp (pathLogIntegral γ) * exp (-pathLogIntegral γ) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  calc exp (pathLogIntegral γ)
        = exp (pathLogIntegral γ) * (γ 1 * exp (-pathLogIntegral γ)) := by rw [hconst, mul_one]
    _ = γ 1 := by rw [mul_left_comm, e, mul_one]

/-- **DLMF 4.2.1, 4.2.6**: every value of `Ln z = ∫₁^z dt/t` (path avoiding `0`) is
`ln z + 2kπi` for some integer `k`. -/
theorem dlmf_4_2_6 {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (h0 : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 0)
    (h1 : γ 0 = 1) : ∃ k : ℤ, pathLogIntegral γ = log (γ 1) + 2 * k * π * I := by
  have he := exp_pathLogIntegral hγ h0 h1
  rw [← exp_log (h0 1 ⟨zero_le_one, le_rfl⟩), exp_eq_exp_iff_exists_int] at he
  obtain ⟨k, hk⟩ := he
  exact ⟨k, by rw [hk]; ring⟩

/-- **DLMF 4.2.1**: `Ln z` is multivalued: for `z ≠ 0` every `ln z + 2kπi` is `∫₁^z dt/t` along
some path from `1` to `z` avoiding `0`. -/
theorem dlmf_4_2_1 {z : ℂ} (hz : z ≠ 0) (k : ℤ) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ 1 γ ∧ (∀ s, γ s ≠ 0) ∧ γ 0 = 1 ∧ γ 1 = z ∧
      pathLogIntegral γ = log z + 2 * k * π * I := by
  set w := log z + 2 * k * π * I
  refine ⟨fun s => exp (s * w), (ofRealCLM.contDiff.mul contDiff_const).cexp,
    fun s => exp_ne_zero _, by simp, ?_, ?_⟩
  · simp only [ofReal_one, one_mul, w, exp_add, exp_log hz]
    rw [show 2 * (k : ℂ) * π * I = k * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I, mul_one]
  · have hd : ∀ s : ℝ, deriv (fun s : ℝ => exp (s * w)) s = w * exp (s * w) := fun s => by
      have := ((hasDerivAt_id s).ofReal_comp.mul_const w).cexp
      simpa [mul_comm] using this.deriv
    simp only [pathLogIntegral, hd, mul_div_assoc, div_self (exp_ne_zero _), mul_one,
      integral_const, sub_zero, one_smul]

/-- **DLMF 4.2.2**: along a path from `1` to `z` that does not meet `(−∞, 0]`,
`∫₁^z dt/t = ln z`. -/
theorem dlmf_4_2_2 {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hs : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ slitPlane) (h1 : γ 0 = 1) : pathLogIntegral γ = log (γ 1) := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 0 := fun s h => slitPlane_ne_zero (hs s h)
  rw [pathLogIntegral, integral_eq_sub_of_hasDerivAt (f := fun s => log (γ s)), h1, log_one,
    sub_zero]
  · intro s h
    rw [uIcc_of_le zero_le_one] at h
    have := (((hγ.differentiable one_ne_zero) s).hasDerivAt).clog_real (hs s h)
    simpa [div_eq_mul_inv, mul_comm] using this
  · exact (pathLog_integrand_continuousOn hγ
      (by rwa [uIcc_of_le zero_le_one])).intervalIntegrable

/-- **DLMF §4.2(i)**: "`ln z` is a single-valued analytic function on `ℂ ∖ (−∞, 0]`". -/
theorem dlmf_4_2_i_analytic : AnalyticOnNhd ℂ log slitPlane := fun _ hz => analyticAt_clog hz

/-- **DLMF §4.2(i)**: "… and real-valued when `z` ranges over the positive real numbers". -/
theorem dlmf_4_2_i_real {x : ℝ} (hx : 0 < x) : log (x : ℂ) = (Real.log x : ℂ) :=
  (ofReal_log hx.le).symm

/-- **DLMF 4.2.3**: `ln z = ln |z| + i ph z`, `−π < ph z < π` (`z` off the cut). -/
theorem dlmf_4_2_3 {z : ℂ} (hz : z ∈ slitPlane) :
    log z = Real.log ‖z‖ + I * arg z ∧ -π < arg z ∧ arg z < π := by
  refine ⟨by rw [log]; ring, neg_pi_lt_arg z, ?_⟩
  exact lt_of_le_of_ne (arg_le_pi z) (mem_slitPlane_iff_arg.mp hz).1

/-- **DLMF §4.2(i)**: "The only zero of `ln z` is at `z = 1`" (`z ≠ 0`). -/
theorem dlmf_4_2_i_zero {z : ℂ} (hz : z ≠ 0) : log z = 0 ↔ z = 1 := by
  constructor
  · intro h; rw [← exp_log hz, h, exp_zero]
  · rintro rfl; exact log_one

/-- **DLMF 4.2.5**: with the cut 4.2.4 included, `ln z = ln |z| + i ph z`, `−π < ph z ≤ π`
(`z ≠ 0`). -/
theorem dlmf_4_2_5 (z : ℂ) :
    log z = Real.log ‖z‖ + I * arg z ∧ -π < arg z ∧ arg z ≤ π :=
  ⟨by rw [log]; ring, neg_pi_lt_arg z, arg_le_pi z⟩

/-- **DLMF 4.2.4, 4.2.5**: on the cut `z = x`, `−∞ < x < 0`, `ln x = ln |x| + iπ`. -/
theorem dlmf_4_2_5_cut {x : ℝ} (hx : x < 0) : log (x : ℂ) = Real.log |x| + π * I := by
  rw [log, arg_ofReal_of_neg hx, norm_real, Real.norm_eq_abs]

/-- **DLMF 4.2.7**: the closed definition: `ln(x ± i0) = ln |x| ± iπ`, `−∞ < x < 0`, as the limits
of `ln z` from the upper (`x + i0`) and lower (`x − i0`) half-planes. -/
theorem dlmf_4_2_7 {x : ℝ} (hx : x < 0) :
    Tendsto log (𝓝[{z | 0 < z.im}] (x : ℂ)) (𝓝 (Real.log |x| + π * I)) ∧
      Tendsto log (𝓝[{z | z.im < 0}] (x : ℂ)) (𝓝 (Real.log |x| - π * I)) := by
  constructor
  · have hc := continuousWithinAt_log_of_re_neg_of_im_zero (z := (x : ℂ)) (by simpa using hx)
      (by simp)
    rw [← dlmf_4_2_5_cut hx]
    exact hc.tendsto.mono_left
      (nhdsWithin_mono _ fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im))
  · have := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := (x : ℂ)) (by simpa using hx)
      (by simp)
    convert this using 2
    rw [norm_real, Real.norm_eq_abs]

/-- **DLMF §4.2(i)**: "`ln z` is two-valued on the cut, and discontinuous across the cut": the
one-sided limits at `x < 0` differ by `2πi`, so `ln` is not continuous at `x`. -/
theorem dlmf_4_2_i_discontinuous {x : ℝ} (hx : x < 0) : ¬ ContinuousAt log (x : ℂ) := by
  intro hc
  have h2 := (dlmf_4_2_7 hx).2
  have h2' : Tendsto log (𝓝[{z | z.im < 0}] (x : ℂ)) (𝓝 (log x)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hne : (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_seq_limit]
    refine ⟨fun n => x - ((1 : ℝ) / (n + 1) : ℝ) * I, fun n => ?_, ?_⟩
    · simp only [mem_ofPred_eq, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero,
        add_zero, mul_one, zero_sub, Left.neg_neg_iff]
      positivity
    · have : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((continuous_ofReal.tendsto 0).comp this).mul_const I
      simpa using (tendsto_const_nhds (x := (x : ℂ))).sub this
  have := tendsto_nhds_unique h2 h2'
  rw [dlmf_4_2_5_cut hx] at this
  have him := congrArg im this
  simp at him
  linarith [Real.pi_pos]

end Azurite.DLMF
