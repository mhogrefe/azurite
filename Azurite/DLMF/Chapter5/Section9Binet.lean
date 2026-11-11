/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9
import Azurite.DLMF.Chapter5.Section6
import Azurite.DLMF.Chapter1.Section14Laplace

/-!
# DLMF §5.9(i): Binet's formula (first form)

Formalization of <https://dlmf.nist.gov/5.9>, equation 5.9.10_2,
`Ln Γ(z) = (z − ½) ln z − z + ½ ln(2π) + ∫₀^∞ e^{−zt} (1/(eᵗ − 1) − 1/t + ½) dt/t`,
`|ph z| < ½π`. Mathlib has no complex `ln Γ`; as in §5.7 the formula is stated exponentiated
(`dlmf_5_9_10_2`, any value of `Ln Γ(z)` is a logarithm of `Γ(z)`) and with the real logarithm on
`(0, ∞)` (`dlmf_5_9_10_2_real`).

* `binetPhi t = (1/(eᵗ − 1) − 1/t + ½)/t` satisfies
  `(1 − e^{−t}) φ(t) = ∫₀¹ (½ − u) e^{−ut} du` (`one_sub_exp_mul_binetPhi`), hence `|φ| ≤ 3`
  (`abs_binetPhi_le`), and Binet's function `J(z) = ∫₀^∞ e^{−zt} φ(t) dt` (`binetJ`, a Laplace
  transform in the sense of §1.14(iii)) is analytic on `ℜz > 0` with `|J(z)| ≤ 3/ℜz`.
* On `(0, ∞)`: `J(x) − J(x + 1) = ∫₀¹ (½ − u)/(x + u) du = (x + ½) ln(1 + 1/x) − 1`
  (`binetJR_sub`, Fubini), the same difference as Stirling's `μ` of §5.6, and both tend to `0`
  along `x + N`, so `J = μ` (`binetJR_eq_stirlingMu`).
* The identity theorem extends `Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + J(z))` to `ℜz > 0`.

5.9.10 (the `arctan` form) and 5.9.10_1 are in `Section9BinetArctan.lean`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- `φ(t) = (1/(eᵗ − 1) − 1/t + ½)/t`, the integrand of Binet's formula 5.9.10_2. -/
noncomputable def binetPhi (t : ℝ) : ℝ := (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t

theorem integral_half_sub_mul_exp {t : ℝ} (ht : 0 < t) :
    ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-(u * t)) =
      Real.exp (-t) / (2 * t) + Real.exp (-t) / t ^ 2 + 1 / (2 * t) - 1 / t ^ 2 := by
  have hG : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => Real.exp (-(u * t)) * ((u - 1 / 2) / t + 1 / t ^ 2))
      ((1 / 2 - u) * Real.exp (-(u * t))) u := fun u _ => by
    have h1 : HasDerivAt (fun u : ℝ => -(u * t)) (-t) u := (hasDerivAt_mul_const t).neg
    have h2 := (((hasDerivAt_id u).sub_const (1 / 2 : ℝ)).div_const t).add_const (1 / t ^ 2)
    refine (h1.exp.mul h2).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((by fun_prop : Continuous fun u : ℝ => (1 / 2 - u) * Real.exp (-(u * t))).intervalIntegrable
      _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  field_simp
  ring

theorem one_sub_exp_mul_binetPhi {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-t)) * binetPhi t = ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-(u * t)) := by
  rw [integral_half_sub_mul_exp ht, binetPhi]
  have he : Real.exp t - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne'
  have he' : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  rw [Real.exp_neg]
  field_simp
  ring

theorem abs_exp_sub_exp_le {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_not_ge hab)
  rw [abs_of_nonpos (by linarith [Real.exp_le_exp.mpr hab]), abs_of_nonpos (by linarith)]
  have h1 := Real.add_one_le_exp (a - b)
  have h2 : Real.exp a = Real.exp b * Real.exp (a - b) := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp b ≤ 1 := Real.exp_le_one_iff.mpr hb
  rw [h2]
  nlinarith [Real.exp_pos b]

theorem abs_integral_half_sub_mul_exp_le {t : ℝ} (ht : 0 < t) :
    |∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-(u * t))| ≤ t / 4 := by
  have hz : ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-(t / 2)) = 0 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
  have heq : ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-(u * t)) =
      ∫ u in (0 : ℝ)..1, (1 / 2 - u) * (Real.exp (-(u * t)) - Real.exp (-(t / 2))) := by
    rw [show (fun u : ℝ => (1 / 2 - u) * (Real.exp (-(u * t)) - Real.exp (-(t / 2)))) =
      fun u => (1 / 2 - u) * Real.exp (-(u * t)) - (1 / 2 - u) * Real.exp (-(t / 2)) from
      funext fun u => by ring, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u : ℝ => (1 / 2 - u) * Real.exp (-(u * t))).intervalIntegrable
        _ _)
      ((by fun_prop : Continuous fun u : ℝ => (1 / 2 - u) * Real.exp (-(t / 2))).intervalIntegrable
        _ _), hz,
      sub_zero]
  rw [heq, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := t / 4)
    (f := fun u : ℝ => (1 / 2 - u) * (Real.exp (-(u * t)) - Real.exp (-(t / 2)))) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |1 / 2 - u| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      have h2 := abs_exp_sub_exp_le (a := -(u * t)) (b := -(t / 2)) (by nlinarith [hu.1])
        (by linarith)
      have h3 : |-(u * t) - -(t / 2)| = t * |1 / 2 - u| := by
        rw [show -(u * t) - -(t / 2) = t * (1 / 2 - u) by ring, abs_mul, abs_of_pos ht]
      rw [h3] at h2
      calc |1 / 2 - u| * |Real.exp (-(u * t)) - Real.exp (-(t / 2))|
          ≤ |1 / 2 - u| * (t * |1 / 2 - u|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ (1 / 2) * (t * (1 / 2)) := by gcongr
        _ = t / 4 := by ring)
  simpa using this

/-- `|φ(t)| ≤ 3` for `t > 0`. -/
theorem abs_binetPhi_le {t : ℝ} (ht : 0 < t) : |binetPhi t| ≤ 3 := by
  rcases le_or_gt t 1 with h1 | h1
  · -- `1 − e^{−t} ≥ t e^{−t} ≥ t/3`
    have hpos : 0 < 1 - Real.exp (-t) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have hlow : t / 3 ≤ 1 - Real.exp (-t) := by
      have e1 := Real.add_one_le_exp t
      have e2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
      have e3 : Real.exp (-t) ≥ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have e4 : Real.exp (-1) > 1 / 3 := by
        have := Real.exp_one_lt_d9
        rw [Real.exp_neg]
        rw [gt_iff_lt, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
        linarith
      nlinarith [Real.exp_pos (-t)]
    have hb := abs_integral_half_sub_mul_exp_le ht
    rw [← one_sub_exp_mul_binetPhi ht, abs_mul, abs_of_pos hpos] at hb
    have : |binetPhi t| ≤ 3 / 4 := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · have he : 1 < Real.exp t - 1 := by
      have := Real.add_one_le_exp t
      linarith
    rw [binetPhi, abs_div, abs_of_pos (by linarith : (0 : ℝ) < t), div_le_iff₀ (by linarith)]
    have h2 : |1 / (Real.exp t - 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by linarith)]; linarith
    have h3 : |1 / t| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by linarith)]; linarith
    calc |1 / (Real.exp t - 1) - 1 / t + 1 / 2|
        ≤ |1 / (Real.exp t - 1)| + |1 / t| + |(1 : ℝ) / 2| := by
          have := abs_sub (1 / (Real.exp t - 1)) (1 / t)
          have := abs_add_le (1 / (Real.exp t - 1) - 1 / t) (1 / 2)
          linarith
      _ ≤ 1 + 1 + 1 / 2 := by norm_num at h2 h3 ⊢; linarith
      _ ≤ 3 * t := by linarith

theorem continuousOn_binetPhi : ContinuousOn binetPhi (Ioi 0) := fun t ht => by
  have ht' : (0 : ℝ) < t := ht
  have he : Real.exp t - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht')).ne'
  unfold binetPhi
  exact ((((continuousAt_const.div (Real.continuous_exp.continuousAt.sub continuousAt_const) he).sub
    (continuousAt_const.div continuousAt_id ht'.ne')).add continuousAt_const).div continuousAt_id
    ht'.ne').continuousWithinAt

/-- Binet's function `J(z) = ∫₀^∞ e^{−zt} φ(t) dt`. -/
noncomputable def binetJ (z : ℂ) : ℂ := laplace (fun t => (binetPhi t : ℂ)) z

theorem expGrowth_binetPhi : ExpGrowth 3 0 (fun t => (binetPhi t : ℂ)) := fun t ht => by
  rw [Complex.norm_real, Real.norm_eq_abs, zero_mul, Real.exp_zero, mul_one]
  rcases ht.eq_or_lt with rfl | ht
  · simp [binetPhi]
  · exact abs_binetPhi_le ht

theorem aestronglyMeasurable_binetPhi :
    AEStronglyMeasurable (fun t => (binetPhi t : ℂ)) (volume.restrict (Ioi 0)) :=
  (continuous_ofReal.comp_continuousOn continuousOn_binetPhi).aestronglyMeasurable
    measurableSet_Ioi

theorem differentiableOn_binetJ : DifferentiableOn ℂ binetJ {z | 0 < z.re} := fun _ hz =>
  (hasDerivAt_laplace aestronglyMeasurable_binetPhi expGrowth_binetPhi hz).differentiableAt
    |>.differentiableWithinAt

theorem norm_binetJ_le {z : ℂ} (hz : 0 < z.re) : ‖binetJ z‖ ≤ 3 / z.re := by
  have := norm_laplace_le expGrowth_binetPhi (s := z) (by simpa using hz)
  simpa [binetJ] using this

/-- The real Binet function. -/
noncomputable def binetJR (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * binetPhi t

theorem binetJ_ofReal (x : ℝ) : binetJ x = binetJR x := by
  rw [binetJ, laplace, binetJR, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; rfl

theorem integrableOn_binetJR {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-(x * t)) * binetPhi t) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hx).const_mul 3) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul
      continuousOn_binetPhi).aestronglyMeasurable measurableSet_Ioi
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm 3, neg_mul]
    exact mul_le_mul_of_nonneg_left (abs_binetPhi_le ht) (Real.exp_pos _).le

/-- `J(x) − J(x + 1) = (x + ½) ln(1 + 1/x) − 1`. -/
theorem binetJR_sub {x : ℝ} (hx : 0 < x) : binetJR x - binetJR (x + 1) = stirlingG x := by
  have hx1 : 0 < x + 1 := by linarith
  -- the difference as a double integral
  have h1 : binetJR x - binetJR (x + 1) =
      ∫ t in Ioi (0 : ℝ), ∫ u in Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-((x + u) * t)) := by
    rw [binetJR, binetJR, ← integral_sub (integrableOn_binetJR hx) (integrableOn_binetJR hx1)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have e : ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-((x + u) * t)) =
        Real.exp (-(x * t)) * ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-(u * t)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [show -((x + u) * t) = -(x * t) + -(u * t) by ring, Real.exp_add]
      ring
    rw [e, ← one_sub_exp_mul_binetPhi ht']
    rw [show -((x + 1) * t) = -(x * t) + -t by ring, Real.exp_add]
    ring
  -- Fubini
  have hint : Integrable (Function.uncurry fun (t u : ℝ) => (1 / 2 - u) *
      Real.exp (-((x + u) * t))) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) := by
    have hb : Integrable (fun p : ℝ × ℝ => Real.exp (-(x * p.1)) * 1)
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) :=
      Integrable.mul_prod (f := fun t : ℝ => Real.exp (-(x * t))) (g := fun _ : ℝ => (1 : ℝ))
        (by have h := exp_neg_integrableOn_Ioi 0 hx; simp only [neg_mul] at h ⊢; exact h)
        (integrable_const 1)
    refine hb.mono' ((by fun_prop : Continuous (Function.uncurry fun (t u : ℝ) => (1 / 2 - u) *
      Real.exp (-((x + u) * t)))).aestronglyMeasurable) ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).mpr
      (ae_of_all _ fun p hp => ?_)
    simp only [Function.uncurry, mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hu : |1 / 2 - p.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hp.2.1, hp.2.2]
    have he : Real.exp (-((x + p.2) * p.1)) ≤ Real.exp (-(x * p.1)) :=
      Real.exp_le_exp.mpr (by nlinarith [hp.2.1])
    calc |1 / 2 - p.2| * Real.exp (-((x + p.2) * p.1)) ≤ 1 * Real.exp (-(x * p.1)) :=
          mul_le_mul hu he (Real.exp_pos _).le zero_le_one
      _ = _ := one_mul _
  have h2 := integral_integral_swap hint
  rw [h1, h2]
  -- the inner integral `∫₀^∞ e^{−(x+u)t} dt = 1/(x + u)`
  have h3 : ∀ u ∈ Ioc (0 : ℝ) 1,
      ∫ t in Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-((x + u) * t)) = (1 / 2 - u) / (x + u) := by
    intro u hu
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -(x + u)) (by linarith [hu.1]) 0
    simp only [mul_zero, Real.exp_zero] at this
    rw [show (fun t : ℝ => Real.exp (-((x + u) * t))) = fun t => Real.exp (-(x + u) * t) from
      funext fun t => by ring_nf, this]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc h3, ← intervalIntegral.integral_of_le zero_le_one]
  -- `∫₀¹ (½ − u)/(x + u) du = (x + ½) ln(1 + 1/x) − 1`
  have hG : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u => (x + 1 / 2) * Real.log (x + u) - u)
      ((1 / 2 - u) / (x + u)) u := fun u hu => by
    rw [uIcc_of_le zero_le_one] at hu
    have hxu : 0 < x + u := by linarith [hu.1]
    have := (((hasDerivAt_id u).const_add x).log hxu.ne').const_mul (x + 1 / 2) |>.sub
      (hasDerivAt_id u)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((continuousOn_const.sub continuousOn_id).div (continuousOn_const.add continuousOn_id)
      (fun u hu => by
        rw [uIcc_of_le zero_le_one] at hu; show x + u ≠ 0; linarith [hu.1])).intervalIntegrable,
    stirlingG, show 1 + 1 / x = (x + 1) / x by field_simp, Real.log_div hx1.ne' hx.ne']
  simp only [add_zero]
  ring

theorem tendsto_binetJR {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => binetJR (x + N)) atTop (𝓝 0) := by
  have hb : ∀ N : ℕ, |binetJR (x + N)| ≤ 3 / (x + N) := fun N => by
    have hxN : 0 < x + N := by positivity
    have := norm_binetJ_le (z := ((x + N : ℝ) : ℂ)) (by simpa using hxN)
    rwa [binetJ_ofReal, Complex.norm_real, Real.norm_eq_abs, ofReal_re] at this
  have hlim : Tendsto (fun N : ℕ => 3 / (x + N)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ x (tendsto_natCast_atTop_atTop (R := ℝ)))
  exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N) hlim

/-- On `(0, ∞)` Binet's function is Stirling's `μ` of §5.6. -/
theorem binetJR_eq_stirlingMu {x : ℝ} (hx : 0 < x) : binetJR x = stirlingMu x := by
  set D : ℝ → ℝ := fun y => stirlingMu y - binetJR y with hD
  have hper : ∀ N : ℕ, D (x + N) = D x := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      have hxn : 0 < x + n := by positivity
      have := binetJR_sub hxn
      have := stirlingMu_sub hxn
      simp only [hD] at ih ⊢
      push_cast
      rw [← add_assoc]
      linarith
  have hlim : Tendsto (fun N : ℕ => D (x + N)) atTop (𝓝 0) := by
    simpa using (tendsto_stirlingMu hx).sub (tendsto_binetJR hx)
  simp_rw [hper] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  simp only [hD] at this
  linarith

/-- **DLMF 5.9.10_2** (Binet's first formula), real form: for `x > 0`,
`ln Γ(x) = (x − ½) ln x − x + ½ ln(2π) + ∫₀^∞ e^{−xt} (1/(eᵗ − 1) − 1/t + ½) dt/t`. -/
theorem dlmf_5_9_10_2_real {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) = (x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π) +
      ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * ((1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t) := by
  have := binetJR_eq_stirlingMu hx
  rw [binetJR] at this
  unfold binetPhi at this
  rw [this, stirlingMu]
  ring

/-- **DLMF 5.9.10_2** (Binet's first formula): for `ℜz > 0`,
`Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + ∫₀^∞ e^{−zt} (1/(eᵗ − 1) − 1/t + ½) dt/t)`, i.e. the
right side is a value of `Ln Γ(z)`. -/
theorem dlmf_5_9_10_2 {z : ℂ} (hz : 0 < z.re) :
    Gamma z = cexp ((z - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) +
      ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) *
        (((1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t : ℝ) : ℂ)) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hslit : ∀ w ∈ U, w ∈ slitPlane := fun w hw => Or.inl hw
  have hΓ : AnalyticOnNhd ℂ Gamma U := fun w hw =>
    dlmf_5_2_i_analytic w (not_mem_gammaPoles_of_re_pos hw)
  have hR : AnalyticOnNhd ℂ (fun w => cexp ((w - 1 / 2) * Complex.log w - w +
      1 / 2 * Complex.log (2 * π) + binetJ w)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (((((differentiableAt_id.sub_const _).mul (differentiableAt_log (hslit w hw))).sub
        differentiableAt_id).add_const _).add
        ((differentiableOn_binetJ w hw).differentiableAt (hUo.mem_nhds hw))).cexp
        |>.differentiableWithinAt) hUo
  have heq := eqOn_of_eq_on_pos_reals hΓ hR (convex_halfSpace_re_gt 0).isPreconnected hUo
    (by simp [hU]) (fun x hx _ => by
      rw [binetJ_ofReal, binetJR_eq_stirlingMu hx, stirlingMu, Gamma_ofReal,
        ← ofReal_log hx.le, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_log (by positivity)]
      have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
      rw [show ((x : ℂ) - 1 / 2) * (Real.log x : ℂ) - x + 1 / 2 * (Real.log (2 * π) : ℂ) +
          ((Real.log (Real.Gamma x) - (x - 1 / 2) * Real.log x + x - 1 / 2 * Real.log (2 * π) :
            ℝ) : ℂ) = ((Real.log (Real.Gamma x) : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_exp, Real.exp_log hG]) (show z ∈ U from hz)
  rw [heq]
  rfl

end Azurite.DLMF
