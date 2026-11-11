/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9BinetArctan
import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF §5.9(i): Binet's function on the right half-plane

Uniform bounds used for Boyd's formulas 5.9.11_1–5.9.11_2 (`Section9BoydCauchy.lean`):

* `φ(t) = ∑_{k≥1} 2/(t² + 4π²k²)` (`hasSum_binetPhi`, the partial fractions of `coth`);
* `|∫₀^∞ e^{−wt} dt/(t² + c²)| ≤ 2/(c²|w|)` for `ℜw > 0` (one integration by parts,
  `norm_laplace_inv_sq_add_sq_le`), hence Stieltjes' bound `|J(w)| ≤ 1/(6|w|)` on `ℜw > 0`
  (`norm_binetJ_le_inv`), uniform up to the imaginary axis;
* the scaled gamma function `Γ*(z) = Γ(z)/(√(2π) e^{−z} z^{z−½})` of 5.11.3 (`scaledGamma`),
  `Γ*(z) = e^{J(z)}` on `ℜz > 0` (`scaledGamma_eq_exp`), so `|Γ*(w) − 1|, |1/Γ*(w) − 1| ≤ 1/(3|w|)`
  for `|w| ≥ 1`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### `φ` as a series -/

theorem hasSum_binetPhi {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 / (t ^ 2 + 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) (binetPhi t) := by
  have h := (hasSum_coth_series_exp ht).div_const t
  rw [binetPhi]
  convert h using 1
  funext n
  field_simp

/-! ### The Laplace transform of `1/(t² + c²)` -/

theorem integral_two_mul_div_sq_add_sq_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => 2 * t / (t ^ 2 + c ^ 2) ^ 2) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 2 * t / (t ^ 2 + c ^ 2) ^ 2 = 1 / c ^ 2 := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(1 / (t ^ 2 + c ^ 2)))
      (2 * t / (t ^ 2 + c ^ 2) ^ 2) t := fun t _ => by
    have hpos : t ^ 2 + c ^ 2 ≠ 0 := by positivity
    have := (((hasDerivAt_pow 2 t).add_const (c ^ 2)).inv hpos).neg
    convert this using 1
    · funext s; simp [one_div]
    · field_simp; ring
  have hcont : ContinuousWithinAt (fun t : ℝ => -(1 / (t ^ 2 + c ^ 2))) (Ici 0) 0 :=
    ((by fun_prop (disch := exact fun _ => by positivity) :
      Continuous fun t : ℝ => -(1 / (t ^ 2 + c ^ 2)))
      |>.continuousWithinAt)
  have hlim : Tendsto (fun t : ℝ => -(1 / (t ^ 2 + c ^ 2))) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t ^ 2 + c ^ 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using (this.inv_tendsto_atTop).neg
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hd
    (fun t ht => by have : (0 : ℝ) < t := ht; positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  simp

/-- `|∫₀^∞ e^{−wt}/(t² + c²) dt| ≤ 2/(c²|w|)` for `ℜw > 0`. -/
theorem norm_laplace_inv_sq_add_sq_le {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    ‖∫ t in Ioi (0 : ℝ), cexp (-(w * t)) * ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ)‖ ≤
      2 / (c ^ 2 * ‖w‖) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl 0 hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hpos : ∀ t : ℝ, t ^ 2 + c ^ 2 ≠ 0 := fun t => by positivity
  obtain ⟨hint', hval'⟩ := integral_two_mul_div_sq_add_sq_sq hc
  have hud : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ))
      (((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) t := fun t _ => by
    have := ((((hasDerivAt_pow 2 t).add_const (c ^ 2)).inv (hpos t)).ofReal_comp)
    convert this using 1
    · funext s; simp [one_div]
    · push_cast; field_simp
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(cexp (-(w * t)) / w))
      (cexp (-(w * t))) t := fun t _ => by
    have h1 : HasDerivAt (fun t : ℝ => -(w * t)) (-w) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul w).neg.comp_ofReal
    have := (h1.cexp.div_const w).neg
    convert this using 1
    field_simp
  have hexp : ∀ t : ℝ, 0 ≤ t → ‖cexp (-(w * t))‖ = Real.exp (-(w.re * t)) := fun t _ => by
    rw [Complex.norm_exp]; simp
  have hexp1 : ∀ t : ℝ, 0 ≤ t → Real.exp (-(w.re * t)) ≤ 1 := fun t ht =>
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hinvle : ∀ t : ℝ, 1 / (t ^ 2 + c ^ 2) ≤ 1 / c ^ 2 := fun t =>
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hcont1 : Continuous fun t : ℝ => ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * cexp (-(w * t)) := by
    fun_prop (disch := exact hpos)
  have hcont2 : Continuous fun t : ℝ => (((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) *
      -(cexp (-(w * t)) / w) := by
    fun_prop (disch := first | exact fun t => pow_ne_zero 2 (hpos t) | exact hw0)
  have huv' : IntegrableOn (fun t : ℝ => ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * cexp (-(w * t)))
      (Ioi 0) := by
    have hb : IntegrableOn (fun t : ℝ => 1 / c ^ 2 * Real.exp (-w.re * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hw).const_mul _
    refine hb.mono' hcont1.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun t ht => ?_))
    have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      hexp t ht'.le, neg_mul]
    exact mul_le_mul_of_nonneg_right (hinvle t) (Real.exp_pos _).le
  have hbound2 : ∀ t : ℝ, 0 < t → ‖(((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) *
      -(cexp (-(w * t)) / w)‖ ≤ 1 / ‖w‖ * (2 * t / (t ^ 2 + c ^ 2) ^ 2) := fun t ht => by
    rw [norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity), hexp t ht.le]
    calc 2 * t / (t ^ 2 + c ^ 2) ^ 2 * (Real.exp (-(w.re * t)) / ‖w‖)
        ≤ 2 * t / (t ^ 2 + c ^ 2) ^ 2 * (1 / ‖w‖) := by
          gcongr; exact hexp1 t ht.le
      _ = 1 / ‖w‖ * (2 * t / (t ^ 2 + c ^ 2) ^ 2) := by ring
  have hu'v : IntegrableOn (fun t : ℝ => (((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) *
      -(cexp (-(w * t)) / w)) (Ioi 0) :=
    (hint'.const_mul (1 / ‖w‖)).mono' hcont2.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => hbound2 t ht))
  have hcont3 : Continuous fun t : ℝ => ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) *
      -(cexp (-(w * t)) / w) := by
    fun_prop (disch := first | exact hpos | exact hw0)
  have h0 : Tendsto (fun t : ℝ => ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * -(cexp (-(w * t)) / w))
      (𝓝[>] 0) (𝓝 (-(1 / (c ^ 2 : ℂ) / w))) := by
    have := (hcont3.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    push_cast
    simp
    ring
  have hinf : Tendsto (fun t : ℝ => ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * -(cexp (-(w * t)) / w))
      atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => 1 / c ^ 2 * (1 / ‖w‖) * Real.exp (-(w.re * t))) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => -(w.re * t)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop' hw)
      have := (Real.tendsto_exp_atBot.comp h1).const_mul (1 / c ^ 2 * (1 / ‖w‖))
      simpa only [mul_zero, Function.comp_def] using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), hexp t ht.le]
    calc 1 / (t ^ 2 + c ^ 2) * (Real.exp (-(w.re * t)) / ‖w‖)
        ≤ 1 / c ^ 2 * (Real.exp (-(w.re * t)) / ‖w‖) := by gcongr; nlinarith [sq_nonneg t]
      _ = _ := by ring
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd huv' hu'v h0 hinf
  have heq : ∫ t in Ioi (0 : ℝ), cexp (-(w * t)) * ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((1 / (t ^ 2 + c ^ 2) : ℝ) : ℂ) * cexp (-(w * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [heq, hparts, zero_sub, neg_neg]
  have hI : ‖∫ t in Ioi (0 : ℝ), (((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) *
      -(cexp (-(w * t)) / w)‖ ≤ 1 / (c ^ 2 * ‖w‖) := by
    refine (norm_integral_le_of_norm_le (hint'.const_mul (1 / ‖w‖))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => hbound2 t ht))).trans
      (le_of_eq ?_)
    rw [integral_const_mul, hval']; field_simp
  have h1 : ‖1 / (c ^ 2 : ℂ) / w‖ = 1 / (c ^ 2 * ‖w‖) := by
    rw [norm_div, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
    field_simp
  calc ‖1 / (c ^ 2 : ℂ) / w - ∫ t in Ioi (0 : ℝ), (((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) *
        -(cexp (-(w * t)) / w)‖
      ≤ ‖1 / (c ^ 2 : ℂ) / w‖ + ‖∫ t in Ioi (0 : ℝ), (((-(2 * t / (t ^ 2 + c ^ 2) ^ 2)) : ℝ) : ℂ) *
        -(cexp (-(w * t)) / w)‖ := norm_sub_le _ _
    _ ≤ 1 / (c ^ 2 * ‖w‖) + 1 / (c ^ 2 * ‖w‖) := by rw [h1]; gcongr
    _ = 2 / (c ^ 2 * ‖w‖) := by ring

/-! ### Stieltjes' bound `|J(w)| ≤ 1/(6|w|)` -/

theorem hasSum_inv_succ_sq : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- Stieltjes' bound: `|J(w)| ≤ 1/(6|w|)` on `ℜw > 0`. -/
theorem norm_binetJ_le_inv {w : ℂ} (hw : 0 < w.re) : ‖binetJ w‖ ≤ 1 / (6 * ‖w‖) := by
  have hπ := Real.pi_pos
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl 0 hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set c : ℕ → ℝ := fun n => 2 * π * ((n : ℝ) + 1) with hc
  have hc0 : ∀ n, 0 < c n := fun n => by rw [hc]; positivity
  have hcsq : ∀ n, c n ^ 2 = 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := fun n => by rw [hc]; ring
  set F : ℕ → ℝ → ℂ := fun n t => cexp (-(w * t)) * ((2 / (t ^ 2 + c n ^ 2) : ℝ) : ℂ) with hF
  have hexp : ∀ t : ℝ, ‖cexp (-(w * t))‖ = Real.exp (-(w.re * t)) := fun t => by
    rw [Complex.norm_exp]; simp
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    refine ((exp_neg_integrableOn_Ioi 0 hw).const_mul (2 / c n ^ 2)).mono'
      ((by fun_prop (disch := exact fun _ => by have := hc0 n; positivity) :
        Continuous (F n)).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have hcn := hc0 n
    simp only [hF]
    rw [norm_mul, hexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      mul_comm, neg_mul]
    gcongr
    nlinarith [sq_nonneg t]
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ ≤ 2 / (c n ^ 2 * w.re) := fun n => by
    have hb : IntegrableOn (fun t : ℝ => 2 / c n ^ 2 * Real.exp (-w.re * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hw).const_mul _
    calc ∫ t in Ioi (0 : ℝ), ‖F n t‖ ≤ ∫ t in Ioi (0 : ℝ), 2 / c n ^ 2 * Real.exp (-w.re * t) := by
          refine setIntegral_mono_on (hint n).norm hb measurableSet_Ioi fun t _ => ?_
          have hcn := hc0 n
          simp only [hF]
          rw [norm_mul, hexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
            mul_comm, neg_mul]
          gcongr
          nlinarith [sq_nonneg t]
      _ = 2 / (c n ^ 2 * w.re) := by
          rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero hw]; field_simp
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    refine (hasSum_inv_succ_sq.summable.mul_left (1 / (2 * π ^ 2 * w.re))).of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _) fun n => (hnorm n).trans (le_of_eq ?_)
    rw [hcsq]; field_simp; ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hJ : ∫ t in Ioi (0 : ℝ), ∑' n, F n t = binetJ w := by
    rw [binetJ, laplace]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hs := ((Complex.hasSum_ofReal.mpr (hasSum_binetPhi ht')).mul_left (cexp (-(w * t))))
    simp only [hF]
    rw [← hs.tsum_eq]
    congr 1
    funext n
    rw [hcsq]
  rw [hJ] at h
  have hg : HasSum (fun n : ℕ => 1 / (π ^ 2 * ‖w‖) * (1 / ((n : ℝ) + 1) ^ 2))
      (1 / (π ^ 2 * ‖w‖) * (π ^ 2 / 6)) := hasSum_inv_succ_sq.mul_left _
  refine (h.norm_le_of_bounded hg fun n => ?_).trans (le_of_eq ?_)
  · have e : ∫ t in Ioi (0 : ℝ), F n t =
        2 * ∫ t in Ioi (0 : ℝ), cexp (-(w * t)) * ((1 / (t ^ 2 + c n ^ 2) : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hF]; push_cast; ring
    rw [e, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖∫ t in Ioi (0 : ℝ), cexp (-(w * t)) * ((1 / (t ^ 2 + c n ^ 2) : ℝ) : ℂ)‖
        ≤ 2 * (2 / (c n ^ 2 * ‖w‖)) := by gcongr; exact norm_laplace_inv_sq_add_sq_le hw (hc0 n)
      _ = _ := by rw [hcsq]; field_simp; ring
  · field_simp

/-! ### The scaled gamma function -/

/-- DLMF 5.11.3: `Γ*(z) = Γ(z)/(√(2π) e^{−z} z^{z−½})` (principal power). -/
noncomputable def scaledGamma (z : ℂ) : ℂ :=
  Gamma z / ((Real.sqrt (2 * π) : ℂ) * cexp (-z) * z ^ (z - 1 / 2))

theorem sqrt_two_pi_eq_exp :
    ((Real.sqrt (2 * π) : ℝ) : ℂ) = cexp (1 / 2 * Complex.log (2 * π)) := by
  have hpos : (0 : ℝ) ≤ 2 * π := by positivity
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos, cpow_def_of_ne_zero (by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0))]
  push_cast
  ring_nf

/-- `Γ*(z) = e^{J(z)}` for `ℜz > 0` (5.9.10_2). -/
theorem scaledGamma_eq_exp {z : ℂ} (hz : 0 < z.re) : scaledGamma z = cexp (binetJ z) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  have h := dlmf_5_9_10_2 hz
  have hJ : (∫ t in Ioi (0 : ℝ), cexp (-(z * t)) *
      (((1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t : ℝ) : ℂ)) = binetJ z := rfl
  rw [hJ] at h
  rw [scaledGamma, h, sqrt_two_pi_eq_exp, cpow_def_of_ne_zero hz0, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  ring

theorem norm_scaledGamma_sub_one_le {w : ℂ} (hw : 0 < w.re) (hw1 : 1 ≤ ‖w‖) :
    ‖scaledGamma w - 1‖ ≤ 1 / (3 * ‖w‖) ∧ ‖(scaledGamma w)⁻¹ - 1‖ ≤ 1 / (3 * ‖w‖) := by
  have hJ := norm_binetJ_le_inv hw
  have hJ1 : ‖binetJ w‖ ≤ 1 := hJ.trans (by rw [div_le_one (by positivity)]; linarith)
  rw [scaledGamma_eq_exp hw, ← Complex.exp_neg]
  constructor
  · refine (norm_exp_sub_one_le hJ1).trans ?_
    calc 2 * ‖binetJ w‖ ≤ 2 * (1 / (6 * ‖w‖)) := by gcongr
      _ = 1 / (3 * ‖w‖) := by field_simp; ring
  · have hJ1' : ‖-binetJ w‖ ≤ 1 := by rwa [norm_neg]
    refine (norm_exp_sub_one_le hJ1').trans ?_
    rw [norm_neg]
    calc 2 * ‖binetJ w‖ ≤ 2 * (1 / (6 * ‖w‖)) := by gcongr
      _ = 1 / (3 * ‖w‖) := by field_simp; ring

/-! ### `Γ*` near `0` -/

theorem rpow_neg_re_le {w : ℂ} (hw : 0 < w.re) (hw1 : ‖w‖ ≤ 1) : ‖w‖ ^ (-w.re) ≤ Real.exp 1 := by
  have hn : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  rw [Real.rpow_def_of_pos hn]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log ‖w‖ ≤ 0 := Real.log_nonpos hn.le hw1
  have h1 := Real.one_sub_inv_le_log_of_pos hn
  have hre : w.re ≤ ‖w‖ := Complex.re_le_norm w
  -- `−ℜw ln|w| ≤ −|w| ln|w| ≤ 1 − |w| ≤ 1`
  have h2 : ‖w‖ * (1 - ‖w‖⁻¹) ≤ ‖w‖ * Real.log ‖w‖ := mul_le_mul_of_nonneg_left h1 hn.le
  have h3 : ‖w‖ * (1 - ‖w‖⁻¹) = ‖w‖ - 1 := by field_simp
  nlinarith

theorem norm_cpow_le_of_re {w s : ℂ} (hw : w ≠ 0) :
    ‖w ^ s‖ ≤ ‖w‖ ^ s.re * Real.exp (π * |s.im|) := by
  rw [norm_cpow_of_ne_zero hw, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg w * s.im) ≤ |arg w * s.im| := neg_le_abs _
    _ = |arg w| * |s.im| := abs_mul _ _
    _ ≤ π * |s.im| := mul_le_mul_of_nonneg_right (abs_arg_le_pi w) (abs_nonneg _)

/-- `|Γ*(w)| ≤ C |w|^{−½}` and `|1/Γ*(w)| ≤ C` for `ℜw > 0`, `|w| ≤ 1`. -/
theorem exists_bound_scaledGamma_near_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 0 < w.re → ‖w‖ ≤ 1 →
      ‖scaledGamma w‖ ≤ C * ‖w‖ ^ (-(1 / 2 : ℝ)) ∧ ‖(scaledGamma w)⁻¹‖ ≤ C := by
  set K : Set ℂ := Metric.closedBall 0 1 ∩ {w | 0 ≤ w.re} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_re)
  have hΓc : ContinuousOn (fun w => Gamma (w + 1)) K := fun w hw =>
    ((differentiableAt_Gamma _ fun m h => by
      have := congrArg re h
      simp at this
      have := hw.2
      simp only [mem_ofPred_eq] at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt.comp
      (continuous_id.add continuous_const).continuousAt).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn hΓc
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    ((differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)).continuous.continuousOn)
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  set C := (max M₁ 1) / Real.sqrt (2 * π) * Real.exp 1 * Real.exp 1 * Real.exp π +
    Real.sqrt (2 * π) * Real.exp 1 * Real.exp π * max M₂ 1 with hC
  refine ⟨C, by positivity, fun w hw hw1 => ?_⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl 0 hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwK : w ∈ K := ⟨by simpa using hw1, le_of_lt hw⟩
  have hΓ1 : Gamma (w + 1) = w * Gamma w := Gamma_add_one w hw0
  have himw : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans hw1
  have hexpw : ‖cexp w‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr ((Complex.re_le_norm w).trans hw1)
  have hexpnw : ‖cexp (-w)‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (by simp; linarith)
  have hsqrt : ‖((Real.sqrt (2 * π) : ℝ) : ℂ)‖ = Real.sqrt (2 * π) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hprod : (Real.sqrt (2 * π) : ℂ) * cexp (-w) * w ^ (w - 1 / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hs.ne') (Complex.exp_ne_zero _))
      (by rw [Ne, cpow_eq_zero_iff]; tauto)
  constructor
  · -- `Γ*(w) = Γ(w + 1) eʷ w^{½−w}/(w √(2π))`
    have e : scaledGamma w = Gamma (w + 1) * cexp w * w ^ (-(1 / 2 : ℂ) - w) /
        (Real.sqrt (2 * π) : ℂ) := by
      have hc : w ^ (-(1 / 2 : ℂ) - w) = (w ^ (w - 1 / 2))⁻¹ * w⁻¹ := by
        rw [show -(1 / 2 : ℂ) - w = -(w - 1 / 2) - 1 by ring, cpow_sub _ _ hw0, cpow_neg,
          cpow_one, div_eq_mul_inv]
      rw [scaledGamma, hΓ1, hc, Complex.exp_neg]
      have : w ^ (w - 1 / 2) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
      have : (Real.sqrt (2 * π) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      field_simp
    have hpow := norm_cpow_le_of_re (s := -(1 / 2 : ℂ) - w) hw0
    have hre : (-(1 / 2 : ℂ) - w).re = -(1 / 2) + -w.re := by simp; ring
    have him : |(-(1 / 2 : ℂ) - w).im| = |w.im| := by simp
    rw [hre, him, Real.rpow_add hn] at hpow
    have hpow2 : ‖w ^ (-(1 / 2 : ℂ) - w)‖ ≤ ‖w‖ ^ (-(1 / 2 : ℝ)) * (Real.exp 1 * Real.exp π) := by
      refine hpow.trans ?_
      have h1 := rpow_neg_re_le hw hw1
      have h2 : Real.exp (π * |w.im|) ≤ Real.exp π :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      calc ‖w‖ ^ (-(1 / 2 : ℝ)) * ‖w‖ ^ (-w.re) * Real.exp (π * |w.im|)
          = ‖w‖ ^ (-(1 / 2 : ℝ)) * (‖w‖ ^ (-w.re) * Real.exp (π * |w.im|)) := by ring
        _ ≤ ‖w‖ ^ (-(1 / 2 : ℝ)) * (Real.exp 1 * Real.exp π) := by gcongr
    have hG : ‖Gamma (w + 1)‖ ≤ max M₁ 1 := (hM₁ w hwK).trans (le_max_left _ _)
    rw [e, norm_div, norm_mul, norm_mul, hsqrt]
    calc ‖Gamma (w + 1)‖ * ‖cexp w‖ * ‖w ^ (-(1 / 2 : ℂ) - w)‖ / Real.sqrt (2 * π)
        ≤ max M₁ 1 * Real.exp 1 * (‖w‖ ^ (-(1 / 2 : ℝ)) * (Real.exp 1 * Real.exp π)) /
            Real.sqrt (2 * π) := by gcongr
      _ = (max M₁ 1) / Real.sqrt (2 * π) * Real.exp 1 * Real.exp 1 * Real.exp π *
            ‖w‖ ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ C * ‖w‖ ^ (-(1 / 2 : ℝ)) := by
          gcongr
          rw [hC]
          have : 0 ≤ Real.sqrt (2 * π) * Real.exp 1 * Real.exp π * max M₂ 1 := by positivity
          linarith
  · -- `1/Γ*(w) = √(2π) e^{−w} w · w^{w−½} / Γ(w + 1)`
    have e : (scaledGamma w)⁻¹ = (Real.sqrt (2 * π) : ℂ) * cexp (-w) * (w * w ^ (w - 1 / 2)) *
        (Gamma (w + 1))⁻¹ := by
      rw [scaledGamma, hΓ1, inv_div]
      by_cases hG : Gamma w = 0
      · simp [hG]
      · field_simp
    have hpow := norm_cpow_le_of_re (s := w - 1 / 2) hw0
    have hre : (w - 1 / 2).re = w.re - 1 / 2 := by simp
    have him : |(w - 1 / 2).im| = |w.im| := by simp
    rw [hre, him] at hpow
    have hww : ‖w * w ^ (w - 1 / 2)‖ ≤ Real.exp π := by
      rw [norm_mul]
      have h1 : ‖w‖ * ‖w‖ ^ (w.re - 1 / 2) = ‖w‖ ^ (w.re + 1 / 2) := by
        rw [show w.re + 1 / 2 = (w.re - 1 / 2) + 1 by ring, Real.rpow_add_one hn.ne']; ring
      have h2 : ‖w‖ ^ (w.re + 1 / 2) ≤ 1 := Real.rpow_le_one hn.le hw1 (by linarith)
      have h3 : Real.exp (π * |w.im|) ≤ Real.exp π :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      calc ‖w‖ * ‖w ^ (w - 1 / 2)‖ ≤ ‖w‖ * (‖w‖ ^ (w.re - 1 / 2) * Real.exp (π * |w.im|)) :=
            mul_le_mul_of_nonneg_left hpow hn.le
        _ = ‖w‖ ^ (w.re + 1 / 2) * Real.exp (π * |w.im|) := by rw [← h1]; ring
        _ ≤ 1 * Real.exp π := by gcongr
        _ = Real.exp π := one_mul _
    have hG : ‖(Gamma (w + 1))⁻¹‖ ≤ max M₂ 1 := by
      have := hM₂ w (by simpa using hw1)
      simp only [Function.comp_apply] at this
      exact this.trans (le_max_left _ _)
    rw [e, norm_mul, norm_mul, norm_mul, hsqrt]
    calc Real.sqrt (2 * π) * ‖cexp (-w)‖ * ‖w * w ^ (w - 1 / 2)‖ * ‖(Gamma (w + 1))⁻¹‖
        ≤ Real.sqrt (2 * π) * Real.exp 1 * Real.exp π * max M₂ 1 := by
          gcongr
          exact hexpnw.trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
      _ ≤ C := by
          rw [hC]
          have : 0 ≤ (max M₁ 1) / Real.sqrt (2 * π) * Real.exp 1 * Real.exp 1 * Real.exp π := by
            positivity
          linarith

/-! ### The reflection identity on the imaginary axis -/

theorem log_ofReal_mul_I {t : ℝ} (ht : 0 < t) : Complex.log (t * I) = Real.log t + π / 2 * I := by
  rw [log_ofReal_mul ht I_ne_zero, log_I]

theorem log_ofReal_mul_neg_I {t : ℝ} (ht : 0 < t) :
    Complex.log (t * -I) = Real.log t - π / 2 * I := by
  rw [log_ofReal_mul ht (neg_ne_zero.mpr I_ne_zero), log_neg_I]; ring

/-- `Γ*(it) Γ*(−it) = 1/(1 − e^{−2πt})` for `t > 0`. -/
theorem scaledGamma_mul_scaledGamma_neg {t : ℝ} (ht : 0 < t) :
    scaledGamma (t * I) * scaledGamma (-(t * I)) = 1 / (1 - cexp (-(2 * π * t))) := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have ht0 : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht.ne') I_ne_zero
  have htn : -((t : ℂ) * I) ≠ 0 := neg_ne_zero.mpr ht0
  -- `Γ(it) Γ(−it) = π/(t sinh(πt))`
  have hrefl := Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hG1 : Gamma (1 - (t : ℂ) * I) = -((t : ℂ) * I) * Gamma (-((t : ℂ) * I)) := by
    rw [show 1 - (t : ℂ) * I = -((t : ℂ) * I) + 1 by ring, Gamma_add_one _ htn]
  have hsin : Complex.sin (π * ((t : ℂ) * I)) = Real.sinh (π * t) * I := by
    rw [show (π : ℂ) * ((t : ℂ) * I) = ((π * t : ℝ) : ℂ) * I by push_cast; ring, sin_mul_I,
      ← ofReal_sinh]
  have hsinh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  rw [hG1, hsin] at hrefl
  have hGG : Gamma ((t : ℂ) * I) * Gamma (-((t : ℂ) * I)) = π / (t * Real.sinh (π * t)) := by
    have hsI : (Real.sinh (π * t) : ℂ) * I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hsinh.ne') I_ne_zero
    have : Gamma ((t : ℂ) * I) * Gamma (-((t : ℂ) * I)) * (-((t : ℂ) * I)) =
        π / ((Real.sinh (π * t) : ℂ) * I) := by rw [← hrefl]; ring
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast ht.ne') (by exact_mod_cast hsinh.ne'))]
    rw [eq_div_iff hsI] at this
    linear_combination this + (Gamma ((t : ℂ) * I) * Gamma (-((t : ℂ) * I)) * t *
      (Real.sinh (π * t) : ℂ)) * I_sq
  -- the powers
  have hp1 : ((t : ℂ) * I) ^ ((t : ℂ) * I - 1 / 2) =
      cexp ((Real.log t + π / 2 * I) * ((t : ℂ) * I - 1 / 2)) := by
    rw [cpow_def_of_ne_zero ht0, log_ofReal_mul_I ht]
  have hp2 : (-((t : ℂ) * I)) ^ (-((t : ℂ) * I) - 1 / 2) =
      cexp ((Real.log t - π / 2 * I) * (-((t : ℂ) * I) - 1 / 2)) := by
    rw [cpow_def_of_ne_zero htn, show -((t : ℂ) * I) = (t : ℂ) * -I by ring,
      log_ofReal_mul_neg_I ht]
  unfold scaledGamma
  rw [hp1, hp2]
  have hden : ((Real.sqrt (2 * π) : ℂ) * cexp (-((t : ℂ) * I)) *
      cexp ((Real.log t + π / 2 * I) * ((t : ℂ) * I - 1 / 2))) *
      ((Real.sqrt (2 * π) : ℂ) * cexp (-(-((t : ℂ) * I))) *
      cexp ((Real.log t - π / 2 * I) * (-((t : ℂ) * I) - 1 / 2))) =
      2 * π * cexp (-(π * t)) / t := by
    have hsq : ((Real.sqrt (2 * π) : ℝ) : ℂ) * (Real.sqrt (2 * π) : ℝ) = 2 * π := by
      rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
    have he : cexp (-((t : ℂ) * I)) * cexp (-(-((t : ℂ) * I))) *
        cexp ((Real.log t + π / 2 * I) * ((t : ℂ) * I - 1 / 2)) *
        cexp ((Real.log t - π / 2 * I) * (-((t : ℂ) * I) - 1 / 2)) =
        cexp (-(π * t)) / t := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      have : -((t : ℂ) * I) + -(-((t : ℂ) * I)) + (Real.log t + π / 2 * I) * ((t : ℂ) * I - 1 / 2) +
          (Real.log t - π / 2 * I) * (-((t : ℂ) * I) - 1 / 2) = -(π * t) - Real.log t := by
        ring_nf; rw [I_sq]; ring
      rw [this, Complex.exp_sub, ofReal_log ht.le, Complex.exp_log
        (ofReal_ne_zero.mpr ht.ne')]
    calc _ = (((Real.sqrt (2 * π) : ℝ) : ℂ) * (Real.sqrt (2 * π) : ℝ)) *
          (cexp (-((t : ℂ) * I)) * cexp (-(-((t : ℂ) * I))) *
          cexp ((Real.log t + π / 2 * I) * ((t : ℂ) * I - 1 / 2)) *
          cexp ((Real.log t - π / 2 * I) * (-((t : ℂ) * I) - 1 / 2))) := by ring
      _ = _ := by rw [hsq, he]; ring
  rw [div_mul_div_comm, hGG, hden]
  have hE : cexp (-(π * (t : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hsh : (Real.sinh (π * t) : ℂ) = (cexp (π * t) - cexp (-(π * t))) / 2 := by
    rw [ofReal_sinh, Complex.sinh]; push_cast; ring_nf
  have h2 : cexp (-(2 * π * (t : ℂ))) = cexp (-(π * t)) * cexp (-(π * t)) := by
    rw [← Complex.exp_add]; ring_nf
  have hm : cexp (π * (t : ℂ)) * cexp (-(π * t)) = 1 := by rw [← Complex.exp_add]; simp
  have key : 2 * (Real.sinh (π * t) : ℂ) * cexp (-(π * t)) = 1 - cexp (-(2 * π * t)) := by
    rw [hsh, h2]; linear_combination hm
  have hsh0 : (Real.sinh (π * t) : ℂ) ≠ 0 := by exact_mod_cast hsinh.ne'
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hπ' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
  rw [← key]
  field_simp

end Azurite.DLMF
