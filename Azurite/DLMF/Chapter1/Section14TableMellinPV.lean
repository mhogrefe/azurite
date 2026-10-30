/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableMellinLog

/-!
# DLMF Table 1.14.5, rows 3 and 6: `1/(1 − x)` and `ln|(1 + x)/(1 − x)|`

* `mellin_log_abs_one_sub`: `𝓜[ln|1 − x|](s) = π cot(sπ)/s` (`−1 < ℜs < 0`), the limit `θ → π` of
  the average of row 5 at `a = e^{±iθ}` (`mellin_log_norm_one_add_cexp`), by dominated
  convergence with `|ln|1 + e^{iθ}x|| ≤ |ln|1 − x|| + ln(1 + x)`.
* Row 6 (`dlmf_table_1_14_5_r6`): `ln|(1 + x)/(1 − x)| = ln(1 + x) − ln|1 − x|` gives the row for
  `ℜs < 0` (`_r6_left`); then `s · 𝓜(s)` and `π tan(sπ/2)` are analytic on `−1 < ℜs < 1` and
  agree there by the identity theorem. Stated for `s ≠ 0`, where DLMF's right side is defined.
* Row 3 (`dlmf_table_1_14_5_r3`): the integral exists only as a principal value; it is stated
  as `lim_{ε→0+} (∫_0^{1−ε} + ∫_{1+ε}^∞) x^{s−1}/(1 − x) dx = π cot(sπ)`. By parts against
  `ln|1 − x|` on both sides of `x = 1`, this reduces to `mellin_log_abs_one_sub` at `s − 1`; the
  boundary terms `((1 + ε)^{s−1} − (1 − ε)^{s−1}) ln ε` vanish.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-! ### `𝓜[ln|1 − x|](s) = π cot(πs)/s` as the limit `θ → π` of row 5 -/

theorem abs_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (|1 - x|)| ≤ 2 * x := by
  have h1 : 0 < 1 - x := by linarith
  rw [abs_of_pos h1, abs_of_nonpos (Real.log_nonpos h1.le (by linarith)), ← Real.log_inv]
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  have h2 : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  linarith

theorem log_abs_one_sub_le_log_one_add {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (|1 - x|)| ≤ Real.log (1 + x) := by
  rw [abs_sub_comm, abs_of_pos (by linarith : 0 < x - 1),
    abs_of_nonneg (Real.log_nonneg (by linarith))]
  exact Real.log_le_log (by linarith) (by linarith)

theorem integrableOn_rpow_mul_abs_log_abs_one_sub {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 1) * |Real.log (|1 - x|)|) (Ioi 0) := by
  have hm : Measurable fun x : ℝ => x ^ (σ - 1) * |Real.log (|1 - x|)| := by fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ (IntegrableOn.union ?_ ?_)
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / 2) h1).const_mul 2)
    refine h.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun x hx => ?_))
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc x ^ (σ - 1) * |Real.log (|1 - x|)| ≤ x ^ (σ - 1) * (2 * x) :=
          mul_le_mul_of_nonneg_left (abs_log_one_sub_le hx0.le hx.2) (by positivity)
      _ = 2 * (x ^ (σ - 1) * x) := by ring
      _ = 2 * x ^ σ := by rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
  · have hlog : IntervalIntegrable (fun x : ℝ => Real.log (x - 1)) volume (1 / 2) 2 := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 1 / 2 - 1)
        (b := 2 - 1)).comp_sub_right 1
      simpa using this
    have hc : ContinuousOn (fun x : ℝ => x ^ (σ - 1)) (uIcc (1 / 2) 2) := fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)).mp
      (hlog.abs.continuousOn_mul hc)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only
    rw [Real.log_abs, show (1 : ℝ) - x = -(x - 1) by ring, Real.log_neg_eq_log]
  · refine (integrableOn_rpow_mul_log_one_add h1 h2).mono_set (Ioi_subset_Ioi (by norm_num))
      |>.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun x hx => ?_))
    have hx2 : (2 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (log_abs_one_sub_le_log_one_add hx2.le) (by positivity)

theorem norm_one_add_cexp_mul_bounds (θ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    |1 - x| ≤ ‖1 + cexp (θ * I) * x‖ ∧ ‖1 + cexp (θ * I) * x‖ ≤ 1 + x := by
  have he : ‖cexp (θ * I) * x‖ = x := by
    rw [norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hx, one_mul]
  refine ⟨?_, ?_⟩
  · have := abs_norm_sub_norm_le (1 : ℂ) (-(cexp (θ * I) * x))
    rwa [norm_one, norm_neg, he, sub_neg_eq_add] at this
  · have := norm_add_le (1 : ℂ) (cexp (θ * I) * x)
    rwa [norm_one, he] at this

theorem abs_log_norm_one_add_cexp_le (θ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≠ 1) :
    |Real.log ‖1 + cexp (θ * I) * x‖| ≤ |Real.log (|1 - x|)| + Real.log (1 + x) := by
  obtain ⟨hl, hu⟩ := norm_one_add_cexp_mul_bounds θ hx
  have hpos : 0 < |1 - x| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx1))
  have hy : 0 < ‖1 + cexp (θ * I) * x‖ := hpos.trans_le hl
  have h1 := Real.log_le_log hy hu
  have h2 := Real.log_le_log hpos hl
  have h3 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log (|1 - x|)), le_abs_self (Real.log (|1 - x|))]

theorem one_add_cexp_neg_eq_conj (θ x : ℝ) :
    1 + cexp ((-θ : ℝ) * I) * x = conj (1 + cexp (θ * I) * x) := by
  rw [map_add, map_one, map_mul, conj_ofReal, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I]
  push_cast; ring_nf

theorem log_add_log_conj_eq {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) {x : ℝ} (hx : 0 ≤ x) :
    1 / 2 * Complex.log (1 + cexp (θ * I) * x) + 1 / 2 * Complex.log (1 + cexp ((-θ : ℝ) * I) * x) =
      ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) : ℂ) := by
  have hslit := one_add_mul_mem_slitPlane (cexp_mul_I_mem_slitPlane h1 h2) hx
  have harg := (mem_slitPlane_iff_arg.mp hslit).1
  rw [one_add_cexp_neg_eq_conj, Complex.log_conj _ harg, ← mul_add, Complex.add_conj, log_re]
  push_cast; ring

theorem cexp_mul_I_cpow' {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) (s : ℂ) :
    (cexp (θ * I) ^ s)⁻¹ = cexp (-(s * θ) * I) := by
  rw [← cpow_neg, cexp_mul_I_cpow h1 h2]

/-- `𝓜[ln|1 + e^{iθ}x|](s) = π cos(sθ)/(s sin(sπ))` (`−π < θ < π`, `−1 < ℜs < 0`), the average of
row 5 at `a = e^{±iθ}`. -/
theorem mellin_log_norm_one_add_cexp {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) {s : ℂ}
    (hs1 : -1 < s.re) (hs2 : s.re < 0) :
    mellin (fun x : ℝ => ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) : ℂ)) s =
      π * Complex.cos (s * θ) / (s * Complex.sin (s * π)) := by
  have h1' : -π < -θ := by linarith
  have h2' : -θ < π := by linarith
  have hc1 : MellinConvergent (fun x : ℝ => 1 / 2 * Complex.log (1 + cexp (θ * I) * x)) s := by
    simpa only [smul_eq_mul] using (mellinConvergent_log_one_add_mul
      (cexp_mul_I_mem_slitPlane h1 h2) hs1 hs2).const_smul (1 / 2 : ℂ)
  have hc2 : MellinConvergent
      (fun x : ℝ => 1 / 2 * Complex.log (1 + cexp ((-θ : ℝ) * I) * x)) s := by
    simpa only [smul_eq_mul] using (mellinConvergent_log_one_add_mul
      (cexp_mul_I_mem_slitPlane h1' h2') hs1 hs2).const_smul (1 / 2 : ℂ)
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      rw [← log_add_log_conj_eq h1 h2 (le_of_lt hx)]), ← mellin, mellin_add' hc1 hc2,
    mellin_const_mul', mellin_const_mul',
    dlmf_table_1_14_5_r5 (cexp_mul_I_mem_slitPlane h1 h2) hs1 hs2,
    dlmf_table_1_14_5_r5 (cexp_mul_I_mem_slitPlane h1' h2') hs1 hs2]
  have e : ∀ z : ℂ, π / Complex.sin (s * π) / (s * z) = π / (s * Complex.sin (s * π)) * z⁻¹ :=
    fun z => by ring
  rw [e, e, cexp_mul_I_cpow' h1 h2, cexp_mul_I_cpow' h1' h2', Complex.cos]
  push_cast
  ring_nf

/-- `𝓜[ln|1 − x|](s) = π cot(sπ)/s` for `−1 < ℜs < 0`: the limit `θ → π` of
`mellin_log_norm_one_add_cexp`, by dominated convergence with
`|ln|1 + e^{iθ}x|| ≤ |ln|1 − x|| + ln(1 + x)`. -/
theorem mellin_log_abs_one_sub {s : ℂ} (hs1 : -1 < s.re) (hs2 : s.re < 0) :
    mellin (fun x : ℝ => ((Real.log (|1 - x|) : ℝ) : ℂ)) s =
      π * Complex.cos (s * π) / (s * Complex.sin (s * π)) := by
  have hbI : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * (|Real.log (|1 - x|)| + Real.log (1 + x)))
      (Ioi 0) := by
    simp_rw [mul_add]
    exact (integrableOn_rpow_mul_abs_log_abs_one_sub hs1 hs2).add
      (integrableOn_rpow_mul_log_one_add hs1 hs2)
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), x ≠ 1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  have hlim : Tendsto (fun θ : ℝ => mellin (fun x : ℝ => ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) :
      ℂ)) s) (𝓝[<] π) (𝓝 (mellin (fun x : ℝ => ((Real.log (|1 - x|) : ℝ) : ℂ)) s)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => x ^ (s.re - 1) * (|Real.log (|1 - x|)| + Real.log (1 + x)))
      (Eventually.of_forall fun θ => ?_) (Eventually.of_forall fun θ => ?_) hbI ?_
    · exact (by fun_prop : Measurable fun x : ℝ =>
        (x : ℂ) ^ (s - 1) • ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) : ℂ)).aestronglyMeasurable
    · filter_upwards [hae, self_mem_ae_restrict measurableSet_Ioi] with x hx1 hx
      have hx0 : (0 : ℝ) < x := hx
      rw [smul_eq_mul, norm_cpow_mul_le hx0, sub_re, one_re, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_log_norm_one_add_cexp_le θ hx0.le hx1)
        (Real.rpow_pos_of_pos hx0 _).le
    · filter_upwards [hae] with x hx1
      have hne : ‖1 + cexp ((π : ℝ) * I) * x‖ ≠ 0 := by
        rw [Complex.exp_pi_mul_I, show (1 : ℂ) + -1 * x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
        exact abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx1))
      have hc : ContinuousAt (fun θ : ℝ => (x : ℂ) ^ (s - 1) •
          ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) : ℂ)) π := by
        have hn : ContinuousAt (fun θ : ℝ => ‖1 + cexp (θ * I) * x‖) π := by fun_prop
        have hl : ContinuousAt (fun θ : ℝ => ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) : ℂ)) π :=
          continuous_ofReal.continuousAt.comp' (hn.log hne)
        simp only [smul_eq_mul]
        exact continuousAt_const.mul hl
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio π))
      convert this using 2
      rw [Complex.exp_pi_mul_I, show (1 : ℂ) + -1 * x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
  have hval : Tendsto (fun θ : ℝ => π * Complex.cos (s * θ) / (s * Complex.sin (s * π)))
      (𝓝[<] π) (𝓝 (π * Complex.cos (s * π) / (s * Complex.sin (s * π)))) :=
    ((by fun_prop : Continuous fun θ : ℝ => π * Complex.cos (s * θ) / (s * Complex.sin (s * π))
      ).tendsto π).mono_left nhdsWithin_le_nhds
  have hev : (fun θ : ℝ => mellin (fun x : ℝ => ((Real.log ‖1 + cexp (θ * I) * x‖ : ℝ) : ℂ)) s)
      =ᶠ[𝓝[<] π] fun θ => π * Complex.cos (s * θ) / (s * Complex.sin (s * π)) := by
    filter_upwards [Ioo_mem_nhdsLT (show -π < π by linarith [Real.pi_pos])] with θ hθ
    exact mellin_log_norm_one_add_cexp hθ.1 hθ.2 hs1 hs2
  exact tendsto_nhds_unique hlim (hval.congr' hev.symm)

/-! ### Row 6: `ln|(1 + x)/(1 − x)|` -/

theorem mellinConvergent_log_abs_one_sub {s : ℂ} (hs1 : -1 < s.re) (hs2 : s.re < 0) :
    MellinConvergent (fun x : ℝ => ((Real.log (|1 - x|) : ℝ) : ℂ)) s := by
  refine (integrableOn_rpow_mul_abs_log_abs_one_sub hs1 hs2).mono'
    ((by fun_prop : Measurable fun x : ℝ =>
      (x : ℂ) ^ (s - 1) • ((Real.log (|1 - x|) : ℝ) : ℂ)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
  rw [smul_eq_mul, norm_cpow_mul_le hx, sub_re, one_re, Complex.norm_real, Real.norm_eq_abs]

theorem abs_log_abs_div_le_small {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    |Real.log (|(1 + x) / (1 - x)|)| ≤ 3 * x := by
  have h1 : 0 < 1 - x := by linarith
  rw [abs_div, abs_of_pos (by linarith : 0 < 1 + x), Real.log_div (by linarith) (by positivity)]
  have ha := abs_log_one_sub_le hx0.le hx
  have hb : Real.log (1 + x) ≤ x := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)]
  have hc := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
  rw [abs_le] at ha ⊢
  constructor <;> linarith

theorem abs_log_abs_div_le_large {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (|(1 + x) / (1 - x)|)| ≤ 4 / x := by
  have hx1 : 0 < x - 1 := by linarith
  have e : |(1 + x) / (1 - x)| = 1 + 2 / (x - 1) := by
    rw [abs_div, abs_of_pos (by linarith : 0 < 1 + x), abs_sub_comm, abs_of_pos hx1]
    field_simp; ring
  have hpos : 0 < 2 / (x - 1) := by positivity
  rw [e, abs_of_nonneg (Real.log_nonneg (by linarith))]
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 2 / (x - 1))
  have h2 : 2 / (x - 1) ≤ 4 / x := by
    rw [div_le_div_iff₀ hx1 (by linarith)]; linarith
  linarith

theorem abs_log_abs_div_le_mid {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) :
    |Real.log (|(1 + x) / (1 - x)|)| ≤ Real.log 3 + |Real.log (|1 - x|)| := by
  rcases eq_or_ne x 1 with rfl | hx1
  · norm_num
    exact Real.log_nonneg (by norm_num)
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  rw [abs_div, abs_of_pos (by linarith : 0 < 1 + x),
    Real.log_div (by linarith) (abs_ne_zero.mpr h1)]
  have hb : Real.log (1 + x) ≤ Real.log 3 := Real.log_le_log (by linarith) (by linarith)
  have hc := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
  have := abs_sub (Real.log (1 + x)) (Real.log (|1 - x|))
  rw [abs_of_nonneg hc] at this
  linarith

theorem mellinConvergent_log_abs_div {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 1) :
    MellinConvergent (fun x : ℝ => ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)) σ := by
  have hm : Measurable fun x : ℝ => (x : ℂ) ^ ((σ : ℂ) - 1) •
      ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ) := by fun_prop
  have hn : ∀ x : ℝ, 0 < x → ‖(x : ℂ) ^ ((σ : ℂ) - 1) •
      ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)‖ =
        x ^ (σ - 1) * |Real.log (|(1 + x) / (1 - x)|)| := fun x hx => by
    rw [smul_eq_mul, norm_cpow_mul_le hx, sub_re, one_re, ofReal_re, Complex.norm_real,
      Real.norm_eq_abs]
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ (IntegrableOn.union ?_ ?_)
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / 2) h1).const_mul 3)
    refine h.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun x hx => ?_))
    have hx0 : 0 < x := hx.1
    rw [hn x hx0]
    calc x ^ (σ - 1) * |Real.log (|(1 + x) / (1 - x)|)| ≤ x ^ (σ - 1) * (3 * x) :=
          mul_le_mul_of_nonneg_left (abs_log_abs_div_le_small hx0 hx.2) (by positivity)
      _ = 3 * (x ^ (σ - 1) * x) := by ring
      _ = 3 * x ^ σ := by rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
  · have hlog : IntervalIntegrable (fun x : ℝ => Real.log (x - 1)) volume (1 / 2) 2 := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 1 / 2 - 1)
        (b := 2 - 1)).comp_sub_right 1
      simpa using this
    have hc : ContinuousOn (fun x : ℝ => x ^ (σ - 1)) (uIcc (1 / 2) 2) := fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
    have hb := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)).mp
      (((intervalIntegrable_const (c := Real.log 3)).add hlog.abs).continuousOn_mul hc)
    refine hb.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun x hx => ?_))
    have hx0 : 0 < x := by linarith [hx.1]
    rw [hn x hx0]
    refine mul_le_mul_of_nonneg_left ((abs_log_abs_div_le_mid hx0 hx.2).trans (le_of_eq ?_))
      (by positivity)
    rw [Real.log_abs, show (1 : ℝ) - x = -(x - 1) by ring, Real.log_neg_eq_log]
  · refine ((integrableOn_Ioi_rpow_of_lt (by linarith : σ - 1 + -1 < -1)
      (by norm_num : (0 : ℝ) < 2)).const_mul 4).mono' hm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    have hx2 : (2 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    rw [hn x hx0, Real.rpow_add hx0, Real.rpow_neg_one]
    calc x ^ (σ - 1) * |Real.log (|(1 + x) / (1 - x)|)| ≤ x ^ (σ - 1) * (4 / x) :=
          mul_le_mul_of_nonneg_left (abs_log_abs_div_le_large hx2.le) (by positivity)
      _ = 4 * (x ^ (σ - 1) * x⁻¹) := by ring

theorem one_sub_cos_div_sin {z : ℂ} (h : Complex.sin z ≠ 0) :
    (1 - Complex.cos z) / Complex.sin z = Complex.tan (z / 2) := by
  have e : z = 2 * (z / 2) := by ring
  rw [e, Complex.sin_two_mul] at h
  have hs : Complex.sin (z / 2) ≠ 0 := fun h' => h (by rw [h']; ring)
  have hc : Complex.cos (z / 2) ≠ 0 := fun h' => h (by rw [h']; ring)
  rw [Complex.tan_eq_sin_div_cos]
  conv_lhs => rw [e, Complex.sin_two_mul, Complex.cos_two_mul]
  field_simp
  linear_combination (-2) * Complex.sin_sq_add_cos_sq (z / 2)

theorem dlmf_table_1_14_5_r6_left {s : ℂ} (hs1 : -1 < s.re) (hs2 : s.re < 0) :
    mellin (fun x : ℝ => ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)) s =
      π * Complex.tan (s * π / 2) / s := by
  have hs : s ≠ 0 := fun h => by rw [h] at hs2; simp at hs2
  have hsin : Complex.sin (s * π) ≠ 0 := by
    rw [mul_comm]; exact sin_pi_mul_ne_zero_of (m := -1) (by simpa using hs1) (by simpa using hs2)
  have hA : MellinConvergent (fun x : ℝ => Complex.log (1 + 1 * x)) s :=
    mellinConvergent_log_one_add_mul (by simp) hs1 hs2
  have hB := mellinConvergent_log_abs_one_sub hs1 hs2
  have e : mellin (fun x : ℝ => ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)) s =
      mellin (fun x : ℝ => Complex.log (1 + 1 * x) - ((Real.log (|1 - x|) : ℝ) : ℂ)) s := by
    rw [mellin, mellin]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume 1),
      self_mem_ae_restrict measurableSet_Ioi] with x hx1 hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [one_mul]
    rw [abs_div, abs_of_pos (by linarith : 0 < 1 + x), Real.log_div (by linarith)
      (abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx1))), ofReal_sub,
      show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith)]
  rw [e, mellin_sub' hA hB, dlmf_table_1_14_5_r5 (by simp) hs1 hs2, mellin_log_abs_one_sub hs1 hs2,
    one_cpow, mul_one, show s * π / 2 = (s * π) / 2 by ring, ← one_sub_cos_div_sin hsin]
  field_simp

/-- **Table 1.14.5, row 6**: `𝓜[ln|(1 + x)/(1 − x)|](s) = π tan(sπ/2)/s` (`−1 < ℜs < 1`, `s ≠ 0`; at
`s = 0` the right side is a removable singularity). Proved for `ℜs < 0` from row 5 and
`mellin_log_abs_one_sub`, then continued to the strip. -/
theorem dlmf_table_1_14_5_r6 {s : ℂ} (hs1 : -1 < s.re) (hs2 : s.re < 1) (hs : s ≠ 0) :
    mellin (fun x : ℝ => ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)) s =
      π * Complex.tan (s * π / 2) / s := by
  set U : Set ℂ := {s | s.re ∈ Ioo (-1) 1}
  have hUo : IsOpen U := isOpen_Ioo.preimage continuous_re
  have hUc : IsPreconnected U :=
    ((convex_Ioo (-1 : ℝ) 1).linear_preimage Complex.reLm).isPreconnected
  have hM := (dlmf_1_14_iv_analytic (a := -1) (b := 1)
    (fun σ hσ => mellinConvergent_log_abs_div hσ.1 hσ.2)).2
  have hcos : ∀ z ∈ U, Complex.cos (z * π / 2) ≠ 0 := fun z hz h => by
    rw [Complex.cos_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hz' : z = 2 * k + 1 := mul_right_cancel₀ hπ (by linear_combination 2 * hk)
    have hre : z.re = 2 * k + 1 := by rw [hz']; simp
    have h1 := hz.1; have h2 := hz.2
    rw [hre] at h1 h2
    have : -1 < 2 * k + 1 := by exact_mod_cast h1
    have : 2 * k + 1 < 1 := by exact_mod_cast h2
    omega
  have hf : AnalyticOnNhd ℂ (fun z => z * mellin
      (fun x : ℝ => ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)) z) U :=
    fun z hz => analyticAt_id.mul (hM z hz)
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => π * Complex.tan (z * π / 2)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hd : DifferentiableAt ℂ (fun z : ℂ => Complex.tan (z * π / 2)) z :=
      DifferentiableAt.comp (g := Complex.tan) z (Complex.differentiableAt_tan.mpr (hcos z hz))
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z * π / 2) z)
    exact (hd.const_mul _).differentiableWithinAt
  have hz0 : (-1 / 2 : ℂ) ∈ U := by simp [U]; norm_num
  have hev : (fun z => z * mellin (fun x : ℝ => ((Real.log (|(1 + x) / (1 - x)|) : ℝ) : ℂ)) z)
      =ᶠ[𝓝 (-1 / 2 : ℂ)] fun z : ℂ => π * Complex.tan (z * π / 2) := by
    have hV : {z : ℂ | z.re ∈ Ioo (-1) 0} ∈ 𝓝 (-1 / 2 : ℂ) :=
      (isOpen_Ioo.preimage continuous_re).mem_nhds (by simp; norm_num)
    filter_upwards [hV] with z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    rw [dlmf_table_1_14_5_r6_left hz.1 hz.2]
    field_simp
  have := hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz0 hev ⟨hs1, hs2⟩
  simp only at this
  rw [eq_div_iff hs, mul_comm, this]

/-! ### Row 3: the principal value of `∫_0^∞ x^{s−1}/(1 − x) dx` -/

theorem hasDerivAt_log_abs_one_sub {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fun x : ℝ => ((Real.log (|1 - x|) : ℝ) : ℂ)) (-(1 / (1 - (x : ℂ)))) x := by
  have hne : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hne
  simp only [Pi.sub_apply, id, zero_sub] at h
  have e : (fun x : ℝ => Real.log (|1 - x|)) = fun x => Real.log (1 - x) :=
    funext fun _ => Real.log_abs _
  have e2 : (fun x : ℝ => ((Real.log (|1 - x|) : ℝ) : ℂ)) = fun x => ((Real.log (1 - x) : ℝ) : ℂ) :=
    funext fun x => by rw [Real.log_abs]
  rw [e2]
  refine h.ofReal_comp.congr_deriv ?_
  have : (1 : ℂ) - x ≠ 0 := by exact_mod_cast hne
  push_cast; field_simp

theorem hasDerivAt_cpow_mul_log {w : ℂ} (hw : w ≠ 0) {x : ℝ} (hx0 : 0 < x) (hx : x ≠ 1) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ w * ((Real.log (|1 - x|) : ℝ) : ℂ))
      (w * (x : ℂ) ^ (w - 1) * ((Real.log (|1 - x|) : ℝ) : ℂ) - (x : ℂ) ^ w / (1 - x)) x := by
  refine ((hasDerivAt_ofReal_cpow_const hx0.ne' hw).mul (hasDerivAt_log_abs_one_sub hx))
    |>.congr_deriv ?_
  ring

theorem norm_cpow_mul_log_le {w : ℂ} {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    ‖(x : ℂ) ^ w * ((Real.log (|1 - x|) : ℝ) : ℂ)‖ ≤ 2 * x ^ (w.re + 1) := by
  rw [norm_cpow_mul_le hx0, Complex.norm_real, Real.norm_eq_abs, Real.rpow_add_one hx0.ne']
  calc x ^ w.re * |Real.log (|1 - x|)| ≤ x ^ w.re * (2 * x) :=
        mul_le_mul_of_nonneg_left (abs_log_one_sub_le hx0.le hx) (by positivity)
    _ = _ := by ring

/-- **Table 1.14.5, row 3**: the principal value `PV ∫_0^∞ x^{s−1}/(1 − x) dx = π cot(sπ)`
(`0 < ℜs < 1`), as `lim_{ε→0+} (∫_0^{1−ε} + ∫_{1+ε}^∞)`. By parts against `ln|1 − x|`, this reduces
to `mellin_log_abs_one_sub` at `s − 1`. -/
theorem dlmf_table_1_14_5_r3 {s : ℂ} (hs1 : 0 < s.re) (hs2 : s.re < 1) :
    Tendsto (fun ε : ℝ => (∫ x in Ioc 0 (1 - ε), (x : ℂ) ^ (s - 1) / (1 - x)) +
        ∫ x in Ioi (1 + ε), (x : ℂ) ^ (s - 1) / (1 - x)) (𝓝[>] 0)
      (𝓝 (π * Complex.cot (s * π))) := by
  set w := s - 1 with hw_def
  have hw1 : -1 < w.re := by simp [w]; linarith
  have hw2 : w.re < 0 := by simp [w]; linarith
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw2; simp at hw2
  set ℓ : ℝ → ℂ := fun x => ((Real.log (|1 - x|) : ℝ) : ℂ)
  set F : ℝ → ℂ := fun x => (x : ℂ) ^ w * ℓ x
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * ℓ x
  have hgI : IntegrableOn g (Ioi 0) := by
    have := mellinConvergent_log_abs_one_sub hw1 hw2
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    simp only [g, ℓ, smul_eq_mul]
  have hM : ∫ x in Ioi (0 : ℝ), g x = π * Complex.cos (w * π) / (w * Complex.sin (w * π)) := by
    rw [← mellin_log_abs_one_sub hw1 hw2, mellin]
    rfl
  -- the two one-sided identities
  have hA : ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), (∫ x in Ioc 0 (1 - ε), (x : ℂ) ^ w / (1 - x)) =
      w * (∫ x in Ioc 0 (1 - ε), g x) - F (1 - ε) := fun ε hε => by
    have hle : (0 : ℝ) ≤ 1 - ε := by linarith [hε.2]
    have hq : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w / (1 - x)) volume 0 (1 - ε) := by
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr ?_
      have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
        ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - ε) hw1).const_mul ε⁻¹)
      refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_))
      · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioc
        have h1 : (1 : ℂ) - x ≠ 0 := by
          have : x < 1 := by linarith [hx.2, hε.1]
          exact_mod_cast (sub_ne_zero.mpr (ne_of_gt this))
        exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
          (ofReal_mem_slitPlane.mpr hx.1)).div (by fun_prop) h1).continuousWithinAt
      · have hx0 : 0 < x := hx.1
        have h1x : ε ≤ 1 - x := by linarith [hx.2]
        rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx0, show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith [hε.1]),
          div_le_iff₀ (by linarith [hε.1]), mul_comm ε⁻¹, mul_assoc]
        refine le_mul_of_one_le_right (by positivity) ?_
        rw [inv_mul_eq_div, le_div_iff₀ hε.1, one_mul]; exact h1x
    have hgi : IntervalIntegrable g volume 0 (1 - ε) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr (hgI.mono_set Ioc_subset_Ioi_self)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (f := F)
      (f' := fun x => w * (x : ℂ) ^ (w - 1) * ℓ x - (x : ℂ) ^ w / (1 - x))
      (fun x hx => by
        rcases hx.1.eq_or_lt with rfl | hx0
        · show Tendsto F (𝓝[Icc 0 (1 - ε)] 0) (𝓝 (F 0))
          have hF0 : F 0 = 0 := by simp [F, ℓ]
          rw [hF0]
          have hz := ((tendsto_rpow_add_one_nhdsGT hw1).const_mul 2)
          rw [mul_zero] at hz
          have hz' : Tendsto (fun x : ℝ => 2 * x ^ (w.re + 1)) (𝓝[Icc 0 (1 - ε)] 0) (𝓝 0) := by
            have hc := ((Real.continuousAt_rpow_const 0 (w.re + 1) (Or.inr (by linarith))).tendsto
              |>.const_mul 2)
            rw [Real.zero_rpow (by linarith), mul_zero] at hc
            exact hc.mono_left nhdsWithin_le_nhds
          refine squeeze_zero_norm' ?_ hz'
          filter_upwards [inter_mem_nhdsWithin (Icc 0 (1 - ε))
            (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with y hy
          rcases hy.1.1.eq_or_lt with rfl | hy0
          · simp [F, ℓ]; positivity
          · exact norm_cpow_mul_log_le hy0 hy.2.le
        · have hx1 : x ≠ 1 := by linarith [hx.2, hε.1]
          exact (hasDerivAt_cpow_mul_log hw0 hx0 hx1).continuousAt.continuousWithinAt)
      (fun x hx => hasDerivAt_cpow_mul_log hw0 hx.1 (by linarith [hx.2, hε.1]))
      (((hgi.const_mul w).congr fun x _ => by simp only [g]; ring).sub hq)
    rw [intervalIntegral.integral_sub ((hgi.const_mul w).congr fun x _ => by simp only [g]; ring)
      hq, intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle] at hFTC
    have hF0 : F 0 = 0 := by simp [F, ℓ]
    rw [hF0, sub_zero] at hFTC
    have e : ∫ x in Ioc 0 (1 - ε), w * (x : ℂ) ^ (w - 1) * ℓ x = w * ∫ x in Ioc 0 (1 - ε), g x := by
      rw [← integral_const_mul]; simp only [g]; simp_rw [mul_assoc]
    rw [e] at hFTC
    linear_combination -hFTC
  have hB : ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), (∫ x in Ioi (1 + ε), (x : ℂ) ^ w / (1 - x)) =
      w * (∫ x in Ioi (1 + ε), g x) + F (1 + ε) := fun ε hε => by
    have hε0 := hε.1
    have hq : IntegrableOn (fun x : ℝ => (x : ℂ) ^ w / (1 - x)) (Ioi (1 + ε)) := by
      refine ((integrableOn_Ioi_rpow_of_lt (by linarith : w.re - 1 < -1)
        (by linarith : (0 : ℝ) < 1 + ε)).const_mul ((1 + ε) / ε)).mono' ?_
        ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
      · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
        have hx' : (1 : ℝ) + ε < x := hx
        have h1 : (1 : ℂ) - (x : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast (ne_of_lt (by linarith : (1 : ℝ) < x))
        have hc : ContinuousAt (fun y : ℝ => (y : ℂ) ^ w / (1 - (y : ℂ))) x :=
          ((continuous_ofReal.continuousAt).cpow continuousAt_const
            (ofReal_mem_slitPlane.mpr (show (0 : ℝ) < x by linarith))).div
            (by fun_prop) h1
        exact hc.continuousWithinAt
      · have hx' : (1 : ℝ) + ε < x := hx
        have hx0 : 0 < x := by linarith
        rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx0, show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
          abs_of_pos (by linarith : 0 < x - 1), div_le_iff₀ (by linarith : 0 < x - 1),
          Real.rpow_sub_one hx0.ne']
        have : ε * x ≤ (1 + ε) * (x - 1) := by nlinarith
        calc x ^ w.re = (1 + ε) / ε * (x ^ w.re / x) * (ε * x / (1 + ε)) := by
              field_simp
          _ ≤ (1 + ε) / ε * (x ^ w.re / x) * (x - 1) := by
              gcongr
              rw [div_le_iff₀ (by linarith)]; linarith
    have hgi : IntegrableOn g (Ioi (1 + ε)) := hgI.mono_set (Ioi_subset_Ioi (by linarith))
    have hF : Tendsto F atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_log_one_add_atTop hw2)
      filter_upwards [eventually_ge_atTop 2] with x hx
      have hx0 : 0 < x := by linarith
      simp only [F, ℓ]
      rw [norm_cpow_mul_le hx0, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (log_abs_one_sub_le_log_one_add hx) (by positivity)
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 1 + ε) (f := F)
      (f' := fun x => w * (x : ℂ) ^ (w - 1) * ℓ x - (x : ℂ) ^ w / (1 - x))
      (hasDerivAt_cpow_mul_log hw0 (by linarith) (by linarith)).continuousAt.continuousWithinAt
      (fun x hx => hasDerivAt_cpow_mul_log hw0 (by linarith [show 1 + ε < x from hx])
        (by linarith [show 1 + ε < x from hx]))
      ((IntegrableOn.congr_fun (hgi.const_mul w) (fun x _ => by simp only [g]; ring)
        measurableSet_Ioi).sub hq)
      hF
    rw [integral_sub (IntegrableOn.congr_fun (hgi.const_mul w) (fun x _ => by simp only [g]; ring)
      measurableSet_Ioi) hq, zero_sub] at h
    have e : ∫ x in Ioi (1 + ε), w * (x : ℂ) ^ (w - 1) * ℓ x = w * ∫ x in Ioi (1 + ε), g x := by
      rw [← integral_const_mul]; simp only [g]; simp_rw [mul_assoc]
    rw [e] at h
    linear_combination -h
  -- the middle limit
  set T : ℝ → Set ℝ := fun ε => Ioc 0 (1 - ε) ∪ Ioi (1 + ε)
  have hT : ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), (∫ x in Ioc 0 (1 - ε), g x) + (∫ x in Ioi (1 + ε), g x) =
      ∫ x in Ioi (0 : ℝ), (T ε).indicator g x := fun ε hε => by
    have hsub : T ε ⊆ Ioi 0 := by
      rintro x (hx | hx)
      · exact hx.1
      · exact lt_trans (by linarith [hε.1] : (0 : ℝ) < 1 + ε) hx
    rw [setIntegral_indicator (measurableSet_Ioc.union measurableSet_Ioi),
      inter_eq_right.mpr hsub, setIntegral_union _ measurableSet_Ioi
        (hgI.mono_set Ioc_subset_Ioi_self) (hgI.mono_set (Ioi_subset_Ioi (by linarith [hε.1])))]
    exact disjoint_left.mpr fun x hx hx' => by linarith [hx.2, show 1 + ε < x from hx', hε.1]
  have hlim1 : Tendsto (fun ε => ∫ x in Ioi (0 : ℝ), (T ε).indicator g x) (𝓝[>] 0)
      (𝓝 (∫ x in Ioi (0 : ℝ), g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖)
      (Eventually.of_forall fun ε => hgI.aestronglyMeasurable.indicator
        (measurableSet_Ioc.union measurableSet_Ioi))
      (Eventually.of_forall fun ε => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
      hgI.norm ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume 1),
      self_mem_ae_restrict measurableSet_Ioi] with x hx1 hx
    have hd : 0 < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr hx1)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    have hxT : x ∈ T ε := by
      rcases lt_or_gt_of_ne hx1 with h | h
      · left; refine ⟨hx, ?_⟩; rw [abs_of_neg (by linarith)] at hε; linarith [hε.2]
      · right; show 1 + ε < x; rw [abs_of_pos (by linarith)] at hε; linarith [hε.2]
    rw [indicator_of_mem hxT]
  -- the boundary terms
  have hFε : ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ‖F (1 + ε) - F (1 - ε)‖ ≤
      ‖w‖ * (1 / 2) ^ (w.re - 1) * 2 * (ε * |Real.log ε|) := fun ε hε => by
    have hε0 := hε.1
    have hε2 := hε.2
    have hl : ∀ y : ℝ, |1 - y| = ε → ℓ y = ((Real.log ε : ℝ) : ℂ) := fun y hy => by
      simp only [ℓ, hy]
    have hD : (((1 + ε : ℝ) : ℂ) ^ w - ((1 - ε : ℝ) : ℂ) ^ w) =
        ∫ t in (1 - ε)..(1 + ε), w * (t : ℂ) ^ (w - 1) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => (t : ℂ) ^ w)]
      · intro t ht
        rw [uIcc_of_le (by linarith)] at ht
        exact hasDerivAt_ofReal_cpow_const (by linarith [ht.1]) hw0
      · refine ContinuousOn.intervalIntegrable (fun t ht => ?_)
        rw [uIcc_of_le (by linarith)] at ht
        exact (continuousAt_const.mul ((continuous_ofReal.continuousAt).cpow continuousAt_const
          (ofReal_mem_slitPlane.mpr (by linarith [ht.1])))).continuousWithinAt
    have hDb : ‖((1 + ε : ℝ) : ℂ) ^ w - ((1 - ε : ℝ) : ℂ) ^ w‖ ≤
        ‖w‖ * (1 / 2) ^ (w.re - 1) * (2 * ε) := by
      rw [hD]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_).trans
        (le_of_eq (by rw [show 1 + ε - (1 - ε) = 2 * ε by ring, abs_of_pos (by linarith)]))
      rw [uIoc_of_le (by linarith)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (x := 1 / 2) (y := t)
        (z := w.re - 1) (by norm_num) (by linarith [ht.1]) (by linarith)) (norm_nonneg _)
    have e : F (1 + ε) - F (1 - ε) =
        (((1 + ε : ℝ) : ℂ) ^ w - ((1 - ε : ℝ) : ℂ) ^ w) * ((Real.log ε : ℝ) : ℂ) := by
      simp only [F]
      rw [hl (1 + ε) (by rw [show (1 : ℝ) - (1 + ε) = -ε by ring, abs_neg, abs_of_pos hε0]),
        hl (1 - ε) (by rw [show (1 : ℝ) - (1 - ε) = ε by ring, abs_of_pos hε0])]
      push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖((1 + ε : ℝ) : ℂ) ^ w - ((1 - ε : ℝ) : ℂ) ^ w‖ * |Real.log ε| ≤
        ‖w‖ * (1 / 2) ^ (w.re - 1) * (2 * ε) * |Real.log ε| :=
          mul_le_mul_of_nonneg_right hDb (abs_nonneg _)
      _ = _ := by ring
  have hlim2 : Tendsto (fun ε => F (1 + ε) - F (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
    have hml : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have hz := hml.abs.const_mul (‖w‖ * (1 / 2) ^ (w.re - 1) * 2)
    rw [abs_zero, mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    rw [abs_mul, abs_of_pos hε.1]
    exact hFε ε hε
  have hsum := (hlim1.const_mul w).add hlim2
  rw [hM, add_zero] at hsum
  have hv : w * (π * Complex.cos (w * π) / (w * Complex.sin (w * π))) =
      π * Complex.cot (s * π) := by
    rw [Complex.cot_eq_cos_div_sin, hw_def, show (s - 1) * π = s * π - π by ring,
      Complex.cos_sub_pi, Complex.sin_sub_pi]
    have hsin : Complex.sin (s * π) ≠ 0 := by
      rw [mul_comm]; exact sin_pi_mul_ne_zero_of (m := 0) (by simpa using hs1) (by simpa using hs2)
    have : s - 1 ≠ 0 := hw0
    field_simp
  rw [hv] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
  rw [hA ε hε, hB ε hε, ← hT ε hε]
  ring

end Azurite.DLMF
