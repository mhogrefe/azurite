/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5
import Azurite.DLMF.Chapter1.Section14Hilbert
import Azurite.BrentZimmermann.Chapter4.ErrorFunction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# DLMF §3.5(ix): other contour integrals

Heavy cancellation in contour integrals is avoided by deforming the path through a saddle point,
e.g. along a steepest descent path (§2.4(iv)).

**Example** (`erfc` is `BZ.erfc`, `erfc x = (2/√π) ∫ₓ^∞ e^{−u²} du`, 7.2.2 for real `x`):

* 3.5.42 and 3.5.44 (the Bromwich integrals, `Section5ContourBromwich`).
* **3.5.43** `dlmf_3_5_43`: `erfc λ ∼ e^{−λ²}/(√π λ)` (from the bounds of 7.12.1).
* The saddle point `t = 1` of `t − 2√t` (`erfcPhase`, `erfcPhase_saddle`); the steepest descent
  path `ℑ(t − 2√t) = 0` is `r = sec²(θ/2)` in polar coordinates (`erfcPhase_im_eq_zero_iff`, via
  `√(re^{iθ}) = √r e^{iθ/2}`, `cpow_half_polar`); along `t(θ) = sec²(θ/2) e^{iθ}` (`erfcPath`,
  `t′ = t (tan(θ/2) + i)`, `hasDerivAt_erfcPath`) the phase is `−1 − tan²(θ/2)`
  (`erfcPhase_erfcPath`) and the integral of 3.5.44 equals `erfc λ` (`dlmf_3_5_45_path`).
* **3.5.45** `dlmf_3_5_45`: `erfc λ = e^{−λ²}/(2π) ∫_{−π}^{π} e^{−λ² tan²(θ/2)} dθ`, by
  `θ = 2 arctan s` (`integral_erfcPathIntegrand`) and
  `∫_ℝ e^{−λ²(1+s²)}/(1+s²) ds = π erfc λ` (`integral_exp_div_one_add_sq`, Fubini).
* The integrand extends to the `2π`-periodic `C^∞` function `e^{λ²} ψ(cos²(θ/2)/λ²)`,
  `ψ = expNegInvGlue` (`erfcPathExt`, `contDiff_erfcPathExt`, `periodic_erfcPathExt`,
  `erfcPathExt_eq`, `erfcPathExt_pi`), so by 3.5.4 the composite trapezoidal error is `O(hᵏ)` for
  every `k` (`erfcPath_trapError_isBigO`). Table 3.5.20: `Section5ContourTable`.

**3.5.46** `dlmf_3_5_46`: the Hilbert transform of §1.14(v) (`hilbert`) is the principal value
`(1/π) ⨍ f(t)/(t − x) dt`.

Not formalized: the deformation of the vertical path of 3.5.44 into the steepest descent path by
Cauchy's theorem (both integrals are proved to equal `erfc λ` independently, which gives the
equality); the pointers to Gil et al. (Scorer functions, §9.12), Kress and Martensen (1970) and
the Hankel (§10.22(v)), Kontorovich–Lebedev (§10.43(v)) and Mellin (§1.14(iv)) transforms;
the modification for meromorphic `f`.
-/

open Set Filter Topology MeasureTheory Real

namespace Azurite.DLMF

/-! ### `∫ e^{−λ²(1+s²)}/(1+s²) ds = π erfc λ` -/

theorem integral_Ioi_two_mul_exp_neg {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    ∫ u in Ioi a, 2 * u * Real.exp (-(c * u ^ 2)) = Real.exp (-(c * a ^ 2)) / c := by
  have hd : ∀ u ∈ Ioi a, HasDerivAt (fun u => -Real.exp (-(c * u ^ 2)) / c)
      (2 * u * Real.exp (-(c * u ^ 2))) u := fun u _ => by
    have h1 : HasDerivAt (fun u => -(c * u ^ 2)) (-(c * (2 * u))) u := by
      convert ((hasDerivAt_pow 2 u).const_mul c).neg using 1; simp
    convert (h1.exp.neg).div_const c using 1
    field_simp
  have ht : Tendsto (fun u => -Real.exp (-(c * u ^ 2)) / c) atTop (𝓝 (-0 / c)) := by
    refine ((Real.tendsto_exp_atBot.comp ?_).neg).div_const c
    exact tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hc)
  have hcont : Continuous fun u => -Real.exp (-(c * u ^ 2)) / c := by fun_prop
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (l := 0) hcont.continuousWithinAt hd]
  · ring
  · exact fun u hu => by have : 0 < u := lt_of_le_of_lt ha hu; positivity
  · simpa using ht

theorem integral_two_mul_exp_neg_one_add_sq {u : ℝ} (hu : 0 < u) :
    ∫ s : ℝ, 2 * u * Real.exp (-((1 + s ^ 2) * u ^ 2)) = 2 * √π * Real.exp (-u ^ 2) := by
  have e : ∀ s : ℝ, 2 * u * Real.exp (-((1 + s ^ 2) * u ^ 2)) =
      2 * u * Real.exp (-u ^ 2) * Real.exp (-(u ^ 2) * s ^ 2) := fun s => by
    rw [mul_assoc (2 * u), ← Real.exp_add]; ring_nf
  simp only [e]
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hu.le]
  field_simp

theorem integrable_two_mul_exp_neg_one_add_sq {u : ℝ} (hu : 0 < u) :
    Integrable fun s : ℝ => 2 * u * Real.exp (-((1 + s ^ 2) * u ^ 2)) := by
  have e : ∀ s : ℝ, 2 * u * Real.exp (-((1 + s ^ 2) * u ^ 2)) =
      2 * u * Real.exp (-u ^ 2) * Real.exp (-(u ^ 2) * s ^ 2) := fun s => by
    rw [mul_assoc (2 * u), ← Real.exp_add]; ring_nf
  simp only [e]
  exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _

/-- `∫_ℝ e^{−λ²(1+s²)}/(1+s²) ds = π erfc λ` (`λ > 0`), by writing the integrand as
`∫_λ^∞ 2u e^{−u²(1+s²)} du` and exchanging the integrations. -/
theorem integral_exp_div_one_add_sq {lam : ℝ} (hlam : 0 < lam) :
    ∫ s : ℝ, Real.exp (-((1 + s ^ 2) * lam ^ 2)) / (1 + s ^ 2) = π * BZ.erfc lam := by
  set F : ℝ → ℝ → ℝ := fun s u => 2 * u * Real.exp (-((1 + s ^ 2) * u ^ 2))
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi lam))) := by
    refine (integrable_prod_iff' ?_).mpr ⟨?_, ?_⟩
    · exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact integrable_two_mul_exp_neg_one_add_sq (lt_trans hlam hu)
    · refine Integrable.congr ((BZ.integrableOn_exp_neg_sq_Ioi lam).const_mul (2 * √π)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := lt_trans hlam hu
      rw [← integral_two_mul_exp_neg_one_add_sq hu0]
      symm
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [F, Function.uncurry_apply_pair, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
  have h1 : ∀ s : ℝ, ∫ u in Ioi lam, F s u = Real.exp (-((1 + s ^ 2) * lam ^ 2)) / (1 + s ^ 2) :=
    fun s => integral_Ioi_two_mul_exp_neg (by positivity) hlam.le
  have h2 := integral_integral_swap hF
  simp only [h1] at h2
  rw [h2]
  have h3 : ∫ u in Ioi lam, ∫ s : ℝ, F s u = ∫ u in Ioi lam, 2 * √π * Real.exp (-u ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu =>
      integral_two_mul_exp_neg_one_add_sq (lt_trans hlam hu)
  rw [h3, integral_const_mul, BZ.erfc, BZ.gaussTail]
  simp only [mul_zero, pow_zero, div_one]
  have hπ : √π * √π = π := Real.mul_self_sqrt pi_pos.le
  have hπ0 : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  field_simp
  linear_combination (∫ u in Ioi lam, Real.exp (-u ^ 2)) * hπ

/-! ### 3.5.45 -/

/-- The integrand `e^{−λ² tan²(θ/2)}` of 3.5.45. -/
noncomputable def erfcPathIntegrand (lam θ : ℝ) : ℝ := Real.exp (-(lam ^ 2 * Real.tan (θ / 2) ^ 2))

theorem image_two_mul_arctan : (fun s => 2 * Real.arctan s) '' univ = Ioo (-π) π := by
  ext θ
  simp only [image_univ, mem_range, mem_Ioo]
  constructor
  · rintro ⟨s, rfl⟩
    constructor <;> linarith [Real.neg_pi_div_two_lt_arctan s, Real.arctan_lt_pi_div_two s]
  · rintro ⟨h1, h2⟩
    exact ⟨Real.tan (θ / 2), by
      rw [Real.arctan_tan (by linarith) (by linarith)]; ring⟩

/-- `∫_{−π}^{π} e^{−λ² tan²(θ/2)} dθ = ∫_ℝ 2 e^{−λ² s²}/(1 + s²) ds` (`θ = 2 arctan s`). -/
theorem integral_erfcPathIntegrand (lam : ℝ) :
    ∫ θ in (-π)..π, erfcPathIntegrand lam θ =
      ∫ s : ℝ, 2 / (1 + s ^ 2) * Real.exp (-(lam ^ 2 * s ^ 2)) := by
  rw [intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo,
    ← image_two_mul_arctan, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (f' := fun s => 2 * (1 / (1 + s ^ 2)))
      (fun s _ => ((Real.hasDerivAt_arctan s).const_mul 2).hasDerivWithinAt)
      (fun a _ b _ h => Real.arctan_injective (by simpa using h)), Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [erfcPathIntegrand, smul_eq_mul]
  rw [abs_of_pos (by positivity), mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan]
  ring

/-- **DLMF 3.5.45**: `erfc λ = e^{−λ²}/(2π) ∫_{−π}^{π} e^{−λ² tan²(θ/2)} dθ`, `λ > 0`. -/
theorem dlmf_3_5_45 {lam : ℝ} (hlam : 0 < lam) :
    BZ.erfc lam = Real.exp (-lam ^ 2) / (2 * π) * ∫ θ in (-π)..π, erfcPathIntegrand lam θ := by
  rw [integral_erfcPathIntegrand]
  have e : ∀ s : ℝ, 2 / (1 + s ^ 2) * Real.exp (-(lam ^ 2 * s ^ 2)) =
      2 * Real.exp (lam ^ 2) * (Real.exp (-((1 + s ^ 2) * lam ^ 2)) / (1 + s ^ 2)) := fun s => by
    rw [mul_div_assoc', mul_assoc, ← Real.exp_add]; ring_nf
  simp only [e]
  rw [integral_const_mul, integral_exp_div_one_add_sq hlam]
  have h := Real.exp_add (-lam ^ 2) (lam ^ 2)
  rw [neg_add_cancel, Real.exp_zero] at h
  field_simp
  linear_combination BZ.erfc lam * h

/-! ### The periodic `C^∞` extension and the trapezoidal rule -/

/-- The extension `e^{λ²} ψ(cos²(θ/2)/λ²)` of the integrand of 3.5.45, `ψ(x) = e^{−1/x}` for
`x > 0`, `ψ(x) = 0` otherwise (`expNegInvGlue`). -/
noncomputable def erfcPathExt (lam θ : ℝ) : ℝ :=
  Real.exp (lam ^ 2) * expNegInvGlue (Real.cos (θ / 2) ^ 2 / lam ^ 2)

/-- The extension is `C^∞` on `ℝ`. -/
theorem contDiff_erfcPathExt (lam : ℝ) {n : ℕ∞} : ContDiff ℝ n (erfcPathExt lam) :=
  contDiff_const.mul (expNegInvGlue.contDiff.comp
    (((Real.contDiff_cos.comp (contDiff_id.div_const 2)).pow 2).div_const _))

/-- The extension has period `2π`. -/
theorem periodic_erfcPathExt (lam : ℝ) : Function.Periodic (erfcPathExt lam) (2 * π) :=
  fun θ => by
    unfold erfcPathExt
    rw [show (θ + 2 * π) / 2 = θ / 2 + π by ring, Real.cos_add_pi, neg_sq]

/-- On `(−π, π)` the extension is the integrand of 3.5.45. -/
theorem erfcPathExt_eq {lam θ : ℝ} (hlam : lam ≠ 0) (hθ : θ ∈ Ioo (-π) π) :
    erfcPathExt lam θ = erfcPathIntegrand lam θ := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hl : 0 < lam ^ 2 := by positivity
  unfold erfcPathExt erfcPathIntegrand
  have hpos : ¬ Real.cos (θ / 2) ^ 2 / lam ^ 2 ≤ 0 := not_le.mpr (by positivity)
  simp only [expNegInvGlue, hpos, ↓reduceIte]
  rw [← Real.exp_add, Real.tan_eq_sin_div_cos]
  congr 1
  have hs := Real.sin_sq_add_cos_sq (θ / 2)
  field_simp
  linear_combination hs

/-- The extension vanishes at `±π`. -/
theorem erfcPathExt_pi (lam : ℝ) : erfcPathExt lam π = 0 := by
  simp [erfcPathExt, Real.cos_pi_div_two, expNegInvGlue.zero]

theorem integral_erfcPathExt {lam : ℝ} (hlam : lam ≠ 0) :
    ∫ θ in (-π)..π, erfcPathExt lam θ = ∫ θ in (-π)..π, erfcPathIntegrand lam θ := by
  rw [intervalIntegral.integral_of_le (by linarith [pi_pos]),
    intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun θ hθ => erfcPathExt_eq hlam hθ

/-- "The trapezoidal rule is exceptionally efficient": by 3.5.4 the error of the composite
trapezoidal rule for the extended integrand over a period is `O(hᵏ)` for every `k`. -/
theorem erfcPath_trapError_isBigO (lam : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℕ => trapError (erfcPathExt lam) (-π) π n) =O[atTop]
      fun n : ℕ => ((π - -π) / n) ^ k :=
  dlmf_3_5_4_isBigO (by linarith [pi_pos]) hk (contDiff_erfcPathExt lam)
    (by rw [show π - -π = 2 * π by ring]; exact periodic_erfcPathExt lam)

/-! ### 3.5.43 -/

/-- **DLMF 3.5.43**: `erfc λ ∼ e^{−λ²}/(√π λ)` as `λ → ∞` (from the bounds
`L(1 − 1/(2λ²)) ≤ erfc λ ≤ L` of the expansion 7.12.1, `BZ.leading_mul_le_erfc`). -/
theorem dlmf_3_5_43 :
    Asymptotics.IsEquivalent atTop BZ.erfc fun lam => Real.exp (-lam ^ 2) / (√π * lam) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have hlo : Tendsto (fun lam : ℝ => 1 - 1 / (2 * lam ^ 2)) atTop (𝓝 1) := by
    have : Tendsto (fun lam : ℝ => 1 / (2 * lam ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop two_pos)
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with lam hlam
    have hL : 0 < Real.exp (-lam ^ 2) / (√π * lam) := by
      have := Real.sqrt_pos.mpr pi_pos; positivity
    rw [Pi.div_apply, le_div_iff₀ hL, mul_comm √π]
    linarith [BZ.leading_mul_le_erfc hlam]
  · filter_upwards [eventually_gt_atTop 0] with lam hlam
    have hL : 0 < Real.exp (-lam ^ 2) / (√π * lam) := by
      have := Real.sqrt_pos.mpr pi_pos; positivity
    rw [Pi.div_apply, div_le_iff₀ hL, one_mul, mul_comm √π]
    exact BZ.erfc_le_leading hlam

/-! ### The saddle point and the steepest descent path of 3.5.44 -/

/-- The phase `t − 2√t` of 3.5.44 (principal square root). -/
noncomputable def erfcPhase (t : ℂ) : ℂ := t - 2 * t ^ (1 / 2 : ℂ)

theorem hasDerivAt_erfcPhase {t : ℂ} (ht : t ∈ Complex.slitPlane) :
    HasDerivAt erfcPhase (1 - t ^ (-(1 / 2) : ℂ)) t := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) ht).hasDerivAt.const_mul 2
  show HasDerivAt (fun t : ℂ => t - 2 * t ^ (1 / 2 : ℂ)) _ t
  convert (hasDerivAt_id' t).sub h using 1
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]
  ring

/-- The saddle point of 3.5.44 is `t = 1`. -/
theorem erfcPhase_saddle : HasDerivAt erfcPhase 0 1 := by
  convert hasDerivAt_erfcPhase (by simp : (1 : ℂ) ∈ Complex.slitPlane) using 1
  simp

/-- `√(r e^{iθ}) = √r e^{iθ/2}` for `r > 0`, `−π < θ < π`. -/
theorem cpow_half_polar {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-π) π) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ (1 / 2 : ℂ) =
      (√r : ℂ) * Complex.exp ((θ / 2 : ℝ) * Complex.I) := by
  have e : (r : ℂ) * Complex.exp (θ * Complex.I) =
      Complex.exp ((Real.log r : ℂ) + θ * Complex.I) := by
    rw [Complex.exp_add, Complex.ofReal_log hr.le,
      Complex.exp_log (by exact_mod_cast hr.ne')]
  rw [e, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using hθ.1) (by simpa using hθ.2.le),
    show ((Real.log r : ℂ) + θ * Complex.I) * (1 / 2) =
      ((Real.log r / 2 : ℝ) : ℂ) + (θ / 2 : ℝ) * Complex.I by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
  ring_nf

theorem im_erfcPhase_polar {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-π) π) :
    (erfcPhase ((r : ℂ) * Complex.exp (θ * Complex.I))).im =
      2 * √r * Real.sin (θ / 2) * (√r * Real.cos (θ / 2) - 1) := by
  rw [erfcPhase, cpow_half_polar hr hθ]
  simp only [Complex.sub_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  rw [show (2 * ((√r : ℂ) * Complex.exp ((θ / 2 : ℝ) * Complex.I))).im =
      2 * (√r * Real.sin (θ / 2)) by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]]
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hq : √r * √r = r := Real.mul_self_sqrt hr.le
  rw [hs]
  linear_combination (-(2 * Real.sin (θ / 2) * Real.cos (θ / 2))) * hq

/-- The steepest descent path: for `t = r e^{iθ}`, `r > 0`, `0 < |θ| < π`,
`ℑ(t − 2√t) = 0 ⟺ r = sec²(θ/2)`. -/
theorem erfcPhase_im_eq_zero_iff {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-π) π) (hθ0 : θ ≠ 0) :
    (erfcPhase ((r : ℂ) * Complex.exp (θ * Complex.I))).im = 0 ↔
      r = (Real.cos (θ / 2) ^ 2)⁻¹ := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hsn : Real.sin (θ / 2) ≠ 0 := by
    rcases lt_or_gt_of_ne hθ0 with h | h
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hθ.1])).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])).ne'
  have hsr : 0 < √r := Real.sqrt_pos.mpr hr
  rw [im_erfcPhase_polar hr hθ]
  constructor
  · intro h
    have h1 : √r * Real.cos (θ / 2) = 1 := by
      have := mul_eq_zero.mp h
      rcases this with h2 | h2
      · exact absurd h2 (mul_ne_zero (by positivity) hsn)
      · linarith
    rw [← Real.mul_self_sqrt hr.le]
    field_simp
    linear_combination (√r * Real.cos (θ / 2) + 1) * h1
  · intro h
    have h1 : √r = (Real.cos (θ / 2))⁻¹ := by
      rw [h, Real.sqrt_inv, Real.sqrt_sq hc.le]
    rw [h1, inv_mul_cancel₀ hc.ne', sub_self, mul_zero]

/-- The path `t(θ) = sec²(θ/2) e^{iθ}`. -/
noncomputable def erfcPath (θ : ℝ) : ℂ :=
  ((Real.cos (θ / 2) ^ 2)⁻¹ : ℝ) * Complex.exp (θ * Complex.I)

/-- `t′(θ) = t(θ) (tan(θ/2) + i)`. -/
noncomputable def erfcPathDeriv (θ : ℝ) : ℂ := erfcPath θ * (Real.tan (θ / 2) + Complex.I)

theorem hasDerivAt_erfcPath {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    HasDerivAt erfcPath (erfcPathDeriv θ) θ := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hu : HasDerivAt (fun θ : ℝ => (Real.cos (θ / 2) ^ 2)⁻¹)
      ((Real.cos (θ / 2) ^ 2)⁻¹ * Real.tan (θ / 2)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => Real.cos (θ / 2)) (-Real.sin (θ / 2) * (1 / 2)) θ := by
      have := (Real.hasDerivAt_cos (θ / 2)).comp θ ((hasDerivAt_id' θ).div_const 2)
      exact this
    convert (h1.pow 2).inv (pow_ne_zero 2 hc.ne') using 1
    rw [Real.tan_eq_sin_div_cos]
    simp only [Pi.pow_apply]
    field_simp
    ring
  have he : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I))
      (Complex.exp (θ * Complex.I) * (1 * Complex.I)) θ :=
    (((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp).comp_ofReal
  show HasDerivAt (fun θ : ℝ => ((((Real.cos (θ / 2) ^ 2)⁻¹ : ℝ) : ℂ) *
    Complex.exp (θ * Complex.I))) _ θ
  convert hu.ofReal_comp.mul he using 1
  unfold erfcPathDeriv erfcPath
  push_cast
  ring

theorem erfcPath_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : erfcPath θ ≠ 0 := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  unfold erfcPath
  exact mul_ne_zero (by exact_mod_cast (inv_pos.mpr (by positivity)).ne') (Complex.exp_ne_zero _)

/-- On the path, `t − 2√t = −1 − tan²(θ/2)` is real. -/
theorem erfcPhase_erfcPath {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    erfcPhase (erfcPath θ) = ((-(1 + Real.tan (θ / 2) ^ 2) : ℝ) : ℂ) := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hr : 0 < (Real.cos (θ / 2) ^ 2)⁻¹ := by positivity
  have hw : Complex.exp (θ * Complex.I) = Complex.exp ((θ / 2 : ℝ) * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [erfcPhase, erfcPath, cpow_half_polar hr hθ, Real.sqrt_inv, Real.sqrt_sq hc.le, hw,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.tan_eq_sin_div_cos]
  have hs := Real.sin_sq_add_cos_sq (θ / 2)
  generalize Real.sin (θ / 2) = sn at *
  generalize Real.cos (θ / 2) = c at *
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hs' : (sn : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  push_cast
  field_simp
  linear_combination (sn : ℂ) ^ 2 * Complex.I_sq

theorem measurable_tan : Measurable Real.tan := by
  rw [show Real.tan = fun x => Real.sin x / Real.cos x from funext Real.tan_eq_sin_div_cos]
  fun_prop

theorem measurable_erfcPathIntegrand (lam : ℝ) : Measurable (erfcPathIntegrand lam) := by
  unfold erfcPathIntegrand
  have := measurable_tan.comp (measurable_id.div_const (2 : ℝ))
  fun_prop

theorem erfcPathIntegrand_nonneg (lam θ : ℝ) : 0 ≤ erfcPathIntegrand lam θ := (Real.exp_pos _).le

theorem erfcPathIntegrand_le_one (lam θ : ℝ) : erfcPathIntegrand lam θ ≤ 1 :=
  Real.exp_le_one_iff.mpr (by
    have := sq_nonneg lam; have := sq_nonneg (Real.tan (θ / 2)); nlinarith)

theorem erfcPathIntegrand_neg (lam θ : ℝ) :
    erfcPathIntegrand lam (-θ) = erfcPathIntegrand lam θ := by
  simp [erfcPathIntegrand, neg_div, Real.tan_neg]

/-- `|x| e^{−λ² x²} ≤ 1/λ`. -/
theorem abs_mul_exp_neg_sq_le {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    |x * Real.exp (-(lam ^ 2 * x ^ 2))| ≤ 1 / lam := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), le_div_iff₀ hlam]
  have h1 := Real.add_one_le_exp (lam ^ 2 * x ^ 2)
  have h2 : Real.exp (-(lam ^ 2 * x ^ 2)) * Real.exp (lam ^ 2 * x ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : lam * |x| ≤ lam ^ 2 * x ^ 2 + 1 := by
    have := sq_nonneg (lam * |x| - 1)
    have : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith
  have h4 : 0 < Real.exp (-(lam ^ 2 * x ^ 2)) := Real.exp_pos _
  calc |x| * Real.exp (-(lam ^ 2 * x ^ 2)) * lam
      = Real.exp (-(lam ^ 2 * x ^ 2)) * (lam * |x|) := by ring
    _ ≤ Real.exp (-(lam ^ 2 * x ^ 2)) * Real.exp (lam ^ 2 * x ^ 2) := by
        gcongr; linarith
    _ = 1 := h2

/-- On the steepest descent path the integrand of 3.5.44 is
`e^{−λ²} e^{−λ² tan²(θ/2)} (tan(θ/2) + i)`. -/
theorem erfcPath_integrand_eq (lam : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    Complex.exp ((lam : ℂ) ^ 2 * erfcPhase (erfcPath θ)) * erfcPathDeriv θ / erfcPath θ =
      ((Real.exp (-lam ^ 2) * (erfcPathIntegrand lam θ * Real.tan (θ / 2)) : ℝ) : ℂ) +
        ((Real.exp (-lam ^ 2) * erfcPathIntegrand lam θ : ℝ) : ℂ) * Complex.I := by
  rw [erfcPhase_erfcPath hθ, erfcPathDeriv, mul_div_assoc,
    mul_div_cancel_left₀ _ (erfcPath_ne_zero hθ)]
  have e : Complex.exp ((lam : ℂ) ^ 2 * ((-(1 + Real.tan (θ / 2) ^ 2) : ℝ) : ℂ)) =
      ((Real.exp (-lam ^ 2) * erfcPathIntegrand lam θ : ℝ) : ℂ) := by
    rw [erfcPathIntegrand, ← Real.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast; ring
  rw [e]
  push_cast
  ring

/-- **DLMF 3.5.45** as the integral of 3.5.44 along the steepest descent path
`t = sec²(θ/2) e^{iθ}`, `−π < θ < π`: `(2πi)^{−1} ∫ e^{λ²(t−2√t)} dt/t = erfc λ`. The odd part
`e^{−λ²} e^{−λ² tan²(θ/2)} tan(θ/2)` integrates to zero. -/
theorem dlmf_3_5_45_path {lam : ℝ} (hlam : 0 < lam) :
    (2 * π * Complex.I)⁻¹ * ∫ θ in (-π)..π,
      Complex.exp ((lam : ℂ) ^ 2 * erfcPhase (erfcPath θ)) * erfcPathDeriv θ / erfcPath θ =
      BZ.erfc lam := by
  set A : ℝ → ℝ := fun θ => Real.exp (-lam ^ 2) * (erfcPathIntegrand lam θ * Real.tan (θ / 2))
  set B : ℝ → ℝ := fun θ => Real.exp (-lam ^ 2) * erfcPathIntegrand lam θ
  have hpi : -π ≤ π := by linarith [pi_pos]
  have hcongr : ∫ θ in (-π)..π,
      Complex.exp ((lam : ℂ) ^ 2 * erfcPhase (erfcPath θ)) * erfcPathDeriv θ / erfcPath θ =
      ∫ θ in (-π)..π, ((A θ : ℝ) : ℂ) + ((B θ : ℝ) : ℂ) * Complex.I := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ θ : ℝ, θ ≠ π := by
      rw [ae_iff]; simp
    filter_upwards [hne] with θ hθ hmem
    rw [uIoc_of_le hpi] at hmem
    exact erfcPath_integrand_eq lam ⟨hmem.1, lt_of_le_of_ne hmem.2 hθ⟩
  have hmA : AEStronglyMeasurable A (volume.restrict (uIoc (-π) π)) := by
    have := measurable_tan.comp (measurable_id.div_const (2 : ℝ))
    exact (by unfold A; have := measurable_erfcPathIntegrand lam; fun_prop :
      Measurable A).aestronglyMeasurable
  have hA : IntervalIntegrable A volume (-π) π := by
    refine (intervalIntegrable_const (c := Real.exp (-lam ^ 2) * (1 / lam))).mono_fun' hmA
      (Eventually.of_forall fun θ => ?_)
    simp only [A, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    gcongr
    rw [erfcPathIntegrand, mul_comm, ← abs_mul]
    exact abs_mul_exp_neg_sq_le hlam _
  have hB : IntervalIntegrable B volume (-π) π := by
    refine (intervalIntegrable_const (c := Real.exp (-lam ^ 2))).mono_fun'
      (by unfold B; exact ((measurable_erfcPathIntegrand lam).const_mul _).aestronglyMeasurable)
      (Eventually.of_forall fun θ => ?_)
    simp only [B, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (erfcPathIntegrand_nonneg lam θ)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (erfcPathIntegrand_le_one lam θ)
  have hodd : ∫ θ in (-π)..π, A θ = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) A
    rw [neg_neg] at h
    have hA' : ∀ θ, A (-θ) = -A θ := fun θ => by
      simp only [A, erfcPathIntegrand_neg, neg_div, Real.tan_neg]; ring
    simp only [hA', intervalIntegral.integral_neg] at h
    linarith
  have hA' : IntervalIntegrable (fun θ => ((A θ : ℝ) : ℂ)) volume (-π) π :=
    ⟨hA.1.ofReal, hA.2.ofReal⟩
  have hB' : IntervalIntegrable (fun θ => ((B θ : ℝ) : ℂ)) volume (-π) π :=
    ⟨hB.1.ofReal, hB.2.ofReal⟩
  rw [hcongr, intervalIntegral.integral_add hA' (hB'.mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hodd, dlmf_3_5_45 hlam]
  simp only [B]
  rw [intervalIntegral.integral_const_mul]
  have hpi0 : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
  push_cast
  field_simp
  ring

/-! ### 3.5.46 -/

/-- **DLMF 3.5.46**: the Hilbert transform (§1.14(v), `hilbert`) is the Cauchy principal value
`ℋf(x) = (1/π) ⨍_{−∞}^{∞} f(t)/(t − x) dt`, `x ∈ ℝ`: whenever it exists, the limits
`lim_{ε→0+} lim_{R→∞} (1/π)(∫_{x−R}^{x−ε} + ∫_{x+ε}^{x+R}) f(t)/(t − x) dt` exist and equal
`ℋf(x)`. -/
theorem dlmf_3_5_46 {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) {x : ℝ} {L : ℂ}
    (h : HasHilbert f x L) :
    ∃ T : ℝ → ℂ, (∀ ε, 0 < ε → Tendsto (fun R => (π : ℂ)⁻¹ *
      ((∫ t in (x - R)..(x - ε), f t / (t - x)) + ∫ t in (x + ε)..(x + R), f t / (t - x)))
        atTop (𝓝 (T ε))) ∧ Tendsto T (𝓝[>] 0) (𝓝 (hilbert f x)) := by
  rw [h.hilbert_eq]
  obtain ⟨T, hT, hL⟩ := h
  refine ⟨T, fun ε hε => (hT ε hε).congr' ?_, hL⟩
  filter_upwards [eventually_ge_atTop ε] with R hR
  exact hilbertTrunc_eq_pv hf x hε hR

end Azurite.DLMF
