/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Contour
import Azurite.DLMF.Chapter3.Section5ComplexGauss

/-!
# DLMF §3.5(ix), Example: the Bromwich integrals 3.5.42 and 3.5.44

* The Laplace pair 7.14.4 (`b = μ²`): `∫₀^∞ e^{−pτ} erfc(μ/√τ) dτ = e^{−2μ√p}/p`, `μ > 0`.
  For real `p > 0` by Fubini (`laplace_erfc_real`) and
  `∫₀^∞ e^{−u² − a²/u²} du = (√π/2) e^{−2a}` (`integral_exp_neg_sq_sub_sq_div`, the substitutions
  `w = u − a/u`, `v = a/u`, `integral_exp_neg_sub_div_sq`); for `ℜp > 0` by analytic
  continuation (`laplace_erfcLapQ`, `erfcLapQ`, `erfcLapG`).
* `erfc′(x) = −(2/√π) e^{−x²}` (`hasDerivAt_erfc`), `0 ≤ erfc x ≤ 1` for `x ≥ 0`
  (`erfc_nonneg`, `erfc_le_one`); the inversion 1.14(iii)/2.4.3 for every `σ > 0`
  (`tendsto_bromwich_erfcLapG`).
* **3.5.42** `dlmf_3_5_42`, `cgI_erfc`: `erfc λ = (2πi)^{−1} ∫_{c−i∞}^{c+i∞} e^{ζ−2λ√ζ} dζ/ζ`,
  `c > 0`, i.e. 3.5.35 with `s = 1`, `f(ζ) = e^{−2λ√ζ}`.
* **3.5.44** `dlmf_3_5_44`: `erfc λ = (2πi)^{−1} ∫_{c−i∞}^{c+i∞} e^{λ²(t−2√t)} dt/t`, `c > 0`.
-/

open Set Filter Topology MeasureTheory Real

namespace Azurite.DLMF

/-! ### `∫₀^∞ e^{−u² − a²/u²} du = (√π/2) e^{−2a}` -/

theorem image_sub_div_Ioi {a : ℝ} (ha : 0 < a) : (fun u => u - a / u) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun w => ?_
  set s := √(w ^ 2 + 4 * a)
  have hs : s * s = w ^ 2 + 4 * a := Real.mul_self_sqrt (by positivity)
  have hsw : |w| < s := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hu : 0 < (w + s) / 2 := by linarith [neg_abs_le w]
  have hne : w + s ≠ 0 := by linarith
  refine ⟨(w + s) / 2, hu, ?_⟩
  simp only
  field_simp
  linear_combination hs

theorem injOn_sub_div {a : ℝ} (ha : 0 < a) : InjOn (fun u => u - a / u) (Ioi 0) := by
  refine StrictMonoOn.injOn fun u (hu : 0 < u) v (hv : 0 < v) huv => ?_
  have : a / v < a / u := div_lt_div_of_pos_left ha hu huv
  linarith

theorem integrableOn_exp_neg_sub_div_sq (a : ℝ) :
    IntegrableOn (fun u => Real.exp (-(u - a / u) ^ 2)) (Ioi 0) := by
  refine Integrable.mono' ((BZ.integrableOn_exp_neg_sq_Ioi 0).const_mul (Real.exp (2 * a)))
    (by fun_prop : Measurable fun u : ℝ => Real.exp (-(u - a / u) ^ 2)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have e : (u - a / u) ^ 2 = u ^ 2 - 2 * a + (a / u) ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg (a / u)]

/-- `∫₀^∞ e^{−(u − a/u)²} du = √π/2` (`a > 0`): the substitutions `w = u − a/u` and `v = a/u`
give `√π = ∫₀^∞ (1 + a/u²) e^{−(u−a/u)²} du = 2 ∫₀^∞ e^{−(u−a/u)²} du`. -/
theorem integral_exp_neg_sub_div_sq {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi 0, Real.exp (-(u - a / u) ^ 2) = √π / 2 := by
  set G : ℝ → ℝ := fun u => Real.exp (-(u - a / u) ^ 2)
  have hd1 : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u => u - a / u) (1 + a / u ^ 2) (Ioi 0) u :=
    fun u (hu : 0 < u) => by
      have := (hasDerivAt_id u).sub ((hasDerivAt_inv hu.ne').const_mul a)
      convert this.hasDerivWithinAt using 1
      · ext v; simp [div_eq_mul_inv]
      · simp; ring
  have hd2 : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u => a / u) (-(a / u ^ 2)) (Ioi 0) u :=
    fun u (hu : 0 < u) => by
      have := (hasDerivAt_inv hu.ne').const_mul a
      convert this.hasDerivWithinAt using 1
      · ext v; simp [div_eq_mul_inv]
      · ring
  have hinj2 : InjOn (fun u => a / u) (Ioi 0) := fun u (hu : 0 < u) v (hv : 0 < v) h => by
    simp only at h
    field_simp at h
    nlinarith
  have himg2 : (fun u => a / u) '' Ioi 0 = Ioi 0 := by
    ext v; constructor
    · rintro ⟨u, hu, rfl⟩; exact div_pos ha hu
    · intro (hv : 0 < v); exact ⟨a / v, div_pos ha hv, by field_simp⟩
  have h1 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd1 (injOn_sub_div ha)
    (fun w => Real.exp (-w ^ 2))
  rw [image_sub_div_Ioi ha, Measure.restrict_univ] at h1
  have hg : ∫ w : ℝ, Real.exp (-w ^ 2) = √π := by
    simpa using integral_gaussian 1
  rw [hg] at h1
  have hGi := integrableOn_exp_neg_sub_div_sq a
  have h2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd2 hinj2 G
  have h2i := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd2 hinj2
    G).mp (by rw [himg2]; exact hGi)
  rw [himg2] at h2
  have e1 : ∀ u ∈ Ioi (0 : ℝ), |1 + a / u ^ 2| • Real.exp (-(u - a / u) ^ 2) =
      G u + |-(a / u ^ 2)| • G (a / u) := fun u (hu : 0 < u) => by
    simp only [G, smul_eq_mul]
    rw [abs_of_pos (by positivity), abs_neg, abs_of_pos (by positivity),
      show a / u - a / (a / u) = -(u - a / u) by field_simp; ring, neg_sq]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e1, integral_add hGi h2i, ← h2] at h1
  linarith

/-- `∫₀^∞ e^{−u² − a²/u²} du = (√π/2) e^{−2a}`, `a > 0`. -/
theorem integral_exp_neg_sq_sub_sq_div {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi 0, Real.exp (-u ^ 2 - a ^ 2 / u ^ 2) = √π / 2 * Real.exp (-(2 * a)) := by
  rw [← integral_exp_neg_sub_div_sq ha, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-! ### The Laplace pair `ℒ[erfc(μ/√τ)](p) = e^{−2μ√p}/p` (7.14.4) -/

theorem integral_Ioi_exp_neg_mul {p : ℝ} (hp : 0 < p) (c : ℝ) :
    ∫ τ in Ioi c, Real.exp (-(p * τ)) = Real.exp (-(p * c)) / p := by
  have := integral_exp_mul_Ioi (neg_lt_zero.mpr hp) c
  simp only [neg_mul] at this
  rw [this, div_neg, neg_div, neg_neg]

/-- For real `p > 0`: `∫₀^∞ e^{−pτ} erfc(μ/√τ) dτ = e^{−2μ√p}/p`, by writing
`erfc(μ/√τ) = (2/√π) ∫_{u√τ > μ} e^{−u²} du` and exchanging the integrations. -/
theorem laplace_erfc_real {μ p : ℝ} (hμ : 0 < μ) (hp : 0 < p) :
    ∫ τ in Ioi 0, Real.exp (-(p * τ)) * BZ.erfc (μ / √τ) = Real.exp (-(2 * μ * √p)) / p := by
  set f : ℝ → ℝ → ℝ := fun τ u =>
    if μ < u * √τ then Real.exp (-(p * τ)) * Real.exp (-u ^ 2) else 0
  have hmeas : Measurable (Function.uncurry f) := by
    refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop)
      measurable_const
  have hI : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    have hg := ((exp_neg_integrableOn_Ioi 0 hp).mul_prod (BZ.integrableOn_exp_neg_sq_Ioi 0) :
      Integrable (fun z : ℝ × ℝ => Real.exp (-p * z.1) * Real.exp (-z.2 ^ 2))
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    refine hg.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    obtain ⟨τ, u⟩ := z
    simp only [f, Function.uncurry_apply_pair]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity), neg_mul]
    · rw [norm_zero]; positivity
  -- inner integral in `u`
  have hu : ∀ τ ∈ Ioi (0 : ℝ), ∫ u in Ioi 0, f τ u =
      Real.exp (-(p * τ)) * (√π / 2 * BZ.erfc (μ / √τ)) := fun τ (hτ : 0 < τ) => by
    have hs : 0 < √τ := Real.sqrt_pos.mpr hτ
    have e : f τ = (Ioi (μ / √τ)).indicator
        fun u => Real.exp (-(p * τ)) * Real.exp (-u ^ 2) := by
      ext u
      simp only [f, indicator, mem_Ioi, div_lt_iff₀ hs]
    rw [e, setIntegral_indicator measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_right (by positivity), integral_const_mul]
    congr 1
    rw [BZ.erfc, BZ.gaussTail]
    simp only [mul_zero, pow_zero, div_one]
    have := Real.sqrt_pos.mpr pi_pos
    field_simp
  -- inner integral in `τ`
  have hτ : ∀ u ∈ Ioi (0 : ℝ), ∫ τ in Ioi 0, f τ u =
      Real.exp (-u ^ 2 - (μ * √p) ^ 2 / u ^ 2) / p := fun u (hu0 : 0 < u) => by
    have e : (fun τ => f τ u) = (Ioi ((μ / u) ^ 2)).indicator
        fun τ => Real.exp (-u ^ 2) * Real.exp (-(p * τ)) := by
      ext τ
      have : μ < u * √τ ↔ (μ / u) ^ 2 < τ := by
        rw [← Real.lt_sqrt (by positivity), div_lt_iff₀ hu0, mul_comm]
      simp only [f, indicator, mem_Ioi, this]
      split_ifs <;> ring
    rw [e, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_right (by positivity), integral_const_mul, integral_Ioi_exp_neg_mul hp,
      mul_div_assoc', ← Real.exp_add]
    congr 2
    rw [mul_pow, Real.sq_sqrt hp.le]
    field_simp
    ring
  have hswap := integral_integral_swap hI
  rw [setIntegral_congr_fun measurableSet_Ioi hu, setIntegral_congr_fun measurableSet_Ioi hτ,
    integral_div, integral_exp_neg_sq_sub_sq_div (by positivity)] at hswap
  simp only [← mul_assoc] at hswap
  have hπ : 0 < √π / 2 := by have := Real.sqrt_pos.mpr pi_pos; positivity
  have e2 : ∫ τ in Ioi 0, Real.exp (-(p * τ)) * (√π / 2) * BZ.erfc (μ / √τ) =
      √π / 2 * ∫ τ in Ioi 0, Real.exp (-(p * τ)) * BZ.erfc (μ / √τ) := by
    rw [← integral_const_mul]; congr 1; ext τ; ring
  rw [e2] at hswap
  rw [mul_div_assoc] at hswap
  exact mul_left_cancel₀ hπ.ne' hswap

/-! ### `erfc′(x) = −(2/√π) e^{−x²}`, `0 ≤ erfc ≤ 1` on `[0, ∞)` -/

theorem erfc_eq_sub (x : ℝ) : BZ.erfc x = 2 / √π *
    ((∫ u in Ioi 0, Real.exp (-u ^ 2)) - ∫ u in (0 : ℝ)..x, Real.exp (-u ^ 2)) := by
  rw [BZ.erfc, BZ.gaussTail, ← intervalIntegral.integral_interval_add_Ioi
    (BZ.integrableOn_exp_neg_sq_Ioi 0) (BZ.integrableOn_exp_neg_sq_Ioi x)]
  simp only [mul_zero, pow_zero, div_one]
  ring

theorem hasDerivAt_erfc (x : ℝ) : HasDerivAt BZ.erfc (-(2 / √π * Real.exp (-x ^ 2))) x := by
  have h := ((by fun_prop : Continuous fun u : ℝ => Real.exp (-u ^ 2)).integral_hasStrictDerivAt
    0 x).hasDerivAt
  have := (h.const_sub (∫ u in Ioi 0, Real.exp (-u ^ 2))).const_mul (2 / √π)
  convert this using 1
  · ext y; exact erfc_eq_sub y
  · ring

theorem continuous_erfc : Continuous BZ.erfc :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_erfc x).continuousAt

theorem erfc_nonneg (x : ℝ) : 0 ≤ BZ.erfc x := by
  unfold BZ.erfc BZ.gaussTail
  simp only [mul_zero, pow_zero, div_one]
  have := Real.sqrt_pos.mpr pi_pos
  exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun u _ => by positivity)

theorem erfc_le_one {x : ℝ} (hx : 0 ≤ x) : BZ.erfc x ≤ 1 := by
  have h0 : ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2) = √π / 2 := by
    simpa using integral_gaussian_Ioi 1
  have hle : ∫ u in Ioi x, Real.exp (-u ^ 2) ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2) :=
    setIntegral_mono_set (BZ.integrableOn_exp_neg_sq_Ioi 0)
      (Eventually.of_forall fun u => (Real.exp_pos _).le)
      (Eventually.of_forall (Ioi_subset_Ioi hx))
  unfold BZ.erfc BZ.gaussTail
  simp only [mul_zero, pow_zero, div_one]
  rw [h0] at hle
  have hπ := Real.sqrt_pos.mpr pi_pos
  rw [div_mul_eq_mul_div, div_le_one hπ]
  linarith

/-! ### The Laplace pair for complex `p` -/

/-- `q(τ) = erfc(μ/√τ)`, the original of `e^{−2μ√p}/p` (7.14.4). -/
noncomputable def erfcLapQ (μ τ : ℝ) : ℂ := (BZ.erfc (μ / √τ) : ℂ)

/-- `q′(τ) = μ e^{−μ²/τ}/(√π τ^{3/2})`. -/
noncomputable def erfcLapQ' (μ τ : ℝ) : ℂ :=
  ((μ * Real.exp (-(μ / √τ) ^ 2) / (√π * √τ ^ 3) : ℝ) : ℂ)

theorem hasDerivAt_erfcLapQ (μ : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (erfcLapQ μ) (erfcLapQ' μ τ) τ := by
  have hs : 0 < √τ := Real.sqrt_pos.mpr hτ
  have hx := (hasDerivAt_const τ μ).div (Real.hasDerivAt_sqrt hτ.ne') hs.ne'
  have h := ((hasDerivAt_erfc (μ / √τ)).comp τ hx).ofReal_comp
  refine h.congr_deriv ?_
  unfold erfcLapQ'
  congr 1
  have hπ := Real.sqrt_pos.mpr pi_pos
  field_simp
  ring

theorem continuousOn_erfcLapQ' (μ : ℝ) : ContinuousOn (erfcLapQ' μ) (Ioi 0) := fun τ hτ => by
  have hs : √τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  have hπ : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  unfold erfcLapQ'
  refine (Complex.continuous_ofReal.continuousAt.comp ?_).continuousWithinAt
  refine ContinuousAt.div ?_ ?_ (mul_ne_zero hπ (pow_ne_zero 3 hs))
  · refine continuousAt_const.mul (Real.continuous_exp.continuousAt.comp ?_)
    exact ((continuousAt_const.div Real.continuous_sqrt.continuousAt hs).pow 2).neg
  · exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.pow 3)

theorem measurable_erfcLapQ (μ : ℝ) : Measurable (erfcLapQ μ) := by
  unfold erfcLapQ
  have := continuous_erfc.measurable
  fun_prop

theorem expGrowth_erfcLapQ {μ : ℝ} (hμ : 0 ≤ μ) : ExpGrowth 1 0 (erfcLapQ μ) := fun τ _ => by
  rw [erfcLapQ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (erfc_nonneg _), zero_mul,
    Real.exp_zero, one_mul]
  exact erfc_le_one (by positivity)

/-- The transform `G(p) = e^{−2μ√p}/p` (principal branch). -/
noncomputable def erfcLapG (μ : ℝ) (p : ℂ) : ℂ := Complex.exp (-(2 * μ) * p ^ (1 / 2 : ℂ)) / p

/-- **DLMF 7.14.4** (as used in §3.5(ix)): `∫₀^∞ e^{−pτ} erfc(μ/√τ) dτ = e^{−2μ√p}/p`, `ℜp > 0`,
`μ > 0`: for real `p` by `laplace_erfc_real`, then by analytic continuation. -/
theorem laplace_erfcLapQ {μ : ℝ} (hμ : 0 < μ) {p : ℂ} (hp : 0 < p.re) :
    laplace (erfcLapQ μ) p = erfcLapG μ p := by
  set U : Set ℂ := {p | 0 < p.re}
  have hf : AnalyticOnNhd ℂ (laplace (erfcLapQ μ)) U := by
    have := analyticOnNhd_laplace (measurable_erfcLapQ μ).aestronglyMeasurable
      (expGrowth_erfcLapQ hμ.le)
    simpa using this
  have hg : AnalyticOnNhd ℂ (erfcLapG μ) U := by
    refine DifferentiableOn.analyticOnNhd (fun q (hq : 0 < q.re) => ?_)
      (isOpen_lt continuous_const Complex.continuous_re)
    have hq0 : q ≠ 0 := fun h => by simp [h] at hq
    have hsl : q ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hq)
    have hc :=
      (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) hsl).hasDerivAt.differentiableAt
    exact (((differentiableAt_const _).mul hc).cexp.div differentiableAt_id
      hq0).differentiableWithinAt
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), laplace (erfcLapQ μ) z = erfcLapG μ z := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 2) (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 2 2 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff]
        exact_mod_cast (ne_of_gt hx : x ≠ 2)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 2 < x)
    have hx0 : 0 < x := by linarith
    have e1 : laplace (erfcLapQ μ) x =
        ((∫ τ in Ioi 0, Real.exp (-(x * τ)) * BZ.erfc (μ / √τ) : ℝ) : ℂ) := by
      rw [laplace, ← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [erfcLapQ]
      push_cast
      rfl
    rw [e1, laplace_erfc_real hμ hx0, erfcLapG,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx0.le, ← Real.sqrt_eq_rpow]
    push_cast
    ring_nf
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU h2 hfreq hp

/-- The inversion of 7.14.4 for every `σ > 0`:
`erfc(μ/√t) = (2πi)^{−1} ∫_{σ−i∞}^{σ+i∞} e^{tp} e^{−2μ√p} dp/p`. -/
theorem tendsto_bromwich_erfcLapG {μ σ t : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (ht : 0 < t) :
    Tendsto (bromwichPartial (erfcLapG μ) σ t) atTop (𝓝 (BZ.erfc (μ / √t) : ℂ)) := by
  have hint : IntegrableOn (fun τ : ℝ => Complex.exp (-((σ : ℂ) * τ)) * erfcLapQ μ τ) (Ioi 0) :=
    integrableOn_laplace (measurable_erfcLapQ μ).aestronglyMeasurable (expGrowth_erfcLapQ hμ.le)
      (by simpa using hσ)
  have h := dlmf_2_4_3 hint (fun τ hτ => hasDerivAt_erfcLapQ μ hτ) (continuousOn_erfcLapQ' μ)
    le_rfl ht
  refine h.congr fun η => ?_
  unfold bromwichPartial
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [laplace_erfcLapQ hμ (by simpa using hσ)]

/-- **DLMF 3.5.42**: `erfc λ = (2πi)^{−1} ∫_{c−i∞}^{c+i∞} e^{ζ − 2λ√ζ} dζ/ζ`, `c > 0`: the integral
3.5.35 with `s = 1`, `f(ζ) = e^{−2λ√ζ}`, as a limit of symmetric partial integrals. -/
theorem dlmf_3_5_42 {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    Tendsto (bromwichPartial (fun z => z ^ (-((1 : ℝ) : ℂ)) *
      Complex.exp (-(2 * lam) * z ^ (1 / 2 : ℂ))) c 1) atTop (𝓝 (BZ.erfc lam : ℂ)) := by
  have h := tendsto_bromwich_erfcLapG hlam hc one_pos
  rw [Real.sqrt_one, div_one] at h
  convert h using 2
  ext z
  simp only [erfcLapG, Complex.ofReal_one, Complex.cpow_neg_one]
  ring

/-- **DLMF 3.5.42** with the value of 3.5.35: `I(f) = erfc λ`, `s = 1`, `f(ζ) = e^{−2λ√ζ}`. -/
theorem cgI_erfc {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    cgI 1 c (fun z => Complex.exp (-(2 * lam) * z ^ (1 / 2 : ℂ))) = BZ.erfc lam :=
  bromwich_eq_of_tendsto (dlmf_3_5_42 hlam hc)

/-- **DLMF 3.5.44** (`ζ = λ²t` in 3.5.42; equivalently 7.14.4 with `μ = λ²` at `τ = λ²`):
`erfc λ = (2πi)^{−1} ∫_{c−i∞}^{c+i∞} e^{λ²(t − 2√t)} dt/t`, `c > 0`. -/
theorem dlmf_3_5_44 {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    Tendsto (fun η : ℝ => (2 * π : ℂ)⁻¹ * ∫ y in (-η)..η,
      Complex.exp ((lam : ℂ) ^ 2 * erfcPhase ((c : ℂ) + y * Complex.I)) /
        ((c : ℂ) + y * Complex.I)) atTop (𝓝 (BZ.erfc lam : ℂ)) := by
  have h := tendsto_bromwich_erfcLapG (pow_pos hlam 2) hc (pow_pos hlam 2)
  rw [Real.sqrt_sq hlam.le, sq, mul_div_cancel_right₀ _ hlam.ne'] at h
  refine h.congr fun η => ?_
  unfold bromwichPartial erfcLapG erfcPhase
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [mul_div_assoc', ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Azurite.DLMF
