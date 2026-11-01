/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14LaplaceInversion
import Azurite.DLMF.Chapter2.Section4WatsonRotation

/-!
# DLMF §2.4(ii): Inverse Laplace transforms (2.4.2–2.4.5)

* 2.4.2: for `e^{−ct} q(t)` absolutely integrable on `(0, ∞)`, the transform `Q = ℒq` (`laplace`
  of §1.14(iii)) is continuous in `ℜz ≥ c` (`dlmf_2_4_2_continuousOn`) and analytic in `ℜz > c`
  (`dlmf_2_4_2_analyticOnNhd`). Differentiability of `q` is not needed here.
* 2.4.3 (`dlmf_2_4_3`): the inversion formula from §1.14(iii), for `q` with continuous derivative
  on `(0, ∞)` (bounded variation near `t`, `boundedVariationOn_Icc_of_deriv`), any `σ ≥ c`.
  The contour integral `(2πi)^{−1} ∫_{σ−iη}^{σ+iη} e^{tz} Q(z) dz` is written with `z = σ + iy`,
  so the prefactor is `(2π)^{−1}` (`bromwichPartial`, `bromwich` for the limit).
* `bromwich_Gamma_cpow`: the inverse transform of `Γ(α) z^{−α}` is `t^{α−1}` (`ℜα > 0`).
* 2.4.4–2.4.5 (`dlmf_2_4_5`): for `Q` analytic in `ℜz > c₀` (`0 ≤ c₀ < c`) with the expansion
  2.4.4 in `ℜz ≥ c` and its differentiated form, the inverse integral 2.4.5 converges for every
  `t > 0` and `σ ≥ c`, is independent of `σ`, and defines `q` with the expansion 2.3.7 as
  `t → 0+`. The proof integrates by parts once (`bromwichPartial_ibp`), bounds the integrand
  of `Q′` by `K|z|^{−ℜα₀−1}` (`half_plane_bound`), and moves the line to `σ = 1/t`
  (`bromwich_shift`, Cauchy's theorem on rectangles) to get `O(t^{ℜαₙ−1})` for the remainder.
* DLMF says the integral 2.4.5 "converges absolutely at each limit". That is false in general:
  for `Q(z) = Γ(λ) z^{−λ}` with `0 < λ ≤ 1` the integrand has norm `e^{σt}|z|^{−λ}`, which is not
  integrable (`dlmf_2_4_5_not_absolutely`). It is the integrated-by-parts form that converges
  absolutely.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-! ### 2.4.2: continuity and analyticity of the transform -/

theorem laplace_eq_shift (q : ℝ → ℂ) (c : ℝ) (z : ℂ) :
    laplace q z = ∫ t in Ioi (0 : ℝ), cexp (-((z - c) * t)) * (cexp (-((c : ℂ) * t)) * q t) := by
  unfold laplace
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem norm_cexp_neg_mul_ofReal_le {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖cexp (-(w * t))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- **DLMF 2.4.2**: `Q(z) = ∫₀^∞ e^{−zt} q(t) dt` is continuous in `ℜz ≥ c` when `e^{−ct} q(t)`
is absolutely integrable. -/
theorem dlmf_2_4_2_continuousOn {q : ℝ → ℂ} {c : ℝ}
    (hq : IntegrableOn (fun t : ℝ => cexp (-((c : ℂ) * t)) * q t) (Ioi 0)) :
    ContinuousOn (laplace q) {z | c ≤ z.re} := by
  set g : ℝ → ℂ := fun t => cexp (-((c : ℂ) * t)) * q t
  have heq : laplace q = fun z => ∫ t in Ioi (0 : ℝ), cexp (-((z - c) * t)) * g t :=
    funext (laplace_eq_shift q c)
  rw [heq]
  refine continuousOn_of_dominated (bound := fun t => ‖g t‖) (fun z _ => ?_) (fun z hz => ?_)
    hq.norm ?_
  · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-((z - c) * t))).aestronglyMeasurable).mul
      hq.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul]
    have hre : 0 ≤ (z - c).re := by simp only [sub_re, ofReal_re]; linarith [show c ≤ z.re from hz]
    calc ‖cexp (-((z - c) * t))‖ * ‖g t‖ ≤ 1 * ‖g t‖ :=
          mul_le_mul_of_nonneg_right (norm_cexp_neg_mul_ofReal_le hre (le_of_lt ht)) (norm_nonneg _)
      _ = ‖g t‖ := one_mul _
  · exact Eventually.of_forall fun t => (by fun_prop : Continuous fun z : ℂ =>
      cexp (-((z - c) * t)) * g t).continuousOn

theorem mul_exp_neg_le_inv {δ t : ℝ} (hδ : 0 < δ) : t * Real.exp (-(δ * t)) ≤ δ⁻¹ := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), ← div_eq_inv_mul,
    le_div_iff₀ hδ]
  have := Real.add_one_le_exp (δ * t)
  nlinarith

/-- **DLMF 2.4.2**: `Q` is analytic in `ℜz > c`. -/
theorem dlmf_2_4_2_analyticOnNhd {q : ℝ → ℂ} {c : ℝ}
    (hq : IntegrableOn (fun t : ℝ => cexp (-((c : ℂ) * t)) * q t) (Ioi 0)) :
    AnalyticOnNhd ℂ (laplace q) {z | c < z.re} := by
  set g : ℝ → ℂ := fun t => cexp (-((c : ℂ) * t)) * q t
  have heq : laplace q = fun z => ∫ t in Ioi (0 : ℝ), cexp (-((z - c) * t)) * g t :=
    funext (laplace_eq_shift q c)
  rw [heq]
  refine DifferentiableOn.analyticOnNhd (fun z₀ hz₀ => ?_)
    (isOpen_lt continuous_const continuous_re)
  have hz₀' : c < z₀.re := hz₀
  set δ := (z₀.re - c) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hball : ∀ z ∈ Metric.ball z₀ δ, δ ≤ (z - c).re := fun z hz => by
    have h1 : |z.re - z₀.re| < δ := by
      calc |z.re - z₀.re| = |(z - z₀).re| := by rw [sub_re]
        _ ≤ ‖z - z₀‖ := abs_re_le_norm _
        _ < δ := by rwa [← dist_eq_norm]
    have := (abs_lt.mp h1).1
    simp only [sub_re, ofReal_re, δ] at this ⊢
    linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => cexp (-((z - c) * t)) * g t)
      (volume.restrict (Ioi 0)) := fun z =>
    ((by fun_prop : Continuous fun t : ℝ => cexp (-((z - c) * t))).aestronglyMeasurable).mul
      hq.aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z t => cexp (-((z - c) * t)) * g t)
    (F' := fun z t => cexp (-((z - c) * t)) * (-(t : ℂ)) * g t)
    (bound := fun t => δ⁻¹ * ‖g t‖) (Metric.ball_mem_nhds z₀ hδ)
    (Eventually.of_forall hmeas) ?_ ?_ ?_ (hq.norm.const_mul _) ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · refine Integrable.mono' hq.norm (hmeas z₀) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))
    rw [norm_mul]
    have hre : 0 ≤ (z₀ - c).re := by simp only [sub_re, ofReal_re]; linarith
    calc ‖cexp (-((z₀ - c) * t))‖ * ‖g t‖ ≤ 1 * ‖g t‖ :=
          mul_le_mul_of_nonneg_right (norm_cexp_neg_mul_ofReal_le hre (le_of_lt ht)) (norm_nonneg _)
      _ = ‖g t‖ := one_mul _
  · exact (((by fun_prop : Continuous fun t : ℝ =>
      cexp (-((z₀ - c) * t)) * (-(t : ℂ)))).aestronglyMeasurable).mul hq.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => ?_)
    have ht0 : 0 < t := ht
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht0.le,
      Complex.norm_exp]
    simp only [neg_re, mul_re, sub_re, ofReal_re, sub_im, ofReal_im, mul_zero, sub_zero]
    have h1 : Real.exp (-((z - c).re * t)) ≤ Real.exp (-(δ * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hball z hz]
    calc Real.exp (-((z - c).re * t)) * t * ‖g t‖ ≤ Real.exp (-(δ * t)) * t * ‖g t‖ := by
          gcongr
      _ = (t * Real.exp (-(δ * t))) * ‖g t‖ := by ring
      _ ≤ δ⁻¹ * ‖g t‖ := by gcongr; exact mul_exp_neg_le_inv hδ
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ z _ => ?_)
    have h0 : HasDerivAt (fun y : ℂ => -((y - c) * t)) (-(t : ℂ)) z := by
      have h1 := (((hasDerivAt_id z).sub_const (c : ℂ)).mul_const (t : ℂ)).neg
      convert h1 using 1
      · ext y
        simp
      · simp
    exact h0.cexp.mul_const (g t)

/-! ### Bounded variation from a continuous derivative -/

/-- A function with a continuous derivative on an open interval containing `[a, b]` has bounded
variation on `[a, b]`. -/
theorem boundedVariationOn_Icc_of_deriv {f f' : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ x ∈ U, HasDerivAt f (f' x) x) (hc : ContinuousOn f' U) {a b : ℝ}
    (hab : Icc a b ⊆ U) : BoundedVariationOn f (Icc a b) := by
  have h1 : ContDiffOn ℝ 1 f U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.mpr (hc.congr fun x hx => (hd x hx).deriv)⟩
  obtain ⟨K, hK⟩ := (h1.mono hab).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  rcases le_or_gt a b with h | h
  · have := hK.locallyBoundedVariationOn a b ⟨le_rfl, h⟩ ⟨h, le_rfl⟩
    rwa [inter_self] at this
  · rw [Icc_eq_empty (not_le.mpr h)]
    show eVariationOn f ∅ ≠ ⊤
    rw [eVariationOn.subsingleton f subsingleton_empty]
    exact ENNReal.zero_ne_top

/-! ### The Bromwich integral -/

/-- The partial Bromwich integral `(2πi)^{−1} ∫_{σ−iη}^{σ+iη} e^{tz} Q(z) dz`, with
`z = σ + iy`. -/
noncomputable def bromwichPartial (Q : ℂ → ℂ) (σ t η : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ y in (-η)..η, cexp (((σ : ℂ) + y * I) * t) * Q (σ + y * I)

/-- The Bromwich integral `(2πi)^{−1} lim_{η→∞} ∫_{σ−iη}^{σ+iη} e^{tz} Q(z) dz` (2.4.3). -/
noncomputable def bromwich (Q : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  limUnder atTop (bromwichPartial Q σ t)

theorem integrableOn_exp_neg_mul_of_le {q : ℝ → ℂ} {c σ : ℝ}
    (hq : IntegrableOn (fun t : ℝ => cexp (-((c : ℂ) * t)) * q t) (Ioi 0)) (hσ : c ≤ σ) :
    IntegrableOn (fun t : ℝ => cexp (-((σ : ℂ) * t)) * q t) (Ioi 0) := by
  refine Integrable.mono' hq.norm (((by fun_prop : Continuous fun t : ℝ =>
    cexp (-((σ : ℂ) * t))).aestronglyMeasurable).mul (by
      have := hq.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => cexp (((c : ℂ) * t)))
          (volume.restrict (Ioi 0)) :=
        (by fun_prop : Continuous fun t : ℝ => cexp (((c : ℂ) * t))).aestronglyMeasurable
      refine (h2.mul this).congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht : (0 : ℝ) < t := ht
  have : cexp (-((σ : ℂ) * t)) * q t = cexp (-(((σ - c : ℝ) : ℂ) * t)) *
      (cexp (-((c : ℂ) * t)) * q t) := by
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, norm_mul]
  calc ‖cexp (-(((σ - c : ℝ) : ℂ) * t))‖ * ‖cexp (-((c : ℂ) * t)) * q t‖
      ≤ 1 * ‖cexp (-((c : ℂ) * t)) * q t‖ :=
        mul_le_mul_of_nonneg_right (norm_cexp_neg_mul_ofReal_le (by simp; linarith) ht.le)
          (norm_nonneg _)
    _ = _ := one_mul _

/-- **DLMF 2.4.3**: for `q` with a continuous derivative on `(0, ∞)` and `e^{−ct} q` absolutely
integrable, `q(t) = (2πi)^{−1} lim_{η→∞} ∫_{σ−iη}^{σ+iη} e^{tz} Q(z) dz` for `t > 0` and every
`σ ≥ c`. -/
theorem dlmf_2_4_3 {q q' : ℝ → ℂ} {c σ : ℝ}
    (hq : IntegrableOn (fun t : ℝ => cexp (-((c : ℂ) * t)) * q t) (Ioi 0))
    (hd : ∀ t, 0 < t → HasDerivAt q (q' t) t) (hq' : ContinuousOn q' (Ioi 0)) (hσ : c ≤ σ)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (bromwichPartial (laplace q) σ t) atTop (𝓝 (q t)) := by
  have hbv : BoundedVariationOn q (Icc (t - t / 2) (t + t / 2)) :=
    boundedVariationOn_Icc_of_deriv isOpen_Ioi hd hq' fun x hx => by
      show 0 < x
      linarith [hx.1]
  have hc : ContinuousAt q t := (hd t ht).continuousAt
  have := dlmf_1_14_20_bv' (integrableOn_exp_neg_mul_of_le hq hσ) (half_pos ht) (by linarith) hbv
    (hc.tendsto.mono_left nhdsWithin_le_nhds) (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rwa [add_self_div_two] at this

theorem bromwich_eq_of_tendsto {Q : ℂ → ℂ} {σ t : ℝ} {L : ℂ}
    (h : Tendsto (bromwichPartial Q σ t) atTop (𝓝 L)) : bromwich Q σ t = L :=
  h.limUnder_eq

/-! ### The inverse transform of `Γ(α) z^{−α}` -/

theorem hasDerivAt_ofReal_cpow {α : ℂ} {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ α) (α * (τ : ℂ) ^ (α - 1)) τ := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c := α)
    (ofReal_mem_slitPlane.mpr hτ)).hasDerivAt.comp_ofReal
  exact h

theorem continuousOn_ofReal_cpow_Ioi (α : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ α) (Ioi 0) :=
  continuous_ofReal.continuousOn.cpow_const fun _ hx => ofReal_mem_slitPlane.mpr hx

theorem laplace_ofReal_cpow {α : ℂ} (hα : 0 < α.re) {z : ℂ} (hz : 0 < z.re) :
    laplace (fun τ : ℝ => (τ : ℂ) ^ (α - 1)) z = Complex.Gamma α * z ^ (-α) := by
  rw [← integral_cexp_mul_cpow hα hz, laplace]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  rw [neg_mul]

/-- The inverse Laplace transform of `Γ(α) z^{−α}` is `t^{α−1}` (`ℜα > 0`, `σ > 0`, `t > 0`). -/
theorem bromwich_Gamma_cpow {α : ℂ} (hα : 0 < α.re) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    Tendsto (bromwichPartial (fun z => Complex.Gamma α * z ^ (-α)) σ t) atTop
      (𝓝 ((t : ℂ) ^ (α - 1))) := by
  have hint : IntegrableOn (fun τ : ℝ => cexp (-((σ : ℂ) * τ)) * (τ : ℂ) ^ (α - 1)) (Ioi 0) := by
    refine (integrableOn_cexp_mul_cpow hα (show 0 < (σ : ℂ).re by simpa using hσ)).congr_fun
      (fun τ _ => ?_) measurableSet_Ioi
    simp only
    rw [neg_mul]
  have h := dlmf_2_4_3 (q' := fun x => (α - 1) * (x : ℂ) ^ (α - 1 - 1)) hint
    (fun τ hτ => hasDerivAt_ofReal_cpow hτ)
    (continuousOn_const.mul (continuousOn_ofReal_cpow_Ioi _)) le_rfl ht
  refine h.congr fun η => ?_
  unfold bromwichPartial
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only
  rw [laplace_ofReal_cpow hα (by simpa using hσ)]

/-! ### Power bounds on a half-plane -/

theorem norm_cpow_le_exp_mul {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ ≤ Real.exp (Real.pi * |w.im|) * ‖z‖ ^ w.re := by
  rw [norm_cpow_of_ne_zero hz, div_le_iff₀ (Real.exp_pos _)]
  have h1 : |arg z * w.im| ≤ Real.pi * |w.im| := by
    rw [abs_mul]
    gcongr
    exact abs_arg_le_pi z
  have h2 : 1 ≤ Real.exp (Real.pi * |w.im|) * Real.exp (arg z * w.im) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith [neg_abs_le (arg z * w.im)])
  calc ‖z‖ ^ w.re = ‖z‖ ^ w.re * 1 := (mul_one _).symm
    _ ≤ ‖z‖ ^ w.re * (Real.exp (Real.pi * |w.im|) * Real.exp (arg z * w.im)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

theorem ne_zero_of_re_ge {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : c ≤ z.re) : z ≠ 0 := by
  rintro rfl
  simp at hz
  linarith

theorem norm_ge_of_re_ge {c : ℝ} {z : ℂ} (hz : c ≤ z.re) : c ≤ ‖z‖ :=
  hz.trans (re_le_norm z)

/-- From `G = O(z^{−β})` as `z → ∞` in `ℜz ≥ c` (`c > 0`, `ℜβ ≥ 0`) and continuity, a bound
`‖G(z)‖ ≤ K ‖z‖^{−ℜβ}` on the whole half-plane. -/
theorem bound_of_isBigO_halfPlane {G : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hG : ContinuousOn G {z | c ≤ z.re}) {β : ℂ} (hβ : 0 ≤ β.re)
    (h : IsBigODLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | c ≤ z.re}) G (fun z => z ^ (-β))) :
    ∃ K, 0 ≤ K ∧ ∀ z : ℂ, c ≤ z.re → ‖G z‖ ≤ K * ‖z‖ ^ (-β.re) := by
  set H := {z : ℂ | c ≤ z.re}
  obtain ⟨K₁, hK₁⟩ := h
  rw [eventually_map, eventually_inf_principal,
    Filter.hasBasis_cobounded_norm.eventually_iff] at hK₁
  obtain ⟨R, -, hRK⟩ := hK₁
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKc : IsCompact (H ∩ Metric.closedBall 0 R') :=
    Metric.isCompact_of_isClosed_isBounded
      ((isClosed_le continuous_const continuous_re).inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hG.mono inter_subset_left)
  set E := Real.exp (Real.pi * |β.im|)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR'p : 0 ≤ R' ^ β.re := Real.rpow_nonneg hR'.le _
  refine ⟨|K₁| * E + |M| * R' ^ β.re, by positivity, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := ne_zero_of_re_ge hc hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hpow : 0 ≤ ‖z‖ ^ (-β.re) := Real.rpow_nonneg hzn.le _
  rcases le_or_gt R ‖z‖ with hRz | hRz
  · have h1 := hRK hRz hz
    have hφ : z ^ (-β) ≠ 0 := cpow_ne_zero_of_ne_zero hz0 _
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hφ)] at h1
    have h2 : ‖z ^ (-β)‖ ≤ E * ‖z‖ ^ (-β.re) := by
      have := norm_cpow_le_exp_mul hz0 (-β)
      rwa [neg_im, abs_neg, neg_re] at this
    calc ‖G z‖ ≤ K₁ * ‖z ^ (-β)‖ := h1
      _ ≤ |K₁| * (E * ‖z‖ ^ (-β.re)) :=
          mul_le_mul (le_abs_self _) h2 (norm_nonneg _) (abs_nonneg _)
      _ ≤ (|K₁| * E + |M| * R' ^ β.re) * ‖z‖ ^ (-β.re) := by
          nlinarith [mul_nonneg (abs_nonneg M) hR'p]
  · have hzR' : ‖z‖ ≤ R' := hRz.le.trans (le_max_left _ _)
    have h1 := hM z ⟨hz, by simpa [Metric.mem_closedBall, dist_zero_right] using hzR'⟩
    have h2 : R' ^ (-β.re) ≤ ‖z‖ ^ (-β.re) :=
      Real.rpow_le_rpow_of_nonpos hzn hzR' (by linarith)
    have h3 : R' ^ β.re * R' ^ (-β.re) = 1 := by
      rw [← Real.rpow_add hR', add_neg_cancel, Real.rpow_zero]
    calc ‖G z‖ ≤ M := h1
      _ ≤ |M| := le_abs_self _
      _ = |M| * (R' ^ β.re * R' ^ (-β.re)) := by rw [h3, mul_one]
      _ ≤ |M| * (R' ^ β.re * ‖z‖ ^ (-β.re)) := by gcongr
      _ ≤ (|K₁| * E + |M| * R' ^ β.re) * ‖z‖ ^ (-β.re) := by
          nlinarith [mul_nonneg (abs_nonneg K₁) hE]

/-- A function analytic in `ℜz > c₀` with `|G(z)| ≤ K|z|^{−p}` and `|G′(z)| ≤ K′|z|^{−p−1}` in
`ℜz ≥ c`, where `0 ≤ c₀ < c` and `p > 0`. -/
structure DecayHalfPlane (G : ℂ → ℂ) (c₀ c p K K' : ℝ) : Prop where
  c₀_nonneg : 0 ≤ c₀
  lt : c₀ < c
  p_pos : 0 < p
  differentiableOn : DifferentiableOn ℂ G {z | c₀ < z.re}
  bound : ∀ z : ℂ, c ≤ z.re → ‖G z‖ ≤ K * ‖z‖ ^ (-p)
  bound' : ∀ z : ℂ, c ≤ z.re → ‖deriv G z‖ ≤ K' * ‖z‖ ^ (-(p + 1))

/-! ### The integrals `∫ (σ² + y²)^{−r/2} dy` -/

/-- `J(r) = ∫_ℝ (1 + u²)^{−r/2} du`. -/
noncomputable def bromwichJ (r : ℝ) : ℝ := ∫ u : ℝ, (1 + u ^ 2) ^ (-r / 2)

theorem integrable_one_add_sq_rpow {r : ℝ} (hr : 1 < r) :
    Integrable (fun u : ℝ => (1 + u ^ 2) ^ (-r / 2)) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := r)
    (by simpa using hr)
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem norm_line_rpow (σ y r : ℝ) :
    ‖(σ : ℂ) + y * I‖ ^ (-r) = (σ ^ 2 + y ^ 2) ^ (-r / 2) := by
  rw [norm_add_mul_I, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem integrable_line_rpow {σ r : ℝ} (hσ : 0 < σ) (hr : 1 < r) :
    Integrable (fun y : ℝ => (σ ^ 2 + y ^ 2) ^ (-r / 2)) := by
  have h := ((integrable_one_add_sq_rpow hr).comp_mul_left' (R := σ⁻¹)
    (inv_ne_zero hσ.ne')).const_mul (σ ^ (-r))
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  have : 1 + (σ⁻¹ * y) ^ 2 = σ⁻¹ ^ 2 * (σ ^ 2 + y ^ 2) := by
    field_simp
  rw [this, Real.mul_rpow (by positivity) (by positivity), ← mul_assoc, ← Real.rpow_natCast σ⁻¹,
    ← Real.rpow_mul (inv_nonneg.mpr hσ.le), Real.inv_rpow hσ.le, ← Real.rpow_neg hσ.le,
    ← Real.rpow_add hσ, show -r + -(((2 : ℕ) : ℝ) * (-r / 2)) = 0 by push_cast; ring,
    Real.rpow_zero, one_mul]

theorem integral_line_rpow {σ : ℝ} (hσ : 0 < σ) (r : ℝ) :
    ∫ y : ℝ, (σ ^ 2 + y ^ 2) ^ (-r / 2) = σ ^ (1 - r) * bromwichJ r := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => (σ ^ 2 + y ^ 2) ^ (-r / 2)) σ
  have h2 : ∀ u : ℝ, (σ ^ 2 + (σ * u) ^ 2) ^ (-r / 2) = σ ^ (-r) * (1 + u ^ 2) ^ (-r / 2) := by
    intro u
    rw [show σ ^ 2 + (σ * u) ^ 2 = σ ^ 2 * (1 + u ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast σ 2,
      ← Real.rpow_mul hσ.le]
    congr 2
    push_cast
    ring
  simp only [h2] at h
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hσ), smul_eq_mul] at h
  have h' : ∫ y : ℝ, (σ ^ 2 + y ^ 2) ^ (-r / 2) = σ * (σ ^ (-r) * bromwichJ r) := by
    rw [bromwichJ, h]
    field_simp
  rw [h', sub_eq_add_neg, Real.rpow_add hσ, Real.rpow_one]
  ring

/-! ### Integration by parts along the line -/

theorem hasDerivAt_line (σ : ℝ) (y : ℝ) : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I) I y := by
  have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ)
  simpa using this

theorem continuous_line_comp {G : ℂ → ℂ} {U : Set ℂ} (hG : ContinuousOn G U) {σ : ℝ}
    (hσ : ∀ y : ℝ, (σ : ℂ) + y * I ∈ U) : Continuous fun y : ℝ => G ((σ : ℂ) + y * I) :=
  hG.comp_continuous (by fun_prop) hσ

theorem mem_halfPlane_line {c₀ σ : ℝ} (hσ : c₀ < σ) (y : ℝ) :
    (σ : ℂ) + y * I ∈ {z : ℂ | c₀ < z.re} := by
  simp [hσ]

/-- One integration by parts in the Bromwich integral:
`(2π)^{−1} ∫_{−η}^{η} e^{(σ+iy)t} G(σ+iy) dy = (2π)^{−1}([G e^{zt}/(it)]_{σ−iη}^{σ+iη}
  − t^{−1} ∫_{−η}^{η} e^{(σ+iy)t} G′(σ+iy) dy)`. -/
theorem bromwichPartial_ibp {G : ℂ → ℂ} {c₀ : ℝ} (hG : DifferentiableOn ℂ G {z | c₀ < z.re})
    {σ t : ℝ} (hσ : c₀ < σ) (ht : 0 < t) (η : ℝ) :
    bromwichPartial G σ t η = (2 * Real.pi : ℂ)⁻¹ *
      ((G ((σ : ℂ) + η * I) * cexp (((σ : ℂ) + η * I) * t) -
          G ((σ : ℂ) + ((-η : ℝ) : ℂ) * I) * cexp (((σ : ℂ) + ((-η : ℝ) : ℂ) * I) * t)) /
            (I * t) -
        (1 / (t : ℂ)) * ∫ y in (-η)..η, cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I)) := by
  have hU : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const continuous_re
  have hGa : AnalyticOnNhd ℂ G {z | c₀ < z.re} := hG.analyticOnNhd hU
  have hdc : ContinuousOn (deriv G) {z | c₀ < z.re} := hGa.deriv.continuousOn
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hIt : I * t ≠ 0 := mul_ne_zero I_ne_zero htc
  set u : ℝ → ℂ := fun y => G ((σ : ℂ) + y * I)
  set u' : ℝ → ℂ := fun y => I * deriv G ((σ : ℂ) + y * I)
  set v : ℝ → ℂ := fun y => cexp (((σ : ℂ) + y * I) * t) / (I * t)
  set v' : ℝ → ℂ := fun y => cexp (((σ : ℂ) + y * I) * t)
  have hu : ∀ y : ℝ, HasDerivAt u (u' y) y := fun y => by
    have h2 : HasDerivAt G (deriv G ((σ : ℂ) + y * I)) ((σ : ℂ) + y * I) :=
      (hG.differentiableAt (hU.mem_nhds (mem_halfPlane_line hσ y))).hasDerivAt
    have := h2.comp y (hasDerivAt_line σ y)
    simp only [u, u']
    rw [mul_comm]
    exact this
  have hv : ∀ y : ℝ, HasDerivAt v (v' y) y := fun y => by
    have h1 := (((hasDerivAt_line σ y).mul_const (t : ℂ)).cexp).div_const (I * t)
    simp only [v, v']
    convert h1 using 1
    field_simp
  have hu'c : Continuous u' := continuous_const.mul (continuous_line_comp hdc fun y =>
    mem_halfPlane_line hσ y)
  have hv'c : Continuous v' := by fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -η) (b := η)
    (fun y _ => hu y) (fun y _ => hv y) (hu'c.intervalIntegrable _ _)
    (hv'c.intervalIntegrable _ _)
  unfold bromwichPartial
  have e1 : ∫ y in (-η)..η, cexp (((σ : ℂ) + y * I) * t) * G (σ + y * I) =
      ∫ y in (-η)..η, u y * v' y :=
    intervalIntegral.integral_congr fun y _ => mul_comm _ _
  have e2 : ∫ y in (-η)..η, u' y * v y =
      (1 / (t : ℂ)) * ∫ y in (-η)..η, cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [u', v]
    field_simp
  rw [e1, key, e2]
  simp only [u, v]
  push_cast
  ring

/-! ### Convergence and the contour shift -/

namespace DecayHalfPlane

variable {G : ℂ → ℂ} {c₀ c p K K' : ℝ}

theorem c_pos (h : DecayHalfPlane G c₀ c p K K') : 0 < c := h.c₀_nonneg.trans_lt h.lt

theorem continuousOn (h : DecayHalfPlane G c₀ c p K K') : ContinuousOn G {z | c ≤ z.re} :=
  h.differentiableOn.continuousOn.mono fun z hz => by
    show c₀ < z.re
    exact h.lt.trans_le hz

theorem continuousOn_deriv (h : DecayHalfPlane G c₀ c p K K') :
    ContinuousOn (deriv G) {z | c₀ < z.re} :=
  (h.differentiableOn.analyticOnNhd (isOpen_lt continuous_const continuous_re)).deriv.continuousOn

/-- The integrand after integration by parts, `e^{(σ+iy)t} G′(σ+iy)`. -/
theorem integrable_deriv_line (h : DecayHalfPlane G c₀ c p K K') {σ t : ℝ} (hσ : c ≤ σ) :
    Integrable fun y : ℝ => cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I) := by
  have hσ0 : 0 < σ := h.c_pos.trans_le hσ
  have hcont : Continuous fun y : ℝ => cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I) :=
    (by fun_prop : Continuous fun y : ℝ => cexp (((σ : ℂ) + y * I) * t)).mul
      (continuous_line_comp h.continuousOn_deriv fun y =>
        mem_halfPlane_line (h.lt.trans_le hσ) y)
  refine Integrable.mono' ((integrable_line_rpow hσ0 (by linarith [h.p_pos] : 1 < p + 1)).const_mul
    (Real.exp (σ * t) * K')) hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_exp]
  simp only [mul_re, add_re, ofReal_re, mul_im, I_re, I_im, ofReal_im, mul_zero, mul_one,
    sub_zero, add_im, zero_add, add_zero]
  have hb := h.bound' ((σ : ℂ) + y * I) (by simpa using hσ)
  rw [norm_line_rpow] at hb
  calc Real.exp (σ * t) * ‖deriv G ((σ : ℂ) + y * I)‖
      ≤ Real.exp (σ * t) * (K' * (σ ^ 2 + y ^ 2) ^ (-(p + 1) / 2)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

theorem norm_boundary_le (h : DecayHalfPlane G c₀ c p K K') {σ t : ℝ} (hσ : c ≤ σ) (y : ℝ)
    (hy : y ≠ 0) :
    ‖G ((σ : ℂ) + y * I) * cexp (((σ : ℂ) + y * I) * t)‖ ≤ K * |y| ^ (-p) * Real.exp (σ * t) := by
  rw [norm_mul, Complex.norm_exp]
  simp only [mul_re, add_re, ofReal_re, mul_im, I_re, I_im, ofReal_im, mul_zero, mul_one,
    sub_zero, add_im, zero_add, add_zero]
  have hb := h.bound ((σ : ℂ) + y * I) (by simpa using hσ)
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hle : |y| ≤ ‖(σ : ℂ) + y * I‖ := by
    have := abs_im_le_norm ((σ : ℂ) + y * I)
    simpa using this
  have h2 : ‖(σ : ℂ) + y * I‖ ^ (-p) ≤ |y| ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hy0 hle (by linarith [h.p_pos])
  have hK : 0 ≤ K := by
    have := h.bound ((σ : ℂ) + y * I) (by simpa using hσ)
    have hpos : 0 < ‖(σ : ℂ) + y * I‖ ^ (-p) := Real.rpow_pos_of_pos (lt_of_lt_of_le hy0 hle) _
    nlinarith [norm_nonneg (G ((σ : ℂ) + y * I))]
  calc ‖G ((σ : ℂ) + y * I)‖ * Real.exp (σ * t)
      ≤ (K * ‖(σ : ℂ) + y * I‖ ^ (-p)) * Real.exp (σ * t) := by gcongr
    _ ≤ (K * |y| ^ (-p)) * Real.exp (σ * t) := by gcongr

/-- The limit of the Bromwich partial integrals, in integrated-by-parts form. -/
theorem tendsto_bromwichPartial (h : DecayHalfPlane G c₀ c p K K') {σ t : ℝ} (hσ : c ≤ σ)
    (ht : 0 < t) :
    Tendsto (bromwichPartial G σ t) atTop (𝓝 ((2 * Real.pi : ℂ)⁻¹ * (-(1 / (t : ℂ)) *
      ∫ y : ℝ, cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I)))) := by
  have hσ' : c₀ < σ := h.lt.trans_le hσ
  have hibp := bromwichPartial_ibp h.differentiableOn hσ' ht
  set B : ℝ → ℂ := fun η => (G ((σ : ℂ) + η * I) * cexp (((σ : ℂ) + η * I) * t) -
    G ((σ : ℂ) + ((-η : ℝ) : ℂ) * I) * cexp (((σ : ℂ) + ((-η : ℝ) : ℂ) * I) * t)) / (I * t)
  have hB : Tendsto B atTop (𝓝 0) := by
    have hp := h.p_pos
    refine squeeze_zero_norm' (f := B) (a := fun η => 2 * K * Real.exp (σ * t) / t * η ^ (-p)) ?_
      ?_
    · filter_upwards [eventually_gt_atTop 0] with η hη
      simp only [B]
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg ht.le, div_le_iff₀ ht]
      have h1 := h.norm_boundary_le (t := t) hσ η hη.ne'
      have h2 := h.norm_boundary_le (t := t) hσ (-η) (neg_ne_zero.mpr hη.ne')
      rw [abs_of_pos hη] at h1
      rw [abs_neg, abs_of_pos hη] at h2
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ K * η ^ (-p) * Real.exp (σ * t) + K * η ^ (-p) * Real.exp (σ * t) := add_le_add h1 h2
        _ = _ := by field_simp; ring
    · have := (tendsto_rpow_neg_atTop hp).const_mul (2 * K * Real.exp (σ * t) / t)
      simpa using this
  have hI : Tendsto (fun η : ℝ => ∫ y in (-η)..η, cexp (((σ : ℂ) + y * I) * t) *
      deriv G (σ + y * I)) atTop
      (𝓝 (∫ y : ℝ, cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I))) :=
    intervalIntegral_tendsto_integral (h.integrable_deriv_line hσ) tendsto_neg_atTop_atBot
      tendsto_id
  have h2 := ((hB.sub (hI.const_mul (1 / (t : ℂ)))).const_mul (2 * Real.pi : ℂ)⁻¹)
  have h3 := h2.congr fun η => (hibp η).symm
  convert h3 using 2
  ring

/-- The bound `‖(2πi)^{−1} ∫_{σ−i∞}^{σ+i∞} e^{tz} G(z) dz‖ ≤ (2πt)^{−1} e^{σt} K′ σ^{−p} J(p+1)`. -/
theorem norm_bromwich_le (h : DecayHalfPlane G c₀ c p K K') {σ t : ℝ} (hσ : c ≤ σ) (ht : 0 < t) :
    ‖bromwich G σ t‖ ≤ (2 * Real.pi)⁻¹ * t⁻¹ *
      (Real.exp (σ * t) * K' * (σ ^ (-p) * bromwichJ (p + 1))) := by
  rw [bromwich_eq_of_tendsto (h.tendsto_bromwichPartial hσ ht)]
  have hσ0 : 0 < σ := h.c_pos.trans_le hσ
  have hp1 : 1 < p + 1 := by linarith [h.p_pos]
  have hJ : ∫ y : ℝ, Real.exp (σ * t) * K' * (σ ^ 2 + y ^ 2) ^ (-(p + 1) / 2) =
      Real.exp (σ * t) * K' * (σ ^ (-p) * bromwichJ (p + 1)) := by
    rw [integral_const_mul, integral_line_rpow hσ0]
    congr 3
    ring
  have hb : ‖∫ y : ℝ, cexp (((σ : ℂ) + y * I) * t) * deriv G (σ + y * I)‖ ≤
      Real.exp (σ * t) * K' * (σ ^ (-p) * bromwichJ (p + 1)) := by
    rw [← hJ]
    refine norm_integral_le_of_norm_le ((integrable_line_rpow hσ0 hp1).const_mul _)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    simp only [mul_re, add_re, ofReal_re, mul_im, I_re, I_im, ofReal_im, mul_zero, mul_one,
      sub_zero, add_im, zero_add, add_zero]
    have hb := h.bound' ((σ : ℂ) + y * I) (by simpa using hσ)
    rw [norm_line_rpow] at hb
    calc Real.exp (σ * t) * ‖deriv G ((σ : ℂ) + y * I)‖
        ≤ Real.exp (σ * t) * (K' * (σ ^ 2 + y ^ 2) ^ (-(p + 1) / 2)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := by ring
  have h2π : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht' : ‖-(1 / (t : ℂ))‖ = t⁻¹ := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg ht.le, one_div]
  rw [norm_mul, norm_mul, h2π, ht', mul_assoc]
  gcongr

/-- **Rotation of the line**: for `c ≤ σ₁ ≤ σ₂` the Bromwich integrals along `ℜz = σ₁` and
`ℜz = σ₂` agree (Cauchy's theorem on the rectangle; the horizontal sides are `O(η^{−p})`). -/
theorem bromwich_shift_le (h : DecayHalfPlane G c₀ c p K K') {σ₁ σ₂ t : ℝ} (h1 : c ≤ σ₁)
    (h12 : σ₁ ≤ σ₂) (ht : 0 < t) : bromwich G σ₁ t = bromwich G σ₂ t := by
  have h2 : c ≤ σ₂ := h1.trans h12
  have hσ₁ : c₀ < σ₁ := h.lt.trans_le h1
  have hU : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const continuous_re
  set F : ℂ → ℂ := fun z => cexp (z * t) * G z with hF
  have hFd : ∀ η : ℝ, DifferentiableOn ℂ F ([[σ₁, σ₂]] ×ℂ [[-η, η]]) := by
    intro η z hz
    rw [Complex.mem_reProdIm, uIcc_of_le h12] at hz
    have hzre : c₀ < z.re := by linarith [hz.1.1]
    have hGz : DifferentiableAt ℂ G z := h.differentiableOn.differentiableAt (hU.mem_nhds hzre)
    exact (((differentiableAt_id.mul_const _).cexp).mul hGz).differentiableWithinAt
  -- Cauchy's theorem on the rectangle `[σ₁, σ₂] × [−η, η]`
  have hcauchy : ∀ η : ℝ, (∫ x in σ₁..σ₂, F (x + ((-η : ℝ) : ℂ) * I)) -
      (∫ x in σ₁..σ₂, F (x + (η : ℂ) * I)) + I • (∫ y in (-η)..η, F (σ₂ + y * I)) -
      I • (∫ y in (-η)..η, F (σ₁ + y * I)) = 0 := by
    intro η
    have hre1 : ((σ₁ : ℂ) + ((-η : ℝ) : ℂ) * I).re = σ₁ := by simp
    have him1 : ((σ₁ : ℂ) + ((-η : ℝ) : ℂ) * I).im = -η := by simp
    have hre2 : ((σ₂ : ℂ) + (η : ℂ) * I).re = σ₂ := by simp
    have him2 : ((σ₂ : ℂ) + (η : ℂ) * I).im = η := by simp
    have hc := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((σ₁ : ℂ) + ((-η : ℝ) : ℂ) * I) ((σ₂ : ℂ) + (η : ℂ) * I)
      (by rw [hre1, him1, hre2, him2]; exact hFd η)
    rwa [hre1, him1, hre2, him2] at hc
  -- the horizontal sides
  have hhor : ∀ η' : ℝ, η' ≠ 0 → ‖∫ x in σ₁..σ₂, F (x + (η' : ℂ) * I)‖ ≤
      K * Real.exp (σ₂ * t) * |σ₂ - σ₁| * |η'| ^ (-p) := by
    intro η' hη'
    have hK : 0 ≤ K := by
      have hb := h.bound (c : ℂ) (by simp)
      have hpos : 0 < ‖(c : ℂ)‖ ^ (-p) := Real.rpow_pos_of_pos
        (by rw [Complex.norm_real, Real.norm_of_nonneg h.c_pos.le]; exact h.c_pos) _
      nlinarith [norm_nonneg (G c)]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := K * Real.exp (σ₂ * t) * |η'| ^ (-p)) fun x hx => ?_).trans ?_
    · rw [uIoc_of_le h12] at hx
      have := h.norm_boundary_le (t := t) (h1.trans hx.1.le) η' hη'
      simp only [hF]
      rw [mul_comm]
      refine this.trans ?_
      have he : Real.exp (x * t) ≤ Real.exp (σ₂ * t) := by
        gcongr
        exact hx.2
      have hKp : 0 ≤ K * |η'| ^ (-p) := mul_nonneg hK (Real.rpow_nonneg (abs_nonneg _) _)
      calc K * |η'| ^ (-p) * Real.exp (x * t) ≤ K * |η'| ^ (-p) * Real.exp (σ₂ * t) :=
            mul_le_mul_of_nonneg_left he hKp
        _ = _ := by ring
    · exact le_of_eq (by ring)
  have hp := h.p_pos
  have hlimp := (tendsto_rpow_neg_atTop hp).const_mul (K * Real.exp (σ₂ * t) * |σ₂ - σ₁|)
  rw [mul_zero] at hlimp
  have hplus : Tendsto (fun η : ℝ => ∫ x in σ₁..σ₂, F (x + (η : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlimp
    filter_upwards [eventually_gt_atTop 0] with η hη
    have := hhor η hη.ne'
    rwa [abs_of_pos hη] at this
  have hminus : Tendsto (fun η : ℝ => ∫ x in σ₁..σ₂, F (x + ((-η : ℝ) : ℂ) * I)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlimp
    filter_upwards [eventually_gt_atTop 0] with η hη
    have := hhor (-η) (neg_ne_zero.mpr hη.ne')
    rwa [abs_neg, abs_of_pos hη] at this
  obtain ⟨L₁, hL₁⟩ : ∃ L, Tendsto (bromwichPartial G σ₁ t) atTop (𝓝 L) :=
    ⟨_, h.tendsto_bromwichPartial h1 ht⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L, Tendsto (bromwichPartial G σ₂ t) atTop (𝓝 L) :=
    ⟨_, h.tendsto_bromwichPartial h2 ht⟩
  rw [bromwich_eq_of_tendsto hL₁, bromwich_eq_of_tendsto hL₂]
  have hdiff : Tendsto (fun η => bromwichPartial G σ₂ t η - bromwichPartial G σ₁ t η) atTop
      (𝓝 0) := by
    have hlim := (hplus.sub hminus).const_mul (-I * (2 * Real.pi : ℂ)⁻¹)
    rw [sub_zero, mul_zero] at hlim
    refine hlim.congr fun η => ?_
    have hc := hcauchy η
    simp only [smul_eq_mul] at hc
    simp only [bromwichPartial]
    set V₁ := ∫ y in (-η)..η, F (σ₁ + y * I)
    set V₂ := ∫ y in (-η)..η, F (σ₂ + y * I)
    set Hp := ∫ x in σ₁..σ₂, F (x + (η : ℂ) * I)
    set Hm := ∫ x in σ₁..σ₂, F (x + ((-η : ℝ) : ℂ) * I)
    linear_combination (I * (2 * Real.pi : ℂ)⁻¹) * hc +
      (-(2 * Real.pi : ℂ)⁻¹ * (V₂ - V₁)) * I_mul_I
  exact (sub_eq_zero.mp (tendsto_nhds_unique (hL₂.sub hL₁) hdiff)).symm

end DecayHalfPlane

/-! ### The expansion 2.4.4 and the inverse transform 2.4.5 -/

theorem continuous_cexp_mul_line {G : ℂ → ℂ} {c₀ σ : ℝ} (hG : ContinuousOn G {z | c₀ < z.re})
    (hσ : c₀ < σ) (t : ℝ) :
    Continuous fun y : ℝ => cexp (((σ : ℂ) + y * I) * t) * G (σ + y * I) :=
  (by fun_prop : Continuous fun y : ℝ => cexp (((σ : ℂ) + y * I) * t)).mul
    (continuous_line_comp hG fun y => mem_halfPlane_line hσ y)

theorem mem_slitPlane_of_re_pos' {z : ℂ} (hz : 0 < z.re) : z ∈ slitPlane := Or.inl hz

/-- The asymptotic scale `t^{(s+λ−μ)/μ}` as `t → 0+`. -/
theorem isAsympScale_cpow_nhdsGT {lam : ℂ} {μ : ℝ} (hμ : 0 < μ) :
    IsAsympScaleDLMF (𝓝[>] (0 : ℝ))
      (fun s (t : ℝ) => (t : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) := fun s => by
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hlim : Tendsto (fun r : ℝ => ((r ^ (1 / μ) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((Real.continuous_rpow_const (one_div_pos.mpr hμ).le).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [Real.zero_rpow (one_div_pos.mpr hμ).ne'] at h0
    have h1 := (continuous_ofReal.tendsto 0).comp h0
    rwa [ofReal_zero] at h1
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : (0 : ℝ) < r := hr
  have hsub : (((s + 1 : ℕ) : ℂ) + lam - μ) / μ - (((s : ℂ) + lam - μ) / μ) =
      ((1 / μ : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← cpow_sub _ _ (ofReal_ne_zero.mpr hr.ne'), hsub, ← ofReal_cpow hr.le]

/-- **DLMF 2.4.4–2.4.5**: let `Q` be analytic in `ℜz > c₀`, `0 ≤ c₀ < c`, with the expansion
2.4.4 `Q(z) ∼ ∑ Γ(αₛ) aₛ z^{−αₛ}`, `αₛ = (s+λ)/μ`, as `z → ∞` in `ℜz ≥ c`, and with the
differentiated expansion `Q′(z) ∼ ∑ −αₛ Γ(αₛ) aₛ z^{−αₛ−1}` (2.4.4 "differentiable"). Then for
every `t > 0`:
* the inverse integral 2.4.5 converges for every `σ ≥ c` (`bromwich Q σ t` is its value);
* it is independent of `σ ∈ [c, ∞)`;
* `q(t) = bromwich Q c t` has the expansion 2.3.7, `q(t) ∼ ∑ aₛ t^{(s+λ−μ)/μ}` as `t → 0+`. -/
theorem dlmf_2_4_5 {Q : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ} {μ c₀ c : ℝ} (hlam : 0 < lam.re)
    (hμ : 0 < μ) (hc₀ : 0 ≤ c₀) (hc : c₀ < c) (hQd : DifferentiableOn ℂ Q {z | c₀ < z.re})
    (hQ : IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | c ≤ z.re})
      (fun s z => z ^ (-watsonExpC lam μ s)) Q
      (fun s z => Complex.Gamma (watsonExpC lam μ s) * a s * z ^ (-watsonExpC lam μ s)))
    (hQ' : IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | c ≤ z.re})
      (fun s z => z ^ (-watsonExpC lam μ s - 1)) (deriv Q)
      (fun s z => -watsonExpC lam μ s * Complex.Gamma (watsonExpC lam μ s) * a s *
        z ^ (-watsonExpC lam μ s - 1))) :
    (∀ σ, c ≤ σ → ∀ t, 0 < t → Tendsto (bromwichPartial Q σ t) atTop (𝓝 (bromwich Q σ t))) ∧
    (∀ σ₁ σ₂, c ≤ σ₁ → c ≤ σ₂ → ∀ t, 0 < t → bromwich Q σ₁ t = bromwich Q σ₂ t) ∧
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun s (t : ℝ) => (t : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) (bromwich Q c)
      (fun s (t : ℝ) => a s * (t : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) := by
  set α := watsonExpC lam μ with hαdef
  have hpos := watsonExpC_re_pos hlam hμ
  have hc0 : 0 < c := hc₀.trans_lt hc
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hαsub : ∀ s : ℕ, ((s : ℂ) + lam - μ) / μ = α s - 1 := fun s => by
    rw [hαdef, watsonExpC, sub_div, div_self hμc]
  set U := {z : ℂ | c₀ < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hslit : ∀ z ∈ U, z ∈ slitPlane := fun z hz =>
    mem_slitPlane_of_re_pos' (hc₀.trans_lt hz)
  have hsub : {z : ℂ | c ≤ z.re} ⊆ U := fun z hz => hc.trans_le hz
  -- the remainders and their derivatives
  set R : ℕ → ℂ → ℂ := fun n z =>
    Q z - ∑ s ∈ Finset.range n, Complex.Gamma (α s) * a s * z ^ (-α s) with hR
  set R' : ℕ → ℂ → ℂ := fun n z =>
    deriv Q z - ∑ s ∈ Finset.range n, -α s * Complex.Gamma (α s) * a s * z ^ (-α s - 1) with hR'
  have hRderivAt : ∀ n, ∀ z ∈ U, HasDerivAt (R n) (R' n z) z := by
    intro n z hz
    have hQz : HasDerivAt Q (deriv Q z) z := (hQd.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hterm : ∀ s, HasDerivAt (fun z => Complex.Gamma (α s) * a s * z ^ (-α s))
        (Complex.Gamma (α s) * a s * (-α s * z ^ (-α s - 1))) z := fun s =>
      (Complex.hasStrictDerivAt_cpow_const (hslit z hz)).hasDerivAt.const_mul _
    have hsum := HasDerivAt.fun_sum (u := Finset.range n) fun s _ => hterm s
    have h := hQz.sub hsum
    refine (h.congr_deriv ?_)
    simp only [hR']
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hRd : ∀ n, DifferentiableOn ℂ (R n) U := fun n z hz =>
    (hRderivAt n z hz).differentiableAt.differentiableWithinAt
  have hRderiv : ∀ n, ∀ z ∈ U, deriv (R n) z = R' n z := fun n z hz => (hRderivAt n z hz).deriv
  have hR'c : ∀ n, ContinuousOn (R' n) U := fun n =>
    (hQd.analyticOnNhd hU).deriv.continuousOn.sub (continuousOn_finsetSum _ fun s _ =>
      (continuousOn_id.cpow_const fun z hz => hslit z hz).const_mul _)
  have hdecay : ∀ n, ∃ K K', DecayHalfPlane (R n) c₀ c (α n).re K K' := by
    intro n
    obtain ⟨K, -, hK⟩ := bound_of_isBigO_halfPlane hc0 ((hRd n).continuousOn.mono hsub)
      (hpos n).le (hQ.2 n)
    have hO' : IsBigODLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | c ≤ z.re}) (R' n)
        (fun z => z ^ (-(α n + 1))) := by
      have := hQ'.2 n
      simp only [neg_add']
      exact this
    obtain ⟨K', -, hK'⟩ := bound_of_isBigO_halfPlane hc0 ((hR'c n).mono hsub)
      (by rw [add_re, one_re]; linarith [hpos n]) hO'
    refine ⟨K, K', hc₀, hc, hpos n, hRd n, hK, fun z hz => ?_⟩
    rw [hRderiv n z (hsub hz)]
    have := hK' z hz
    rwa [add_re, one_re] at this
  have hR0 : R 0 = Q := by
    funext z
    simp [hR]
  obtain ⟨K₀, K₀', hd0⟩ := hdecay 0
  rw [hR0] at hd0
  refine ⟨fun σ hσ t ht => ?_, fun σ₁ σ₂ h1 h2 t ht => ?_, isAsympScale_cpow_nhdsGT hμ,
    fun n => ?_⟩
  · have := hd0.tendsto_bromwichPartial hσ ht
    rwa [bromwich_eq_of_tendsto this]
  · rcases le_total σ₁ σ₂ with h12 | h12
    · exact hd0.bromwich_shift_le h1 h12 ht
    · exact (hd0.bromwich_shift_le h2 h12 ht).symm
  -- the remainder after `n` terms
  obtain ⟨K, K', hdn⟩ := hdecay n
  have hslitc : ∀ y : ℝ, (c : ℂ) + y * I ∈ slitPlane := fun y =>
    mem_slitPlane_of_re_pos' (by simpa using hc0)
  have hdiff : ∀ t : ℝ, 0 < t → bromwich Q c t - ∑ s ∈ Finset.range n,
      a s * (t : ℂ) ^ (((s : ℂ) + lam - μ) / μ) = bromwich (R n) c t := by
    intro t ht
    have hdec : ∀ η, bromwichPartial Q c t η = bromwichPartial (R n) c t η +
        ∑ s ∈ Finset.range n,
          a s * bromwichPartial (fun z => Complex.Gamma (α s) * z ^ (-α s)) c t η := by
      intro η
      simp only [bromwichPartial, hR]
      have hQi : IntervalIntegrable (fun y : ℝ => cexp (((c : ℂ) + y * I) * t) * Q (c + y * I))
          volume (-η) η :=
        (continuous_cexp_mul_line hQd.continuousOn hc t).intervalIntegrable _ _
      have hti : ∀ s, Continuous fun y : ℝ =>
          a s * (cexp (((c : ℂ) + y * I) * t) *
            (Complex.Gamma (α s) * ((c : ℂ) + y * I) ^ (-α s))) := fun s => by
        refine continuous_const.mul ((by fun_prop : Continuous fun y : ℝ =>
          cexp (((c : ℂ) + y * I) * t)).mul (continuous_const.mul ?_))
        exact (by fun_prop : Continuous fun y : ℝ => (c : ℂ) + y * I).cpow continuous_const
          fun y => hslitc y
      have heq : ∀ y : ℝ, cexp (((c : ℂ) + y * I) * t) *
          (Q (c + y * I) - ∑ s ∈ Finset.range n,
            Complex.Gamma (α s) * a s * ((c : ℂ) + y * I) ^ (-α s)) =
          cexp (((c : ℂ) + y * I) * t) * Q (c + y * I) - ∑ s ∈ Finset.range n,
            a s * (cexp (((c : ℂ) + y * I) * t) *
              (Complex.Gamma (α s) * ((c : ℂ) + y * I) ^ (-α s))) := by
        intro y
        rw [mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      rw [intervalIntegral.integral_congr (fun y _ => heq y), intervalIntegral.integral_sub hQi
        ((continuous_finsetSum _ fun s _ => hti s).intervalIntegrable _ _),
        intervalIntegral.integral_finsetSum fun s _ => (hti s).intervalIntegrable _ _, mul_sub,
        Finset.mul_sum]
      have hsum_eq : ∑ s ∈ Finset.range n, (2 * Real.pi : ℂ)⁻¹ * ∫ y in (-η)..η,
          a s * (cexp (((c : ℂ) + y * I) * t) *
            (Complex.Gamma (α s) * ((c : ℂ) + y * I) ^ (-α s))) =
          ∑ s ∈ Finset.range n, a s * ((2 * Real.pi : ℂ)⁻¹ * ∫ y in (-η)..η,
            cexp (((c : ℂ) + y * I) * t) * (Complex.Gamma (α s) * ((c : ℂ) + y * I) ^ (-α s))) :=
        Finset.sum_congr rfl fun s _ => by rw [intervalIntegral.integral_const_mul]; ring
      rw [hsum_eq]
      ring
    have hlimR := hdn.tendsto_bromwichPartial le_rfl ht
    have hlimQ := hd0.tendsto_bromwichPartial le_rfl ht
    have hlimS : Tendsto (fun η => ∑ s ∈ Finset.range n,
        a s * bromwichPartial (fun z => Complex.Gamma (α s) * z ^ (-α s)) c t η) atTop
        (𝓝 (∑ s ∈ Finset.range n, a s * (t : ℂ) ^ (α s - 1))) :=
      tendsto_finsetSum _ fun s _ => (bromwich_Gamma_cpow (hpos s) hc0 ht).const_mul (a s)
    have huniq := tendsto_nhds_unique hlimQ ((hlimR.add hlimS).congr fun η => (hdec η).symm)
    rw [bromwich_eq_of_tendsto hlimQ, bromwich_eq_of_tendsto hlimR, huniq]
    simp only [hαsub]
    ring
  set p := (α n).re with hp
  have hp0 : 0 < p := hpos n
  refine isBigODLMF_of_bound
    (K := (2 * Real.pi)⁻¹ * (Real.exp 1 * K' * bromwichJ (p + 1))) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (one_div_pos.mpr hc0)] with t ht
    have ht0 : 0 < t := ht.1
    have hσ : c ≤ 1 / t := by
      rw [le_div_iff₀ ht0]
      have := ht.2
      rw [lt_div_iff₀ hc0] at this
      linarith
    rw [hdiff t ht0, hdn.bromwich_shift_le le_rfl hσ ht0]
    have hb := hdn.norm_bromwich_le hσ ht0
    have h1 : 1 / t * t = 1 := by field_simp
    have h2 : (1 / t) ^ (-p) = t ^ p := by
      rw [one_div, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, neg_neg]
    rw [h1, h2] at hb
    have hnorm : ‖(t : ℂ) ^ (((n : ℂ) + lam - μ) / μ)‖ = t ^ (p - 1) := by
      rw [norm_cpow_eq_rpow_re_of_pos ht0, hαsub, sub_re, one_re]
    rw [hnorm]
    calc _ ≤ (2 * Real.pi)⁻¹ * t⁻¹ * (Real.exp 1 * K' * (t ^ p * bromwichJ (p + 1))) := hb
      _ = (2 * Real.pi)⁻¹ * (Real.exp 1 * K' * bromwichJ (p + 1)) * (t⁻¹ * t ^ p) := by ring
      _ = _ := by rw [Real.rpow_sub_one ht0.ne', div_eq_inv_mul]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)) _

/-! ### The integral 2.4.5 need not converge absolutely -/

/-- DLMF says the integral 2.4.5 "converges absolutely at each limit". For `Q(z) = Γ(λ) z^{−λ}`
with `0 < λ ≤ 1` (which satisfies all hypotheses of 2.4.5, with `μ = 1`, `a₀ = 1`,
`aₛ = 0` otherwise) it does not: `|e^{tz} Q(z)| = e^{σt} Γ(λ) |z|^{−λ}` is not integrable on the
line. -/
theorem dlmf_2_4_5_not_absolutely {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {σ t : ℝ}
    (hσ : 0 < σ) :
    ¬ IntegrableOn (fun y : ℝ => cexp (((σ : ℂ) + y * I) * t) *
      (Complex.Gamma lam * ((σ : ℂ) + y * I) ^ (-(lam : ℂ)))) (Ioi 0) := by
  intro hint
  have hΓ : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos h0
  set C := Real.exp (σ * t) * Real.Gamma lam * 2 ^ (-lam) with hC
  have hC0 : 0 < C := by positivity
  have hlow : ∀ y : ℝ, σ ≤ y → C * y ^ (-lam) ≤
      ‖cexp (((σ : ℂ) + y * I) * t) * (Complex.Gamma lam * ((σ : ℂ) + y * I) ^ (-(lam : ℂ)))‖ := by
    intro y hy
    have hy0 : 0 < y := hσ.trans_le hy
    rw [norm_mul, norm_mul, Complex.norm_exp, show -(lam : ℂ) = ((-lam : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_real, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg hΓ.le]
    simp only [mul_re, add_re, ofReal_re, mul_im, I_re, I_im, ofReal_im, mul_zero, mul_one,
      sub_zero, add_im, zero_add, add_zero]
    have hle : ‖(σ : ℂ) + y * I‖ ≤ 2 * y := by
      calc ‖(σ : ℂ) + y * I‖ ≤ ‖(σ : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = σ + y := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg hσ.le, Real.norm_of_nonneg hy0.le]
        _ ≤ 2 * y := by linarith
    have hpow : (2 * y) ^ (-lam) ≤ ‖(σ : ℂ) + y * I‖ ^ (-lam) :=
      Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr (ne_zero_of_re_ge hσ (by simp))) hle
        (by linarith)
    rw [Real.mul_rpow (by norm_num) hy0.le] at hpow
    calc C * y ^ (-lam) = Real.exp (σ * t) * (Real.Gamma lam * (2 ^ (-lam) * y ^ (-lam))) := by
          rw [hC]; ring
      _ ≤ _ := by gcongr
  have hI : IntegrableOn (fun y : ℝ => C * y ^ (-lam)) (Ioi σ) := by
    refine Integrable.mono' (hint.mono_set (Ioi_subset_Ioi hσ.le)).norm
      ((measurable_id.pow_const _).const_mul C).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_))
    have hy : σ < y := hy
    rw [Real.norm_of_nonneg (mul_nonneg hC0.le (Real.rpow_nonneg (hσ.trans hy).le _))]
    exact hlow y hy.le
  have hI' : IntegrableOn (fun y : ℝ => y ^ (-lam)) (Ioi σ) := by
    refine IntegrableOn.congr_fun (hI.const_mul C⁻¹) (fun y _ => ?_) measurableSet_Ioi
    rw [← mul_assoc, inv_mul_cancel₀ hC0.ne', one_mul]
  have := (integrableOn_Ioi_rpow_iff hσ).mp hI'
  linarith

end Azurite.DLMF
