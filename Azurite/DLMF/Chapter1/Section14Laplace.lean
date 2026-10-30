/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Parseval
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# DLMF §1.14(iii): Laplace Transform

Formalizations of <https://dlmf.nist.gov/1.14#iii> (definitions, analyticity, translation,
differentiation in `s`, periodic functions, convolution, uniqueness); inversion, integration and
derivatives are in `Section14LaplaceInversion.lean`.

**Conventions.** `laplace f s = ∫₀^∞ e^{−st} f(t) dt` (1.14.17) for `f : ℝ → ℂ`, `s : ℂ`.
DLMF's "piecewise continuous of exponential growth" is replaced by the weaker "measurable on
`(0, ∞)` with `|f(t)| ≤ M e^{αt}`" (`ExpGrowth`, 1.14.18).

**Results.**
* Absolute convergence and the bound `|ℒ(f)(s)| ≤ M/(ℜs − α)` (`integrableOn_laplace`,
  `norm_laplace_le`); analyticity for `ℜs > α` (`analyticOnNhd_laplace`, through
  `hasDerivAt_laplace`: `ℒ(f)′ = −ℒ(t f)`); 1.14.19 (`dlmf_1_14_19`, uniformly in `ℑs`).
* 1.14.21–1.14.22: translations (`dlmf_1_14_21`, `dlmf_1_14_22`; `H(0)` immaterial).
* 1.14.23 (`dlmf_1_14_23`): `(−1)ⁿ dⁿℒ(f)/dsⁿ = ℒ(tⁿ f)`, using `tⁿ e^{αt} ≤ n! ε^{−n} e^{(α+ε)t}`
  (`ExpGrowth.pow_mul`).
* 1.14.25–1.14.26: periodic and antiperiodic `f` (`dlmf_1_14_25`, `dlmf_1_14_26`).
* 1.14.30–1.14.31 (`laplaceConv`, `dlmf_1_14_31`): through Mathlib's `integral_convolution`
  applied to `H(t) e^{−st} f(t)`.
* Uniqueness (`dlmf_1_14_iii_unique`): `ℒ(f) = ℒ(g)` on `ℜs > α` forces `f = g` on `[0, ∞)` for
  continuous `f`, `g`. Along `ℜs = α + 1` the transform is a Fourier transform, and an integrable
  function with vanishing Fourier transform vanishes at its continuity points
  (`eq_zero_of_fourier_eq_zero`, from the Gaussian approximate identity of §1.14(i)).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Nat FourierTransform Convolution

namespace Azurite.DLMF

/-- **DLMF (1.14.17)**: `ℒ(f)(s) = ∫₀^∞ e^{−st} f(t) dt`. -/
noncomputable def laplace (f : ℝ → ℂ) (s : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * f t

/-- **DLMF (1.14.18)**: exponential growth `|f(t)| ≤ M e^{αt}`, `0 ≤ t < ∞`. -/
def ExpGrowth (M α : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M * Real.exp (α * t)

theorem norm_cexp_neg_mul (s : ℂ) (t : ℝ) : ‖cexp (-(s * t))‖ = Real.exp (-(s.re * t)) := by
  rw [Complex.norm_exp]; simp

theorem ExpGrowth.nonneg {M α : ℝ} {f : ℝ → ℂ} (h : ExpGrowth M α f) : 0 ≤ M := by
  have := (norm_nonneg _).trans (h 0 le_rfl)
  simpa using this

/-- The Laplace integrand is dominated by `M e^{−(ℜs − α)t}`. -/
theorem norm_laplace_integrand_le {M α : ℝ} {f : ℝ → ℂ} (hg : ExpGrowth M α f) (s : ℂ) {t : ℝ}
    (ht : 0 ≤ t) : ‖cexp (-(s * t)) * f t‖ ≤ M * Real.exp (-(s.re - α) * t) := by
  rw [norm_mul, norm_cexp_neg_mul]
  calc Real.exp (-(s.re * t)) * ‖f t‖ ≤ Real.exp (-(s.re * t)) * (M * Real.exp (α * t)) :=
        mul_le_mul_of_nonneg_left (hg t ht) (Real.exp_pos _).le
    _ = M * Real.exp (-(s.re - α) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem integral_exp_neg_mul_Ioi_zero {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi 0, Real.exp (-b * t) = b⁻¹ := by
  have := MeasureTheory.integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) 0 hb
  simp only [mul_zero] at this
  rw [show (fun t : ℝ => Real.exp (-b * t)) = fun t => Real.exp (-(b * t)) from
    funext fun t => by ring_nf, this, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]

/-- The Laplace integral converges absolutely for `ℜs > α`. -/
theorem integrableOn_laplace {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) : IntegrableOn (fun t : ℝ => cexp (-(s * t)) * f t) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - α) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hs)).const_mul M
  refine hb.mono' (((by fun_prop : Continuous fun t : ℝ => cexp (-(s * t))).aestronglyMeasurable
    ).mul hfm) ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  exact norm_laplace_integrand_le hg s (le_of_lt ht)

theorem norm_laplace_le {M α : ℝ} {f : ℝ → ℂ} (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) : ‖laplace f s‖ ≤ M / (s.re - α) := by
  have hb : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - α) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hs)).const_mul M
  unfold laplace
  refine (norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun t ht => norm_laplace_integrand_le hg s (le_of_lt ht)))).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero (sub_pos.mpr hs), div_eq_mul_inv]

/-- **DLMF (1.14.19)**: `ℒ(f)(s) → 0` as `ℜs → ∞`. -/
theorem dlmf_1_14_19 {M α : ℝ} {f : ℝ → ℂ} (hg : ExpGrowth M α f) :
    Tendsto (laplace f) (comap re atTop) (𝓝 0) := by
  have hM := hg.nonneg
  have h1 : Tendsto (fun s : ℂ => M / (s.re - α)) (comap re atTop) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s.re - α) (comap re atTop) atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_comap
    exact this.const_div_atTop M |>.mono_right le_rfl
  refine squeeze_zero_norm' ?_ h1
  have : ∀ᶠ s : ℂ in comap re atTop, α < s.re :=
    tendsto_comap.eventually (eventually_gt_atTop α)
  filter_upwards [this] with s hs using norm_laplace_le hg hs

/-! ### Analyticity and differentiation (1.14.23) -/

theorem ExpGrowth.pow_mul {M α : ℝ} {f : ℝ → ℂ} (hg : ExpGrowth M α f) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) : ExpGrowth (M * k ! / ε ^ k) (α + ε) (fun t => (t : ℂ) ^ k * f t) := by
  intro t ht
  have hM := hg.nonneg
  have h1 : t ^ k ≤ k ! / ε ^ k * Real.exp (ε * t) := by
    have := Real.pow_div_factorial_le_exp (ε * t) (mul_nonneg hε.le ht) k
    rw [div_le_iff₀ (by positivity), mul_pow] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht]
  calc t ^ k * ‖f t‖ ≤ (k ! / ε ^ k * Real.exp (ε * t)) * (M * Real.exp (α * t)) :=
        mul_le_mul h1 (hg t ht) (norm_nonneg _) (by positivity)
    _ = M * k ! / ε ^ k * Real.exp ((α + ε) * t) := by
        rw [add_mul, Real.exp_add]; ring

theorem aestronglyMeasurable_pow_mul {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (k : ℕ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ k * f t) (volume.restrict (Ioi 0)) :=
  ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ k).aestronglyMeasurable).mul hfm

/-- `ℒ(f)′ = −ℒ(t f)` for `ℜs > α`. -/
theorem hasDerivAt_laplace {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s₀ : ℂ}
    (hs : α < s₀.re) :
    HasDerivAt (laplace f) (-laplace (fun t => (t : ℂ) * f t) s₀) s₀ := by
  set ε := (s₀.re - α) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨M', hg1⟩ : ∃ M', ExpGrowth M' (α + ε / 2) (fun t => (t : ℂ) * f t) :=
    ⟨_, by simpa only [pow_one] using hg.pow_mul 1 (half_pos hε)⟩
  have hM' : 0 ≤ M' := hg1.nonneg
  have hre : ∀ s ∈ Metric.ball s₀ ε, α + ε < s.re := fun s hs' => by
    have := (Complex.abs_re_le_norm (s - s₀)).trans_lt (by rwa [← dist_eq_norm])
    rw [sub_re, abs_lt] at this
    linarith [this.1]
  have hbound : IntegrableOn (fun t : ℝ => M' * Real.exp (-(ε / 2) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (half_pos hε)).const_mul M'
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s (t : ℝ) => cexp (-(s * t)) * f t)
    (F' := fun s (t : ℝ) => -(cexp (-(s * t)) * ((t : ℂ) * f t)))
    (bound := fun t => M' * Real.exp (-(ε / 2) * t)) (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hε)
    (Eventually.of_forall fun s =>
      ((by fun_prop : Continuous fun t : ℝ => cexp (-(s * t))).aestronglyMeasurable).mul hfm)
    (integrableOn_laplace hfm hg hs)
    (((by fun_prop : Continuous fun t : ℝ => cexp (-(s₀ * t))).aestronglyMeasurable).mul
      (aestronglyMeasurable_pow_mul hfm 1 |>.congr (ae_of_all _ fun t => by simp))).neg
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht s hs' => by
      rw [norm_neg]
      refine (norm_laplace_integrand_le hg1 s (le_of_lt ht)).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM'
      have := hre s hs'
      have ht' : (0 : ℝ) < t := ht
      nlinarith))
    hbound
    (ae_of_all _ fun t s _ => by
      have h1 : HasDerivAt (fun s : ℂ => -(s * t)) (-(t : ℂ)) s := by
        have := ((hasDerivAt_id s).mul_const (t : ℂ)).neg
        exact this.congr_deriv (by simp)
      exact (h1.cexp.mul_const (f t)).congr_deriv (by ring))
  have h2 := key.2
  have heq : ∫ t in Ioi (0 : ℝ), -(cexp (-(s₀ * t)) * ((t : ℂ) * f t)) =
      -laplace (fun t => (t : ℂ) * f t) s₀ := by
    rw [integral_neg]; rfl
  rw [heq] at h2
  exact h2

/-- **DLMF §1.14(iii)**: `ℒ(f)` is analytic for `ℜs > α`. -/
theorem analyticOnNhd_laplace {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) :
    AnalyticOnNhd ℂ (laplace f) {s | α < s.re} :=
  DifferentiableOn.analyticOnNhd (fun _ hs =>
    (hasDerivAt_laplace hfm hg hs).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const continuous_re)

theorem iteratedDeriv_laplace {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) (n : ℕ) :
    ∀ s : ℂ, α < s.re →
      iteratedDeriv n (laplace f) s = (-1) ^ n * laplace (fun t => (t : ℂ) ^ n * f t) s := by
  induction n with
  | zero =>
    intro _ _
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    intro s hs
    have hU : IsOpen {z : ℂ | α < z.re} := isOpen_lt continuous_const continuous_re
    have heq : iteratedDeriv n (laplace f) =ᶠ[𝓝 s]
        fun z => (-1) ^ n * laplace (fun t => (t : ℂ) ^ n * f t) z := by
      filter_upwards [hU.mem_nhds hs] with z hz using ih z hz
    set ε := (s.re - α) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hd := hasDerivAt_laplace (aestronglyMeasurable_pow_mul hfm n) (hg.pow_mul n hε)
      (show α + ε < s.re by rw [hεdef]; linarith)
    rw [iteratedDeriv_succ, heq.deriv_eq, (hd.const_mul ((-1 : ℂ) ^ n)).deriv]
    have : (fun t : ℝ => (t : ℂ) * ((t : ℂ) ^ n * f t)) = fun t : ℝ => (t : ℂ) ^ (n + 1) * f t :=
      funext fun t => by ring
    rw [this]
    ring

/-- **DLMF (1.14.23)**: `(−1)ⁿ dⁿℒ(f)/dsⁿ = ℒ(tⁿ f)` for `ℜs > α`. -/
theorem dlmf_1_14_23 {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) (n : ℕ)
    {s : ℂ} (hs : α < s.re) :
    (-1) ^ n * iteratedDeriv n (laplace f) s = laplace (fun t => (t : ℂ) ^ n * f t) s := by
  rw [iteratedDeriv_laplace hfm hg n s hs, ← mul_assoc, ← mul_pow, show (-1 : ℂ) * -1 = 1 by
    norm_num, one_pow, one_mul]

/-! ### Translation (1.14.21)–(1.14.22) -/

theorem setIntegral_Ioi_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (a : ℝ) : ∫ t in Ioi a, g t = ∫ u in Ioi 0, g (u + a) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun t => (Ioi a).indicator g t) a]
  congr 1
  funext u
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u + a ∈ Ioi a by simp [hu]),
      indicator_of_mem (show u ∈ Ioi 0 from hu)]
  · rw [indicator_of_notMem (show u + a ∉ Ioi a by simpa using hu),
      indicator_of_notMem (show u ∉ Ioi 0 from hu)]

/-- **DLMF (1.14.21)**: `ℒ(f)(s − a) = ℒ(f_a)(s)` with `f_a(t) = e^{at} f(t)`. -/
theorem dlmf_1_14_21 (f : ℝ → ℂ) (a s : ℂ) :
    laplace f (s - a) = laplace (fun t => cexp (a * t) * f t) s := by
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- **DLMF (1.14.22)**: for `a ≥ 0`, `ℒ(f_a⁺)(s) = e^{−as} ℒ(f)(s)` with
`f_a⁺(t) = H(t − a) f(t − a)` (the value at `t = a` is immaterial). -/
theorem dlmf_1_14_22 (f : ℝ → ℂ) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    laplace (fun t => if a < t then f (t - a) else 0) s = cexp (-(a * s)) * laplace f s := by
  have h1 : laplace (fun t => if a < t then f (t - a) else 0) s =
      ∫ t in Ioi a, cexp (-(s * t)) * f (t - a) := by
    unfold laplace
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases ht : a < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from lt_of_le_of_lt ha ht),
        indicator_of_mem (show t ∈ Ioi a from ht)]
      simp [ht]
    · rw [indicator_of_notMem (show t ∉ Ioi a from ht)]
      by_cases ht0 : 0 < t
      · rw [indicator_of_mem (show t ∈ Ioi 0 from ht0)]; simp [ht]
      · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht0)]
  rw [h1, setIntegral_Ioi_shift, laplace, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_sub_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-! ### Periodic functions (1.14.25)–(1.14.26) -/

theorem norm_cexp_neg_lt_one {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖cexp (-(a * s))‖ < 1 := by
  have hr : (-((a : ℂ) * s)).re = -(a * s.re) := by simp
  rw [Complex.norm_exp, hr, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

theorem laplace_split {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) {a : ℝ} (ha : 0 < a) :
    laplace f s = (∫ t in (0 : ℝ)..a, cexp (-(s * t)) * f t) +
      cexp (-(a * s)) * ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * f (u + a) := by
  have hi := integrableOn_laplace hfm hg hs
  have h1 : laplace f s = (∫ t in Ioc 0 a, cexp (-(s * t)) * f t) +
      ∫ t in Ioi a, cexp (-(s * t)) * f t := by
    unfold laplace
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi ha.le)),
      Ioc_union_Ioi_eq_Ioi ha.le]
  rw [h1, intervalIntegral.integral_of_le ha.le, setIntegral_Ioi_shift,
    ← integral_const_mul (cexp (-(↑a * s)))]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **DLMF (1.14.25)**: if `f(t + a) = f(t)` for `t > 0`, then
`ℒ(f)(s) = (1 − e^{−as})^{−1} ∫₀^a e^{−st} f(t) dt` (`ℜs > max(α, 0)`). -/
theorem dlmf_1_14_25 {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) (hs0 : 0 < s.re) {a : ℝ} (ha : 0 < a) (hper : ∀ t, 0 < t → f (t + a) = f t) :
    laplace f s = (1 - cexp (-(a * s)))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-(s * t)) * f t := by
  have hsplit := laplace_split hfm hg hs ha
  have heq : ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * f (u + a) = laplace f s :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [hper u hu]
  rw [heq] at hsplit
  have hne : 1 - cexp (-(a * s)) ≠ 0 := by
    intro h
    have := norm_cexp_neg_lt_one ha hs0
    rw [← sub_eq_zero.mp h] at this
    simp at this
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  linear_combination hsplit

/-- **DLMF (1.14.26)**: if `f(t + a) = −f(t)` for `t > 0`, then
`ℒ(f)(s) = (1 + e^{−as})^{−1} ∫₀^a e^{−st} f(t) dt`. -/
theorem dlmf_1_14_26 {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) (hs0 : 0 < s.re) {a : ℝ} (ha : 0 < a)
    (hper : ∀ t, 0 < t → f (t + a) = -f t) :
    laplace f s = (1 + cexp (-(a * s)))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-(s * t)) * f t := by
  have hsplit := laplace_split hfm hg hs ha
  have heq : ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * f (u + a) = -laplace f s := by
    rw [laplace, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [hper u hu]; ring
  rw [heq] at hsplit
  have hne : 1 + cexp (-(a * s)) ≠ 0 := by
    intro h
    have := norm_cexp_neg_lt_one ha hs0
    rw [show cexp (-(a * s)) = -1 by linear_combination h] at this
    simp at this
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  linear_combination hsplit

/-! ### Convolution (1.14.30)–(1.14.31) -/

/-- **DLMF (1.14.30)**: `(f ∗ g)(t) = ∫₀ᵗ f(u) g(t − u) du`. -/
noncomputable def laplaceConv (f g : ℝ → ℂ) (t : ℝ) : ℂ := ∫ u in (0 : ℝ)..t, f u * g (t - u)

/-- **DLMF (1.14.31)**: `ℒ(f ∗ g) = ℒ(f) ℒ(g)` (for `ℜs > α`, `f`, `g` measurable of
exponential growth). -/
theorem dlmf_1_14_31 {M N α : ℝ} {f g : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hf : ExpGrowth M α f)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0))) (hg : ExpGrowth N α g) {s : ℂ}
    (hs : α < s.re) : laplace (laplaceConv f g) s = laplace f s * laplace g s := by
  set F : ℝ → ℂ := (Ioi 0).indicator fun u => cexp (-(s * u)) * f u with hF
  set G : ℝ → ℂ := (Ioi 0).indicator fun u => cexp (-(s * u)) * g u with hG
  have hFi : Integrable F :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_laplace hfm hf hs)
  have hGi : Integrable G :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_laplace hgm hg hs)
  have hconv : ∀ t, (F ⋆[ContinuousLinearMap.mul ℂ ℂ] G) t =
      (Ioi 0).indicator (fun t : ℝ => cexp (-(s * t)) * laplaceConv f g t) t := fun t => by
    simp only [convolution, ContinuousLinearMap.mul_apply']
    have hpt : ∀ u, F u * G (t - u) =
        (Ioo 0 t).indicator (fun u => cexp (-(s * t)) * (f u * g (t - u))) u := fun u => by
      by_cases hu : u ∈ Ioo 0 t
      · rw [indicator_of_mem hu, hF, hG, indicator_of_mem (show u ∈ Ioi 0 from hu.1),
          indicator_of_mem (show t - u ∈ Ioi 0 from sub_pos.mpr hu.2)]
        rw [show cexp (-(s * t)) = cexp (-(s * u)) * cexp (-(s * ↑(t - u))) by
          rw [← Complex.exp_add]; push_cast; ring_nf]
        ring
      · rw [indicator_of_notMem hu]
        simp only [mem_Ioo, not_and_or, not_lt] at hu
        rcases hu with hu | hu
        · rw [hF, indicator_of_notMem (show u ∉ Ioi 0 from not_lt.mpr hu), zero_mul]
        · rw [hG, indicator_of_notMem (show t - u ∉ Ioi 0 by simp; linarith), mul_zero]
    simp_rw [hpt]
    rw [integral_indicator measurableSet_Ioo]
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht), laplaceConv, integral_const_mul,
        intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht), Ioo_eq_empty (by simpa using ht),
        Measure.restrict_empty, integral_zero_measure]
  have hint := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume)
    (ν := volume) hFi hGi
  simp_rw [hconv] at hint
  rw [integral_indicator measurableSet_Ioi, hF, hG, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioi, ContinuousLinearMap.mul_apply'] at hint
  exact hint

/-! ### Uniqueness -/

/-- If `𝓕 h = 0` for integrable `h`, then `h` vanishes at each of its continuity points. -/
theorem eq_zero_of_fourier_eq_zero {h : ℝ → ℂ} (hh : Integrable h) (h0 : ∀ w, 𝓕 h w = 0)
    {v : ℝ} (hv : ContinuousAt h v) : h v = 0 := by
  set hv' : ℝ → ℂ := fun t => h (t + v)
  have hi : Integrable hv' := hh.comp_add_right v
  have hc : ContinuousAt hv' 0 := by
    have hcont : ContinuousAt (fun t : ℝ => t + v) 0 :=
      (continuous_id.add continuous_const).continuousAt
    exact ContinuousAt.comp (g := h) (f := fun t : ℝ => t + v) (by simpa using hv) hcont
  have hF : ∀ w, 𝓕 hv' w = 0 := fun w => by
    rw [Real.fourier_real_eq_integral_exp_smul]
    show ∫ t : ℝ, cexp (↑(-2 * Real.pi * t * w) * I) • h (t + v) = 0
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => cexp (↑(-2 * Real.pi * (x - v) * w) * I) • h x) v
    simp only [add_sub_cancel_right] at this
    rw [this]
    have h1 := h0 w
    rw [Real.fourier_real_eq_integral_exp_smul] at h1
    calc ∫ x : ℝ, cexp (↑(-2 * Real.pi * (x - v) * w) * I) • h x
        = cexp (↑(2 * Real.pi * v * w) * I) *
            ∫ x : ℝ, cexp (↑(-2 * Real.pi * x * w) * I) • h x := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only [smul_eq_mul]
          rw [← mul_assoc, ← Complex.exp_add]
          push_cast
          ring_nf
      _ = 0 := by rw [h1, mul_zero]
  have hlim := tendsto_gauss_fourier hi hc
  simp only [hF, mul_zero, integral_zero] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  simpa [hv'] using this

theorem ExpGrowth.sub {M N α : ℝ} {f g : ℝ → ℂ} (hf : ExpGrowth M α f) (hg : ExpGrowth N α g) :
    ExpGrowth (M + N) α (fun t => f t - g t) := fun t ht =>
  (norm_sub_le _ _).trans (by linarith [hf t ht, hg t ht])

/-- **DLMF §1.14(iii)** (uniqueness): if `f`, `g` are continuous on `[0, ∞)`, of exponential
growth, and `ℒ(f)(s) = ℒ(g)(s)` for `ℜs > α`, then `f = g` on `[0, ∞)`. -/
theorem dlmf_1_14_iii_unique {M N α : ℝ} {f g : ℝ → ℂ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpGrowth M α f) (hg : ExpGrowth N α g)
    (h : ∀ s : ℂ, α < s.re → laplace f s = laplace g s) : ∀ t, 0 ≤ t → f t = g t := by
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    (hfc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    (hgc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  set σ := α + 1
  set H : ℝ → ℂ := (Ioi 0).indicator fun t => cexp (-((σ : ℂ) * t)) * (f t - g t) with hH
  have hHi : Integrable H := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_laplace (hfm.sub hgm) (hf.sub hg) (show α < (σ : ℂ).re by simp [σ]))
  have hF : ∀ w, 𝓕 H w = 0 := fun w => by
    have hs : α < ((σ : ℂ) + 2 * Real.pi * w * I).re := by simp [σ]
    have hl : laplace (fun t => f t - g t) ((σ : ℂ) + 2 * Real.pi * w * I) = 0 := by
      have hlin : laplace (fun t => f t - g t) ((σ : ℂ) + 2 * Real.pi * w * I) =
          laplace f ((σ : ℂ) + 2 * Real.pi * w * I) -
            laplace g ((σ : ℂ) + 2 * Real.pi * w * I) := by
        unfold laplace
        rw [← integral_sub (integrableOn_laplace hfm hf hs) (integrableOn_laplace hgm hg hs)]
        exact integral_congr_ae (ae_of_all _ fun t => by ring)
      rw [hlin, h _ hs, sub_self]
    rw [← hl, Real.fourier_real_eq_integral_exp_smul, laplace, ← integral_indicator
      measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Ioi 0
    · simp only [hH, indicator_of_mem ht, smul_eq_mul]
      rw [← mul_assoc, ← Complex.exp_add]
      push_cast
      ring_nf
    · simp only [hH, indicator_of_notMem ht, smul_zero]
  have hpos : ∀ v, 0 < v → f v = g v := fun v hv => by
    have hca : ContinuousAt H v := by
      have hev : H =ᶠ[𝓝 v] fun t => cexp (-((σ : ℂ) * t)) * (f t - g t) := by
        filter_upwards [Ioi_mem_nhds hv] with t ht
        rw [hH, indicator_of_mem ht]
      refine ContinuousAt.congr ?_ hev.symm
      have hfv := hfc.continuousAt (Ici_mem_nhds hv)
      have hgv := hgc.continuousAt (Ici_mem_nhds hv)
      exact ((by fun_prop : Continuous fun t : ℝ => cexp (-((σ : ℂ) * t))).continuousAt).mul
        (hfv.sub hgv)
    have h0 := eq_zero_of_fourier_eq_zero hHi hF hca
    rw [hH, indicator_of_mem (show v ∈ Ioi 0 from hv)] at h0
    have := (mul_eq_zero.mp h0).resolve_left (Complex.exp_ne_zero _)
    exact sub_eq_zero.mp this
  intro t ht
  rcases ht.lt_or_eq with ht | rfl
  · exact hpos t ht
  · have hf0 := ((hfc 0 (mem_Ici.mpr le_rfl)).mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self))
    have hg0 := ((hgc 0 (mem_Ici.mpr le_rfl)).mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self))
    refine tendsto_nhds_unique hf0 (hg0.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with v hv using (hpos v hv).symm

end Azurite.DLMF
