/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Watson
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# DLMF §2.4(i): Watson's lemma for a complex parameter (2.4.1)

`laplaceIntegralC q z` is the improper Laplace transform `lim_{R→∞} ∫₀^R e^{−zt} q(t) dt` for
complex `z`. The hypotheses are those of §2.3(ii) (`dlmf_2_3_8`), with `λ` complex, `ℜλ > 0`. The
expansion 2.3.7 is `q(t) ∼ ∑ aₛ t^{(s+λ−μ)/μ}` as `t → 0+`, with complex powers of `t > 0`. As in
DLMF, the transform converges for all sufficiently large `ℜz`.

* `integral_cpow_mul_cexp_neg_complex`:
  `∫₀^∞ t^{a−1} e^{−zt} dt = Γ(a) z^{−a}` for `ℜa > 0`, `ℜz > 0`. Mathlib has only real `z`;
  the complex case follows by analytic continuation in `z`.
* `watsonC_near_zero`: the contribution of `(0, b]`, with explicit constants depending on `z`
  only through `ℜz`.
* `laplace_tail_le_complex`, `laplace_tail_exists_complex`: the tail beyond `b` is at most
  `B(1 + |z − x₀|/(ℜz − x₀)) e^{−(ℜz−x₀)b}` (Abel summation against the convergent transform at
  a real `x₀`).
* `dlmf_2_4_1`: 2.4.1 as a generalized expansion with scale `z^{−(s+λ)/μ}` (principal powers), as
  `z → ∞` in the sector `|ph z| ≤ π/2 − δ` (`watsonSector δ`), i.e. along
  `Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ)`. In the sector `ℜz ≥ |z| sin δ`, so the tail is
  exponentially small and `(ℜz)^{−ℜαₙ} ≤ (sin δ)^{−ℜαₙ} |z|^{−ℜαₙ}`.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory

namespace Azurite.DLMF

/-! ### `∫₀^∞ t^{a−1} e^{−zt} dt = Γ(a) z^{−a}` for complex `a` and `z` -/

theorem norm_cexp_neg_mul_ofReal (z : ℂ) (t : ℝ) : ‖cexp (-z * t)‖ = Real.exp (-(z.re * t)) := by
  rw [Complex.norm_exp]
  simp

theorem norm_ofReal_cpow_mul_cexp {a z : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (a - 1) * cexp (-(z * t))‖ = t ^ (a.re - 1) * Real.exp (-z.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, Real.rpow_one]
  simp

theorem measurable_cpow_mul_cexp (a z : ℂ) :
    Measurable fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(z * t)) := by
  fun_prop

theorem integrableOn_cpow_mul_cexp_neg {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(z * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < a.re - 1) one_pos hz
  exact Integrable.mono' h (measurable_cpow_mul_cexp a z).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (norm_ofReal_cpow_mul_cexp ht).le)

/-- The function `z ↦ ∫₀^∞ t^{a−1} e^{−zt} dt` is analytic on `ℜz > 0`. -/
theorem analyticOnNhd_integral_cpow_mul_cexp {a : ℂ} (ha : 0 < a.re) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(z * t)))
      {z | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s₀ hs₀ => ?_)
    (isOpen_lt continuous_const continuous_re)
  have hs₀' : 0 < s₀.re := hs₀
  set δ := s₀.re / 2
  have hδ : 0 < δ := half_pos hs₀'
  have hball : ∀ s ∈ Metric.ball s₀ δ, δ < s.re := fun s hs => by
    have h1 : |s.re - s₀.re| < δ := by
      calc |s.re - s₀.re| = |(s - s₀).re| := by rw [sub_re]
        _ ≤ ‖s - s₀‖ := abs_re_le_norm _
        _ < δ := by rwa [← dist_eq_norm]
    have := (abs_lt.mp h1).1
    simp only [δ] at this ⊢
    linarith
  have hbound := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < a.re) one_pos hδ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s t => (t : ℂ) ^ (a - 1) * cexp (-(s * t)))
    (F' := fun s t => (t : ℂ) ^ (a - 1) * (cexp (-(s * t)) * (-(t : ℂ))))
    (bound := fun t => t ^ a.re * Real.exp (-δ * t ^ (1 : ℝ)))
    (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s => (measurable_cpow_mul_cexp a s).aestronglyMeasurable)
    (integrableOn_cpow_mul_cexp_neg ha hs₀')
    ((by fun_prop : Measurable fun t : ℝ =>
      (t : ℂ) ^ (a - 1) * (cexp (-(s₀ * t)) * (-(t : ℂ))))).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht s hs => by
      have ht0 : 0 < t := ht
      rw [← mul_assoc, norm_mul, norm_ofReal_cpow_mul_cexp ht0, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg ht0.le, Real.rpow_one]
      calc t ^ (a.re - 1) * Real.exp (-s.re * t) * t = t ^ a.re * Real.exp (-s.re * t) := by
            rw [mul_right_comm, ← Real.rpow_add_one ht0.ne', sub_add_cancel]
        _ ≤ t ^ a.re * Real.exp (-δ * t) := by
            gcongr
            nlinarith [hball s hs])
    hbound
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ s _ => by
      have h0 : HasDerivAt (fun y : ℂ => -(y * t)) (-(t : ℂ)) s := by
        have h1 := ((hasDerivAt_id s).mul_const (t : ℂ)).neg
        simp only [id, one_mul] at h1
        exact h1
      exact h0.cexp.const_mul ((t : ℂ) ^ (a - 1)))
  exact key.2.differentiableAt.differentiableWithinAt

/-- `∫₀^∞ t^{a−1} e^{−zt} dt = (1/z)^a Γ(a)` for `ℜa > 0`, `ℜz > 0`. -/
theorem integral_cpow_mul_cexp_neg_complex {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(z * t)) = (1 / z) ^ a * Complex.Gamma a := by
  set U := {s : ℂ | 0 < s.re}
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (1 / s) ^ a * Complex.Gamma a) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_)
      (isOpen_lt continuous_const continuous_re)
    have hw' : 0 < w.re := hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw'; simp at hw'
    have hslit : 1 / w ∈ slitPlane := by
      left
      rw [one_div, inv_re]
      exact div_pos hw' (normSq_pos.mpr hw0)
    exact ((((differentiableAt_id.inv hw0).congr_of_eventuallyEq
      (Eventually.of_forall fun w => by simp [one_div])).cpow_const hslit).mul_const
      _).differentiableWithinAt
  have hEq := (analyticOnNhd_integral_cpow_mul_cexp ha).eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 0).isPreconnected (show (1 : ℂ) ∈ U by simp [U]) ?_
  · exact hEq hz
  have hreal : ∀ r : ℝ, 0 < r → ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * t)) =
      (1 / (r : ℂ)) ^ a * Complex.Gamma a := fun r hr =>
    integral_cpow_mul_exp_neg_mul_Ioi ha hr
  set u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
      rw [add_zero] at h
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
      rw [Complex.ofReal_one] at h2
      exact h2
    · simp only [u, mem_compl_iff, mem_singleton_iff]
      rw [← Complex.ofReal_one, Complex.ofReal_inj]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall fun n => ?_)
  exact hreal _ (by positivity)

theorem arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ Real.pi := by
  intro h
  have := norm_mul_cos_arg z
  rw [h, Real.cos_pi] at this
  linarith [norm_nonneg z]

theorem one_div_cpow_of_re_pos {z : ℂ} (hz : 0 < z.re) (a : ℂ) : (1 / z) ^ a = z ^ (-a) := by
  rw [one_div, inv_cpow z a (arg_ne_pi_of_re_pos hz), cpow_neg]

/-- `∫₀^∞ e^{−zt} t^{a−1} dt = Γ(a) z^{−a}` (principal power) for `ℜa > 0`, `ℜz > 0`. -/
theorem integral_cexp_mul_cpow {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-z * t) * (t : ℂ) ^ (a - 1) = Complex.Gamma a * z ^ (-a) := by
  have h : (fun t : ℝ => cexp (-z * t) * (t : ℂ) ^ (a - 1)) =
      fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(z * t)) := funext fun t => by
    rw [neg_mul, mul_comm]
  rw [h, integral_cpow_mul_cexp_neg_complex ha hz, one_div_cpow_of_re_pos hz, mul_comm]

theorem integrableOn_cexp_mul_cpow {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-z * t) * (t : ℂ) ^ (a - 1)) (Ioi 0) :=
  (integrableOn_cpow_mul_cexp_neg ha hz).congr_fun (fun t _ => by
    simp only
    rw [neg_mul, mul_comm]) measurableSet_Ioi

/-! ### The contribution of a neighbourhood of the origin -/

/-- The tail `∫_b^∞ e^{−zt} t^{a−1} dt` is at most `e^{−(ℜz−1)b} Γ(ℜa)` for `ℜz ≥ 1`. -/
theorem norm_integral_Ioi_cexp_mul_cpow_le {a z : ℂ} (ha : 0 < a.re) (hz : 1 ≤ z.re) {b : ℝ}
    (hb : 0 ≤ b) :
    ‖∫ t in Ioi b, cexp (-z * t) * (t : ℂ) ^ (a - 1)‖ ≤
      Real.exp (-((z.re - 1) * b)) * Real.Gamma a.re := by
  have hG := Real.GammaIntegral_convergent ha
  have hGb := hG.mono_set (Ioi_subset_Ioi hb)
  calc ‖∫ t in Ioi b, cexp (-z * t) * (t : ℂ) ^ (a - 1)‖
      ≤ ∫ t in Ioi b, Real.exp (-((z.re - 1) * b)) * (Real.exp (-t) * t ^ (a.re - 1)) := by
        refine norm_integral_le_of_norm_le (hGb.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
        have ht : b < t := ht
        have ht0 : 0 < t := hb.trans_lt ht
        rw [norm_mul, norm_cexp_neg_mul_ofReal, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
          ← mul_assoc, ← Real.exp_add]
        gcongr
        nlinarith
    _ = Real.exp (-((z.re - 1) * b)) * ∫ t in Ioi b, Real.exp (-t) * t ^ (a.re - 1) :=
        integral_const_mul _ _
    _ ≤ Real.exp (-((z.re - 1) * b)) * Real.Gamma a.re := by
        gcongr
        rw [Real.Gamma_eq_integral ha]
        exact setIntegral_mono_set hG ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun t ht => mul_nonneg (Real.exp_pos _).le
            (Real.rpow_nonneg (le_of_lt ht) _))) (Ioi_subset_Ioi hb).eventuallyLE

/-- `∫₀^∞ t^{β−1} e^{−rt} dt = Γ(β) r^{−β}` (real form). -/
theorem integral_rpow_mul_exp_neg_eq {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * Real.exp (-(r * t)) = Real.Gamma β * r ^ (-β) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hr, one_div, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le, mul_comm]

theorem integrableOn_rpow_mul_exp_neg' {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (β - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < β - 1) one_pos hr
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- The core of 2.4.1 near `t = 0`: if `|q(t) − ∑_{s<n} aₛ t^{αₛ−1}| ≤ C t^{ℜαₙ−1}` on `(0, b]`
(`ℜαₛ > 0`), then for `ℜz ≥ 1`,
`|∫₀^b e^{−zt} q(t) dt − ∑_{s<n} Γ(αₛ) aₛ z^{−αₛ}|
  ≤ C Γ(ℜαₙ) (ℜz)^{−ℜαₙ} + (∑ |aₛ| Γ(ℜαₛ)) e^{−(ℜz−1)b}`. -/
theorem watsonC_near_zero {q : ℝ → ℂ} {a : ℕ → ℂ} {α : ℕ → ℂ} {n : ℕ} {b C : ℝ} {z : ℂ}
    (hb : 0 < b) (hz : 1 ≤ z.re) (hq : Measurable q) (hα : ∀ s ≤ n, 0 < (α s).re)
    (hr : ∀ t ∈ Ioc 0 b,
      ‖q t - ∑ s ∈ Finset.range n, a s * (t : ℂ) ^ (α s - 1)‖ ≤ C * t ^ ((α n).re - 1)) :
    IntegrableOn (fun t : ℝ => cexp (-z * t) * q t) (Ioc 0 b) ∧
    ‖(∫ t in Ioc 0 b, cexp (-z * t) * q t) -
        ∑ s ∈ Finset.range n, Complex.Gamma (α s) * a s * z ^ (-α s)‖ ≤
      C * Real.Gamma (α n).re * z.re ^ (-(α n).re) +
        (∑ s ∈ Finset.range n, ‖a s‖ * Real.Gamma (α s).re) * Real.exp (-((z.re - 1) * b)) := by
  have hz0 : 0 < z.re := by linarith
  have hαn := hα n le_rfl
  have hC : 0 ≤ C := by
    have h := hr b ⟨hb, le_rfl⟩
    have hp : 0 < b ^ ((α n).re - 1) := Real.rpow_pos_of_pos hb _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (q b - ∑ s ∈ Finset.range n, a s * (b : ℂ) ^ (α s - 1))]
  set r : ℝ → ℂ := fun t => q t - ∑ s ∈ Finset.range n, a s * (t : ℂ) ^ (α s - 1) with hrdef
  set g : ℕ → ℝ → ℂ := fun s t => cexp (-z * t) * (t : ℂ) ^ (α s - 1) with hgdef
  have hgI : ∀ s ∈ Finset.range n, IntegrableOn (g s) (Ioi 0) := fun s hs =>
    integrableOn_cexp_mul_cpow (hα s (Finset.mem_range.mp hs).le) hz0
  have hgIoc : ∀ s ∈ Finset.range n, IntegrableOn (g s) (Ioc 0 b) := fun s hs =>
    (hgI s hs).mono_set Ioc_subset_Ioi_self
  -- the remainder
  have hbnd : IntegrableOn (fun t : ℝ => C * (t ^ ((α n).re - 1) * Real.exp (-(z.re * t))))
      (Ioi 0) := (integrableOn_rpow_mul_exp_neg' hαn hz0).const_mul C
  have hrm : Measurable fun t : ℝ => cexp (-z * t) * r t := by
    simp only [hrdef]
    fun_prop
  have hrI : IntegrableOn (fun t : ℝ => cexp (-z * t) * r t) (Ioc 0 b) := by
    refine Integrable.mono' (hbnd.mono_set Ioc_subset_Ioi_self) hrm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_))
    rw [norm_mul, norm_cexp_neg_mul_ofReal]
    calc Real.exp (-(z.re * t)) * ‖r t‖ ≤ Real.exp (-(z.re * t)) * (C * t ^ ((α n).re - 1)) :=
          mul_le_mul_of_nonneg_left (hr t ht) (Real.exp_pos _).le
      _ = _ := by ring
  have hdecomp : (fun t : ℝ => cexp (-z * t) * q t) =
      fun t : ℝ => cexp (-z * t) * r t + ∑ s ∈ Finset.range n, a s * g s t := by
    funext t
    simp only [hrdef, hgdef]
    rw [mul_sub, Finset.mul_sum]
    have : ∑ x ∈ Finset.range n, cexp (-z * t) * (a x * (t : ℂ) ^ (α x - 1)) =
        ∑ x ∈ Finset.range n, a x * (cexp (-z * t) * (t : ℂ) ^ (α x - 1)) :=
      Finset.sum_congr rfl fun s _ => by ring
    rw [this, sub_add_cancel]
  have hsumI : IntegrableOn (fun t => ∑ s ∈ Finset.range n, a s * g s t) (Ioc 0 b) :=
    integrable_finsetSum _ fun s hs => (hgIoc s hs).const_mul (a s)
  refine ⟨by rw [hdecomp]; exact hrI.add hsumI, ?_⟩
  -- each term
  have hterm : ∀ s ∈ Finset.range n, ∫ t in Ioc 0 b, g s t =
      Complex.Gamma (α s) * z ^ (-α s) - ∫ t in Ioi b, g s t := by
    intro s hs
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := b))
      measurableSet_Ioi (hgIoc s hs) ((hgI s hs).mono_set (Ioi_subset_Ioi hb.le))
    rw [Ioc_union_Ioi_eq_Ioi hb.le, integral_cexp_mul_cpow
      (hα s (Finset.mem_range.mp hs).le) hz0] at hsplit
    rw [hsplit, add_sub_cancel_right]
  rw [hdecomp, integral_add hrI hsumI, integral_finsetSum _ fun s hs => (hgIoc s hs).const_mul _]
  have hsum_eq : ∑ s ∈ Finset.range n, ∫ t in Ioc 0 b, a s * g s t =
      ∑ s ∈ Finset.range n, Complex.Gamma (α s) * a s * z ^ (-α s) -
        ∑ s ∈ Finset.range n, a s * ∫ t in Ioi b, g s t := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [integral_const_mul, hterm s hs]
    ring
  rw [hsum_eq]
  have h1 : ‖∫ t in Ioc 0 b, cexp (-z * t) * r t‖ ≤
      C * Real.Gamma (α n).re * z.re ^ (-(α n).re) := by
    calc ‖∫ t in Ioc 0 b, cexp (-z * t) * r t‖
        ≤ ∫ t in Ioc 0 b, C * (t ^ ((α n).re - 1) * Real.exp (-(z.re * t))) := by
          refine norm_integral_le_of_norm_le (hbnd.mono_set Ioc_subset_Ioi_self)
            ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_))
          rw [norm_mul, norm_cexp_neg_mul_ofReal]
          calc Real.exp (-(z.re * t)) * ‖r t‖ ≤
                Real.exp (-(z.re * t)) * (C * t ^ ((α n).re - 1)) :=
              mul_le_mul_of_nonneg_left (hr t ht) (Real.exp_pos _).le
            _ = _ := by ring
      _ ≤ ∫ t in Ioi 0, C * (t ^ ((α n).re - 1) * Real.exp (-(z.re * t))) :=
          setIntegral_mono_set hbnd ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun t ht => mul_nonneg hC (mul_nonneg
              (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)))
            Ioc_subset_Ioi_self.eventuallyLE
      _ = C * Real.Gamma (α n).re * z.re ^ (-(α n).re) := by
          rw [integral_const_mul, integral_rpow_mul_exp_neg_eq hαn hz0]
          ring
  have h2 : ‖∑ s ∈ Finset.range n, a s * ∫ t in Ioi b, g s t‖ ≤
      (∑ s ∈ Finset.range n, ‖a s‖ * Real.Gamma (α s).re) * Real.exp (-((z.re - 1) * b)) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
    rw [norm_mul, mul_assoc]
    gcongr
    rw [mul_comm]
    exact norm_integral_Ioi_cexp_mul_cpow_le (hα s (Finset.mem_range.mp hs).le) hz hb.le
  calc _ = ‖(∫ t in Ioc 0 b, cexp (-z * t) * r t) -
        ∑ s ∈ Finset.range n, a s * ∫ t in Ioi b, g s t‖ := by ring_nf
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add h1 h2)

/-! ### The tail -/

/-- Complex form of `laplace_tail_le`: if `|∫_b^t e^{−x₀u} q(u) du| ≤ B` on `[b, R]` and
`ℜz > x₀`, then `|∫_b^R e^{−zt} q(t) dt| ≤ B(1 + |z − x₀|/(ℜz − x₀)) e^{−(ℜz−x₀)b}`. -/
theorem laplace_tail_le_complex {q : ℝ → ℂ} {b x₀ B R : ℝ} {z : ℂ} (hbR : b ≤ R)
    (hz : x₀ < z.re)
    (hk : IntervalIntegrable (fun u : ℝ => cexp (-(x₀ : ℂ) * u) * q u) volume b R)
    (hB : ∀ t ∈ Icc b R, ‖∫ u in b..t, cexp (-(x₀ : ℂ) * u) * q u‖ ≤ B) :
    ‖∫ t in b..R, cexp (-z * t) * q t‖ ≤
      B * (1 + ‖z - x₀‖ / (z.re - x₀)) * Real.exp (-((z.re - x₀) * b)) := by
  set c : ℂ := z - x₀ with hcdef
  have hcre : c.re = z.re - x₀ := by simp [hcdef]
  have hc : 0 < c.re := by rw [hcre]; linarith
  have hB0 : 0 ≤ B := by
    have := hB b (left_mem_Icc.mpr hbR)
    rwa [intervalIntegral.integral_same, norm_zero] at this
  set k := fun u : ℝ => cexp (-(x₀ : ℂ) * u) * q u with hkdef
  set Φ := fun t : ℝ => ∫ u in b..t, k u with hΦdef
  set ψ := fun t : ℝ => cexp (-c * t) with hψdef
  have hψ : ∀ t, HasDerivAt ψ (-c * ψ t) t := fun t => by
    have h := ((hasDerivAt_id (t : ℂ)).const_mul (-c)).cexp
    rw [mul_one] at h
    have h2 := h.comp_ofReal
    simp only [id_eq] at h2
    rw [mul_comm] at h2
    exact h2
  have hψc : Continuous ψ := by fun_prop
  have key := integral_primitive_mul_deriv_on hbR hk (fun t _ => hψ t)
    (by fun_prop : Continuous fun t : ℝ => -c * ψ t).continuousOn
  have hks : ∀ u, k u * ψ u = cexp (-z * u) * q u := fun u => by
    simp only [hkdef, hψdef]
    rw [mul_right_comm, ← Complex.exp_add]
    congr 2
    rw [hcdef]
    ring
  have hsplit : ∫ u in b..R, k u * (ψ R - ψ u) =
      ψ R * Φ R - ∫ u in b..R, cexp (-z * u) * q u := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hk.mul_continuousOn continuousOn_const)
      (hk.mul_continuousOn hψc.continuousOn)]
    simp_rw [hks]
    congr 1
    rw [intervalIntegral.integral_mul_const]
    exact mul_comm _ _
  have heq : ∫ u in b..R, cexp (-z * u) * q u =
      ψ R * Φ R - ∫ t in b..R, Φ t * (-c * ψ t) := by
    linear_combination key + hsplit
  have hnψ : ∀ t, ‖ψ t‖ = Real.exp (-(c.re * t)) := fun t => norm_cexp_neg_mul_ofReal c t
  have h1 : ‖ψ R * Φ R‖ ≤ B * Real.exp (-(c.re * b)) := by
    rw [norm_mul, hnψ, mul_comm]
    have hR := hB R (right_mem_Icc.mpr hbR)
    have he : Real.exp (-(c.re * R)) ≤ Real.exp (-(c.re * b)) := by
      gcongr
    exact mul_le_mul hR he (Real.exp_pos _).le hB0
  set M := ‖c‖ with hM
  have h2 : ‖∫ t in b..R, Φ t * (-c * ψ t)‖ ≤ B * M * Real.exp (-(c.re * b)) / c.re := by
    refine norm_intervalIntegral_le_exp (f := fun t => Φ t * (-c * ψ t)) (K := B * M)
      hbR hc (by positivity) fun t ht => ?_
    rw [norm_mul, norm_mul, norm_neg, hnψ, ← hM]
    have hBt := hB t (Ioc_subset_Icc_self ht)
    calc ‖Φ t‖ * (M * Real.exp (-(c.re * t))) ≤ B * (M * Real.exp (-(c.re * t))) := by
          gcongr
      _ = B * M * Real.exp (-(c.re * t)) := by ring
  have hfin : B * Real.exp (-(c.re * b)) + B * M * Real.exp (-(c.re * b)) / c.re =
      B * (1 + M / (z.re - x₀)) * Real.exp (-((z.re - x₀) * b)) := by
    rw [← hcre]
    field_simp
  rw [heq, ← hfin]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- The tail of a Laplace transform convergent at `x₀`: for `ℜz > x₀`,
`|∫_b^∞ e^{−zt} q(t) dt| ≤ B(1 + |z − x₀|/(ℜz − x₀)) e^{−(ℜz−x₀)b}`, `B` independent of `z`. -/
theorem laplace_tail_exists_complex {q : ℝ → ℂ} {x₀ b : ℝ} (hb : 0 < b)
    (hloc : ∀ R, 0 ≤ R → IntervalIntegrable q volume 0 R)
    (hconv : ∃ L, Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(x₀ : ℂ) * t) * q t) atTop
      (𝓝 L)) :
    ∃ B, 0 ≤ B ∧ ∀ z : ℂ, x₀ < z.re → ∀ L,
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-z * t) * q t) atTop (𝓝 L) →
      ‖L - ∫ t in (0 : ℝ)..b, cexp (-z * t) * q t‖ ≤
        B * (1 + ‖z - x₀‖ / (z.re - x₀)) * Real.exp (-((z.re - x₀) * b)) := by
  have hii := intervalIntegrable_laplace_mul hloc
  have hiiC : ∀ (z : ℂ) {α β : ℝ}, 0 ≤ α → α ≤ β →
      IntervalIntegrable (fun t : ℝ => cexp (-z * t) * q t) volume α β := fun z α β hα hαβ => by
    have h := (hloc β (hα.trans hαβ)).mono_set (by
      rw [uIcc_of_le hαβ, uIcc_of_le (hα.trans hαβ)]; exact Icc_subset_Icc_left hα)
    exact h.continuousOn_mul (by fun_prop)
  obtain ⟨L₀, hL₀⟩ := hconv
  set Φ := fun t : ℝ => ∫ u in b..t, cexp (-(x₀ : ℂ) * u) * q u with hΦdef
  set Λ := L₀ - ∫ u in (0 : ℝ)..b, cexp (-(x₀ : ℂ) * u) * q u
  have hΦt : Tendsto Φ atTop (𝓝 Λ) := by
    refine (hL₀.sub_const _).congr' ?_
    filter_upwards [eventually_ge_atTop b] with t ht
    rw [hΦdef, ← intervalIntegral.integral_add_adjacent_intervals
      (hii x₀ le_rfl hb.le) (hii x₀ hb.le ht), add_sub_cancel_left]
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hΦt.norm.eventually (gt_mem_nhds (lt_add_one ‖Λ‖)))
  set T' := max T b
  have hΦc : ContinuousOn Φ (Icc b T') := by
    have h := intervalIntegral.continuousOn_primitive_interval' (hii x₀ hb.le
      (le_max_right T b)) (a := b) left_mem_uIcc
    rwa [uIcc_of_le (le_max_right _ _)] at h
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦc
  set B := max B₁ (‖Λ‖ + 1)
  have hBall : ∀ t, b ≤ t → ‖Φ t‖ ≤ B := by
    intro t ht
    rcases le_or_gt t T' with h | h
    · exact (hB₁ t ⟨ht, h⟩).trans (le_max_left _ _)
    · exact (hT t ((le_max_left _ _).trans h.le)).le.trans (le_max_right _ _)
  refine ⟨B, (norm_nonneg _).trans (hBall b le_rfl), fun z hz L hL => ?_⟩
  refine le_of_tendsto ((hL.sub_const _).norm) ?_
  filter_upwards [eventually_ge_atTop b] with R hR
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiiC z le_rfl hb.le)
    (hiiC z hb.le hR), add_sub_cancel_left]
  exact laplace_tail_le_complex hR hz (hii x₀ hb.le hR) (fun t ht => hBall t ht.1)

/-! ### Watson's lemma in a sector -/

/-- The Laplace transform `lim_{R→∞} ∫₀^R e^{−zt} q(t) dt` for complex `z`. -/
noncomputable def laplaceIntegralC (q : ℝ → ℂ) (z : ℂ) : ℂ :=
  limUnder atTop fun R => ∫ t in (0 : ℝ)..R, cexp (-z * t) * q t

/-- The closed sector `|ph z| ≤ π/2 − δ`. -/
def watsonSector (δ : ℝ) : Set ℂ := {z | |arg z| ≤ Real.pi / 2 - δ}

theorem re_ge_of_mem_watsonSector {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : z ∈ watsonSector δ) :
    Real.sin δ * ‖z‖ ≤ z.re := by
  have hz' : |arg z| ≤ Real.pi / 2 - δ := hz
  rw [← norm_mul_cos_arg z, ← Real.cos_abs (arg z), ← Real.cos_pi_div_two_sub δ, mul_comm]
  gcongr
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz'

/-- The exponents `αₛ = (s+λ)/μ` of 2.4.1, now complex. -/
noncomputable def watsonExpC (lam : ℂ) (μ : ℝ) (s : ℕ) : ℂ := ((s : ℂ) + lam) / μ

theorem watsonExpC_re {lam : ℂ} {μ : ℝ} (s : ℕ) :
    (watsonExpC lam μ s).re = ((s : ℝ) + lam.re) / μ := by
  simp [watsonExpC, div_re, normSq_ofReal]
  field_simp

theorem watsonExpC_re_pos {lam : ℂ} {μ : ℝ} (hlam : 0 < lam.re) (hμ : 0 < μ) (s : ℕ) :
    0 < (watsonExpC lam μ s).re := by
  rw [watsonExpC_re]
  positivity

theorem norm_cpow_neg_ge {z : ℂ} (hz : z ≠ 0) (α : ℂ) :
    ‖z‖ ^ (-α.re) ≤ Real.exp (Real.pi * |α.im|) * ‖z ^ (-α)‖ := by
  rw [norm_cpow_of_ne_zero hz, neg_re, neg_im, mul_div_assoc', le_div_iff₀ (Real.exp_pos _),
    mul_comm (Real.exp (Real.pi * |α.im|))]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  calc arg z * -α.im ≤ |arg z * -α.im| := le_abs_self _
    _ = |arg z| * |α.im| := by rw [abs_mul, abs_neg]
    _ ≤ Real.pi * |α.im| := by
        gcongr
        exact abs_arg_le_pi z

theorem cpow_ne_zero_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) : z ^ w ≠ 0 := by
  rw [cpow_def_of_ne_zero hz]
  exact Complex.exp_ne_zero _

/-- **DLMF 2.4.1 (Watson's lemma, complex parameter)**: if `ℜλ > 0`, `μ > 0`,
`q(t) ∼ ∑ aₛ t^{(s+λ−μ)/μ}` as `t → 0+` (2.3.7) and the Laplace transform converges for all
sufficiently large `ℜz`, then `∫₀^∞ e^{−zt} q(t) dt ∼ ∑ Γ((s+λ)/μ) aₛ z^{−(s+λ)/μ}` as
`z → ∞` in `|ph z| ≤ π/2 − δ`, with principal powers. -/
theorem dlmf_2_4_1 {q : ℝ → ℂ} {a : ℕ → ℂ} {lam : ℂ} {μ x₀ δ : ℝ} (hlam : 0 < lam.re)
    (hμ : 0 < μ) (hδ : 0 < δ) (hδ' : δ ≤ Real.pi / 2) (hq : Measurable q)
    (hloc : ∀ c R, 0 < c → c ≤ R → IntervalIntegrable q volume c R)
    (hexp : IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun s (t : ℝ) => (t : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) q
      (fun s (t : ℝ) => a s * (t : ℂ) ^ (((s : ℂ) + lam - μ) / μ)))
    (hconv : ∀ z : ℂ, x₀ ≤ z.re → ∃ L,
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-z * t) * q t) atTop (𝓝 L)) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ))
      (fun s z => z ^ (-watsonExpC lam μ s)) (laplaceIntegralC q)
      (fun s z => Complex.Gamma (watsonExpC lam μ s) * a s * z ^ (-watsonExpC lam μ s)) := by
  set α := watsonExpC lam μ with hαdef
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hαsub : ∀ s : ℕ, ((s : ℂ) + lam - μ) / μ = α s - 1 := fun s => by
    rw [hαdef, watsonExpC, sub_div, div_self hμc]
  have hpos := watsonExpC_re_pos hlam hμ
  have hcob : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ)) atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hsec : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ), z ∈ watsonSector δ :=
    mem_inf_of_right (mem_principal_self _)
  refine ⟨fun s => ?_, fun n => ?_⟩
  · have hlim : Tendsto (fun z : ℂ => ‖z‖ ^ (-(1 / μ)))
        (Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ)) (𝓝 0) :=
      (tendsto_rpow_neg_atTop (one_div_pos.mpr hμ)).comp hcob
    rw [IsLittleODLMF, tendsto_zero_iff_norm_tendsto_zero]
    refine hlim.congr' ?_
    filter_upwards [hcob.eventually (eventually_gt_atTop 0)] with z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp hz
    rw [← cpow_sub _ _ hz0]
    have : -α (s + 1) - -α s = (((-(1 / μ)) : ℝ) : ℂ) := by
      simp only [hαdef, watsonExpC]
      push_cast
      ring
    rw [this, norm_cpow_real]
  have hφ0 : ∀ m : ℕ, ∀ t : ℝ, 0 < t → (t : ℂ) ^ (((m : ℂ) + lam - μ) / μ) ≠ 0 :=
    fun m t ht => by
      rw [← norm_pos_iff, norm_cpow_eq_rpow_re_of_pos ht]
      exact Real.rpow_pos_of_pos ht _
  have hbd : ∀ m : ℕ, ∃ b C, 0 < b ∧ b ≤ 1 ∧ ∀ t ∈ Ioc 0 b,
      ‖q t - ∑ s ∈ Finset.range m, a s * (t : ℂ) ^ (α s - 1)‖ ≤ C * t ^ ((α m).re - 1) := by
    intro m
    obtain ⟨b, C, hb, hb1, h⟩ :=
      exists_bound_of_isBigODLMF_nhdsGT (hexp.2 m) (hφ0 m) zero_lt_one
    refine ⟨b, C, hb, hb1, fun t ht => ?_⟩
    have h1 := h t ht
    simp only [hαsub] at h1
    rwa [norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re] at h1
  obtain ⟨b, C, hb, -, hr⟩ := hbd n
  obtain ⟨b₀, C₀, hb₀, -, hr₀⟩ := hbd 0
  have hloc0 := intervalIntegrable_zero_of_bound hb₀
    (by linarith [hpos 0] : -1 < (α 0).re - 1) hq.aestronglyMeasurable
    (by simpa using hr₀) hloc
  obtain ⟨B, hB0, hBt⟩ := laplace_tail_exists_complex hb hloc0 (hconv x₀ (by simp))
  set β := (α n).re with hβ
  have hβ0 : 0 < β := hpos n
  have hC : 0 ≤ C := by
    have h := hr b ⟨hb, le_rfl⟩
    have hp : 0 < b ^ (β - 1) := Real.rpow_pos_of_pos hb _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (q b - ∑ s ∈ Finset.range n, a s * (b : ℂ) ^ (α s - 1))]
  set sδ := Real.sin δ with hsδdef
  have hsδ : 0 < sδ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hsδ1 : sδ ≤ 1 := Real.sin_le_one δ
  set D := ∑ s ∈ Finset.range n, ‖a s‖ * Real.Gamma (α s).re with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun s _ =>
    mul_nonneg (norm_nonneg _) (Real.Gamma_pos_of_pos (hpos s)).le
  have hG0 : 0 ≤ Real.Gamma β := (Real.Gamma_pos_of_pos hβ0).le
  set K := B * (1 + 4 / sδ) + C * Real.Gamma β * sδ ^ (-β) + D * Real.exp b with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ sδ ^ (-β) := Real.rpow_nonneg hsδ.le _
    positivity
  refine isBigODLMF_of_bound (K := K * Real.exp (Real.pi * |(α n).im|)) ?_ ?_
  · filter_upwards [hsec, hcob.eventually (eventually_ge_atTop (2 * (|x₀| + 1) / sδ)),
      hcob.eventually (eventually_exp_neg_le_rpow_neg β (half_pos (mul_pos hsδ hb))),
      hcob.eventually (eventually_exp_neg_le_rpow_neg β (mul_pos hsδ hb)),
      hcob.eventually (eventually_gt_atTop 0)] with z hzS hzR he1 he2 hz0
    have hre := re_ge_of_mem_watsonSector hδ.le hzS
    have hR : 2 * (|x₀| + 1) ≤ sδ * ‖z‖ := by rwa [div_le_iff₀' hsδ] at hzR
    have hx₀ := le_abs_self x₀
    have hzre1 : 1 ≤ z.re := by linarith [abs_nonneg x₀]
    have hzx : x₀ < z.re := by linarith
    have hgap : sδ * ‖z‖ / 2 ≤ z.re - x₀ := by linarith
    have hnorm : ‖z - (x₀ : ℂ)‖ ≤ 2 * ‖z‖ := by
      have h1 : sδ * ‖z‖ ≤ ‖z‖ := by nlinarith [norm_nonneg z]
      calc ‖z - (x₀ : ℂ)‖ ≤ ‖z‖ + ‖(x₀ : ℂ)‖ := norm_sub_le _ _
        _ = ‖z‖ + |x₀| := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 * ‖z‖ := by linarith
    have hratio : ‖z - (x₀ : ℂ)‖ / (z.re - x₀) ≤ 4 / sδ := by
      rw [div_le_div_iff₀ (by linarith) hsδ]
      nlinarith [mul_le_mul_of_nonneg_right hnorm hsδ.le]
    obtain ⟨L, hL⟩ := hconv z hzx.le
    have hF : laplaceIntegralC q z = L := hL.limUnder_eq
    have htail := hBt z hzx L hL
    obtain ⟨-, hNZ⟩ := watsonC_near_zero (α := α) hb hzre1 hq (fun s _ => hpos s) hr
    have hexp1 : Real.exp (-((z.re - x₀) * b)) ≤ ‖z‖ ^ (-β) := by
      refine le_trans (Real.exp_le_exp.mpr ?_) he1
      have h := mul_le_mul_of_nonneg_right hgap hb.le
      have e : sδ * b / 2 * ‖z‖ = sδ * ‖z‖ / 2 * b := by ring
      linarith
    have hexp2 : Real.exp (-((z.re - 1) * b)) ≤ Real.exp b * ‖z‖ ^ (-β) := by
      calc Real.exp (-((z.re - 1) * b)) = Real.exp b * Real.exp (-(z.re * b)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ Real.exp b * Real.exp (-(sδ * b * ‖z‖)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            have h := mul_le_mul_of_nonneg_right hre hb.le
            have e : sδ * b * ‖z‖ = sδ * ‖z‖ * b := by ring
            linarith
        _ ≤ Real.exp b * ‖z‖ ^ (-β) := by gcongr
    have hrpow : z.re ^ (-β) ≤ sδ ^ (-β) * ‖z‖ ^ (-β) := by
      rw [← Real.mul_rpow hsδ.le (norm_nonneg _)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hre (by linarith)
    have hI : ∫ t in (0 : ℝ)..b, cexp (-z * t) * q t = ∫ t in Ioc 0 b, cexp (-z * t) * q t :=
      intervalIntegral.integral_of_le hb.le
    have hmain : ‖L - ∑ s ∈ Finset.range n, Complex.Gamma (α s) * a s * z ^ (-α s)‖ ≤
        K * ‖z‖ ^ (-β) := by
      calc _ = ‖(L - ∫ t in (0 : ℝ)..b, cexp (-z * t) * q t) +
            ((∫ t in Ioc 0 b, cexp (-z * t) * q t) -
              ∑ s ∈ Finset.range n, Complex.Gamma (α s) * a s * z ^ (-α s))‖ := by
            rw [hI]
            ring_nf
        _ ≤ ‖L - ∫ t in (0 : ℝ)..b, cexp (-z * t) * q t‖ +
            ‖(∫ t in Ioc 0 b, cexp (-z * t) * q t) -
              ∑ s ∈ Finset.range n, Complex.Gamma (α s) * a s * z ^ (-α s)‖ := norm_add_le _ _
        _ ≤ B * (1 + ‖z - (x₀ : ℂ)‖ / (z.re - x₀)) * Real.exp (-((z.re - x₀) * b)) +
            (C * Real.Gamma β * z.re ^ (-β) + D * Real.exp (-((z.re - 1) * b))) :=
            add_le_add htail hNZ
        _ ≤ B * (1 + 4 / sδ) * ‖z‖ ^ (-β) +
            (C * Real.Gamma β * (sδ ^ (-β) * ‖z‖ ^ (-β)) + D * (Real.exp b * ‖z‖ ^ (-β))) := by
            have h4 : 0 ≤ B * (1 + 4 / sδ) := by positivity
            exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hratio]) hB0)
              hexp1 (Real.exp_pos _).le h4)
              (add_le_add (mul_le_mul_of_nonneg_left hrpow (mul_nonneg hC hG0))
                (mul_le_mul_of_nonneg_left hexp2 hD0))
        _ = K * ‖z‖ ^ (-β) := by rw [hK]; ring
    rw [hF]
    calc _ ≤ K * ‖z‖ ^ (-β) := hmain
      _ ≤ K * (Real.exp (Real.pi * |(α n).im|) * ‖z ^ (-α n)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_cpow_neg_ge (norm_pos_iff.mp hz0) _) hK0
      _ = _ := by ring
  · filter_upwards [hcob.eventually (eventually_gt_atTop 0)] with z hz
    exact cpow_ne_zero_of_ne_zero (norm_pos_iff.mp hz) _

end Azurite.DLMF
