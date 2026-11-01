/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.L2Space

/-!
# DLMF §1.18(iii): the differential operator `d²/dx²`

https://dlmf.nist.gov/1.18.iii

Real functions on a finite interval `[a, b]`, with `⟨f, g⟩ = ∫_a^b f g`.

* 1.18.25–1.18.26: integration by parts twice (`dlmf_1_18_26`, for functions with first and
  second derivatives on `[a, b]` and integrable second derivatives).
* 1.18.27: `T = d²/dx²` is formally self-adjoint. The boundary terms vanish under Dirichlet
  conditions (`dlmf_1_18_27`), so `T` with domain `𝒟(T)` = `C²` functions with `f(a) = f(b) = 0`
  (`IsDirichletC2`) is symmetric (`dlmf_1_18_iii_symmetric`).
* **DLMF imprecision**: DLMF concludes that `𝒟(T*) = 𝒟(T)` and that this `T` "is indeed self
  adjoint". With `𝒟(T*)` the adjoint domain in `L²(a, b)` (`InAdjointDomainDirichlet`), that is
  false (`dlmf_1_18_iii_not_selfAdjoint`). The `C¹` function
  `g(x) = ((x − c)|x − c| − d(x − c))/2` satisfies `⟨Tf, g⟩ = ⟨f, sign(x − c)⟩` for all `f ∈ 𝒟(T)`,
  but agrees a.e. with no element of `𝒟(T)`, because its second derivative jumps at the midpoint
  `c`. The symmetric operator is only essentially self-adjoint; its closure, with domain
  `H² ∩ H¹₀`, is self-adjoint.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

/-! ### Integration by parts (1.18.25–1.18.27) -/

theorem intervalIntegrable_of_hasDerivAt {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) : IntervalIntegrable f volume a b :=
  ContinuousOn.intervalIntegrable fun x hx => (hf x hx).continuousAt.continuousWithinAt

/-- DLMF 1.18.26: integrating by parts twice,
`∫_a^b f″g = [f′g]_a^b − [fg′]_a^b + ∫_a^b fg″`. -/
theorem dlmf_1_18_26 {a b : ℝ} {f f₁ f₂ g g₁ g₂ : ℝ → ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x ∈ uIcc a b, HasDerivAt f₁ (f₂ x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g₁ x) x) (hg₁ : ∀ x ∈ uIcc a b, HasDerivAt g₁ (g₂ x) x)
    (hf₂ : IntervalIntegrable f₂ volume a b) (hg₂ : IntervalIntegrable g₂ volume a b) :
    ∫ x in a..b, f₂ x * g x =
      (f₁ b * g b - f₁ a * g a) - (f b * g₁ b - f a * g₁ a) + ∫ x in a..b, f x * g₂ x := by
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hf₁
    (intervalIntegrable_of_hasDerivAt hg₁) hf₂
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hg₁
    (intervalIntegrable_of_hasDerivAt hf₁) hg₂
  have e1 : ∫ x in a..b, f₂ x * g x = ∫ x in a..b, g x * f₂ x :=
    intervalIntegral.integral_congr fun x _ => mul_comm _ _
  have e2 : ∫ x in a..b, g₁ x * f₁ x = ∫ x in a..b, f₁ x * g₁ x :=
    intervalIntegral.integral_congr fun x _ => mul_comm _ _
  rw [e1, h1, e2]
  linarith

/-- DLMF 1.18.27: `T = d²/dx²` is formally self-adjoint: `⟨Tf, g⟩ = ⟨f, Tg⟩` up to the boundary
terms of 1.18.26, which vanish when `f(a) = f(b) = 0` and `g(a) = g(b) = 0`. -/
theorem dlmf_1_18_27 {a b : ℝ} {f f₁ f₂ g g₁ g₂ : ℝ → ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x ∈ uIcc a b, HasDerivAt f₁ (f₂ x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g₁ x) x) (hg₁ : ∀ x ∈ uIcc a b, HasDerivAt g₁ (g₂ x) x)
    (hf₂ : IntervalIntegrable f₂ volume a b) (hg₂ : IntervalIntegrable g₂ volume a b)
    (hfa : f a = 0) (hfb : f b = 0) (hga : g a = 0) (hgb : g b = 0) :
    ∫ x in a..b, f₂ x * g x = ∫ x in a..b, f x * g₂ x := by
  rw [dlmf_1_18_26 hf hf₁ hg hg₁ hf₂ hg₂, hfa, hfb, hga, hgb]
  ring

/-- The domain `𝒟(T)` of DLMF's example: `C²` functions with `f(a) = f(b) = 0`. -/
def IsDirichletC2 (a b : ℝ) (f : ℝ → ℝ) : Prop := ContDiff ℝ 2 f ∧ f a = 0 ∧ f b = 0

theorem contDiff_one_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  ContDiff.deriv' (n := 1) (by convert hf; norm_num)

theorem hasDerivAt_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  ⟨(hf.differentiable (by norm_num) x).hasDerivAt,
    ((contDiff_one_deriv hf).differentiable one_ne_zero x).hasDerivAt⟩

/-- DLMF §1.18(iii): with Dirichlet conditions `T = d²/dx²` is symmetric:
`∫_a^b f″ g = ∫_a^b f g″` for `f, g ∈ 𝒟(T)`. -/
theorem dlmf_1_18_iii_symmetric {a b : ℝ} {f g : ℝ → ℝ} (hf : IsDirichletC2 a b f)
    (hg : IsDirichletC2 a b g) :
    ∫ x in a..b, deriv (deriv f) x * g x = ∫ x in a..b, f x * deriv (deriv g) x :=
  dlmf_1_18_27 (fun x _ => (hasDerivAt_of_contDiff_two hf.1 x).1)
    (fun x _ => (hasDerivAt_of_contDiff_two hf.1 x).2)
    (fun x _ => (hasDerivAt_of_contDiff_two hg.1 x).1)
    (fun x _ => (hasDerivAt_of_contDiff_two hg.1 x).2)
    ((contDiff_one_deriv hf.1).continuous_deriv le_rfl |>.intervalIntegrable _ _)
    ((contDiff_one_deriv hg.1).continuous_deriv le_rfl |>.intervalIntegrable _ _)
    hf.2.1 hf.2.2 hg.2.1 hg.2.2

/-! ### The adjoint domain is larger than `𝒟(T)` -/

/-- The domain of the adjoint `T*` in `L²(a, b)` of `T = d²/dx²` on `𝒟(T)`: the `g ∈ L²(a, b)` for
which some `h ∈ L²(a, b)` satisfies `⟨Tf, g⟩ = ⟨f, h⟩` for all `f ∈ 𝒟(T)`. -/
def InAdjointDomainDirichlet (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  MemLp g 2 (volume.restrict (Ioo a b)) ∧ ∃ h : ℝ → ℝ, MemLp h 2 (volume.restrict (Ioo a b)) ∧
    ∀ f, IsDirichletC2 a b f → ∫ x in a..b, deriv (deriv f) x * g x = ∫ x in a..b, f x * h x

theorem hasDerivAt_quadratic (p q r x : ℝ) :
    HasDerivAt (fun y => p * y ^ 2 + q * y + r) (2 * p * x + q) x := by
  have := (((hasDerivAt_pow 2 x).const_mul p).add ((hasDerivAt_id x).const_mul q)).add_const r
  convert this using 1
  simp; ring

theorem hasDerivAt_affine (q r x : ℝ) : HasDerivAt (fun y => q * y + r) q x := by
  have := ((hasDerivAt_id x).const_mul q).add_const r
  simpa using this

/-- **DLMF imprecision in §1.18(iii)**: for `T = d²/dx²` on the Dirichlet `C²` functions of
`[a, b]`, DLMF concludes `𝒟(T*) = 𝒟(T)`, "thus `T` is indeed self adjoint". The operator is
symmetric (`dlmf_1_18_iii_symmetric`) but not self-adjoint. The `C¹` function
`g(x) = ((x − c)|x − c| − d(x − c))/2` (`c, d` the midpoint and half-length of `[a, b]`) lies in
`𝒟(T*)` with `T*g = sign(x − c)`, yet no element of `𝒟(T)` agrees with it a.e., since its second
derivative jumps at `c`. (The self-adjoint operator is the closure, with domain `H² ∩ H¹₀`.) -/
theorem dlmf_1_18_iii_not_selfAdjoint {a b : ℝ} (hab : a < b) :
    ∃ g : ℝ → ℝ, InAdjointDomainDirichlet a b g ∧
      ¬ ∃ f, IsDirichletC2 a b f ∧ f =ᵐ[volume.restrict (Ioo a b)] g := by
  set c := (a + b) / 2
  set d := (b - a) / 2
  have hac : a < c := by simp only [c]; linarith
  have hcb : c < b := by simp only [c]; linarith
  set g : ℝ → ℝ := fun x => ((x - c) * |x - c| - d * (x - c)) / 2
  -- the two quadratic pieces and their derivatives
  set qp : ℝ → ℝ := fun y => (1 / 2) * y ^ 2 + (-(2 * c + d) / 2) * y + (c ^ 2 + d * c) / 2
  set qm : ℝ → ℝ := fun y => (-1 / 2) * y ^ 2 + ((2 * c - d) / 2) * y + (-c ^ 2 + d * c) / 2
  set qp₁ : ℝ → ℝ := fun y => 1 * y + (-(2 * c + d) / 2)
  set qm₁ : ℝ → ℝ := fun y => (-1) * y + ((2 * c - d) / 2)
  have hqp : ∀ x, HasDerivAt qp (qp₁ x) x := fun x => by
    convert hasDerivAt_quadratic (1 / 2) (-(2 * c + d) / 2) ((c ^ 2 + d * c) / 2) x using 1
    simp only [qp₁]; ring
  have hqm : ∀ x, HasDerivAt qm (qm₁ x) x := fun x => by
    convert hasDerivAt_quadratic (-1 / 2) ((2 * c - d) / 2) ((-c ^ 2 + d * c) / 2) x using 1
    simp only [qm₁]; ring
  have hqp₁ : ∀ x, HasDerivAt qp₁ 1 x := fun x => hasDerivAt_affine 1 _ x
  have hqm₁ : ∀ x, HasDerivAt qm₁ (-1) x := fun x => hasDerivAt_affine (-1) _ x
  have hgp : ∀ x, c ≤ x → g x = qp x := fun x hx => by
    simp only [g, qp, abs_of_nonneg (sub_nonneg.mpr hx)]; ring
  have hgm : ∀ x, x ≤ c → g x = qm x := fun x hx => by
    simp only [g, qm, abs_of_nonpos (sub_nonpos.mpr hx)]; ring
  have hgc : Continuous g := by fun_prop
  set h : ℝ → ℝ := fun x => if c < x then 1 else -1
  have hhm : Measurable h := Measurable.ite measurableSet_Ioi measurable_const measurable_const
  refine ⟨g, ⟨?_, h, ?_, fun f hf => ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hgc.continuousOn
    exact MemLp.of_bound hgc.aestronglyMeasurable C
      (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => hC x (Ioo_subset_Icc_self hx))
  · refine MemLp.of_bound hhm.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
    simp only [h]; split_ifs <;> simp
  · -- `∫ f″ g = ∫ f h`
    obtain ⟨hf2, hfa, hfb⟩ := hf
    have hd := hasDerivAt_of_contDiff_two hf2
    have hf₂c : Continuous (deriv (deriv f)) := (contDiff_one_deriv hf2).continuous_deriv le_rfl
    have hfc : Continuous f := hf2.continuous
    have hL : ∫ x in a..c, deriv (deriv f) x * g x = ∫ x in a..c, deriv (deriv f) x * qm x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hac.le] at hx; rw [hgm x hx.2]
    have hR : ∫ x in c..b, deriv (deriv f) x * g x = ∫ x in c..b, deriv (deriv f) x * qp x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hcb.le] at hx; rw [hgp x hx.1]
    have hL' := dlmf_1_18_26 (fun x _ => (hd x).1) (fun x _ => (hd x).2) (fun x _ => hqm x)
      (fun x _ => hqm₁ x) (hf₂c.intervalIntegrable a c) intervalIntegrable_const
    have hR' := dlmf_1_18_26 (fun x _ => (hd x).1) (fun x _ => (hd x).2) (fun x _ => hqp x)
      (fun x _ => hqp₁ x) (hf₂c.intervalIntegrable c b) intervalIntegrable_const
    have hfh : IntervalIntegrable (fun x => f x * h x) volume a b := by
      refine (hfc.intervalIntegrable a b).mono_fun (hfc.measurable.mul hhm).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      simp only [h, norm_mul]
      split_ifs <;> simp
    have hhL : ∫ x in a..c, f x * h x = ∫ x in a..c, f x * (-1) :=
      intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => by
        rw [uIoc_of_le hac.le] at hx
        simp [h, not_lt.mpr hx.2])
    have hhR : ∫ x in c..b, f x * h x = ∫ x in c..b, f x * 1 :=
      intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => by
        rw [uIoc_of_le hcb.le] at hx
        simp [h, hx.1])
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (f := fun x => deriv (deriv f) x * g x) ((hf₂c.mul hgc).intervalIntegrable a c)
        ((hf₂c.mul hgc).intervalIntegrable c b),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hfh.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hab.le]; exact ⟨hac.le, hcb.le⟩)))
        (hfh.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hab.le]; exact ⟨hac.le, hcb.le⟩))),
      hL, hR, hL', hR', hhL, hhR, hfa, hfb]
    have e1 : qm a = 0 := by simp only [qm, c, d]; ring
    have e2 : qp b = 0 := by simp only [qp, c, d]; ring
    have e3 : qm c = qp c := by simp only [qm, qp]; ring
    have e4 : qm₁ c = qp₁ c := by simp only [qm₁, qp₁]; ring
    rw [e1, e2, e3, e4]
    ring
  · -- no element of `𝒟(T)` agrees with `g` a.e.
    rintro ⟨f, ⟨hf2, -, -⟩, hfg⟩
    have heq : EqOn f g (Ioo a b) :=
      Measure.eqOn_of_ae_eq hfg hf2.continuous.continuousOn hgc.continuousOn
        (by rw [interior_Ioo]; exact subset_closure)
    have hf₂c : Continuous (deriv (deriv f)) := (contDiff_one_deriv hf2).continuous_deriv le_rfl
    have hright : ∀ x ∈ Ioo c b, deriv (deriv f) x = 1 := fun x hx => by
      have hev : f =ᶠ[𝓝 x] qp := Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2)
        fun y hy => by rw [heq ⟨hac.trans hy.1, hy.2⟩, hgp y hy.1.le]
      have hev' : deriv f =ᶠ[𝓝 x] qp₁ := hev.deriv.trans
        (Eventually.of_forall fun y => (hqp y).deriv)
      rw [hev'.deriv_eq, (hqp₁ x).deriv]
    have hleft : ∀ x ∈ Ioo a c, deriv (deriv f) x = -1 := fun x hx => by
      have hev : f =ᶠ[𝓝 x] qm := Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2)
        fun y hy => by rw [heq ⟨hy.1, hy.2.trans hcb⟩, hgm y hy.2.le]
      have hev' : deriv f =ᶠ[𝓝 x] qm₁ := hev.deriv.trans
        (Eventually.of_forall fun y => (hqm y).deriv)
      rw [hev'.deriv_eq, (hqm₁ x).deriv]
    have h1 : deriv (deriv f) c = 1 := by
      have ht := (hf₂c.tendsto c).mono_left (nhdsWithin_le_nhds (s := Ioi c))
      refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
      filter_upwards [Ioo_mem_nhdsGT hcb] with x hx using (hright x hx).symm
    have h2 : deriv (deriv f) c = -1 := by
      have ht := (hf₂c.tendsto c).mono_left (nhdsWithin_le_nhds (s := Iio c))
      refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
      filter_upwards [Ioo_mem_nhdsLT hac] with x hx using (hleft x hx).symm
    rw [h1] at h2
    norm_num at h2

end Azurite.DLMF
