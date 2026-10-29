/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# DLMF §1.13(viii): Eigenvalues and Eigenfunctions: Sturm–Liouville and Liouville forms

Formalizations of <https://dlmf.nist.gov/1.13#viii>, in the real variable.

**Conventions.** The coefficients `p`, `ρ` are taken `C²` and positive on all of `ℝ` (DLMF's
data on `[a, b]` can be extended), so that `t(x) = ∫ₐˣ √(ρ/p)` (`lvT`) is a strictly increasing
`C³` function whose inverse `x(t)` (`lvX`) is differentiable on the open range of `t`. One-sided
derivatives at the endpoints are avoided this way. "Twice differentiable at `x`" (`TwiceDiffAt`)
means differentiable near `x` with derivative differentiable at `x`.

**Results.**
* 1.13.26–1.13.28: `IsSLSolution`, `UnmixedBC`, `PeriodicBC`, `IsRegularUnmixed`, eigenvalues and
  eigenfunctions (`IsSLEigenvalue`, `IsSLEigenfunction`), and the Liouville counterparts
  (`IsLiouvilleSolution`, `IsLiouvilleEigenvalue`, `IsLiouvilleEigenfunction`).
* 1.13.29–1.13.31: the Liouville transformation `w(t) = u(x)(pρ)^{1/4}` (`lvW`, inverse `lvU`),
  `q̂ = q/ρ + (pρ)^{−1/4} d²(pρ)^{1/4}/dt²` (`lvQhat`). The key identity
  `ẅ + (λ − q̂) w = ((pρ)^{1/4}/ρ) ((p u′)′ + (λρ − q) u)` (`lv_identity`) uses only
  `p s² = ρ`, `m² = p s` and its derivative, for `s = √(ρ/p)`, `m = (pρ)^{1/4}`. Hence
  `dlmf_1_13_29` (pointwise equivalence) and the correspondence of solutions
  (`isLiouvilleSolution_lvW`, `isSLSolution_lvU`).
* (i) identical eigenvalues and (iii) un-mixed conditions go to un-mixed conditions
  (`dlmf_1_13_viii_eigenvalues_unmixed`; the transformed coefficients `lvBC₁`, `lvBC₂` are not
  both zero, `lvBC_ne`, and the boundary forms agree exactly, `lv_bc_eq`).
* (ii) the same number of zeros in `(a, b)` and `(0, c)` (`dlmf_1_13_viii_zeros`,
  `dlmf_1_13_viii_zeros'`, counted with `encard`).
* (iii) for periodic conditions (`lv_periodic_iff`, `dlmf_1_13_viii_eigenvalues_periodic`): this
  needs `p`, `ρ`, `p′`, `ρ′` to agree at `a` and `b`, which DLMF leaves implicit; in general the
  Liouville transformation does not preserve periodicity.
-/

open Filter Topology Set

namespace Azurite.DLMF

/-! ### The Liouville change of variables -/

/-- `√(ρ/p)`, the integrand of `t` in (1.13.30). -/
noncomputable def lvS (p ρ : ℝ → ℝ) (x : ℝ) : ℝ := √(ρ x / p x)

/-- `(p ρ)^{1/4}` in (1.13.30). -/
noncomputable def lvM (p ρ : ℝ → ℝ) (x : ℝ) : ℝ := (p x * ρ x) ^ (1 / 4 : ℝ)

/-- **DLMF (1.13.30)**: `t = ∫ₐˣ √(ρ(s)/p(s)) ds`. -/
noncomputable def lvT (p ρ : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ y in a..x, lvS p ρ y

/-- The inverse `x(t)` of `t(x)`. -/
noncomputable def lvX (p ρ : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := Function.invFun (lvT p ρ a)

section Setup

variable {p ρ : ℝ → ℝ} (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ) (hp0 : ∀ x, 0 < p x)
  (hρ0 : ∀ x, 0 < ρ x)

include hp0 hρ0 in
theorem lvS_pos (x : ℝ) : 0 < lvS p ρ x := Real.sqrt_pos.mpr (div_pos (hρ0 x) (hp0 x))

include hp0 hρ0 in
theorem lvM_pos (x : ℝ) : 0 < lvM p ρ x := Real.rpow_pos_of_pos (mul_pos (hp0 x) (hρ0 x)) _

include hp0 hρ0 in
theorem p_mul_lvS_sq (x : ℝ) : p x * lvS p ρ x ^ 2 = ρ x := by
  rw [lvS, Real.sq_sqrt (div_pos (hρ0 x) (hp0 x)).le]
  field_simp [(hp0 x).ne']

include hp0 hρ0 in
theorem lvM_sq (x : ℝ) : lvM p ρ x ^ 2 = p x * lvS p ρ x := by
  have h4 : lvM p ρ x ^ 4 = p x * ρ x := by
    rw [lvM, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow (mul_pos (hp0 x) (hρ0 x)).le (by norm_num)
  have hs := p_mul_lvS_sq hp0 hρ0 x
  have hpos : 0 < p x * lvS p ρ x := mul_pos (hp0 x) (lvS_pos hp0 hρ0 x)
  have hm := lvM_pos hp0 hρ0 x
  have : (lvM p ρ x ^ 2) ^ 2 = (p x * lvS p ρ x) ^ 2 := by
    rw [← pow_mul, h4, ← hs]
    ring
  exact (pow_left_inj₀ (by positivity) hpos.le (by norm_num : 2 ≠ 0)).mp this

include hp hρ hp0 hρ0 in
theorem contDiff_lvS : ContDiff ℝ 2 (lvS p ρ) :=
  (hρ.div hp fun x => (hp0 x).ne').sqrt fun x => (div_pos (hρ0 x) (hp0 x)).ne'

include hp hρ hp0 hρ0 in
theorem contDiff_lvM : ContDiff ℝ 2 (lvM p ρ) :=
  (hp.mul hρ).rpow_const_of_ne fun x => (mul_pos (hp0 x) (hρ0 x)).ne'

/-- `C²` functions have differentiable derivatives. -/
theorem differentiable_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) :=
  ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)

include hp hρ hp0 hρ0 in
theorem hasDerivAt_lvT (a x : ℝ) : HasDerivAt (lvT p ρ a) (lvS p ρ x) x :=
  ((contDiff_lvS hp hρ hp0 hρ0).continuous.integral_hasStrictDerivAt a x).hasDerivAt

include hp hρ hp0 hρ0 in
theorem strictMono_lvT (a : ℝ) : StrictMono (lvT p ρ a) :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_lvT hp hρ hp0 hρ0 a x).deriv]
    exact lvS_pos hp0 hρ0 x

theorem lvT_self (a : ℝ) : lvT p ρ a a = 0 := intervalIntegral.integral_same

include hp hρ hp0 hρ0 in
theorem lvX_lvT (a x : ℝ) : lvX p ρ a (lvT p ρ a x) = x :=
  Function.leftInverse_invFun (strictMono_lvT hp hρ hp0 hρ0 a).injective x

theorem lvT_lvX {a t : ℝ} (ht : t ∈ range (lvT p ρ a)) : lvT p ρ a (lvX p ρ a t) = t :=
  Function.invFun_eq ht

include hp hρ hp0 hρ0 in
theorem isOpen_range_lvT (a : ℝ) : IsOpen (range (lvT p ρ a)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, rfl⟩
  have hT : Continuous (lvT p ρ a) := continuous_iff_continuousAt.2 fun y =>
    (hasDerivAt_lvT hp hρ hp0 hρ0 a y).continuousAt
  have hm := strictMono_lvT hp hρ hp0 hρ0 a
  refine mem_of_superset (Ioo_mem_nhds (hm (show x - 1 < x by linarith))
    (hm (show x < x + 1 by linarith))) ?_
  intro t ht
  obtain ⟨y, -, hy⟩ := intermediate_value_Ioo (by linarith : x - 1 ≤ x + 1) hT.continuousOn ht
  exact ⟨y, hy⟩

include hp hρ hp0 hρ0 in
theorem continuousAt_lvX {a t : ℝ} (ht : t ∈ range (lvT p ρ a)) :
    ContinuousAt (lvX p ρ a) t := by
  have hm := strictMono_lvT hp hρ hp0 hρ0 a
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := range (lvT p ρ a)) ?_
    ((isOpen_range_lvT hp hρ hp0 hρ0 a).mem_nhds ht) ?_
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    rw [lvX_lvT hp hρ hp0 hρ0, lvX_lvT hp hρ hp0 hρ0]
    exact hm.le_iff_le.mp hxy
  · have : lvX p ρ a '' range (lvT p ρ a) = univ := by
      refine eq_univ_of_forall fun x => ⟨lvT p ρ a x, ⟨x, rfl⟩, lvX_lvT hp hρ hp0 hρ0 a x⟩
    rw [this]
    exact univ_mem

include hp hρ hp0 hρ0 in
theorem hasDerivAt_lvX {a t : ℝ} (ht : t ∈ range (lvT p ρ a)) :
    HasDerivAt (lvX p ρ a) (lvS p ρ (lvX p ρ a t))⁻¹ t :=
  HasDerivAt.of_local_left_inverse (continuousAt_lvX hp hρ hp0 hρ0 ht)
    (hasDerivAt_lvT hp hρ hp0 hρ0 a _) (lvS_pos hp0 hρ0 _).ne'
    (mem_of_superset ((isOpen_range_lvT hp hρ hp0 hρ0 a).mem_nhds ht) fun _ h => lvT_lvX h)

end Setup

theorem lvT_mem_range (p ρ : ℝ → ℝ) (a x : ℝ) : lvT p ρ a x ∈ range (lvT p ρ a) := ⟨x, rfl⟩

/-- `u` is differentiable near `x` and `u′` is differentiable at `x`. -/
def TwiceDiffAt (u : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y) ∧ DifferentiableAt ℝ (deriv u) x

theorem twiceDiffAt_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) : TwiceDiffAt f x :=
  ⟨Eventually.of_forall fun y => hf.differentiable (by norm_num) y,
    differentiable_deriv_of_contDiff_two hf x⟩

/-- **DLMF (1.13.31)**: `q̂(t) = q/ρ + (pρ)^{−1/4} d²(pρ)^{1/4}/dt²`, with `(pρ)^{1/4}` as a
function of `t`. -/
noncomputable def lvQhat (p q ρ : ℝ → ℝ) (a t : ℝ) : ℝ :=
  q (lvX p ρ a t) / ρ (lvX p ρ a t) +
    (lvM p ρ (lvX p ρ a t))⁻¹ * deriv (deriv (fun τ => lvM p ρ (lvX p ρ a τ))) t

/-- **DLMF (1.13.30)**: `w(t) = u(x) (p(x) ρ(x))^{1/4}` with `x = x(t)`. -/
noncomputable def lvW (p ρ : ℝ → ℝ) (a : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  u (lvX p ρ a t) * lvM p ρ (lvX p ρ a t)

section Chain

variable {p ρ : ℝ → ℝ} (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ) (hp0 : ∀ x, 0 < p x)
  (hρ0 : ∀ x, 0 < ρ x) {a : ℝ}
include hp hρ hp0 hρ0

theorem hasDerivAt_comp_lvX {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ range (lvT p ρ a))
    (hF : DifferentiableAt ℝ F (lvX p ρ a t)) :
    HasDerivAt (fun τ => F (lvX p ρ a τ)) (deriv F (lvX p ρ a t) / lvS p ρ (lvX p ρ a t)) t := by
  have := hF.hasDerivAt.comp t (hasDerivAt_lvX hp hρ hp0 hρ0 ht)
  rwa [div_eq_mul_inv]

theorem deriv_comp_lvX_eventually {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ range (lvT p ρ a))
    (hF : ∀ᶠ y in 𝓝 (lvX p ρ a t), DifferentiableAt ℝ F y) :
    deriv (fun τ => F (lvX p ρ a τ)) =ᶠ[𝓝 t]
      fun τ => deriv F (lvX p ρ a τ) / lvS p ρ (lvX p ρ a τ) := by
  filter_upwards [(isOpen_range_lvT hp hρ hp0 hρ0 a).mem_nhds ht,
    (continuousAt_lvX hp hρ hp0 hρ0 ht).eventually hF] with τ hτ hd
  exact (hasDerivAt_comp_lvX hp hρ hp0 hρ0 hτ hd).deriv

theorem differentiableAt_quot {F : ℝ → ℝ} {x : ℝ} (hF : TwiceDiffAt F x) :
    DifferentiableAt ℝ (fun y => deriv F y / lvS p ρ y) x :=
  hF.2.div ((contDiff_lvS hp hρ hp0 hρ0).differentiable (by norm_num) x)
    (lvS_pos hp0 hρ0 x).ne'

/-- Twice differentiability and the second derivative under `x = x(t)`. -/
theorem twiceDiffAt_comp_lvX {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ range (lvT p ρ a))
    (hF : TwiceDiffAt F (lvX p ρ a t)) :
    TwiceDiffAt (fun τ => F (lvX p ρ a τ)) t ∧
      deriv (deriv (fun τ => F (lvX p ρ a τ))) t =
        deriv (fun y => deriv F y / lvS p ρ y) (lvX p ρ a t) / lvS p ρ (lvX p ρ a t) := by
  have he := deriv_comp_lvX_eventually hp hρ hp0 hρ0 ht hF.1
  have hG := hasDerivAt_comp_lvX hp hρ hp0 hρ0 ht (differentiableAt_quot hp hρ hp0 hρ0 hF)
  refine ⟨⟨?_, (hG.congr_of_eventuallyEq he).differentiableAt⟩, ?_⟩
  · filter_upwards [(isOpen_range_lvT hp hρ hp0 hρ0 a).mem_nhds ht,
      (continuousAt_lvX hp hρ hp0 hρ0 ht).eventually hF.1] with τ hτ hd
    exact (hasDerivAt_comp_lvX hp hρ hp0 hρ0 hτ hd).differentiableAt
  · rw [he.deriv_eq, hG.deriv]

end Chain

/-! ### The Liouville transformation -/

section Liouville

variable {p q ρ : ℝ → ℝ} (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ) (hp0 : ∀ x, 0 < p x)
  (hρ0 : ∀ x, 0 < ρ x) {a : ℝ}
include hp hρ hp0 hρ0

/-- `2 m m′ = p′ s + p s′`, from `m² = p s`. -/
theorem lvM_deriv_rel (x : ℝ) :
    2 * lvM p ρ x * deriv (lvM p ρ) x =
      deriv p x * lvS p ρ x + p x * deriv (lvS p ρ) x := by
  have h1 := ((contDiff_lvM hp hρ hp0 hρ0).differentiable (by norm_num) x).hasDerivAt.pow 2
  have h2 := (hp.differentiable (by norm_num) x).hasDerivAt.mul
    ((contDiff_lvS hp hρ hp0 hρ0).differentiable (by norm_num) x).hasDerivAt
  have h1' : HasDerivAt (fun y => p y * lvS p ρ y)
      (↑2 * lvM p ρ x ^ (2 - 1) * deriv (lvM p ρ) x) x :=
    h1.congr_of_eventuallyEq (Eventually.of_forall fun y => by
      show p y * lvS p ρ y = lvM p ρ y ^ 2
      rw [lvM_sq hp0 hρ0 y])
  have := h1'.unique h2
  push_cast at this
  linear_combination this

/-- **DLMF (1.13.29)–(1.13.31)** (the Liouville transformation), pointwise: if
`w = u (pρ)^{1/4}` near `t = t(x)`, then `w` is twice differentiable at `t` and
`ẅ + (λ − q̂) w = ((pρ)^{1/4}/ρ) ((p u′)′ + (λρ − q) u)` there. -/
theorem lv_identity {u : ℝ → ℝ} {x : ℝ} (hu : TwiceDiffAt u x) {w : ℝ → ℝ}
    (hw : w =ᶠ[𝓝 (lvT p ρ a x)] lvW p ρ a u) (μ : ℝ) :
    TwiceDiffAt w (lvT p ρ a x) ∧
      deriv (deriv w) (lvT p ρ a x) + (μ - lvQhat p q ρ a (lvT p ρ a x)) * w (lvT p ρ a x) =
        lvM p ρ x / ρ x * (deriv (fun y => p y * deriv u y) x + (μ * ρ x - q x) * u x) := by
  have ht := lvT_mem_range p ρ a x
  have hXt := lvX_lvT hp hρ hp0 hρ0 a x
  have hM := contDiff_lvM hp hρ hp0 hρ0
  have hS := contDiff_lvS hp hρ hp0 hρ0
  -- `W = u m` is twice differentiable at `x`
  have hW : TwiceDiffAt (fun y => u y * lvM p ρ y) x := by
    refine ⟨hu.1.mono fun y hy => hy.mul (hM.differentiable (by norm_num) y), ?_⟩
    have he : deriv (fun y => u y * lvM p ρ y) =ᶠ[𝓝 x]
        fun y => deriv u y * lvM p ρ y + u y * deriv (lvM p ρ) y := by
      filter_upwards [hu.1] with y hy
      exact (hy.hasDerivAt.mul (hM.differentiable (by norm_num) y).hasDerivAt).deriv
    exact ((hu.2.mul (hM.differentiable (by norm_num) x)).add
      ((hu.1.self_of_nhds).mul (differentiable_deriv_of_contDiff_two hM x))).congr_of_eventuallyEq
        he
  rw [← hXt] at hW
  obtain ⟨hwt, hw2⟩ := twiceDiffAt_comp_lvX hp hρ hp0 hρ0 ht hW
  obtain ⟨-, hM2⟩ := twiceDiffAt_comp_lvX hp hρ hp0 hρ0 ht
    (twiceDiffAt_of_contDiff hM (lvX p ρ a _))
  rw [hXt] at hw2 hM2
  -- transfer from `lvW` to `w`
  have hw' : w =ᶠ[𝓝 (lvT p ρ a x)] fun τ => u (lvX p ρ a τ) * lvM p ρ (lvX p ρ a τ) := hw
  have hev := hw'.eventually_nhds
  have hd1 := hw'.deriv
  have hdd := hd1.deriv_eq
  refine ⟨⟨?_, hwt.2.congr_of_eventuallyEq hd1⟩, ?_⟩
  · filter_upwards [hev, hwt.1] with τ hτ hd
    exact hd.congr_of_eventuallyEq hτ
  rw [hdd, hw2, hw'.self_of_nhds, lvQhat, hM2, hXt]
  -- the derivatives at `x`
  have hu1 := (hu.1.self_of_nhds).hasDerivAt
  have hu2 := hu.2.hasDerivAt
  have hm1 := (hM.differentiable (by norm_num) x).hasDerivAt
  have hm2 := (differentiable_deriv_of_contDiff_two hM x).hasDerivAt
  have hs1 := (hS.differentiable (by norm_num) x).hasDerivAt
  have hs2 := (differentiable_deriv_of_contDiff_two hS x).hasDerivAt
  have hp1 := (hp.differentiable (by norm_num) x).hasDerivAt
  have hs0 := (lvS_pos hp0 hρ0 x).ne'
  have hG : deriv (fun y => deriv (fun y => u y * lvM p ρ y) y / lvS p ρ y) x =
      ((deriv (deriv u) x * lvM p ρ x + deriv u x * deriv (lvM p ρ) x +
        (deriv u x * deriv (lvM p ρ) x + u x * deriv (deriv (lvM p ρ)) x)) * lvS p ρ x -
        (deriv u x * lvM p ρ x + u x * deriv (lvM p ρ) x) * deriv (lvS p ρ) x) /
        lvS p ρ x ^ 2 := by
    have he : (fun y => deriv (fun y => u y * lvM p ρ y) y / lvS p ρ y) =ᶠ[𝓝 x]
        fun y => (deriv u y * lvM p ρ y + u y * deriv (lvM p ρ) y) / lvS p ρ y := by
      filter_upwards [hu.1] with y hy
      have h : HasDerivAt (fun y => u y * lvM p ρ y)
          (deriv u y * lvM p ρ y + u y * deriv (lvM p ρ) y) y :=
        hy.hasDerivAt.mul (hM.differentiable (by norm_num) y).hasDerivAt
      rw [h.deriv]
    have hd : HasDerivAt
        (fun y => (deriv u y * lvM p ρ y + u y * deriv (lvM p ρ) y) / lvS p ρ y)
        (((deriv (deriv u) x * lvM p ρ x + deriv u x * deriv (lvM p ρ) x +
          (deriv u x * deriv (lvM p ρ) x + u x * deriv (deriv (lvM p ρ)) x)) * lvS p ρ x -
          (deriv u x * lvM p ρ x + u x * deriv (lvM p ρ) x) * deriv (lvS p ρ) x) /
          lvS p ρ x ^ 2) x :=
      ((hu2.mul hm1).add (hu1.mul hm2)).div hs1 hs0
    rw [he.deriv_eq, hd.deriv]
  have hGm : deriv (fun y => deriv (lvM p ρ) y / lvS p ρ y) x =
      (deriv (deriv (lvM p ρ)) x * lvS p ρ x - deriv (lvM p ρ) x * deriv (lvS p ρ) x) /
        lvS p ρ x ^ 2 := (hm2.div hs1 hs0).deriv
  have hpu : deriv (fun y => p y * deriv u y) x =
      deriv p x * deriv u x + p x * deriv (deriv u) x := (hp1.mul hu2).deriv
  rw [hG, hGm, hpu]
  have hρx := p_mul_lvS_sq hp0 hρ0 x
  have hmx := lvM_sq hp0 hρ0 x
  have hdm := lvM_deriv_rel hp hρ hp0 hρ0 x
  have hm0 := (lvM_pos hp0 hρ0 x).ne'
  rw [← hρx]
  have hp0x := (hp0 x).ne'
  simp only [hXt]
  field_simp
  linear_combination (lvM p ρ x * deriv u x) * hdm +
    (-2 * deriv (lvM p ρ) x * deriv u x) * hmx

end Liouville

/-! ### Sturm–Liouville systems and eigenvalues -/

/-- **DLMF (1.13.26)**: `u` solves the Sturm–Liouville equation `(p u′)′ + (λρ − q) u = 0` on
`[a, b]` (with `u′` differentiable there). -/
def IsSLSolution (p q ρ : ℝ → ℝ) (μ a b : ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc a b, TwiceDiffAt u x ∧ deriv (fun y => p y * deriv u y) x + (μ * ρ x - q x) * u x = 0

/-- **DLMF (1.13.27)**: un-mixed boundary conditions. -/
def UnmixedBC (a b α α' β β' : ℝ) (u : ℝ → ℝ) : Prop :=
  α * u a + α' * deriv u a = 0 ∧ β * u b + β' * deriv u b = 0

/-- **DLMF (1.13.28)**: periodic boundary conditions. -/
def PeriodicBC (a b : ℝ) (u : ℝ → ℝ) : Prop := u a = u b ∧ deriv u a = deriv u b

/-- A regular Sturm–Liouville system on a finite interval: `p, ρ > 0` on `[a, b]`, with
un-mixed boundary conditions whose coefficient pairs are not both zero. -/
structure IsRegularUnmixed (p ρ : ℝ → ℝ) (a b α α' β β' : ℝ) : Prop where
  lt : a < b
  p_pos : ∀ x ∈ Icc a b, 0 < p x
  ρ_pos : ∀ x ∈ Icc a b, 0 < ρ x
  hα : ¬(α = 0 ∧ α' = 0)
  hβ : ¬(β = 0 ∧ β' = 0)

/-- **DLMF §1.13(viii)**: `λ` is an eigenvalue of the Sturm–Liouville problem with boundary
condition `bc` if a solution satisfying `bc` is not identically zero on `[a, b]`; such a solution
is an eigenfunction. -/
def IsSLEigenfunction (p q ρ : ℝ → ℝ) (a b : ℝ) (bc : (ℝ → ℝ) → Prop) (μ : ℝ)
    (u : ℝ → ℝ) : Prop :=
  IsSLSolution p q ρ μ a b u ∧ bc u ∧ ∃ x ∈ Icc a b, u x ≠ 0

def IsSLEigenvalue (p q ρ : ℝ → ℝ) (a b : ℝ) (bc : (ℝ → ℝ) → Prop) (μ : ℝ) : Prop :=
  ∃ u, IsSLEigenfunction p q ρ a b bc μ u

/-- **DLMF (1.13.29)**: `w` solves the Liouville normal form `ẅ + (λ − q̂) w = 0` on `[0, c]`. -/
def IsLiouvilleSolution (qhat : ℝ → ℝ) (μ c : ℝ) (w : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc 0 c, TwiceDiffAt w t ∧ deriv (deriv w) t + (μ - qhat t) * w t = 0

def IsLiouvilleEigenfunction (qhat : ℝ → ℝ) (c : ℝ) (bc : (ℝ → ℝ) → Prop) (μ : ℝ)
    (w : ℝ → ℝ) : Prop :=
  IsLiouvilleSolution qhat μ c w ∧ bc w ∧ ∃ t ∈ Icc 0 c, w t ≠ 0

def IsLiouvilleEigenvalue (qhat : ℝ → ℝ) (c : ℝ) (bc : (ℝ → ℝ) → Prop) (μ : ℝ) : Prop :=
  ∃ w, IsLiouvilleEigenfunction qhat c bc μ w

/-- The inverse transformation `u(x) = w(t(x)) (p ρ)^{−1/4}`. -/
noncomputable def lvU (p ρ : ℝ → ℝ) (a : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  w (lvT p ρ a x) / lvM p ρ x

section Eigen

variable {p q ρ : ℝ → ℝ} (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ) (hp0 : ∀ x, 0 < p x)
  (hρ0 : ∀ x, 0 < ρ x) {a b : ℝ}
include hp hρ hp0 hρ0

theorem lvT_image_Icc (hab : a ≤ b) : lvT p ρ a '' Icc a b = Icc 0 (lvT p ρ a b) := by
  have hm := strictMono_lvT hp hρ hp0 hρ0 a
  have hT : Continuous (lvT p ρ a) := continuous_iff_continuousAt.2 fun y =>
    (hasDerivAt_lvT hp hρ hp0 hρ0 a y).continuousAt
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [← lvT_self (p := p) (ρ := ρ) a]
    exact ⟨hm.monotone hx.1, hm.monotone hx.2⟩
  · have := intermediate_value_Icc hab hT.continuousOn
    rwa [lvT_self] at this

theorem lvT_image_Ioo (hab : a ≤ b) : lvT p ρ a '' Ioo a b = Ioo 0 (lvT p ρ a b) := by
  have hm := strictMono_lvT hp hρ hp0 hρ0 a
  have hT : Continuous (lvT p ρ a) := continuous_iff_continuousAt.2 fun y =>
    (hasDerivAt_lvT hp hρ hp0 hρ0 a y).continuousAt
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [← lvT_self (p := p) (ρ := ρ) a]
    exact ⟨hm hx.1, hm hx.2⟩
  · have := intermediate_value_Ioo hab hT.continuousOn
    rwa [lvT_self] at this

/-- Values at `t(x)` of a function equal to `lvW u` near `t(x)`. -/
theorem lv_values {u : ℝ → ℝ} {x : ℝ} (hu : DifferentiableAt ℝ u x) {w : ℝ → ℝ}
    (hw : w =ᶠ[𝓝 (lvT p ρ a x)] lvW p ρ a u) :
    w (lvT p ρ a x) = u x * lvM p ρ x ∧
      deriv w (lvT p ρ a x) =
        (deriv u x * lvM p ρ x + u x * deriv (lvM p ρ) x) / lvS p ρ x := by
  have hXt := lvX_lvT hp hρ hp0 hρ0 a x
  have hM := (contDiff_lvM hp hρ hp0 hρ0).differentiable (by norm_num) x
  have hF : DifferentiableAt ℝ (fun y => u y * lvM p ρ y) (lvX p ρ a (lvT p ρ a x)) := by
    rw [hXt]; exact hu.mul hM
  have h := hasDerivAt_comp_lvX hp hρ hp0 hρ0 (lvT_mem_range p ρ a x) hF
  rw [hXt] at h
  have hd : deriv (fun y => u y * lvM p ρ y) x =
      deriv u x * lvM p ρ x + u x * deriv (lvM p ρ) x := (hu.hasDerivAt.mul hM.hasDerivAt).deriv
  refine ⟨by rw [hw.self_of_nhds, lvW, hXt], ?_⟩
  rw [hw.deriv_eq, ← hd]
  exact h.deriv

theorem twiceDiffAt_comp_lvT {w : ℝ → ℝ} {x : ℝ} (hw : TwiceDiffAt w (lvT p ρ a x)) :
    TwiceDiffAt (fun y => w (lvT p ρ a y)) x := by
  have hT := fun y => hasDerivAt_lvT hp hρ hp0 hρ0 a y
  have hS := contDiff_lvS hp hρ hp0 hρ0
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ w (lvT p ρ a y) :=
    (hT x).continuousAt.eventually hw.1
  refine ⟨hev.mono fun y hy => (hy.hasDerivAt.comp y (hT y)).differentiableAt, ?_⟩
  have he : deriv (fun y => w (lvT p ρ a y)) =ᶠ[𝓝 x]
      fun y => deriv w (lvT p ρ a y) * lvS p ρ y := by
    filter_upwards [hev] with y hy using (hy.hasDerivAt.comp y (hT y)).deriv
  exact ((hw.2.comp x (hT x).differentiableAt).mul
    (hS.differentiable (by norm_num) x)).congr_of_eventuallyEq he

omit hp hρ hp0 hρ0 in
theorem twiceDiffAt_div {F g : ℝ → ℝ} {x : ℝ} (hF : TwiceDiffAt F x) (hg : ContDiff ℝ 2 g)
    (hg0 : ∀ y, g y ≠ 0) : TwiceDiffAt (fun y => F y / g y) x := by
  have hg1 := hg.differentiable (by norm_num)
  refine ⟨hF.1.mono fun y hy => hy.div (hg1 y) (hg0 y), ?_⟩
  have he : deriv (fun y => F y / g y) =ᶠ[𝓝 x]
      fun y => (deriv F y * g y - F y * deriv g y) / g y ^ 2 := by
    filter_upwards [hF.1] with y hy using (hy.hasDerivAt.div (hg1 y).hasDerivAt (hg0 y)).deriv
  exact (((hF.2.mul (hg1 x)).sub ((hF.1.self_of_nhds).mul
    (differentiable_deriv_of_contDiff_two hg x))).div ((hg1 x).pow 2)
    (pow_ne_zero 2 (hg0 x))).congr_of_eventuallyEq he

theorem lvW_lvU_eventually {w : ℝ → ℝ} {t : ℝ} (ht : t ∈ range (lvT p ρ a)) :
    w =ᶠ[𝓝 t] lvW p ρ a (lvU p ρ a w) := by
  filter_upwards [(isOpen_range_lvT hp hρ hp0 hρ0 a).mem_nhds ht] with τ hτ
  simp only [lvW, lvU, lvT_lvX hτ]
  rw [div_mul_cancel₀ _ (lvM_pos hp0 hρ0 _).ne']

/-- Solutions of (1.13.26) are carried to solutions of (1.13.29). -/
theorem isLiouvilleSolution_lvW (hab : a ≤ b) {μ : ℝ} {u : ℝ → ℝ}
    (hu : IsSLSolution p q ρ μ a b u) :
    IsLiouvilleSolution (lvQhat p q ρ a) μ (lvT p ρ a b) (lvW p ρ a u) := by
  intro t ht
  rw [← lvT_image_Icc hp hρ hp0 hρ0 hab] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  obtain ⟨h1, h2⟩ := lv_identity (q := q) hp hρ hp0 hρ0 (hu x hx).1 EventuallyEq.rfl μ
  exact ⟨h1, by rw [h2, (hu x hx).2, mul_zero]⟩

/-- Solutions of (1.13.29) are carried back to solutions of (1.13.26). -/
theorem isSLSolution_lvU (hab : a ≤ b) {μ : ℝ} {w : ℝ → ℝ}
    (hw : IsLiouvilleSolution (lvQhat p q ρ a) μ (lvT p ρ a b) w) :
    IsSLSolution p q ρ μ a b (lvU p ρ a w) := by
  intro x hx
  have hT : lvT p ρ a x ∈ Icc 0 (lvT p ρ a b) := by
    rw [← lvT_image_Icc hp hρ hp0 hρ0 hab]; exact ⟨x, hx, rfl⟩
  have hU : TwiceDiffAt (lvU p ρ a w) x :=
    twiceDiffAt_div (twiceDiffAt_comp_lvT hp hρ hp0 hρ0 (hw _ hT).1)
      (contDiff_lvM hp hρ hp0 hρ0) fun y => (lvM_pos hp0 hρ0 y).ne'
  obtain ⟨-, h2⟩ := lv_identity (q := q) hp hρ hp0 hρ0 hU
    (lvW_lvU_eventually hp hρ hp0 hρ0 (lvT_mem_range p ρ a x)) μ
  rw [(hw _ hT).2] at h2
  refine ⟨hU, ?_⟩
  have hc : lvM p ρ x / ρ x ≠ 0 := div_ne_zero (lvM_pos hp0 hρ0 x).ne' (hρ0 x).ne'
  exact (mul_eq_zero.mp h2.symm).resolve_left hc

/-- The transformed un-mixed boundary coefficients at an endpoint `x`. -/
noncomputable def lvBC₁ (p ρ : ℝ → ℝ) (x α α' : ℝ) : ℝ :=
  α / lvM p ρ x - α' * deriv (lvM p ρ) x / lvM p ρ x ^ 2

noncomputable def lvBC₂ (p ρ : ℝ → ℝ) (x α' : ℝ) : ℝ := α' * lvS p ρ x / lvM p ρ x

omit hp hρ in
include hp0 hρ0 in
theorem lvBC_ne (x : ℝ) {α α' : ℝ} (h : ¬(α = 0 ∧ α' = 0)) :
    ¬(lvBC₁ p ρ x α α' = 0 ∧ lvBC₂ p ρ x α' = 0) := by
  rintro ⟨h1, h2⟩
  have hm := (lvM_pos hp0 hρ0 x).ne'
  have hs := (lvS_pos hp0 hρ0 x).ne'
  have hα' : α' = 0 := by
    unfold lvBC₂ at h2
    rw [div_eq_zero_iff, or_iff_left hm, mul_eq_zero, or_iff_left hs] at h2
    exact h2
  subst hα'
  unfold lvBC₁ at h1
  simp only [zero_mul, zero_div, sub_zero, div_eq_zero_iff] at h1
  exact h ⟨h1.resolve_right hm, rfl⟩

/-- The boundary forms agree: `α̂ w + α̂′ ẇ` at `t(x)` equals `α u + α′ u′` at `x`. -/
theorem lv_bc_eq {u : ℝ → ℝ} {x : ℝ} (hu : DifferentiableAt ℝ u x) {w : ℝ → ℝ}
    (hw : w =ᶠ[𝓝 (lvT p ρ a x)] lvW p ρ a u) (α α' : ℝ) :
    lvBC₁ p ρ x α α' * w (lvT p ρ a x) + lvBC₂ p ρ x α' * deriv w (lvT p ρ a x) =
      α * u x + α' * deriv u x := by
  obtain ⟨h0, h1⟩ := lv_values hp hρ hp0 hρ0 hu hw
  rw [h0, h1, lvBC₁, lvBC₂]
  have hm := (lvM_pos hp0 hρ0 x).ne'
  have hs := (lvS_pos hp0 hρ0 x).ne'
  field_simp
  ring

end Eigen

section Main

variable {p q ρ : ℝ → ℝ} (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ) (hp0 : ∀ x, 0 < p x)
  (hρ0 : ∀ x, 0 < ρ x) {a b : ℝ}
include hp hρ hp0 hρ0

/-- **DLMF (1.13.29)–(1.13.31)**: at each point, `u` satisfies (1.13.26) if and only if
`w = u (pρ)^{1/4}` satisfies the Liouville normal form `ẅ + (λ − q̂) w = 0` at `t = t(x)`. -/
theorem dlmf_1_13_29 {u : ℝ → ℝ} {x : ℝ} (hu : TwiceDiffAt u x) (μ : ℝ) :
    deriv (fun y => p y * deriv u y) x + (μ * ρ x - q x) * u x = 0 ↔
      deriv (deriv (lvW p ρ a u)) (lvT p ρ a x) +
        (μ - lvQhat p q ρ a (lvT p ρ a x)) * lvW p ρ a u (lvT p ρ a x) = 0 := by
  obtain ⟨-, h⟩ := lv_identity (q := q) hp hρ hp0 hρ0 hu EventuallyEq.rfl μ
  rw [h]
  have hc : lvM p ρ x / ρ x ≠ 0 := div_ne_zero (lvM_pos hp0 hρ0 x).ne' (hρ0 x).ne'
  constructor
  · intro h0; rw [h0, mul_zero]
  · intro h0; exact (mul_eq_zero.mp h0).resolve_left hc

/-- **DLMF §1.13(viii)(i) and (iii)** for un-mixed boundary conditions: (1.13.26) with (1.13.27)
and (1.13.29) with the transformed un-mixed conditions (whose coefficient pairs are again not both
zero, `lvBC_ne`) have identical eigenvalues. -/
theorem dlmf_1_13_viii_eigenvalues_unmixed (hab : a < b) (α α' β β' μ : ℝ) :
    IsSLEigenvalue p q ρ a b (UnmixedBC a b α α' β β') μ ↔
      IsLiouvilleEigenvalue (lvQhat p q ρ a) (lvT p ρ a b)
        (UnmixedBC 0 (lvT p ρ a b) (lvBC₁ p ρ a α α') (lvBC₂ p ρ a α') (lvBC₁ p ρ b β β')
          (lvBC₂ p ρ b β')) μ := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  constructor
  · rintro ⟨u, hu, ⟨hbca, hbcb⟩, x, hx, hux⟩
    refine ⟨lvW p ρ a u, isLiouvilleSolution_lvW hp hρ hp0 hρ0 hab.le hu, ⟨?_, ?_⟩,
      lvT p ρ a x, ?_, ?_⟩
    · have := lv_bc_eq hp hρ hp0 hρ0 (a := a) ((hu a ha).1.1.self_of_nhds) EventuallyEq.rfl α α'
      rw [lvT_self] at this
      rw [this, hbca]
    · have := lv_bc_eq hp hρ hp0 hρ0 (a := a) ((hu b hb).1.1.self_of_nhds) EventuallyEq.rfl β β'
      rw [this, hbcb]
    · rw [← lvT_image_Icc hp hρ hp0 hρ0 hab.le]; exact ⟨x, hx, rfl⟩
    · rw [(lv_values hp hρ hp0 hρ0 (a := a) ((hu x hx).1.1.self_of_nhds) EventuallyEq.rfl).1]
      exact mul_ne_zero hux (lvM_pos hp0 hρ0 x).ne'
  · rintro ⟨w, hw, ⟨hbca, hbcb⟩, t, ht, hwt⟩
    have hu := isSLSolution_lvU hp hρ hp0 hρ0 hab.le hw
    refine ⟨lvU p ρ a w, hu, ⟨?_, ?_⟩, ?_⟩
    · have := lv_bc_eq hp hρ hp0 hρ0 (a := a) ((hu a ha).1.1.self_of_nhds)
        (lvW_lvU_eventually hp hρ hp0 hρ0 (lvT_mem_range p ρ a a)) α α'
      rw [lvT_self, hbca] at this
      exact this.symm
    · have := lv_bc_eq hp hρ hp0 hρ0 (a := a) ((hu b hb).1.1.self_of_nhds)
        (lvW_lvU_eventually hp hρ hp0 hρ0 (lvT_mem_range p ρ a b)) β β'
      rw [hbcb] at this
      exact this.symm
    · rw [← lvT_image_Icc hp hρ hp0 hρ0 hab.le] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      exact ⟨x, hx, div_ne_zero hwt (lvM_pos hp0 hρ0 x).ne'⟩

/-- **DLMF §1.13(viii)(ii)**: `u` on `(a, b)` and `w = u (pρ)^{1/4}` on `(0, c)` have the same
number of zeros (nodes). -/
theorem dlmf_1_13_viii_zeros (hab : a ≤ b) (u : ℝ → ℝ) :
    {t ∈ Ioo 0 (lvT p ρ a b) | lvW p ρ a u t = 0}.encard = {x ∈ Ioo a b | u x = 0}.encard := by
  have himg : lvT p ρ a '' {x ∈ Ioo a b | u x = 0} =
      {t ∈ Ioo 0 (lvT p ρ a b) | lvW p ρ a u t = 0} := by
    ext t
    constructor
    · rintro ⟨x, ⟨hx, hux⟩, rfl⟩
      refine ⟨by rw [← lvT_image_Ioo hp hρ hp0 hρ0 hab]; exact ⟨x, hx, rfl⟩, ?_⟩
      simp [lvW, lvX_lvT hp hρ hp0 hρ0, hux]
    · rintro ⟨ht, hwt⟩
      rw [← lvT_image_Ioo hp hρ hp0 hρ0 hab] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      simp only [lvW, lvX_lvT hp hρ hp0 hρ0] at hwt
      exact ⟨x, ⟨hx, (mul_eq_zero.mp hwt).resolve_right (lvM_pos hp0 hρ0 x).ne'⟩, rfl⟩
  rw [← himg, (strictMono_lvT hp hρ hp0 hρ0 a).injective.encard_image]

/-- **DLMF §1.13(viii)(ii)**, for eigenfunctions of (1.13.29): `w` on `(0, c)` and the
corresponding `u = w (pρ)^{−1/4}` on `(a, b)` have the same number of zeros. -/
theorem dlmf_1_13_viii_zeros' (hab : a ≤ b) (w : ℝ → ℝ) :
    {t ∈ Ioo 0 (lvT p ρ a b) | w t = 0}.encard =
      {x ∈ Ioo a b | lvU p ρ a w x = 0}.encard := by
  rw [← dlmf_1_13_viii_zeros hp hρ hp0 hρ0 hab]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, and_congr_right_iff]
  intro ht
  have hr : t ∈ range (lvT p ρ a) := by
    have := Ioo_subset_Icc_self ht
    rw [← lvT_image_Icc hp hρ hp0 hρ0 hab] at this
    obtain ⟨x, -, rfl⟩ := this
    exact ⟨x, rfl⟩
  rw [(lvW_lvU_eventually hp hρ hp0 hρ0 (w := w) hr).self_of_nhds]

theorem deriv_lvM (x : ℝ) : deriv (lvM p ρ) x =
    (deriv p x * ρ x + p x * deriv ρ x) * (1 / 4) * (p x * ρ x) ^ ((1 / 4 : ℝ) - 1) :=
  (((hp.differentiable (by norm_num) x).hasDerivAt.mul
    (hρ.differentiable (by norm_num) x).hasDerivAt).rpow_const
    (Or.inl (mul_pos (hp0 x) (hρ0 x)).ne')).deriv

/-- **DLMF §1.13(viii)(iii)** for periodic boundary conditions: when `p`, `ρ`, `p′`, `ρ′` take the
same values at `a` and `b` (a hypothesis DLMF leaves implicit; without it the transformed
conditions are not periodic in general), `u` satisfies (1.13.28) if and only if
`w = u (pρ)^{1/4}` satisfies periodic conditions on `[0, c]`. -/
theorem lv_periodic_iff (hpab : p a = p b) (hρab : ρ a = ρ b) (hdp : deriv p a = deriv p b)
    (hdρ : deriv ρ a = deriv ρ b) {u : ℝ → ℝ} (hua : DifferentiableAt ℝ u a)
    (hub : DifferentiableAt ℝ u b) {w : ℝ → ℝ} (hwa : w =ᶠ[𝓝 (lvT p ρ a a)] lvW p ρ a u)
    (hwb : w =ᶠ[𝓝 (lvT p ρ a b)] lvW p ρ a u) :
    PeriodicBC a b u ↔ PeriodicBC 0 (lvT p ρ a b) w := by
  obtain ⟨wa, dwa⟩ := lv_values hp hρ hp0 hρ0 hua hwa
  obtain ⟨wb, dwb⟩ := lv_values hp hρ hp0 hρ0 hub hwb
  rw [lvT_self] at wa dwa
  have hM : lvM p ρ a = lvM p ρ b := by simp only [lvM, hpab, hρab]
  have hS : lvS p ρ a = lvS p ρ b := by simp only [lvS, hpab, hρab]
  have hdM : deriv (lvM p ρ) a = deriv (lvM p ρ) b := by
    rw [deriv_lvM hp hρ hp0 hρ0, deriv_lvM hp hρ hp0 hρ0, hpab, hρab, hdp, hdρ]
  have hm := (lvM_pos hp0 hρ0 b).ne'
  have hs := (lvS_pos hp0 hρ0 b).ne'
  unfold PeriodicBC
  rw [wa, dwa, wb, dwb, hM, hS, hdM]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have h1' : u a = u b := mul_right_cancel₀ hm h1
    refine ⟨h1', ?_⟩
    rw [h1'] at h2
    field_simp at h2
    exact mul_right_cancel₀ hm (by linarith)

/-- **DLMF §1.13(viii)(i) and (iii)** for periodic boundary conditions (under the hypotheses of
`lv_periodic_iff`): identical eigenvalues, with periodic conditions on both sides. -/
theorem dlmf_1_13_viii_eigenvalues_periodic (hab : a < b) (hpab : p a = p b) (hρab : ρ a = ρ b)
    (hdp : deriv p a = deriv p b) (hdρ : deriv ρ a = deriv ρ b) (μ : ℝ) :
    IsSLEigenvalue p q ρ a b (PeriodicBC a b) μ ↔
      IsLiouvilleEigenvalue (lvQhat p q ρ a) (lvT p ρ a b) (PeriodicBC 0 (lvT p ρ a b)) μ := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  constructor
  · rintro ⟨u, hu, hbc, x, hx, hux⟩
    refine ⟨lvW p ρ a u, isLiouvilleSolution_lvW hp hρ hp0 hρ0 hab.le hu,
      (lv_periodic_iff hp hρ hp0 hρ0 hpab hρab hdp hdρ ((hu a ha).1.1.self_of_nhds)
        ((hu b hb).1.1.self_of_nhds) EventuallyEq.rfl EventuallyEq.rfl).mp hbc,
      lvT p ρ a x, ?_, ?_⟩
    · rw [← lvT_image_Icc hp hρ hp0 hρ0 hab.le]; exact ⟨x, hx, rfl⟩
    · rw [(lv_values hp hρ hp0 hρ0 (a := a) ((hu x hx).1.1.self_of_nhds) EventuallyEq.rfl).1]
      exact mul_ne_zero hux (lvM_pos hp0 hρ0 x).ne'
  · rintro ⟨w, hw, hbc, t, ht, hwt⟩
    have hu := isSLSolution_lvU hp hρ hp0 hρ0 hab.le hw
    refine ⟨lvU p ρ a w, hu, (lv_periodic_iff hp hρ hp0 hρ0 hpab hρab hdp hdρ
      ((hu a ha).1.1.self_of_nhds) ((hu b hb).1.1.self_of_nhds)
      (lvW_lvU_eventually hp hρ hp0 hρ0 (lvT_mem_range p ρ a a))
      (lvW_lvU_eventually hp hρ hp0 hρ0 (lvT_mem_range p ρ a b))).mpr hbc, ?_⟩
    rw [← lvT_image_Icc hp hρ hp0 hρ0 hab.le] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    exact ⟨x, hx, div_ne_zero hwt (lvM_pos hp0 hρ0 x).ne'⟩

end Main

end Azurite.DLMF
