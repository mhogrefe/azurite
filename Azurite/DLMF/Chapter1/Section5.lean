/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section4
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.TietzeExtension

/-!
# DLMF §1.5: Calculus of Two or More Variables

Formalizations of <https://dlmf.nist.gov/1.5>, one theorem per equation, named `dlmf_1_5_N`;
statements made in the prose are named `dlmf_1_5_i_<topic>`.  A function `f(x, y)` of two real
variables is a curried `f : ℝ → ℝ → ℝ`; its continuity and differentiability as a function on the
plane are those of `Function.uncurry f : ℝ × ℝ → ℝ` (the product metric on `ℝ × ℝ` is the max
metric, which is exactly the `|α|, |β| < δ` of 1.5.2).

## §1.5(i) Partial derivatives

* 1.5.1 `dlmf_1_5_1`, 1.5.2 `dlmf_1_5_2`: continuity at `(a, b)`; `dlmf_1_5_i_continuousOn`
  (continuity on an open point set `D`); `IsPiecewiseContinuous₂` (piecewise continuity on
  `I₁ × I₂`, in each variable separately).
* 1.5.3–1.5.4 `partialX`, `partialY`, `dlmf_1_5_3`, `dlmf_1_5_4` (difference quotients),
  `partialX_eq_of_tendsto`, `partialY_eq_of_tendsto`; 1.5.5 `partialXY`, `partialYX`,
  `partialXX`, `partialYY`, `dlmf_1_5_5`.
* `IsContinuouslyDifferentiable` (`f, f_x, f_y` exist and are continuous),
  `isContinuouslyDifferentiable_iff` (iff `uncurry f` is `C¹`), `fderiv_uncurry_eq`;
  `IsTwiceContinuouslyDifferentiable`, `isTwiceContinuouslyDifferentiable_iff` (iff `C²`);
  1.5.6 `dlmf_1_5_6` (`∂²f/∂x∂y = ∂²f/∂y∂x`, via Mathlib's symmetry of second derivatives).
* Chain rule: `fderiv_uncurry_apply` (`Df(a, b) = f_x a + f_y b`), 1.5.7 `dlmf_1_5_7`, 1.5.8
  `dlmf_1_5_8`, 1.5.9 `dlmf_1_5_9` (three intermediate variables).
* Implicit function theorem: `dlmf_1_5_i_implicit` (`F(a, b) = 0`, `F_y(a, b) ≠ 0`: a function
  `g`, `C¹` near `a`, with `g(a) = b`, `F(x, g(x)) = 0`, the solutions of `F = 0` near `(a, b)`
  are the graph of `g`, and `g'(x) = −F_x/F_y`).

## §1.5(ii) Coordinate systems

Physicists' notation: `θ` polar angle, `φ` azimuth (mathematicians usually interchange them).

* Polar: 1.5.10 `dlmf_1_5_10` (every point is `(r cos φ, r sin φ)`, `r ≥ 0`, `0 ≤ φ < 2π`),
  `polarPullback`, `hasDerivAt_polar_r`, `hasDerivAt_polar_φ`, `hasDerivAt_polar_rr`,
  `hasDerivAt_polar_φφ`; 1.5.11 `dlmf_1_5_11`, 1.5.12 `dlmf_1_5_12` (`r ≠ 0`); 1.5.13
  `dlmf_1_5_13` (Laplacian `f_rr + f_r/r + f_φφ/r²`).
* Cylindrical: `laplacian3`; 1.5.14 `dlmf_1_5_14`, `dlmf_1_5_14_partial` (1.5.11–1.5.12 still
  apply); 1.5.15 `dlmf_1_5_15`.
* Spherical: 1.5.16 `dlmf_1_5_16` (`ρ ≥ 0`, `0 ≤ θ ≤ π`, `0 ≤ φ < 2π`;
  `exists_polar_of_nonneg`), `sphericalPullback`; 1.5.17 `dlmf_1_5_17` (for `C²` `f`, `ρ ≠ 0`,
  `sin θ ≠ 0`; the cylindrical Laplacian composed with polar coordinates in the `(z, r)`
  half-plane).

## §1.5(iii) Taylor's theorem; maxima and minima

* `taylor_remainder_le` (Peano remainder `o(‖y‖ⁿ)` for `Cⁿ` functions on a normed space, from
  Mathlib's integral remainder), `dirDeriv` (`λ ∂/∂x + μ ∂/∂y`), `iterate_dirDeriv`
  (`(λ ∂x + μ ∂y)^k f = D^k f(v, …, v)`), `norm_le_sqrt_sq_add_sq`; 1.5.18 `dlmf_1_5_18`
  (`R_n/(λ² + μ²)^{n/2} → 0`), `taylor_two`.
* 1.5.19–1.5.21 `dlmf_1_5_19_min`, `dlmf_1_5_19_max` (second-derivative test, `C²` `f`),
  `dlmf_1_5_20_21` (positive definiteness of the second-order term), `quadratic_lower_bound`,
  `isLocalMin_of_quadratic`.

## §1.5(iv) Leibniz's theorem for differentiation of integrals

* `hasDerivAt_integral_param` (fixed limits), `hasDerivAt_integral_variable` (variable limits, `f`,
  `f_x` continuous on the plane; strict differentiability of `(x, u, w) ↦ ∫_u^w f`).
* 1.5.22 `dlmf_1_5_22` (DLMF's rectangle conditions; clamping `f` to the rectangle),
  `hasDerivAt_integral_Icc`.
* 1.5.23–1.5.24 `dlmf_1_5_24` (`d` finite, `ConvergesLeft`), `dlmf_1_5_24_atTop` (`d = ∞`,
  `ConvergesAtTop`): uniform convergence 1.5.23 of `∫ ∂f/∂x` gives differentiation under the
  integral sign (Mathlib's `hasDerivAt_of_tendstoUniformlyOn`).

## §1.5(v) Multiple integrals

* Double Riemann integrals: 1.5.25–1.5.26 grids from two `TaggedPartition`s, `doubleRiemannSum`,
  1.5.27 `HasDoubleRiemannIntegral` and `dlmf_1_5_27` (for `f` continuous on `R` the limit
  exists and is the Lebesgue double integral; `hasDoubleRiemannIntegral_of_continuous`,
  `exists_continuous_extension_rect`).
* 1.5.28 `extendByZero` (`f*`), 1.5.29 `HasDoubleRiemannIntegralOn` (Riemann form) and
  `dlmf_1_5_29` (Lebesgue form).
* 1.5.30–1.5.32 `regionX`, `isCompact_regionX`, `dlmf_1_5_31`; 1.5.33–1.5.34 `regionY`,
  `isCompact_regionY`, `dlmf_1_5_34`; 1.5.35 `dlmf_1_5_35` (change of order of integration).
* 1.5.36 `dlmf_1_5_36` (infinite double integrals: the repeated integrals over arbitrary
  intervals agree when one is absolutely convergent).
* 1.5.37 `regionXYZ`, `dlmf_1_5_37` (triple integrals as repeated integrals).
* Piecewise continuous `f` (1.5.27): `IsPiecewiseContinuousRect` (bounded on `R`, continuous
  off finitely many continuous curves `y = φᵢ(x)`, `x = ψⱼ(y)`; the standard two-dimensional
  notion, since DLMF's slice-wise definition does not control the set of discontinuities),
  `stripY`/`stripX` and their area bounds `volume_stripY_le`/`volume_stripX_le`,
  `IsPiecewiseContinuousRect.integrableOn`, `exists_continuous_extension_of_isClosed` (Tietze),
  `TaggedPartition.sum_lengths_le_of_near`, `dlmf_1_5_27_piecewise` (the double Riemann sums
  converge to the Lebesgue double integral).
* Riemann forms of 1.5.29–1.5.31 and 1.5.34: `isPiecewiseContinuousRect_extendByZero_regionX`,
  `…_regionY` (`f*` is piecewise continuous), `dlmf_1_5_31_riemann`, `dlmf_1_5_34_riemann`
  (`∬_R f* dA` exists as a Riemann limit and equals `∬_D f dA` and the repeated integral).
-/

namespace Azurite.DLMF

open Set Filter Topology Function

/-! ### Continuity -/

/-- **DLMF 1.5.1**: `f(x, y)` is continuous at `(a, b)` iff `f(x, y) → f(a, b)` as
`(x, y) → (a, b)`. -/
theorem dlmf_1_5_1 (f : ℝ → ℝ → ℝ) (a b : ℝ) :
    ContinuousAt (uncurry f) (a, b) ↔ Tendsto (uncurry f) (𝓝 (a, b)) (𝓝 (f a b)) :=
  Iff.rfl

/-- **DLMF 1.5.2**: `f` is continuous at `(a, b)` iff for every `ε > 0` there is `δ > 0` with
`|f(a + α, b + β) − f(a, b)| < ε` whenever `|α|, |β| < δ`. -/
theorem dlmf_1_5_2 (f : ℝ → ℝ → ℝ) (a b : ℝ) :
    ContinuousAt (uncurry f) (a, b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ α β : ℝ, |α| < δ → |β| < δ →
      |f (a + α) (b + β) - f a b| < ε := by
  rw [Metric.continuousAt_iff]
  refine forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ => ?_
  constructor
  · intro h α β hα hβ
    have := @h (a + α, b + β) (by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, add_sub_cancel_left,
        add_sub_cancel_left]
      exact ⟨hα, hβ⟩)
    rwa [Real.dist_eq] at this
  · intro h p hp
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
    have := h (p.1 - a) (p.2 - b) hp.1 hp.2
    rw [add_sub_cancel, add_sub_cancel] at this
    rwa [Real.dist_eq]

/-- **DLMF §1.5(i)**: a function is continuous on an (open) point set `D` iff it is continuous at
all points of `D`. -/
theorem dlmf_1_5_i_continuousOn (f : ℝ → ℝ → ℝ) {D : Set (ℝ × ℝ)} (hD : IsOpen D) :
    ContinuousOn (uncurry f) D ↔ ∀ p ∈ D, ContinuousAt (uncurry f) p :=
  hD.continuousOn_iff

/-- **DLMF §1.5(i)**: `f(x, y)` is piecewise continuous on `I₁ × I₂` if it is piecewise continuous
in `x` for each `y ∈ I₂` and piecewise continuous in `y` for each `x ∈ I₁`. -/
def IsPiecewiseContinuous₂ (f : ℝ → ℝ → ℝ) (I₁ I₂ : Set ℝ) : Prop :=
  (∀ y ∈ I₂, IsPiecewiseContinuous (fun x => f x y) I₁) ∧
    ∀ x ∈ I₁, IsPiecewiseContinuous (f x) I₂

/-! ### Partial derivatives -/

/-- **DLMF 1.5.3**: the partial derivative `∂f/∂x = D_x f = f_x`. -/
noncomputable def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

/-- **DLMF 1.5.4**: the partial derivative `∂f/∂y = D_y f = f_y`. -/
noncomputable def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (f x) y

/-- **DLMF 1.5.3**: `f_x = lim_{h → 0} (f(x + h, y) − f(x, y))/h`. -/
theorem dlmf_1_5_3 (f : ℝ → ℝ → ℝ) (x y L : ℝ) :
    Tendsto (fun h => (f (x + h) y - f x y) / h) (𝓝[≠] 0) (𝓝 L) ↔
      HasDerivAt (fun t => f t y) L x := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, inv_mul_eq_div]

/-- **DLMF 1.5.4**: `f_y = lim_{h → 0} (f(x, y + h) − f(x, y))/h`. -/
theorem dlmf_1_5_4 (f : ℝ → ℝ → ℝ) (x y L : ℝ) :
    Tendsto (fun h => (f x (y + h) - f x y) / h) (𝓝[≠] 0) (𝓝 L) ↔ HasDerivAt (f x) L y := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, inv_mul_eq_div]

theorem partialX_eq_of_tendsto {f : ℝ → ℝ → ℝ} {x y L : ℝ}
    (h : Tendsto (fun h => (f (x + h) y - f x y) / h) (𝓝[≠] 0) (𝓝 L)) : partialX f x y = L :=
  ((dlmf_1_5_3 f x y L).mp h).deriv

theorem partialY_eq_of_tendsto {f : ℝ → ℝ → ℝ} {x y L : ℝ}
    (h : Tendsto (fun h => (f x (y + h) - f x y) / h) (𝓝[≠] 0) (𝓝 L)) : partialY f x y = L :=
  ((dlmf_1_5_4 f x y L).mp h).deriv

/-- **DLMF 1.5.5**: `∂²f/∂x∂y = ∂/∂x (∂f/∂y)`. -/
noncomputable def partialXY (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := partialX (partialY f)

/-- **DLMF 1.5.5**: `∂²f/∂y∂x = ∂/∂y (∂f/∂x)`. -/
noncomputable def partialYX (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := partialY (partialX f)

/-- `∂²f/∂x²`. -/
noncomputable def partialXX (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := partialX (partialX f)

/-- `∂²f/∂y²`. -/
noncomputable def partialYY (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := partialY (partialY f)

/-- **DLMF 1.5.5**. -/
theorem dlmf_1_5_5 (f : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialXY f x y = deriv (fun t => partialY f t y) x ∧
      partialYX f x y = deriv (partialX f x) y :=
  ⟨rfl, rfl⟩

/-! ### Partial derivatives and the total derivative -/

/-- If `uncurry f` has derivative `L` at `(x, y)`, then `f_x(x, y) = L (1, 0)`. -/
theorem hasDerivAt_partialX {f : ℝ → ℝ → ℝ} {x y : ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (h : HasFDerivAt (uncurry f) L (x, y)) : HasDerivAt (fun t => f t y) (L (1, 0)) x := by
  have := h.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  exact this

/-- If `uncurry f` has derivative `L` at `(x, y)`, then `f_y(x, y) = L (0, 1)`. -/
theorem hasDerivAt_partialY {f : ℝ → ℝ → ℝ} {x y : ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (h : HasFDerivAt (uncurry f) L (x, y)) : HasDerivAt (f x) (L (0, 1)) y := by
  have := h.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact this

theorem partialX_of_hasFDerivAt {f : ℝ → ℝ → ℝ} {x y : ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (h : HasFDerivAt (uncurry f) L (x, y)) : partialX f x y = L (1, 0) :=
  (hasDerivAt_partialX h).deriv

theorem partialY_of_hasFDerivAt {f : ℝ → ℝ → ℝ} {x y : ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (h : HasFDerivAt (uncurry f) L (x, y)) : partialY f x y = L (0, 1) :=
  (hasDerivAt_partialY h).deriv

/-- A linear map on `ℝ × ℝ` is determined by its values at `(1, 0)` and `(0, 1)`. -/
theorem clm_apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = L (1, 0) * a + L (0, 1) * b := by
  have e : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The total derivative in terms of the partial derivatives: `Df(x, y)(a, b) = f_x a + f_y b`. -/
theorem fderiv_uncurry_apply {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (hf : DifferentiableAt ℝ (uncurry f) (x, y)) (a b : ℝ) :
    fderiv ℝ (uncurry f) (x, y) (a, b) = partialX f x y * a + partialY f x y * b := by
  rw [clm_apply_pair, partialX_of_hasFDerivAt hf.hasFDerivAt,
    partialY_of_hasFDerivAt hf.hasFDerivAt]

/-- **DLMF §1.5(i)**: `f(x, y)` is continuously differentiable if `f`, `∂f/∂x` and `∂f/∂y` (exist
and) are continuous. -/
def IsContinuouslyDifferentiable (f : ℝ → ℝ → ℝ) : Prop :=
  Continuous (uncurry f) ∧ (∀ x y, DifferentiableAt ℝ (fun t => f t y) x) ∧
    (∀ x y, DifferentiableAt ℝ (f x) y) ∧ Continuous (uncurry (partialX f)) ∧
    Continuous (uncurry (partialY f))

theorem toSpanSingleton_eq_smul_one (c : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ c = c • (1 : ℝ →L[ℝ] ℝ) := by
  ext
  simp

theorem coprod_smul_one (c d : ℝ) :
    (c • (1 : ℝ →L[ℝ] ℝ)).coprod (d • (1 : ℝ →L[ℝ] ℝ)) =
      c • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  ext <;> simp

/-- A continuously differentiable `f` has total derivative `f_x dx + f_y dy` at every point. -/
theorem IsContinuouslyDifferentiable.hasStrictFDerivAt {f : ℝ → ℝ → ℝ}
    (hf : IsContinuouslyDifferentiable f) (p : ℝ × ℝ) :
    HasStrictFDerivAt (uncurry f) (partialX f p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      partialY f p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  obtain ⟨-, hdx, hdy, hcx, hcy⟩ := hf
  have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := f)
    (f₁ := fun x y => partialX f x y • (1 : ℝ →L[ℝ] ℝ))
    (f₂ := fun x y => partialY f x y • (1 : ℝ →L[ℝ] ℝ))
    (Eventually.of_forall fun v => by
      have := (hdx v.1 v.2).hasDerivAt.hasFDerivAt
      rw [toSpanSingleton_eq_smul_one] at this
      exact this)
    (Eventually.of_forall fun v => by
      have := (hdy v.1 v.2).hasDerivAt.hasFDerivAt
      rw [toSpanSingleton_eq_smul_one] at this
      exact this)
    (hcx.smul continuous_const).continuousAt (hcy.smul continuous_const).continuousAt
  rw [← coprod_smul_one]
  exact h

theorem fderiv_uncurry_eq {f : ℝ → ℝ → ℝ} (hf : IsContinuouslyDifferentiable f) :
    fderiv ℝ (uncurry f) = fun p => partialX f p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      partialY f p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ :=
  funext fun p => (hf.hasStrictFDerivAt p).hasFDerivAt.fderiv

/-- **DLMF §1.5(i)**: `f` is continuously differentiable (`f`, `f_x`, `f_y` continuous) iff
`f` is `C¹` on the plane. -/
theorem isContinuouslyDifferentiable_iff (f : ℝ → ℝ → ℝ) :
    IsContinuouslyDifferentiable f ↔ ContDiff ℝ 1 (uncurry f) := by
  constructor
  · intro hf
    rw [contDiff_one_iff_fderiv, fderiv_uncurry_eq hf]
    exact ⟨fun p => (hf.hasStrictFDerivAt p).hasFDerivAt.differentiableAt,
      ((hf.2.2.2.1.smul continuous_const).add (hf.2.2.2.2.smul continuous_const))⟩
  · intro hf
    have hd : Differentiable ℝ (uncurry f) := hf.differentiable one_ne_zero
    have hc : Continuous (fderiv ℝ (uncurry f)) := hf.continuous_fderiv one_ne_zero
    have hX : partialX f = fun x y => fderiv ℝ (uncurry f) (x, y) (1, 0) :=
      funext₂ fun x y => partialX_of_hasFDerivAt (hd (x, y)).hasFDerivAt
    have hY : partialY f = fun x y => fderiv ℝ (uncurry f) (x, y) (0, 1) :=
      funext₂ fun x y => partialY_of_hasFDerivAt (hd (x, y)).hasFDerivAt
    refine ⟨hf.continuous, fun x y => (hasDerivAt_partialX (hd (x, y)).hasFDerivAt)
      |>.differentiableAt, fun x y => (hasDerivAt_partialY (hd (x, y)).hasFDerivAt)
      |>.differentiableAt, ?_, ?_⟩
    · rw [hX]
      exact hc.clm_apply continuous_const
    · rw [hY]
      exact hc.clm_apply continuous_const

/-- **DLMF §1.5(i)**: `f` is twice-continuously differentiable if moreover `∂²f/∂x²`, `∂²f/∂y²`,
`∂²f/∂x∂y` and `∂²f/∂y∂x` (exist and) are continuous, i.e. `f_x` and `f_y` are themselves
continuously differentiable. -/
def IsTwiceContinuouslyDifferentiable (f : ℝ → ℝ → ℝ) : Prop :=
  IsContinuouslyDifferentiable f ∧ IsContinuouslyDifferentiable (partialX f) ∧
    IsContinuouslyDifferentiable (partialY f)

/-- Twice-continuous differentiability is `C²` on the plane. -/
theorem isTwiceContinuouslyDifferentiable_iff (f : ℝ → ℝ → ℝ) :
    IsTwiceContinuouslyDifferentiable f ↔ ContDiff ℝ 2 (uncurry f) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  constructor
  · rintro ⟨hf, hX, hY⟩
    rw [isContinuouslyDifferentiable_iff] at hX hY
    rw [fderiv_uncurry_eq hf]
    exact ⟨fun p => (hf.hasStrictFDerivAt p).hasFDerivAt.differentiableAt, fun h => by simp at h,
      (hX.smul contDiff_const).add (hY.smul contDiff_const)⟩
  · rintro ⟨hd, -, hc⟩
    have hC1 : ContDiff ℝ 1 (uncurry f) := contDiff_one_iff_fderiv.mpr ⟨hd, hc.continuous⟩
    have hX : partialX f = fun x y => fderiv ℝ (uncurry f) (x, y) (1, 0) :=
      funext₂ fun x y => partialX_of_hasFDerivAt (hd (x, y)).hasFDerivAt
    have hY : partialY f = fun x y => fderiv ℝ (uncurry f) (x, y) (0, 1) :=
      funext₂ fun x y => partialY_of_hasFDerivAt (hd (x, y)).hasFDerivAt
    refine ⟨(isContinuouslyDifferentiable_iff f).mpr hC1, ?_, ?_⟩
    · rw [isContinuouslyDifferentiable_iff, hX]
      exact hc.clm_apply contDiff_const
    · rw [isContinuouslyDifferentiable_iff, hY]
      exact hc.clm_apply contDiff_const

/-- **DLMF 1.5.6**: for twice-continuously differentiable `f`, `∂²f/∂x∂y = ∂²f/∂y∂x`. -/
theorem dlmf_1_5_6 {f : ℝ → ℝ → ℝ} (hf : IsTwiceContinuouslyDifferentiable f) (x y : ℝ) :
    partialXY f x y = partialYX f x y := by
  have h2 := (isTwiceContinuouslyDifferentiable_iff f).mp hf
  have hd : Differentiable ℝ (uncurry f) := h2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ (uncurry f)) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hsym : IsSymmSndFDerivAt ℝ (uncurry f) (x, y) :=
    h2.contDiffAt.isSymmSndFDerivAt (by simp)
  have hX : partialX f = fun x y => fderiv ℝ (uncurry f) (x, y) (1, 0) :=
    funext₂ fun x y => partialX_of_hasFDerivAt (hd (x, y)).hasFDerivAt
  have hY : partialY f = fun x y => fderiv ℝ (uncurry f) (x, y) (0, 1) :=
    funext₂ fun x y => partialY_of_hasFDerivAt (hd (x, y)).hasFDerivAt
  -- the derivative of `p ↦ Df(p) w` is `v ↦ D²f(p) v w`
  have happ : ∀ w : ℝ × ℝ, HasFDerivAt (fun p => fderiv ℝ (uncurry f) p w)
      ((fderiv ℝ (uncurry f) (x, y)).comp 0 +
        (fderiv ℝ (fderiv ℝ (uncurry f)) (x, y)).flip w) (x, y) := fun w =>
    (hdd (x, y)).hasFDerivAt.clm_apply (hasFDerivAt_const w (x, y))
  have e1 : partialX (fun x y => fderiv ℝ (uncurry f) (x, y) (0, 1)) x y =
      fderiv ℝ (fderiv ℝ (uncurry f)) (x, y) (1, 0) (0, 1) := by
    rw [partialX_of_hasFDerivAt (f := fun x y => fderiv ℝ (uncurry f) (x, y) (0, 1)) (happ _)]
    simp
  have e2 : partialY (fun x y => fderiv ℝ (uncurry f) (x, y) (1, 0)) x y =
      fderiv ℝ (fderiv ℝ (uncurry f)) (x, y) (0, 1) (1, 0) := by
    rw [partialY_of_hasFDerivAt (f := fun x y => fderiv ℝ (uncurry f) (x, y) (1, 0)) (happ _)]
    simp
  rw [partialXY, partialYX, hY, hX, e1, e2]
  exact hsym _ _

/-! ### Chain rule -/

/-- **DLMF 1.5.7**: `d/dt f(x(t), y(t)) = f_x dx/dt + f_y dy/dt`, for `f` differentiable at
`(x(t), y(t))`. -/
theorem dlmf_1_5_7 {f : ℝ → ℝ → ℝ} {x y : ℝ → ℝ} {t x' y' : ℝ} (hx : HasDerivAt x x' t)
    (hy : HasDerivAt y y' t) (hf : DifferentiableAt ℝ (uncurry f) (x t, y t)) :
    HasDerivAt (fun s => f (x s) (y s))
      (partialX f (x t) (y t) * x' + partialY f (x t) (y t) * y') t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t (hx.prodMk hy)
  rwa [fderiv_uncurry_apply hf] at h

/-- **DLMF 1.5.8**: `∂/∂u f(x(u, v), y(u, v)) = f_x ∂x/∂u + f_y ∂y/∂u`. -/
theorem dlmf_1_5_8 {f x y : ℝ → ℝ → ℝ} {u v : ℝ}
    (hx : DifferentiableAt ℝ (fun s => x s v) u) (hy : DifferentiableAt ℝ (fun s => y s v) u)
    (hf : DifferentiableAt ℝ (uncurry f) (x u v, y u v)) :
    partialX (fun u v => f (x u v) (y u v)) u v =
      partialX f (x u v) (y u v) * partialX x u v + partialY f (x u v) (y u v) * partialX y u v :=
  (dlmf_1_5_7 hx.hasDerivAt hy.hasDerivAt hf).deriv

/-- A linear map on `ℝ × ℝ × ℝ` is determined by its values on the standard basis. -/
theorem clm_apply_triple (L : ℝ × ℝ × ℝ →L[ℝ] ℝ) (a b c : ℝ) :
    L (a, b, c) = L (1, 0, 0) * a + L (0, 1, 0) * b + L (0, 0, 1) * c := by
  have e : ((a, b, c) : ℝ × ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
      b • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [e, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- **DLMF 1.5.9**: `∂/∂v f(x(u, v), y(u, v), z(u, v)) = f_x ∂x/∂v + f_y ∂y/∂v + f_z ∂z/∂v`, for
`f` differentiable at `(x, y, z)`. -/
theorem dlmf_1_5_9 {f : ℝ → ℝ → ℝ → ℝ} {x y z : ℝ → ℝ → ℝ} {u v : ℝ}
    (hx : DifferentiableAt ℝ (x u) v) (hy : DifferentiableAt ℝ (y u) v)
    (hz : DifferentiableAt ℝ (z u) v)
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (x u v, y u v, z u v)) :
    partialY (fun u v => f (x u v) (y u v) (z u v)) u v =
      deriv (fun s => f s (y u v) (z u v)) (x u v) * partialY x u v +
      deriv (fun s => f (x u v) s (z u v)) (y u v) * partialY y u v +
      deriv (fun s => f (x u v) (y u v) s) (z u v) * partialY z u v := by
  set L := fderiv ℝ (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (x u v, y u v, z u v)
  have hL := hf.hasFDerivAt
  have h1 : deriv (fun s => f s (y u v) (z u v)) (x u v) = L (1, 0, 0) := by
    have := hL.comp_hasDerivAt (x u v) ((hasDerivAt_id (x u v)).prodMk
      ((hasDerivAt_const (x u v) (y u v)).prodMk (hasDerivAt_const (x u v) (z u v))))
    exact this.deriv
  have h2 : deriv (fun s => f (x u v) s (z u v)) (y u v) = L (0, 1, 0) := by
    have := hL.comp_hasDerivAt (y u v) ((hasDerivAt_const (y u v) (x u v)).prodMk
      ((hasDerivAt_id (y u v)).prodMk (hasDerivAt_const (y u v) (z u v))))
    exact this.deriv
  have h3 : deriv (fun s => f (x u v) (y u v) s) (z u v) = L (0, 0, 1) := by
    have := hL.comp_hasDerivAt (z u v) ((hasDerivAt_const (z u v) (x u v)).prodMk
      ((hasDerivAt_const (z u v) (y u v)).prodMk (hasDerivAt_id (z u v))))
    exact this.deriv
  have h := hL.comp_hasDerivAt v (hx.hasDerivAt.prodMk (hy.hasDerivAt.prodMk hz.hasDerivAt))
  rw [h1, h2, h3, ← clm_apply_triple]
  exact h.deriv

/-! ### Implicit function theorem -/

/-- **DLMF §1.5(i), implicit function theorem**: if `F(x, y)` is continuously differentiable,
`F(a, b) = 0` and `∂F/∂y ≠ 0` at `(a, b)`, then in a neighborhood of `(a, b)` the equation
`F(x, y) = 0` defines a continuously differentiable function `y = g(x)` with `F(x, g(x)) = 0`,
`b = g(a)` and `g'(x) = −F_x/F_y`. -/
theorem dlmf_1_5_i_implicit {F : ℝ → ℝ → ℝ} (hF : IsContinuouslyDifferentiable F) {a b : ℝ}
    (h0 : F a b = 0) (hy : partialY F a b ≠ 0) :
    ∃ g : ℝ → ℝ, g a = b ∧ (∀ᶠ x in 𝓝 a, F x (g x) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p.1 p.2 = 0 ↔ g p.1 = p.2) ∧
      (∀ᶠ x in 𝓝 a, ContDiffAt ℝ 1 g x) ∧
      ∀ᶠ x in 𝓝 a, HasDerivAt g (-partialX F x (g x) / partialY F x (g x)) x := by
  have hC := (isContinuouslyDifferentiable_iff F).mp hF
  have cdf : ContDiffAt ℝ 1 (uncurry F) (a, b) := hC.contDiffAt
  have hD : fderiv ℝ (uncurry F) (a, b) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      partialY F a b • (1 : ℝ →L[ℝ] ℝ) := by
    ext
    simp [fderiv_uncurry_apply ((hC.differentiable one_ne_zero) (a, b))]
  have if₂ : (fderiv ℝ (uncurry F) (a, b) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hD]
    exact ContinuousLinearMap.IsInvertible.of_inverse (g := (partialY F a b)⁻¹ • 1)
      (by ext; simp [hy]) (by ext; simp [hy])
  set g := cdf.implicitFunction one_ne_zero if₂
  have hga : g a = b := cdf.implicitFunction_apply_self one_ne_zero if₂
  have hzero : ∀ᶠ x in 𝓝 a, F x (g x) = 0 := by
    filter_upwards [cdf.eventually_apply_implicitFunction one_ne_zero if₂] with x hx
    rw [← h0]
    exact hx
  have hcd : ∀ᶠ x in 𝓝 a, ContDiffAt ℝ 1 g x :=
    (cdf.contDiffAt_implicitFunction one_ne_zero if₂).eventually (by simp)
  -- `F_y(x, g x) ≠ 0` near `a`, by continuity
  have hgc : ContinuousAt g a := (cdf.contDiffAt_implicitFunction one_ne_zero if₂).continuousAt
  have hFy : ∀ᶠ x in 𝓝 a, partialY F x (g x) ≠ 0 := by
    have hcont : ContinuousAt (fun x => partialY F x (g x)) a :=
      ContinuousAt.comp (g := uncurry (partialY F)) (f := fun x => (x, g x))
        hF.2.2.2.2.continuousAt (continuousAt_id.prodMk hgc)
    have := hcont.eventually_ne (by rwa [hga])
    exact this
  refine ⟨g, hga, hzero, ?_, hcd, ?_⟩
  · filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂] with p hp
    rw [← hp]
    show F p.1 p.2 = 0 ↔ F p.1 p.2 = F a b
    rw [h0]
  · filter_upwards [hcd, hzero.eventually_nhds, hFy] with x hx hz hne
    have hgd := (hx.differentiableAt one_ne_zero).hasDerivAt
    have hch := dlmf_1_5_7 (hasDerivAt_id x) hgd ((hC.differentiable one_ne_zero) (x, g x))
    have h0' : HasDerivAt (fun s => F (id s) (g s)) 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (by
        filter_upwards [hz] with s hs
        exact hs)
    have hsum := hch.unique h0'
    have hg' : deriv g x = -partialX F x (g x) / partialY F x (g x) := by
      field_simp
      simp only [id] at hsum
      linarith
    rwa [hg'] at hgd

/-! ## §1.5(ii) Coordinate systems

The DLMF follows the physicists' notation: `θ` is the polar (colatitude) angle and `φ` the azimuth;
mathematicians usually interchange the two symbols. -/

open Real

/-- Upper-half-plane polar coordinates: `(x, y)` with `y ≥ 0` is `(r cos θ, r sin θ)` with `r ≥ 0`
and `0 ≤ θ ≤ π`. -/
theorem exists_polar_of_nonneg {x y : ℝ} (hy : 0 ≤ y) :
    ∃ r θ : ℝ, 0 ≤ r ∧ θ ∈ Icc 0 π ∧ x = r * cos θ ∧ y = r * sin θ := by
  set w : ℂ := ⟨x, y⟩
  refine ⟨‖w‖, Complex.arg w, norm_nonneg _, ⟨Complex.arg_nonneg_iff.mpr hy,
    Complex.arg_le_pi w⟩, ?_, ?_⟩
  · rw [Complex.norm_mul_cos_arg]
  · rw [Complex.norm_mul_sin_arg]

/-- **DLMF 1.5.10** (polar coordinates): every `(x, y)` is `(r cos φ, r sin φ)` with `0 ≤ r < ∞`,
`0 ≤ φ < 2π`. -/
theorem dlmf_1_5_10 (x y : ℝ) :
    ∃ r φ : ℝ, 0 ≤ r ∧ φ ∈ Ico 0 (2 * π) ∧ x = r * cos φ ∧ y = r * sin φ := by
  set w : ℂ := ⟨x, y⟩
  have hc : ‖w‖ * cos (Complex.arg w) = x := Complex.norm_mul_cos_arg w
  have hs : ‖w‖ * sin (Complex.arg w) = y := Complex.norm_mul_sin_arg w
  have h1 := Complex.neg_pi_lt_arg w
  have h2 := Complex.arg_le_pi w
  rcases le_or_gt 0 (Complex.arg w) with h | h
  · refine ⟨‖w‖, Complex.arg w, norm_nonneg _, ⟨h, by linarith [pi_pos]⟩, hc.symm, hs.symm⟩
  · refine ⟨‖w‖, Complex.arg w + 2 * π, norm_nonneg _, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [cos_add_two_pi, hc]
    · rw [sin_add_two_pi, hs]

/-- A function `f(x, y)` expressed in polar coordinates: `(r, φ) ↦ f(r cos φ, r sin φ)`. -/
noncomputable def polarPullback (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r φ => f (r * cos φ) (r * sin φ)

/-- `∂/∂r f(r cos φ, r sin φ) = f_x cos φ + f_y sin φ`. -/
theorem hasDerivAt_polar_r {f : ℝ → ℝ → ℝ} {r φ : ℝ}
    (hf : DifferentiableAt ℝ (uncurry f) (r * cos φ, r * sin φ)) :
    HasDerivAt (fun s => f (s * cos φ) (s * sin φ))
      (partialX f (r * cos φ) (r * sin φ) * cos φ + partialY f (r * cos φ) (r * sin φ) * sin φ)
      r :=
  (dlmf_1_5_7 ((hasDerivAt_id r).mul_const (cos φ)) ((hasDerivAt_id r).mul_const (sin φ))
    hf).congr_deriv (by simp)

/-- `∂/∂φ f(r cos φ, r sin φ) = −f_x r sin φ + f_y r cos φ`. -/
theorem hasDerivAt_polar_φ {f : ℝ → ℝ → ℝ} {r φ : ℝ}
    (hf : DifferentiableAt ℝ (uncurry f) (r * cos φ, r * sin φ)) :
    HasDerivAt (fun t => f (r * cos t) (r * sin t))
      (partialX f (r * cos φ) (r * sin φ) * (r * -sin φ) +
        partialY f (r * cos φ) (r * sin φ) * (r * cos φ)) φ :=
  dlmf_1_5_7 ((hasDerivAt_cos φ).const_mul r) ((hasDerivAt_sin φ).const_mul r) hf

/-- **DLMF 1.5.11**: `∂/∂x = cos φ ∂/∂r − (sin φ / r) ∂/∂φ`. -/
theorem dlmf_1_5_11 {f : ℝ → ℝ → ℝ} {r φ : ℝ} (hr : r ≠ 0)
    (hf : DifferentiableAt ℝ (uncurry f) (r * cos φ, r * sin φ)) :
    partialX f (r * cos φ) (r * sin φ) =
      cos φ * partialX (polarPullback f) r φ - sin φ / r * partialY (polarPullback f) r φ := by
  have e1 : partialX (polarPullback f) r φ = _ := (hasDerivAt_polar_r hf).deriv
  have e2 : partialY (polarPullback f) r φ = _ := (hasDerivAt_polar_φ hf).deriv
  rw [e1, e2]
  have e3 : sin φ / r * (partialX f (r * cos φ) (r * sin φ) * (r * -sin φ) +
      partialY f (r * cos φ) (r * sin φ) * (r * cos φ)) = sin φ *
      (partialX f (r * cos φ) (r * sin φ) * -sin φ +
        partialY f (r * cos φ) (r * sin φ) * cos φ) := by
    field_simp
  rw [e3]
  linear_combination (-partialX f (r * cos φ) (r * sin φ)) * sin_sq_add_cos_sq φ

/-- **DLMF 1.5.12**: `∂/∂y = sin φ ∂/∂r + (cos φ / r) ∂/∂φ`. -/
theorem dlmf_1_5_12 {f : ℝ → ℝ → ℝ} {r φ : ℝ} (hr : r ≠ 0)
    (hf : DifferentiableAt ℝ (uncurry f) (r * cos φ, r * sin φ)) :
    partialY f (r * cos φ) (r * sin φ) =
      sin φ * partialX (polarPullback f) r φ + cos φ / r * partialY (polarPullback f) r φ := by
  have e1 : partialX (polarPullback f) r φ = _ := (hasDerivAt_polar_r hf).deriv
  have e2 : partialY (polarPullback f) r φ = _ := (hasDerivAt_polar_φ hf).deriv
  rw [e1, e2]
  have e3 : cos φ / r * (partialX f (r * cos φ) (r * sin φ) * (r * -sin φ) +
      partialY f (r * cos φ) (r * sin φ) * (r * cos φ)) = cos φ *
      (partialX f (r * cos φ) (r * sin φ) * -sin φ +
        partialY f (r * cos φ) (r * sin φ) * cos φ) := by
    field_simp
  rw [e3]
  linear_combination (-partialY f (r * cos φ) (r * sin φ)) * sin_sq_add_cos_sq φ

/-- A twice-continuously differentiable `f` and its first partials are differentiable on the
plane. -/
theorem IsTwiceContinuouslyDifferentiable.differentiable {f : ℝ → ℝ → ℝ}
    (hf : IsTwiceContinuouslyDifferentiable f) :
    Differentiable ℝ (uncurry f) ∧ Differentiable ℝ (uncurry (partialX f)) ∧
      Differentiable ℝ (uncurry (partialY f)) :=
  ⟨((isContinuouslyDifferentiable_iff f).mp hf.1).differentiable one_ne_zero,
    ((isContinuouslyDifferentiable_iff _).mp hf.2.1).differentiable one_ne_zero,
    ((isContinuouslyDifferentiable_iff _).mp hf.2.2).differentiable one_ne_zero⟩

/-- `∂²/∂r²` of `f(r cos φ, r sin φ)`. -/
theorem hasDerivAt_polar_rr {f : ℝ → ℝ → ℝ} (hf : IsTwiceContinuouslyDifferentiable f)
    (r φ : ℝ) : HasDerivAt (fun s => partialX (polarPullback f) s φ)
      ((partialXX f (r * cos φ) (r * sin φ) * cos φ + partialYX f (r * cos φ) (r * sin φ) *
        sin φ) * cos φ + (partialXY f (r * cos φ) (r * sin φ) * cos φ +
        partialYY f (r * cos φ) (r * sin φ) * sin φ) * sin φ) r := by
  obtain ⟨h0, hX, hY⟩ := hf.differentiable
  have e : (fun s => partialX (polarPullback f) s φ) = fun s =>
      partialX f (s * cos φ) (s * sin φ) * cos φ + partialY f (s * cos φ) (s * sin φ) * sin φ :=
    funext fun s => (hasDerivAt_polar_r (h0 _)).deriv
  rw [e]
  exact ((hasDerivAt_polar_r (hX _)).mul_const (cos φ)).add
    ((hasDerivAt_polar_r (hY _)).mul_const (sin φ))

/-- `∂²/∂φ²` of `f(r cos φ, r sin φ)`. -/
theorem hasDerivAt_polar_φφ {f : ℝ → ℝ → ℝ} (hf : IsTwiceContinuouslyDifferentiable f)
    (r φ : ℝ) : HasDerivAt (fun t => partialY (polarPullback f) r t)
      ((partialXX f (r * cos φ) (r * sin φ) * (r * -sin φ) +
          partialYX f (r * cos φ) (r * sin φ) * (r * cos φ)) * (r * -sin φ) +
        partialX f (r * cos φ) (r * sin φ) * (r * -cos φ) +
        ((partialXY f (r * cos φ) (r * sin φ) * (r * -sin φ) +
          partialYY f (r * cos φ) (r * sin φ) * (r * cos φ)) * (r * cos φ) +
        partialY f (r * cos φ) (r * sin φ) * (r * -sin φ))) φ := by
  obtain ⟨h0, hX, hY⟩ := hf.differentiable
  have e : (fun t => partialY (polarPullback f) r t) = fun t =>
      partialX f (r * cos t) (r * sin t) * (r * -sin t) +
        partialY f (r * cos t) (r * sin t) * (r * cos t) :=
    funext fun t => (hasDerivAt_polar_φ (h0 _)).deriv
  rw [e]
  exact ((hasDerivAt_polar_φ (hX _)).mul ((hasDerivAt_sin φ).neg.const_mul r)).add
    ((hasDerivAt_polar_φ (hY _)).mul ((hasDerivAt_cos φ).const_mul r))

/-- **DLMF 1.5.13** (Laplacian in polar coordinates): `∇²f = f_xx + f_yy = f_rr + f_r/r + f_φφ/r²`,
for twice-continuously differentiable `f` and `r ≠ 0`. -/
theorem dlmf_1_5_13 {f : ℝ → ℝ → ℝ} (hf : IsTwiceContinuouslyDifferentiable f) {r φ : ℝ}
    (hr : r ≠ 0) :
    partialXX f (r * cos φ) (r * sin φ) + partialYY f (r * cos φ) (r * sin φ) =
      partialXX (polarPullback f) r φ + partialX (polarPullback f) r φ / r +
        partialYY (polarPullback f) r φ / r ^ 2 := by
  have e1 : partialXX (polarPullback f) r φ = _ := (hasDerivAt_polar_rr hf r φ).deriv
  have e2 : partialYY (polarPullback f) r φ = _ := (hasDerivAt_polar_φφ hf r φ).deriv
  have e3 : partialX (polarPullback f) r φ = _ :=
    (hasDerivAt_polar_r (hf.differentiable.1 (r * cos φ, r * sin φ))).deriv
  rw [e1, e2, e3]
  set A := partialXX f (r * cos φ) (r * sin φ)
  set B := partialYX f (r * cos φ) (r * sin φ)
  set C := partialXY f (r * cos φ) (r * sin φ)
  set D := partialYY f (r * cos φ) (r * sin φ)
  set a := partialX f (r * cos φ) (r * sin φ)
  set b := partialY f (r * cos φ) (r * sin φ)
  have e4 : ((A * (r * -sin φ) + B * (r * cos φ)) * (r * -sin φ) + a * (r * -cos φ) +
      ((C * (r * -sin φ) + D * (r * cos φ)) * (r * cos φ) + b * (r * -sin φ))) / r ^ 2 =
      A * sin φ ^ 2 - B * sin φ * cos φ - C * sin φ * cos φ + D * cos φ ^ 2 -
        (a * cos φ + b * sin φ) / r := by
    field_simp
    ring
  rw [e4]
  linear_combination (-(A + D)) * sin_sq_add_cos_sq φ

/-- `∇²f = f_xx + f_yy + f_zz` for `f(x, y, z)`, the second derivatives taken in each variable with
the other two fixed. -/
noncomputable def laplacian3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partialXX (fun a b => f a b z) x y + partialYY (fun a b => f a b z) x y + deriv (deriv (f x y)) z

/-- **DLMF 1.5.14** (cylindrical coordinates): every `(x, y, z)` is `(r cos φ, r sin φ, z)` with
`0 ≤ r < ∞`, `0 ≤ φ < 2π`. -/
theorem dlmf_1_5_14 (x y z : ℝ) : ∃ r φ : ℝ, 0 ≤ r ∧ φ ∈ Ico 0 (2 * π) ∧
    (x, y, z) = (r * cos φ, r * sin φ, z) := by
  obtain ⟨r, φ, hr, hφ, hx, hy⟩ := dlmf_1_5_10 x y
  exact ⟨r, φ, hr, hφ, by rw [hx, hy]⟩

/-- **DLMF §1.5(ii)**: in cylindrical coordinates 1.5.11 and 1.5.12 still apply (to `f(·, ·, z)`
for each `z`). -/
theorem dlmf_1_5_14_partial {f : ℝ → ℝ → ℝ → ℝ} {r φ z : ℝ} (hr : r ≠ 0)
    (hf : DifferentiableAt ℝ (uncurry fun a b => f a b z) (r * cos φ, r * sin φ)) :
    partialX (fun a b => f a b z) (r * cos φ) (r * sin φ) =
        cos φ * partialX (fun r φ => f (r * cos φ) (r * sin φ) z) r φ -
          sin φ / r * partialY (fun r φ => f (r * cos φ) (r * sin φ) z) r φ ∧
      partialY (fun a b => f a b z) (r * cos φ) (r * sin φ) =
        sin φ * partialX (fun r φ => f (r * cos φ) (r * sin φ) z) r φ +
          cos φ / r * partialY (fun r φ => f (r * cos φ) (r * sin φ) z) r φ :=
  ⟨dlmf_1_5_11 hr hf, dlmf_1_5_12 hr hf⟩

/-- **DLMF 1.5.15** (Laplacian in cylindrical coordinates):
`∇²f = f_rr + f_r/r + f_φφ/r² + f_zz`, for `f(·, ·, z)` twice-continuously differentiable for
every `z`, and `r ≠ 0`. -/
theorem dlmf_1_5_15 {f : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ z, IsTwiceContinuouslyDifferentiable fun a b => f a b z) {r φ z : ℝ} (hr : r ≠ 0) :
    laplacian3 f (r * cos φ) (r * sin φ) z =
      partialXX (fun r φ => f (r * cos φ) (r * sin φ) z) r φ +
        partialX (fun r φ => f (r * cos φ) (r * sin φ) z) r φ / r +
        partialYY (fun r φ => f (r * cos φ) (r * sin φ) z) r φ / r ^ 2 +
        deriv (deriv fun z => f (r * cos φ) (r * sin φ) z) z := by
  have h := dlmf_1_5_13 (hf z) hr (φ := φ)
  unfold laplacian3
  rw [h]
  rfl

/-- **DLMF 1.5.16** (spherical coordinates): every `(x, y, z)` is
`(ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ)` with `0 ≤ ρ < ∞`, `0 ≤ θ ≤ π`, `0 ≤ φ < 2π`. -/
theorem dlmf_1_5_16 (x y z : ℝ) : ∃ ρ θ φ : ℝ, 0 ≤ ρ ∧ θ ∈ Icc 0 π ∧ φ ∈ Ico 0 (2 * π) ∧
    (x, y, z) = (ρ * sin θ * cos φ, ρ * sin θ * sin φ, ρ * cos θ) := by
  obtain ⟨r, φ, hr, hφ, hx, hy⟩ := dlmf_1_5_10 x y
  obtain ⟨ρ, θ, hρ, hθ, hz, hr'⟩ := exists_polar_of_nonneg (x := z) hr
  exact ⟨ρ, θ, φ, hρ, hθ, hφ, by rw [hx, hy, hz, hr']⟩

/-- A function `f(x, y, z)` expressed in spherical coordinates:
`(ρ, θ, φ) ↦ f(ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ)`. -/
noncomputable def sphericalPullback (f : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun ρ θ φ => f (ρ * sin θ * cos φ) (ρ * sin θ * sin φ) (ρ * cos θ)

/-- **DLMF 1.5.17** (Laplacian in spherical coordinates): for `C²` `f(x, y, z)`, `ρ ≠ 0` and
`sin θ ≠ 0`,
`∇²f = (1/ρ²) ∂/∂ρ (ρ² ∂f/∂ρ) + (1/(ρ² sin² θ)) ∂²f/∂φ² + (1/(ρ² sin θ)) ∂/∂θ (sin θ ∂f/∂θ)`.
The proof composes the cylindrical Laplacian 1.5.15 with polar coordinates `(z, r) =
(ρ cos θ, ρ sin θ)` in the `(z, r)` half-plane (1.5.12, 1.5.13). -/
theorem dlmf_1_5_17 {f : ℝ → ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
    {ρ θ φ : ℝ} (hρ : ρ ≠ 0) (hθ : sin θ ≠ 0) :
    laplacian3 f (ρ * sin θ * cos φ) (ρ * sin θ * sin φ) (ρ * cos θ) =
      1 / ρ ^ 2 * deriv (fun s => s ^ 2 * deriv (fun t => sphericalPullback f t θ φ) s) ρ +
        1 / (ρ ^ 2 * sin θ ^ 2) * deriv (deriv fun t => sphericalPullback f ρ θ t) φ +
        1 / (ρ ^ 2 * sin θ) *
          deriv (fun t => sin t * deriv (fun u => sphericalPullback f ρ u φ) t) θ := by
  have hslice : ∀ z, IsTwiceContinuouslyDifferentiable fun a b => f a b z := fun z =>
    (isTwiceContinuouslyDifferentiable_iff _).mpr
      (hf.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)))
  set G : ℝ → ℝ → ℝ := fun z r => f (r * cos φ) (r * sin φ) z with hGdef
  have hG : IsTwiceContinuouslyDifferentiable G := (isTwiceContinuouslyDifferentiable_iff _).mpr
    (hf.comp ((contDiff_snd.mul contDiff_const).prodMk
      ((contDiff_snd.mul contDiff_const).prodMk contDiff_fst)))
  -- the cylindrical Laplacian at `r = ρ sin θ`, `z = ρ cos θ`
  have hA := dlmf_1_5_15 hslice (mul_ne_zero hρ hθ) (φ := φ) (z := ρ * cos θ)
  -- polar coordinates `(z, r) = (ρ cos θ, ρ sin θ)` in the `(z, r)` half-plane
  have hB : deriv (deriv fun z => f (ρ * sin θ * cos φ) (ρ * sin θ * sin φ) z) (ρ * cos θ) +
      partialXX (fun r φ => f (r * cos φ) (r * sin φ) (ρ * cos θ)) (ρ * sin θ) φ =
      partialXX (polarPullback G) ρ θ + partialX (polarPullback G) ρ θ / ρ +
        partialYY (polarPullback G) ρ θ / ρ ^ 2 :=
    dlmf_1_5_13 hG hρ (φ := θ)
  have hC : partialX (fun r φ => f (r * cos φ) (r * sin φ) (ρ * cos θ)) (ρ * sin θ) φ =
      sin θ * partialX (polarPullback G) ρ θ + cos θ / ρ * partialY (polarPullback G) ρ θ :=
    dlmf_1_5_12 hρ (hG.differentiable.1 _)
  have h1 : deriv (fun s => s ^ 2 * deriv (fun t => sphericalPullback f t θ φ) s) ρ =
      2 * ρ * partialX (polarPullback G) ρ θ + ρ ^ 2 * partialXX (polarPullback G) ρ θ := by
    have hd : HasDerivAt (fun s => partialX (polarPullback G) s θ)
        (partialXX (polarPullback G) ρ θ) ρ :=
      (hasDerivAt_polar_rr hG ρ θ).differentiableAt.hasDerivAt
    exact (((hasDerivAt_pow 2 ρ).mul hd).congr_deriv (by norm_num)).deriv
  have h2 : deriv (fun t => sin t * deriv (fun u => sphericalPullback f ρ u φ) t) θ =
      cos θ * partialY (polarPullback G) ρ θ + sin θ * partialYY (polarPullback G) ρ θ := by
    have hd : HasDerivAt (fun t => partialY (polarPullback G) ρ t)
        (partialYY (polarPullback G) ρ θ) θ :=
      (hasDerivAt_polar_φφ hG ρ θ).differentiableAt.hasDerivAt
    exact ((hasDerivAt_sin θ).mul hd).deriv
  have h3 : deriv (deriv fun t => sphericalPullback f ρ θ t) φ =
      partialYY (fun r φ => f (r * cos φ) (r * sin φ) (ρ * cos θ)) (ρ * sin θ) φ := rfl
  rw [hA, h1, h2, h3, hC]
  linear_combination (norm := skip) hB
  field_simp
  ring

/-! ## §1.5(iii) Taylor's theorem; maxima and minima -/

section TaylorTwo

open Finset

/-- Taylor's theorem with Peano remainder in a normed space: for `F` of class `Cⁿ`, the remainder
`F(x + y) − ∑_{k ≤ n} D^k F(x)(y, …, y)/k!` is `o(‖y‖ⁿ)`.  (From Mathlib's integral form of the
remainder at order `n − 1` and the continuity of `Dⁿ F`.) -/
theorem taylor_remainder_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {n : ℕ} (hF : ContDiff ℝ n F) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : E, ‖y‖ < δ → |F (x + y) - ∑ k ∈ range (n + 1),
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k F x (fun _ => y)| ≤ ε * ‖y‖ ^ n := by
  cases n with
  | zero =>
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (hF.continuous.continuousAt (x := x)) ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have := @h (x + y) (by rwa [dist_eq_norm, add_sub_cancel_left])
    rw [Real.dist_eq] at this
    simpa using this.le
  | succ m =>
    have hc : Continuous (iteratedFDeriv ℝ (m + 1) F) := hF.continuous_iteratedFDeriv le_rfl
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := x)) ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hT := map_add_eq_sum_add_integral_iteratedFDeriv (f := F) (x := x) (y := y) (n := m)
      (fun t _ => hF.contDiffAt)
    simp only [smul_eq_mul] at hT
    set c := iteratedFDeriv ℝ (m + 1) F x (fun _ => y)
    set g : ℝ → ℝ := fun t => iteratedFDeriv ℝ (m + 1) F (x + t • y) (fun _ => y)
    have hg : Continuous g :=
      (continuous_eval_const (fun _ : Fin (m + 1) => y)).comp
        (hc.comp (continuous_const.add (continuous_id.smul continuous_const)))
    have hI1 : ∫ t in (0 : ℝ)..1, (1 - t) ^ m = 1 / (m + 1) := by
      rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ m)]
      simp [integral_pow]
    have hint1 : IntervalIntegrable (fun t => (1 - t) ^ m * g t) MeasureTheory.volume 0 1 :=
      ((continuous_const.sub continuous_id).pow m |>.mul hg).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ m * c) MeasureTheory.volume 0 1 :=
      ((continuous_const.sub continuous_id).pow m |>.mul continuous_const).intervalIntegrable 0 1
    have key : ((m + 1).factorial : ℝ)⁻¹ * c =
        (m.factorial : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, (1 - t) ^ m * c := by
      rw [intervalIntegral.integral_mul_const, hI1, Nat.factorial_succ]
      push_cast
      field_simp
    have hR : F (x + y) - ∑ k ∈ range (m + 1 + 1),
        (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k F x (fun _ => y) =
        (m.factorial : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, ((1 - t) ^ m * g t - (1 - t) ^ m * c) := by
      rw [sum_range_succ, hT, key, intervalIntegral.integral_sub hint1 hint2]
      ring
    rw [hR]
    have hbound : ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ m * g t - (1 - t) ^ m * c)‖ ≤
        ε * ‖y‖ ^ (m + 1) * |1 - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le zero_le_one] at ht
      have h1 : |(1 - t) ^ m| ≤ 1 := by
        rw [abs_pow, abs_of_nonneg (by linarith [ht.2])]
        exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
      have hd : dist (x + t • y) x < δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht.1]
        calc t * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ < δ := by rwa [one_mul]
      have h2 : ‖g t - c‖ ≤ ε * ‖y‖ ^ (m + 1) := by
        have hop := ((iteratedFDeriv ℝ (m + 1) F (x + t • y)) -
          iteratedFDeriv ℝ (m + 1) F x).le_opNorm (fun _ => y)
        simp only [_root_.sub_apply, prod_const, card_univ,
          Fintype.card_fin] at hop
        refine hop.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        have := h hd
        rw [dist_eq_norm] at this
        exact this.le
      rw [← mul_sub, norm_mul, Real.norm_eq_abs]
      calc |(1 - t) ^ m| * ‖g t - c‖ ≤ 1 * (ε * ‖y‖ ^ (m + 1)) :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = ε * ‖y‖ ^ (m + 1) := one_mul _
    rw [abs_mul, abs_inv, Nat.abs_cast]
    have h1fac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hfac : (m.factorial : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1fac
    rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hbound
    calc (m.factorial : ℝ)⁻¹ * |∫ t in (0 : ℝ)..1, ((1 - t) ^ m * g t - (1 - t) ^ m * c)|
        ≤ 1 * (ε * ‖y‖ ^ (m + 1)) :=
          mul_le_mul hfac hbound (abs_nonneg _) zero_le_one
      _ = ε * ‖y‖ ^ (m + 1) := one_mul _

/-- The operator `λ ∂/∂x + μ ∂/∂y` of DLMF 1.5.18 (here `ℓ ∂/∂x + μ ∂/∂y`). -/
noncomputable def dirDeriv (ℓ μ : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => ℓ * partialX g x y + μ * partialY g x y

/-- For `f` of class `Cⁿ` and `k ≤ n`, `(ℓ ∂/∂x + μ ∂/∂y)^k f = D^k f((ℓ, μ), …, (ℓ, μ))`. -/
theorem iterate_dirDeriv {f : ℝ → ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n (uncurry f)) (ℓ μ : ℝ) :
    ∀ k ≤ n, ∀ x y, (dirDeriv ℓ μ)^[k] f x y =
      iteratedFDeriv ℝ k (uncurry f) (x, y) (fun _ => (ℓ, μ)) := by
  intro k
  induction k with
  | zero => intro _ x y; simp
  | succ k ih =>
    intro hk x y
    have hk' : (k : WithTop ℕ∞) < n := by exact_mod_cast hk
    have e : (dirDeriv ℓ μ)^[k] f =
        fun x y => iteratedFDeriv ℝ k (uncurry f) (x, y) (fun _ => (ℓ, μ)) :=
      funext₂ (ih (by omega))
    rw [Function.iterate_succ_apply', e]
    have hd := ((hf.differentiable_iteratedFDeriv hk') (x, y)).hasFDerivAt
      |>.continuousMultilinear_apply_const (fun _ : Fin k => ((ℓ, μ) : ℝ × ℝ))
    simp only [dirDeriv]
    rw [partialX_of_hasFDerivAt
        (f := fun a b => iteratedFDeriv ℝ k (uncurry f) (a, b) (fun _ => (ℓ, μ))) hd,
      partialY_of_hasFDerivAt
        (f := fun a b => iteratedFDeriv ℝ k (uncurry f) (a, b) (fun _ => (ℓ, μ))) hd,
      mul_comm ℓ, mul_comm μ, ← clm_apply_pair, iteratedFDeriv_succ_apply_left]
    rfl

theorem norm_le_sqrt_sq_add_sq (v : ℝ × ℝ) : ‖v‖ ≤ √(v.1 ^ 2 + v.2 ^ 2) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (Real.abs_le_sqrt (by nlinarith [sq_nonneg v.2]))
    (Real.abs_le_sqrt (by nlinarith [sq_nonneg v.1]))

/-- **DLMF 1.5.18** (Taylor's theorem): if `f` is `n + 1` times continuously differentiable, then
`f(a + λ, b + μ) = ∑_{k=0}^n (1/k!) (λ ∂/∂x + μ ∂/∂y)^k f(a, b) + R_n` with
`R_n / (λ² + μ²)^{n/2} → 0` as `(λ, μ) → (0, 0)`. -/
theorem dlmf_1_5_18 {f : ℝ → ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) (uncurry f)) (a b : ℝ) :
    Tendsto (fun v : ℝ × ℝ => (f (a + v.1) (b + v.2) - ∑ k ∈ range (n + 1),
      (k.factorial : ℝ)⁻¹ * (dirDeriv v.1 v.2)^[k] f a b) / (v.1 ^ 2 + v.2 ^ 2) ^ ((n : ℝ) / 2))
      (𝓝[≠] 0) (𝓝 0) := by
  have hn : ContDiff ℝ n (uncurry f) := hf.of_le (by exact_mod_cast Nat.le_succ n)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := taylor_remainder_le hn (a, b) (half_pos hε)
  refine ⟨δ, hδ, fun v hv hvd => ?_⟩
  rw [dist_zero_right] at hvd
  rw [Real.dist_eq, sub_zero]
  have hv0 : v ≠ 0 := hv
  have hsum : ∑ k ∈ range (n + 1), (k.factorial : ℝ)⁻¹ * (dirDeriv v.1 v.2)^[k] f a b =
      ∑ k ∈ range (n + 1), (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k (uncurry f) (a, b)
        (fun _ => v) :=
    sum_congr rfl fun k hk => by
      rw [iterate_dirDeriv hn v.1 v.2 k (Nat.lt_succ_iff.mp (mem_range.mp hk)) a b,
        Prod.mk.eta]
  have hR := h v hvd
  have hfv : uncurry f ((a, b) + v) = f (a + v.1) (b + v.2) := rfl
  rw [hfv] at hR
  have hpos : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases v with ⟨p, q⟩
    have : p ≠ 0 ∨ q ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv0 (by rw [hc.1, hc.2]; rfl)
    rcases this with h' | h' <;> positivity
  have hpow : (v.1 ^ 2 + v.2 ^ 2) ^ ((n : ℝ) / 2) = √(v.1 ^ 2 + v.2 ^ 2) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hpos.le]
    congr 1
    ring
  set r := √(v.1 ^ 2 + v.2 ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  rw [hpow, hsum, abs_div, abs_of_pos (pow_pos hr n), div_lt_iff₀ (pow_pos hr n)]
  calc _ ≤ ε / 2 * ‖v‖ ^ n := hR
    _ ≤ ε / 2 * r ^ n := by
        gcongr
        exact norm_le_sqrt_sq_add_sq v
    _ < ε * r ^ n := by
        have := mul_pos hε (pow_pos hr n)
        linarith

/-- Second-order expansion: for `C²` `f`, `f(a + λ, b + μ) − f − (λ f_x + μ f_y) −
(λ² f_xx + 2λμ f_xy + μ² f_yy)/2 = o(λ² + μ²)`. -/
theorem taylor_two {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (uncurry f)) (a b : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ v : ℝ × ℝ, ‖v‖ < δ →
      |f (a + v.1) (b + v.2) - f a b - (v.1 * partialX f a b + v.2 * partialY f a b) -
        (v.1 ^ 2 * partialXX f a b + 2 * v.1 * v.2 * partialXY f a b +
          v.2 ^ 2 * partialYY f a b) / 2| ≤ ε * ‖v‖ ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := taylor_remainder_le (n := 2) hf (a, b) hε
  have hf2 := (isTwiceContinuouslyDifferentiable_iff f).mpr hf
  obtain ⟨-, hX, hY⟩ := hf2.differentiable
  have hsym := dlmf_1_5_6 hf2 a b
  refine ⟨δ, hδ, fun v hv => ?_⟩
  have hR := h v hv
  have hfv : uncurry f ((a, b) + v) = f (a + v.1) (b + v.2) := rfl
  rw [hfv] at hR
  have hk : ∀ k ≤ 2, iteratedFDeriv ℝ k (uncurry f) (a, b) (fun _ => v) =
      (dirDeriv v.1 v.2)^[k] f a b := fun k hk => by
    rw [iterate_dirDeriv hf v.1 v.2 k (by exact_mod_cast hk) a b, Prod.mk.eta]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add] at hR
  rw [hk 0 (by norm_num), hk 1 (by norm_num), hk 2 (by norm_num)] at hR
  -- `(ℓ ∂x + μ ∂y)² f = ℓ² f_xx + ℓμ (f_xy + f_yx) + μ² f_yy`
  have hdx : HasDerivAt (fun t => v.1 * partialX f t b + v.2 * partialY f t b)
      (v.1 * partialXX f a b + v.2 * partialXY f a b) a :=
    (HasDerivAt.const_mul v.1
      (hasDerivAt_partialX (hX (a, b)).hasFDerivAt).differentiableAt.hasDerivAt).add
      (HasDerivAt.const_mul v.2
        (hasDerivAt_partialX (hY (a, b)).hasFDerivAt).differentiableAt.hasDerivAt)
  have hdy : HasDerivAt (fun t => v.1 * partialX f a t + v.2 * partialY f a t)
      (v.1 * partialYX f a b + v.2 * partialYY f a b) b :=
    (HasDerivAt.const_mul v.1
      (hasDerivAt_partialY (hX (a, b)).hasFDerivAt).differentiableAt.hasDerivAt).add
      (HasDerivAt.const_mul v.2
        (hasDerivAt_partialY (hY (a, b)).hasFDerivAt).differentiableAt.hasDerivAt)
  have h2 : (dirDeriv v.1 v.2)^[2] f a b = v.1 * (v.1 * partialXX f a b +
      v.2 * partialXY f a b) + v.2 * (v.1 * partialYX f a b + v.2 * partialYY f a b) := by
    show v.1 * partialX (dirDeriv v.1 v.2 f) a b + v.2 * partialY (dirDeriv v.1 v.2 f) a b = _
    rw [show partialX (dirDeriv v.1 v.2 f) a b = _ from hdx.deriv,
      show partialY (dirDeriv v.1 v.2 f) a b = _ from hdy.deriv]
  rw [h2, ← hsym] at hR
  have h1 : (dirDeriv v.1 v.2)^[1] f a b = v.1 * partialX f a b + v.2 * partialY f a b := rfl
  rw [h1] at hR
  simp only [Function.iterate_zero, id, Nat.factorial_zero, Nat.factorial_one,
    Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, inv_one, one_mul] at hR
  convert hR using 2
  ring

/-- A positive definite binary quadratic form is bounded below by a multiple of `λ² + μ²`. -/
theorem quadratic_lower_bound {A B C : ℝ} (hA : 0 < A) (hD : 0 < A * C - B ^ 2) (ℓ μ : ℝ) :
    (A * C - B ^ 2) / (A + C) / 2 * (ℓ ^ 2 + μ ^ 2) ≤ A * ℓ ^ 2 + 2 * B * ℓ * μ + C * μ ^ 2 := by
  have hC : 0 < C := by nlinarith [sq_nonneg B]
  rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (A * ℓ + B * μ), sq_nonneg (C * μ + B * ℓ),
    mul_nonneg hD.le (add_nonneg (sq_nonneg ℓ) (sq_nonneg μ))]

/-- **DLMF 1.5.20–1.5.21**: the second-order term `λ² f_xx + 2λμ f_xy + μ² f_yy` of 1.5.18 is
positive definite iff `f_xx > 0` and `f_xx f_yy − f_xy² > 0`. -/
theorem dlmf_1_5_20_21 (A B C : ℝ) :
    (∀ ℓ μ : ℝ, (ℓ, μ) ≠ 0 → 0 < A * ℓ ^ 2 + 2 * B * ℓ * μ + C * μ ^ 2) ↔
      0 < A ∧ 0 < A * C - B ^ 2 := by
  constructor
  · intro h
    have hA : 0 < A := by simpa using h 1 0 (by simp)
    refine ⟨hA, ?_⟩
    have := h (-B) A (by simp [hA.ne'])
    have e : A * (-B) ^ 2 + 2 * B * (-B) * A + C * A ^ 2 = A * (A * C - B ^ 2) := by ring
    rw [e] at this
    exact pos_of_mul_pos_right this hA.le
  · rintro ⟨hA, hD⟩ ℓ μ hne
    have hpos : 0 < ℓ ^ 2 + μ ^ 2 := by
      have : ℓ ≠ 0 ∨ μ ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hne (by rw [hc.1, hc.2]; rfl)
      rcases this with h' | h' <;> positivity
    have hC : 0 < C := by nlinarith [sq_nonneg B]
    exact lt_of_lt_of_le (by positivity) (quadratic_lower_bound hA hD ℓ μ)

/-- Core of the second-derivative test: at a critical point, if the second-order form is bounded
below by `c (λ² + μ²)` with `c > 0`, then `f` has a local minimum. -/
theorem isLocalMin_of_quadratic {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (uncurry f)) {a b c : ℝ}
    (hx : partialX f a b = 0) (hy : partialY f a b = 0) (hc : 0 < c)
    (hQ : ∀ ℓ μ : ℝ, c * (ℓ ^ 2 + μ ^ 2) ≤
      ℓ ^ 2 * partialXX f a b + 2 * ℓ * μ * partialXY f a b + μ ^ 2 * partialYY f a b) :
    IsLocalMin (uncurry f) (a, b) := by
  obtain ⟨δ, hδ, h⟩ := taylor_two hf a b (show 0 < c / 4 by positivity)
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun {q} hq => ?_⟩
  set v : ℝ × ℝ := q - (a, b)
  have hv : ‖v‖ < δ := by rwa [← dist_eq_norm]
  have hq' : uncurry f q = f (a + v.1) (b + v.2) := by
    simp only [v, Prod.fst_sub, Prod.snd_sub, add_sub_cancel]
    rfl
  have hR := h v hv
  rw [hx, hy] at hR
  have hQv := hQ v.1 v.2
  have hn : ‖v‖ ^ 2 ≤ v.1 ^ 2 + v.2 ^ 2 := by
    calc ‖v‖ ^ 2 ≤ √(v.1 ^ 2 + v.2 ^ 2) ^ 2 := by
          gcongr
          exact norm_le_sqrt_sq_add_sq v
      _ = v.1 ^ 2 + v.2 ^ 2 := Real.sq_sqrt (by positivity)
  show f a b ≤ uncurry f q
  rw [hq']
  have := (abs_le.mp hR).1
  nlinarith

/-- **DLMF 1.5.19–1.5.21** (local minimum): if `f_x = f_y = 0` at `(a, b)`, `f_xx > 0` and
`f_xx f_yy − f_xy² > 0` there, then `f` has a local minimum at `(a, b)`. -/
theorem dlmf_1_5_19_min {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (uncurry f)) {a b : ℝ}
    (hx : partialX f a b = 0) (hy : partialY f a b = 0) (hxx : 0 < partialXX f a b)
    (hdet : 0 < partialXX f a b * partialYY f a b - partialXY f a b ^ 2) :
    IsLocalMin (uncurry f) (a, b) := by
  have hC : 0 < partialYY f a b := by nlinarith [sq_nonneg (partialXY f a b)]
  refine isLocalMin_of_quadratic hf hx hy (show 0 < (partialXX f a b * partialYY f a b -
    partialXY f a b ^ 2) / (partialXX f a b + partialYY f a b) / 2 by positivity) fun ℓ μ => ?_
  have := quadratic_lower_bound hxx hdet ℓ μ
  linarith

/-- **DLMF 1.5.19–1.5.21** (local maximum): if `f_x = f_y = 0` at `(a, b)`, `f_xx < 0` and
`f_xx f_yy − f_xy² > 0` there, then `f` has a local maximum at `(a, b)`. -/
theorem dlmf_1_5_19_max {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (uncurry f)) {a b : ℝ}
    (hx : partialX f a b = 0) (hy : partialY f a b = 0) (hxx : partialXX f a b < 0)
    (hdet : 0 < partialXX f a b * partialYY f a b - partialXY f a b ^ 2) :
    IsLocalMax (uncurry f) (a, b) := by
  have hA : 0 < -partialXX f a b := neg_pos.mpr hxx
  have hD : 0 < -partialXX f a b * -partialYY f a b - (-partialXY f a b) ^ 2 := by
    nlinarith
  have hC : 0 < -partialYY f a b := by nlinarith [sq_nonneg (partialXY f a b)]
  obtain ⟨δ, hδ, h⟩ := taylor_two hf a b
    (show 0 < (-partialXX f a b * -partialYY f a b - (-partialXY f a b) ^ 2) /
      (-partialXX f a b + -partialYY f a b) / 2 / 4 by positivity)
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun {q} hq => ?_⟩
  set v : ℝ × ℝ := q - (a, b)
  have hv : ‖v‖ < δ := by rwa [← dist_eq_norm]
  have hq' : uncurry f q = f (a + v.1) (b + v.2) := by
    simp only [v, Prod.fst_sub, Prod.snd_sub, add_sub_cancel]
    rfl
  have hR := h v hv
  rw [hx, hy] at hR
  have hQv := quadratic_lower_bound hA hD v.1 v.2
  have hn : ‖v‖ ^ 2 ≤ v.1 ^ 2 + v.2 ^ 2 := by
    calc ‖v‖ ^ 2 ≤ √(v.1 ^ 2 + v.2 ^ 2) ^ 2 := by
          gcongr
          exact norm_le_sqrt_sq_add_sq v
      _ = v.1 ^ 2 + v.2 ^ 2 := Real.sq_sqrt (by positivity)
  show uncurry f q ≤ f a b
  rw [hq']
  have := (abs_le.mp hR).2
  have hc : 0 < (-partialXX f a b * -partialYY f a b - (-partialXY f a b) ^ 2) /
      (-partialXX f a b + -partialYY f a b) / 2 := by positivity
  nlinarith

end TaylorTwo

/-! ## §1.5(iv) Leibniz's theorem for differentiation of integrals -/

section Leibniz

open MeasureTheory

/-- Differentiation under the integral sign with fixed limits, for `f`, `f_x` continuous on the
plane and `f_x` the `x`-derivative of `f` on an open set `U`. -/
theorem hasDerivAt_integral_param {f f' : ℝ → ℝ → ℝ} (hf : Continuous (uncurry f))
    (hf' : Continuous (uncurry f')) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ x ∈ U, ∀ y, HasDerivAt (fun t => f t y) (f' x y) x) {x₀ : ℝ} (hx₀ : x₀ ∈ U)
    (u w : ℝ) : HasDerivAt (fun x => ∫ y in u..w, f x y) (∫ y in u..w, f' x₀ y) x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hK : IsCompact (Metric.closedBall x₀ (ε / 2) ×ˢ uIcc u w) :=
    (isCompact_closedBall _ _).prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf'.continuousOn
  have hfx : ∀ x, Continuous (f x) := fun x => by
    exact hf.comp (continuous_const.prodMk continuous_id)
  have hf'x : ∀ x, Continuous (f' x) := fun x => by
    exact hf'.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M)
    (Metric.ball_mem_nhds x₀ (half_pos hε))
    (Eventually.of_forall fun x => (hfx x).aestronglyMeasurable)
    ((hfx x₀).intervalIntegrable u w) (hf'x x₀).aestronglyMeasurable
    (ae_of_all _ fun t ht x hx => hM (x, t) ⟨Metric.ball_subset_closedBall hx,
      uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (ae_of_all _ fun t _ x hx => hd x (hball (Metric.ball_subset_ball (by linarith) hx)) t)).2

/-- Leibniz's rule with variable limits, for `f`, `f_x` continuous on the plane:
`d/dx ∫_{α(x)}^{β(x)} f(x, y) dy = f(x, β)β' − f(x, α)α' + ∫_α^β f_x dy`.  The map
`(x, u, w) ↦ ∫_u^w f(x, y) dy` is strictly differentiable, its partial derivatives
(`∫_u^w f_x`, `−f(x, u)`, `f(x, w)`) being continuous. -/
theorem hasDerivAt_integral_variable {α β : ℝ → ℝ} {α' β' : ℝ} {f f' : ℝ → ℝ → ℝ}
    (hf : Continuous (uncurry f)) (hf' : Continuous (uncurry f')) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ x ∈ U, ∀ y, HasDerivAt (fun t => f t y) (f' x y) x) {x₀ : ℝ} (hx₀ : x₀ ∈ U)
    (hα : HasDerivAt α α' x₀) (hβ : HasDerivAt β β' x₀) :
    HasDerivAt (fun x => ∫ y in α x..β x, f x y)
      (f x₀ (β x₀) * β' - f x₀ (α x₀) * α' + ∫ y in α x₀..β x₀, f' x₀ y) x₀ := by
  have hfx : ∀ x, Continuous (f x) := fun x => by
    exact hf.comp (continuous_const.prodMk continuous_id)
  -- continuity of `(x, u, w) ↦ ∫_u^w f_x(x, y) dy`
  have hI : Continuous fun v : ℝ × ℝ × ℝ => ∫ y in v.2.1..v.2.2, f' v.1 y := by
    have hf'' : Continuous (uncurry fun (v : ℝ × ℝ × ℝ) (y : ℝ) => f' v.1 y) :=
      hf'.comp (continuous_fst.fst.prodMk continuous_snd)
    have e : (fun v : ℝ × ℝ × ℝ => ∫ y in v.2.1..v.2.2, f' v.1 y) = fun v =>
        (∫ y in (0 : ℝ)..v.2.2, f' v.1 y) - ∫ y in (0 : ℝ)..v.2.1, f' v.1 y := by
      funext v
      have hc : Continuous (f' v.1) := by
        exact hf'.comp (continuous_const.prodMk continuous_id)
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
    rw [e]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf''
      continuous_snd.snd).sub
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf''
        continuous_snd.fst)
  have hU' : {v : ℝ × ℝ × ℝ | v.1 ∈ U} ∈ 𝓝 (x₀, (α x₀, β x₀)) :=
    continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hx₀)
  have hstrict := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (x₀, (α x₀, β x₀)))
    (f := fun x (q : ℝ × ℝ) => ∫ y in q.1..q.2, f x y)
    (f₁ := fun x q => (∫ y in q.1..q.2, f' x y) • (1 : ℝ →L[ℝ] ℝ))
    (f₂ := fun x q => f x q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ -
      f x q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
    (by
      filter_upwards [hU'] with v hv
      have := (hasDerivAt_integral_param hf hf' hU hd hv v.2.1 v.2.2).hasFDerivAt
      rw [toSpanSingleton_eq_smul_one] at this
      exact this)
    (Eventually.of_forall fun v => by
      have := (intervalIntegral.integral_hasStrictFDerivAt (f := f v.1) (a := v.2.1)
        (b := v.2.2) ((hfx v.1).intervalIntegrable _ _)
        ((hfx v.1).stronglyMeasurableAtFilter _ _) ((hfx v.1).stronglyMeasurableAtFilter _ _)
        (hfx v.1).continuousAt (hfx v.1).continuousAt).hasFDerivAt
      show HasFDerivAt _ (f v.1 v.2.2 • ContinuousLinearMap.snd ℝ ℝ ℝ -
        f v.1 v.2.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) v.2
      convert this using 1
      ext <;> simp [mul_comm])
    (hI.smul continuous_const).continuousAt
    (((hf.comp (continuous_fst.prodMk continuous_snd.snd)).smul continuous_const).sub
      ((hf.comp (continuous_fst.prodMk continuous_snd.fst)).smul continuous_const)).continuousAt
  have hstrict' : HasStrictFDerivAt (fun p : ℝ × ℝ × ℝ => ∫ y in p.2.1..p.2.2, f p.1 y)
      (((∫ y in α x₀..β x₀, f' x₀ y) • (1 : ℝ →L[ℝ] ℝ)).coprod
        (f x₀ (β x₀) • ContinuousLinearMap.snd ℝ ℝ ℝ -
          f x₀ (α x₀) • ContinuousLinearMap.fst ℝ ℝ ℝ)) (x₀, (α x₀, β x₀)) := hstrict
  refine (hstrict'.hasFDerivAt.comp_hasDerivAt x₀
    ((hasDerivAt_id x₀).prodMk (hα.prodMk hβ))).congr_deriv ?_
  simp
  ring

/-- **DLMF 1.5.22** (Leibniz's theorem, finite integrals): if `f` is continuous on the rectangle
`[a, b] × [c, d]`, `∂f/∂x` exists and is continuous for `a < x < b`, `c ≤ y ≤ d`, and `α(x)`,
`β(x)` lie in `[c, d]` for `x ∈ [a, b]` and are differentiable at `x₀ ∈ (a, b)`, then
`d/dx ∫_{α(x)}^{β(x)} f(x, y) dy = f(x, β(x))β'(x) − f(x, α(x))α'(x) + ∫_{α(x)}^{β(x)} ∂f/∂x dy`
at `x₀`.  (The proof clamps `f` to the rectangle and applies `hasDerivAt_integral_variable`.) -/
theorem dlmf_1_5_22 {f : ℝ → ℝ → ℝ} {α β : ℝ → ℝ} {a b c d x₀ : ℝ}
    (hfc : ContinuousOn (uncurry f) (Icc a b ×ˢ Icc c d))
    (hfd : ∀ x ∈ Ioo a b, ∀ y ∈ Icc c d, DifferentiableAt ℝ (fun t => f t y) x)
    (hfx : ContinuousOn (uncurry (partialX f)) (Ioo a b ×ˢ Icc c d))
    (hαc : ∀ x ∈ Icc a b, α x ∈ Icc c d) (hβc : ∀ x ∈ Icc a b, β x ∈ Icc c d)
    (hα : DifferentiableAt ℝ α x₀) (hβ : DifferentiableAt ℝ β x₀) (hx₀ : x₀ ∈ Ioo a b) :
    HasDerivAt (fun x => ∫ y in α x..β x, f x y)
      (f x₀ (β x₀) * deriv β x₀ - f x₀ (α x₀) * deriv α x₀ +
        ∫ y in α x₀..β x₀, partialX f x₀ y) x₀ := by
  obtain ⟨hax, hxb⟩ := hx₀
  set a' := (a + x₀) / 2
  set b' := (x₀ + b) / 2
  have ha' : a < a' := by simp only [a']; linarith
  have ha'x : a' < x₀ := by simp only [a']; linarith
  have hxb' : x₀ < b' := by simp only [b']; linarith
  have hb' : b' < b := by simp only [b']; linarith
  have hcd : c ≤ d := (hαc x₀ ⟨hax.le, hxb.le⟩).1.trans (hαc x₀ ⟨hax.le, hxb.le⟩).2
  -- clamping into `[a', b'] × [c, d]`
  set cx : ℝ → ℝ := fun t => max a' (min b' t)
  set cy : ℝ → ℝ := fun y => max c (min d y)
  have hcx : ∀ t, cx t ∈ Icc a' b' := fun t =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcy : ∀ y, cy y ∈ Icc c d := fun y => ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩
  have hcx_eq : ∀ t ∈ Icc a' b', cx t = t := fun t ht => by
    simp only [cx, min_eq_right ht.2, max_eq_right ht.1]
  have hcy_eq : ∀ y ∈ Icc c d, cy y = y := fun y hy => by
    simp only [cy, min_eq_right hy.2, max_eq_right hy.1]
  have hccont : Continuous fun p : ℝ × ℝ => (cx p.1, cy p.2) :=
    (continuous_const.max (continuous_const.min continuous_fst)).prodMk
      (continuous_const.max (continuous_const.min continuous_snd))
  set g : ℝ → ℝ → ℝ := fun x y => f (cx x) (cy y)
  set g' : ℝ → ℝ → ℝ := fun x y => partialX f (cx x) (cy y)
  have hg : Continuous (uncurry g) := hfc.comp_continuous hccont fun p =>
    ⟨⟨by linarith [(hcx p.1).1], by linarith [(hcx p.1).2]⟩, hcy p.2⟩
  have hg' : Continuous (uncurry g') := hfx.comp_continuous hccont fun p =>
    ⟨⟨by linarith [(hcx p.1).1], by linarith [(hcx p.1).2]⟩, hcy p.2⟩
  have hd : ∀ x ∈ Ioo a' b', ∀ y, HasDerivAt (fun t => g t y) (g' x y) x := by
    intro x hx y
    have h1 := (hfd x ⟨by linarith [hx.1], by linarith [hx.2]⟩ (cy y) (hcy y)).hasDerivAt
    have e : g' x y = partialX f x (cy y) := by
      simp only [g', hcx_eq x ⟨hx.1.le, hx.2.le⟩]
    rw [e]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    simp only [g, hcx_eq t ⟨ht.1.le, ht.2.le⟩]
  have hG := hasDerivAt_integral_variable hg hg' isOpen_Ioo hd ⟨ha'x, hxb'⟩ hα.hasDerivAt
    hβ.hasDerivAt
  -- `g = f` where it matters
  have hIcc : ∀ x ∈ Icc a b, uIcc (α x) (β x) ⊆ Icc c d := fun x hx =>
    uIcc_subset_Icc (hαc x hx) (hβc x hx)
  have heq : (fun x => ∫ y in α x..β x, f x y) =ᶠ[𝓝 x₀]
      fun x => ∫ y in α x..β x, g x y := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x₀ ∈ Ioo a' b' from ⟨ha'x, hxb'⟩)] with x hx
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy' := hIcc x ⟨by linarith [hx.1], by linarith [hx.2]⟩ hy
    simp only [g, hcx_eq x ⟨hx.1.le, hx.2.le⟩, hcy_eq y hy']
  have hx₀' : x₀ ∈ Icc a' b' := ⟨ha'x.le, hxb'.le⟩
  have hx₀ab : x₀ ∈ Icc a b := ⟨hax.le, hxb.le⟩
  have hval : g x₀ (β x₀) * deriv β x₀ - g x₀ (α x₀) * deriv α x₀ +
      ∫ y in α x₀..β x₀, g' x₀ y = f x₀ (β x₀) * deriv β x₀ - f x₀ (α x₀) * deriv α x₀ +
        ∫ y in α x₀..β x₀, partialX f x₀ y := by
    have e1 : g x₀ (β x₀) = f x₀ (β x₀) := by
      simp only [g, hcx_eq x₀ hx₀', hcy_eq _ (hβc x₀ hx₀ab)]
    have e2 : g x₀ (α x₀) = f x₀ (α x₀) := by
      simp only [g, hcx_eq x₀ hx₀', hcy_eq _ (hαc x₀ hx₀ab)]
    have e3 : ∫ y in α x₀..β x₀, g' x₀ y = ∫ y in α x₀..β x₀, partialX f x₀ y :=
      intervalIntegral.integral_congr fun y hy => by
        simp only [g', hcx_eq x₀ hx₀', hcy_eq y (hIcc x₀ hx₀ab hy)]
    rw [e1, e2, e3]
  exact (hG.congr_of_eventuallyEq heq).congr_deriv hval

/-- DLMF 1.5.22 with constant limits `c` and `N`, used for 1.5.24. -/
theorem hasDerivAt_integral_Icc {f : ℝ → ℝ → ℝ} {a b c N x₀ : ℝ} (hcN : c ≤ N)
    (hfc : ContinuousOn (uncurry f) (Icc a b ×ˢ Icc c N))
    (hfd : ∀ x ∈ Ioo a b, ∀ y ∈ Icc c N, DifferentiableAt ℝ (fun t => f t y) x)
    (hfx : ContinuousOn (uncurry (partialX f)) (Ioo a b ×ˢ Icc c N)) (hx₀ : x₀ ∈ Ioo a b) :
    HasDerivAt (fun x => ∫ y in c..N, f x y) (∫ y in c..N, partialX f x₀ y) x₀ :=
  (dlmf_1_5_22 (α := fun _ => c) (β := fun _ => N) hfc hfd hfx
    (fun _ _ => ⟨le_rfl, hcN⟩) (fun _ _ => ⟨hcN, le_rfl⟩) (differentiableAt_const _)
    (differentiableAt_const _) hx₀).congr_deriv (by simp)

/-- **DLMF 1.5.23–1.5.24** (Leibniz's theorem, infinite integrals, `d` finite): suppose `f` and
`∂f/∂x` are continuous on `[a, b] × [c, d)`, `∫_c^d f(x, y) dy` converges (to `F(x)`), and
`∫_c^d ∂f/∂x dy` (with value `G(x)`) converges uniformly on `[a, b]` (1.5.23: for every `ε > 0`
there is `c₀ ∈ [c, d)` with `|∫_{c₁}^d ∂f/∂x dy| = |G(x) − ∫_c^{c₁} ∂f/∂x dy| < ε` for all
`c₁ ∈ [c₀, d)`, `x ∈ [a, b]`).  Then `∫_c^d ∂f/∂x dy` converges to `G(x)` and
`d/dx ∫_c^d f(x, y) dy = ∫_c^d ∂f/∂x dy` for `a < x < b`. -/
theorem dlmf_1_5_24 {f : ℝ → ℝ → ℝ} {F G : ℝ → ℝ} {a b c d x₀ : ℝ} (hcd : c < d)
    (hfc : ContinuousOn (uncurry f) (Icc a b ×ˢ Ico c d))
    (hfd : ∀ x ∈ Ioo a b, ∀ y ∈ Ico c d, DifferentiableAt ℝ (fun t => f t y) x)
    (hfx : ContinuousOn (uncurry (partialX f)) (Ioo a b ×ˢ Ico c d))
    (hF : ∀ x ∈ Icc a b, ConvergesLeft (f x) c d (F x))
    (h_1_5_23 : ∀ ε > 0, ∃ c₀ ∈ Ico c d, ∀ c₁ ∈ Ico c₀ d, ∀ x ∈ Icc a b,
      |G x - ∫ y in c..c₁, partialX f x y| < ε)
    (hx₀ : x₀ ∈ Ioo a b) :
    ConvergesLeft (partialX f x₀) c d (G x₀) ∧ HasDerivAt F (G x₀) x₀ := by
  have hunif : TendstoUniformlyOn (fun N x => ∫ y in c..N, partialX f x y) G (𝓝[<] d)
      (Ioo a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨c₀, hc₀, h⟩ := h_1_5_23 ε hε
    filter_upwards [Ico_mem_nhdsLT hc₀.2] with N hN x hx
    rw [Real.dist_eq]
    exact h N hN x ⟨hx.1.le, hx.2.le⟩
  refine ⟨hunif.tendsto_at hx₀, hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hunif ?_
    (fun x hx => hF x ⟨hx.1.le, hx.2.le⟩) hx₀⟩
  filter_upwards [Ico_mem_nhdsLT hcd] with N hN x hx
  have hsub : Icc c N ⊆ Ico c d := Icc_subset_Ico_right hN.2
  exact hasDerivAt_integral_Icc hN.1 (hfc.mono (prod_mono subset_rfl hsub))
    (fun x hx y hy => hfd x hx y (hsub hy)) (hfx.mono (prod_mono subset_rfl hsub)) hx

/-- **DLMF 1.5.23–1.5.24** with `d = +∞` (the infinite strip `[a, b] × [c, ∞)`). -/
theorem dlmf_1_5_24_atTop {f : ℝ → ℝ → ℝ} {F G : ℝ → ℝ} {a b c x₀ : ℝ}
    (hfc : ContinuousOn (uncurry f) (Icc a b ×ˢ Ici c))
    (hfd : ∀ x ∈ Ioo a b, ∀ y ∈ Ici c, DifferentiableAt ℝ (fun t => f t y) x)
    (hfx : ContinuousOn (uncurry (partialX f)) (Ioo a b ×ˢ Ici c))
    (hF : ∀ x ∈ Icc a b, ConvergesAtTop (f x) c (F x))
    (h_1_5_23 : ∀ ε > 0, ∃ c₀ ≥ c, ∀ c₁ ≥ c₀, ∀ x ∈ Icc a b,
      |G x - ∫ y in c..c₁, partialX f x y| < ε)
    (hx₀ : x₀ ∈ Ioo a b) :
    ConvergesAtTop (partialX f x₀) c (G x₀) ∧ HasDerivAt F (G x₀) x₀ := by
  have hunif : TendstoUniformlyOn (fun N x => ∫ y in c..N, partialX f x y) G atTop
      (Ioo a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨c₀, -, h⟩ := h_1_5_23 ε hε
    filter_upwards [eventually_ge_atTop c₀] with N hN x hx
    rw [Real.dist_eq]
    exact h N hN x ⟨hx.1.le, hx.2.le⟩
  refine ⟨hunif.tendsto_at hx₀, hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hunif ?_
    (fun x hx => hF x ⟨hx.1.le, hx.2.le⟩) hx₀⟩
  filter_upwards [eventually_ge_atTop c] with N hN x hx
  have hsub : Icc c N ⊆ Ici c := Icc_subset_Ici_self
  exact hasDerivAt_integral_Icc hN (hfc.mono (prod_mono subset_rfl hsub))
    (fun x hx y hy => hfd x hx y (hsub hy)) (hfx.mono (prod_mono subset_rfl hsub)) hx

end Leibniz

/-! ## §1.5(v) Multiple integrals -/

section MultipleIntegrals

open MeasureTheory

/-! ### Regions between graphs (Lebesgue double integrals) -/

/-- The region `a ≤ x ≤ b`, `φ₁(x) ≤ y ≤ φ₂(x)` of DLMF 1.5.30. -/
def regionX (a b : ℝ) (φ₁ φ₂ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ b ∧ φ₁ p.1 ≤ p.2 ∧ p.2 ≤ φ₂ p.1}

/-- The region `c ≤ y ≤ d`, `ψ₁(y) ≤ x ≤ ψ₂(y)` of DLMF 1.5.33. -/
def regionY (c d : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | c ≤ p.2 ∧ p.2 ≤ d ∧ ψ₁ p.2 ≤ p.1 ∧ p.1 ≤ ψ₂ p.2}

theorem isCompact_regionX {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) :
    IsCompact (regionX a b φ₁ φ₂) := by
  have hclosed : IsClosed (regionX a b φ₁ φ₂) := by
    simp only [regionX, ofPred_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le (hφ₁.comp continuous_fst) continuous_snd).inter
          (isClosed_le continuous_snd (hφ₂.comp continuous_fst))))
  rcases (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hφ₁.abs.add hφ₂.abs).continuousOn with ⟨M, hM⟩
  refine ((isCompact_Icc (a := a) (b := b)).prod
    (isCompact_Icc (a := -M) (b := M))).of_isClosed_subset hclosed ?_
  rintro ⟨x, y⟩ ⟨h1, h2, h3, h4⟩
  dsimp only at h1 h2 h3 h4
  have := hM x ⟨h1, h2⟩
  simp only [Pi.add_apply, Real.norm_eq_abs] at this
  rw [abs_of_nonneg (by positivity)] at this
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩
  · linarith [neg_abs_le (φ₁ x), abs_nonneg (φ₂ x)]
  · linarith [le_abs_self (φ₂ x), abs_nonneg (φ₁ x)]

theorem isCompact_regionY {c d : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂) :
    IsCompact (regionY c d ψ₁ ψ₂) := by
  have h := (isCompact_regionX (a := c) (b := d) hψ₁ hψ₂).image continuous_swap
  convert h using 1
  ext ⟨x, y⟩
  simp [regionX, regionY]

/-- **DLMF 1.5.30–1.5.32**: for `f` continuous on `D = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` with
`φ₁ ≤ φ₂` continuous, `∬_D f dA = ∫_a^b (∫_{φ₁(x)}^{φ₂(x)} f(x, y) dy) dx` (the double integral
being the Lebesgue integral over `D ⊆ ℝ²`). -/
theorem dlmf_1_5_31 {f : ℝ → ℝ → ℝ} {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} (hab : a ≤ b)
    (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hle : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x)
    (hf : ContinuousOn (uncurry f) (regionX a b φ₁ φ₂)) :
    ∫ p in regionX a b φ₁ φ₂, f p.1 p.2 = ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, f x y := by
  have hK := isCompact_regionX (a := a) (b := b) hφ₁ hφ₂
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (regionX a b φ₁ φ₂) :=
    hf.integrableOn_compact hK
  rw [← integral_indicator hK.isClosed.measurableSet, Measure.volume_eq_prod,
    integral_prod _ ((integrable_indicator_iff hK.isClosed.measurableSet).mpr hint),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc a b
  · rw [indicator_of_mem hx, intervalIntegral.integral_of_le (hle x hx),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    congr 1
    funext y
    simp only [indicator, regionX, mem_ofPred_eq, mem_Icc, hx.1, hx.2, true_and]
  · rw [indicator_of_notMem hx]
    have : (fun y => (regionX a b φ₁ φ₂).indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) =
        fun _ => 0 := by
      funext y
      refine indicator_of_notMem (fun h => hx ⟨h.1, h.2.1⟩) _
    rw [this, integral_zero]

/-- **DLMF 1.5.33–1.5.34**: for `f` continuous on `D = {c ≤ y ≤ d, ψ₁(y) ≤ x ≤ ψ₂(y)}`,
`∬_D f dA = ∫_c^d (∫_{ψ₁(y)}^{ψ₂(y)} f(x, y) dx) dy`. -/
theorem dlmf_1_5_34 {f : ℝ → ℝ → ℝ} {c d : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} (hcd : c ≤ d)
    (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂) (hle : ∀ y ∈ Icc c d, ψ₁ y ≤ ψ₂ y)
    (hf : ContinuousOn (uncurry f) (regionY c d ψ₁ ψ₂)) :
    ∫ p in regionY c d ψ₁ ψ₂, f p.1 p.2 = ∫ y in c..d, ∫ x in ψ₁ y..ψ₂ y, f x y := by
  have hK := isCompact_regionY (c := c) (d := d) hψ₁ hψ₂
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (regionY c d ψ₁ ψ₂) :=
    hf.integrableOn_compact hK
  rw [← integral_indicator hK.isClosed.measurableSet, Measure.volume_eq_prod,
    integral_prod_symm _ ((integrable_indicator_iff hK.isClosed.measurableSet).mpr hint),
    intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1
  funext y
  by_cases hy : y ∈ Icc c d
  · rw [indicator_of_mem hy, intervalIntegral.integral_of_le (hle y hy),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    congr 1
    funext x
    simp only [indicator, regionY, mem_ofPred_eq, mem_Icc, hy.1, hy.2, true_and]
  · rw [indicator_of_notMem hy]
    have : (fun x => (regionY c d ψ₁ ψ₂).indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) =
        fun _ => 0 := by
      funext x
      refine indicator_of_notMem (fun h => hy ⟨h.1, h.2.1⟩) _
    rw [this, integral_zero]

/-- **DLMF 1.5.35** (change of order of integration): if `D` has both forms 1.5.30 and 1.5.33
and `f` is continuous on `D`, the two repeated integrals agree. -/
theorem dlmf_1_5_35 {f : ℝ → ℝ → ℝ} {a b c d : ℝ} {φ₁ φ₂ ψ₁ ψ₂ : ℝ → ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hψ₁ : Continuous ψ₁)
    (hψ₂ : Continuous ψ₂) (hφ : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x) (hψ : ∀ y ∈ Icc c d, ψ₁ y ≤ ψ₂ y)
    (hD : regionX a b φ₁ φ₂ = regionY c d ψ₁ ψ₂)
    (hf : ContinuousOn (uncurry f) (regionX a b φ₁ φ₂)) :
    ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, f x y = ∫ y in c..d, ∫ x in ψ₁ y..ψ₂ y, f x y := by
  rw [← dlmf_1_5_31 hab hφ₁ hφ₂ hφ hf, ← dlmf_1_5_34 hcd hψ₁ hψ₂ hψ (hD ▸ hf), hD]

/-- **DLMF 1.5.36** (infinite double integrals): for `s`, `t` arbitrary intervals (finite or
infinite) and `f` measurable on `s × t` (for instance piecewise continuous), the two repeated
integrals `∫_s ∫_t f dy dx` and `∫_t ∫_s f dx dy` agree as soon as one of them is absolutely
convergent. -/
theorem dlmf_1_5_36 {f : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hf : AEStronglyMeasurable (uncurry f) ((volume.restrict s).prod (volume.restrict t)))
    (habs : ((∀ᵐ x ∂volume.restrict s, IntegrableOn (f x) t) ∧
        IntegrableOn (fun x => ∫ y in t, |f x y|) s) ∨
      ((∀ᵐ y ∂volume.restrict t, IntegrableOn (fun x => f x y) s) ∧
        IntegrableOn (fun y => ∫ x in s, |f x y|) t)) :
    ∫ x in s, ∫ y in t, f x y = ∫ y in t, ∫ x in s, f x y := by
  refine integral_integral_swap ?_
  rcases habs with h | h
  · refine (integrable_prod_iff hf).mpr ⟨h.1, ?_⟩
    simp only [Real.norm_eq_abs, uncurry_apply_pair]
    exact h.2
  · refine (integrable_prod_iff' hf).mpr ⟨h.1, ?_⟩
    simp only [Real.norm_eq_abs, uncurry_apply_pair]
    exact h.2

/-- **DLMF 1.5.28**: `f*`, the extension of `f` from `D` to the rectangle `R` by zero. -/
noncomputable def extendByZero (D : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => D.indicator (uncurry f) (x, y)

/-- **DLMF 1.5.29**: `∬_D f dA = ∬_R f* dA` for `D ⊆ R` (Lebesgue double integrals). -/
theorem dlmf_1_5_29 {D R : Set (ℝ × ℝ)} (hD : MeasurableSet D) (hDR : D ⊆ R)
    (f : ℝ → ℝ → ℝ) :
    ∫ p in R, extendByZero D f p.1 p.2 = ∫ p in D, f p.1 p.2 := by
  simp only [extendByZero, Prod.mk.eta]
  rw [setIntegral_indicator hD, inter_eq_right.mpr hDR]
  rfl

/-! ### Triple integrals -/

/-- The region `a ≤ x ≤ b`, `φ₁(x) ≤ y ≤ φ₂(x)`, `ψ₁(x, y) ≤ z ≤ ψ₂(x, y)` of DLMF 1.5.37. -/
def regionXYZ (a b : ℝ) (φ₁ φ₂ : ℝ → ℝ) (ψ₁ ψ₂ : ℝ → ℝ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ b ∧ φ₁ p.1 ≤ p.2.1 ∧ p.2.1 ≤ φ₂ p.1 ∧
    ψ₁ p.1 p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ ψ₂ p.1 p.2.1}

/-- **DLMF 1.5.37** (triple integrals): for `f` continuous on
`D = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x), ψ₁(x, y) ≤ z ≤ ψ₂(x, y)}` (continuous bounding functions,
`φ₁ ≤ φ₂`, `ψ₁ ≤ ψ₂`), `∭_D f dV = ∫_a^b ∫_{φ₁}^{φ₂} ∫_{ψ₁}^{ψ₂} f dz dy dx`. -/
theorem dlmf_1_5_37 {f : ℝ → ℝ → ℝ → ℝ} {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} {ψ₁ ψ₂ : ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hψ₁ : Continuous (uncurry ψ₁))
    (hψ₂ : Continuous (uncurry ψ₂)) (hφ : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x)
    (hψ : ∀ x ∈ Icc a b, ∀ y ∈ Icc (φ₁ x) (φ₂ x), ψ₁ x y ≤ ψ₂ x y)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (regionXYZ a b φ₁ φ₂ ψ₁ ψ₂)) :
    ∫ p in regionXYZ a b φ₁ φ₂ ψ₁ ψ₂, f p.1 p.2.1 p.2.2 =
      ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, ∫ z in ψ₁ x y..ψ₂ x y, f x y z := by
  set D := regionXYZ a b φ₁ φ₂ ψ₁ ψ₂
  -- `D` is compact
  have hclosed : IsClosed D := by
    simp only [D, regionXYZ, ofPred_and]
    refine (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le (hφ₁.comp continuous_fst) continuous_snd.fst).inter
          ((isClosed_le continuous_snd.fst (hφ₂.comp continuous_fst)).inter
            ((isClosed_le (hψ₁.comp (continuous_fst.prodMk continuous_snd.fst))
              continuous_snd.snd).inter
              (isClosed_le continuous_snd.snd
                (hψ₂.comp (continuous_fst.prodMk continuous_snd.fst)))))))
  have hK2 : IsCompact (regionX a b φ₁ φ₂) := isCompact_regionX hφ₁ hφ₂
  obtain ⟨M₁, hM₁⟩ := hK2.exists_bound_of_continuousOn continuous_snd.continuousOn
  obtain ⟨M₂, hM₂⟩ := hK2.exists_bound_of_continuousOn
    ((hψ₁.abs.add hψ₂.abs).continuousOn)
  have hK : IsCompact D := by
    refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hclosed
      (s := Icc a b ×ˢ (Icc (-M₁) M₁ ×ˢ Icc (-M₂) M₂)) ?_
    rintro ⟨x, y, z⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    have hy := hM₁ (x, y) ⟨h1, h2, h3, h4⟩
    have hz := hM₂ (x, y) ⟨h1, h2, h3, h4⟩
    simp only [Pi.add_apply, Real.norm_eq_abs, uncurry_apply_pair] at hy hz
    rw [abs_of_nonneg (by positivity)] at hz
    refine ⟨⟨h1, h2⟩, ⟨(abs_le.mp hy).1, (abs_le.mp hy).2⟩, ?_, ?_⟩
    · linarith [neg_abs_le (ψ₁ x y), abs_nonneg (ψ₂ x y)]
    · linarith [le_abs_self (ψ₂ x y), abs_nonneg (ψ₁ x y)]
  have hint : IntegrableOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) D :=
    hf.integrableOn_compact hK
  rw [← integral_indicator hK.isClosed.measurableSet, Measure.volume_eq_prod,
    integral_prod _ ((integrable_indicator_iff hK.isClosed.measurableSet).mpr hint),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc a b
  · rw [indicator_of_mem hx]
    -- the slice at `x` is the planar region of 1.5.30 for `ψ₁(x, ·)`, `ψ₂(x, ·)`
    have hslice : (fun q : ℝ × ℝ => D.indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
        (x, q)) = (regionX (φ₁ x) (φ₂ x) (ψ₁ x) (ψ₂ x)).indicator (uncurry (f x)) := by
      funext q
      simp only [indicator, D, regionXYZ, regionX, mem_ofPred_eq, hx.1, hx.2, true_and]
      congr 1
    have hψ₁x : Continuous (ψ₁ x) := by exact hψ₁.comp (continuous_const.prodMk continuous_id)
    have hψ₂x : Continuous (ψ₂ x) := by exact hψ₂.comp (continuous_const.prodMk continuous_id)
    rw [hslice, integral_indicator
      (isCompact_regionX (a := φ₁ x) (b := φ₂ x) hψ₁x hψ₂x).isClosed.measurableSet]
    refine dlmf_1_5_31 (hφ x hx) hψ₁x hψ₂x (fun y hy => hψ x hx y hy) ?_
    refine (hf.comp (continuous_const.prodMk continuous_id).continuousOn ?_)
    rintro ⟨y, z⟩ ⟨h1, h2, h3, h4⟩
    exact ⟨hx.1, hx.2, h1, h2, h3, h4⟩
  · rw [indicator_of_notMem hx]
    have : (fun q : ℝ × ℝ => D.indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (x, q)) =
        fun _ => 0 := by
      funext q
      refine indicator_of_notMem (fun h => hx ⟨h.1, h.2.1⟩) _
    rw [this, integral_zero]

/-! ### Double Riemann integrals -/

/-- The double Riemann sum of DLMF 1.5.27 over the grid of the partitions `P` of `[a, b]` and `Q`
of `[c, d]` (DLMF 1.5.25–1.5.26; only the points `xⱼ`, `yₖ` of `P`, `Q` are used), with a point
`τ j k = (ξⱼ, ηₖ)` of each cell `[xⱼ, xⱼ₊₁] × [yₖ, yₖ₊₁]`. -/
noncomputable def doubleRiemannSum (f : ℝ → ℝ → ℝ) {a b c d : ℝ} (P : TaggedPartition a b)
    (Q : TaggedPartition c d) (τ : ℕ → ℕ → ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
    f (τ j k).1 (τ j k).2 * (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)

/-- **DLMF 1.5.27**: `∬_R f dA = I` as the limit of the double Riemann sums as
`max((xⱼ₊₁ − xⱼ) + (yₖ₊₁ − yₖ)) → 0`. -/
def HasDoubleRiemannIntegral (f : ℝ → ℝ → ℝ) (a b c d I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (P : TaggedPartition a b) (Q : TaggedPartition c d) (τ : ℕ → ℕ → ℝ × ℝ),
    (∀ j < P.n, ∀ k < Q.n, τ j k ∈ Icc (P.x j) (P.x (j + 1)) ×ˢ Icc (Q.x k) (Q.x (k + 1))) →
    (∀ j < P.n, ∀ k < Q.n, (P.x (j + 1) - P.x j) + (Q.x (k + 1) - Q.x k) < δ) →
    |doubleRiemannSum f P Q τ - I| < ε

/-- **DLMF 1.5.29** (Riemann form): `∬_D f dA = ∬_R f* dA` for `D ⊆ R = [a, b] × [c, d]`. -/
def HasDoubleRiemannIntegralOn (D : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ) (a b c d I : ℝ) : Prop :=
  HasDoubleRiemannIntegral (extendByZero D f) a b c d I

/-- Double Riemann sums of a function continuous on the plane converge to the repeated
integral. -/
theorem hasDoubleRiemannIntegral_of_continuous {g : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hg : Continuous (uncurry g)) :
    HasDoubleRiemannIntegral g a b c d (∫ x in a..b, ∫ y in c..d, g x y) := by
  intro ε hε
  have hA : 0 < (b - a) * (d - c) + 1 := by
    have := mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hcd)
    linarith
  set ε' := ε / ((b - a) * (d - c) + 1)
  have hε' : 0 < ε' := div_pos hε hA
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (((isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
      ).uniformContinuousOn_of_continuous hg.continuousOn) ε' hε'
  refine ⟨δ, hδ, fun P Q τ hτ hmesh => ?_⟩
  have hgx : ∀ x, Continuous (g x) := fun x => by
    exact hg.comp (continuous_const.prodMk continuous_id)
  have hparam : ∀ u w, Continuous fun x => ∫ y in u..w, g x y := fun u w =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg u w
  have hrow : ∀ x, ∫ y in c..d, g x y =
      ∑ k ∈ Finset.range Q.n, ∫ y in Q.x k..Q.x (k + 1), g x y := fun x => by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g x)
      (a := Q.x) (n := Q.n) fun k _ => (hgx x).intervalIntegrable _ _
    rw [Q.first, Q.last] at this
    exact this.symm
  have hcol : ∫ x in a..b, ∫ y in c..d, g x y = ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
      ∫ x in P.x j..P.x (j + 1), ∫ y in Q.x k..Q.x (k + 1), g x y := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun x => ∫ y in c..d, g x y) (a := P.x) (n := P.n)
      fun j _ => (hparam c d).intervalIntegrable _ _
    rw [P.first, P.last] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [hrow]
    exact intervalIntegral.integral_finsetSum fun k _ => (hparam _ _).intervalIntegrable _ _
  -- the error on one cell
  have hcell : ∀ j < P.n, ∀ k < Q.n,
      |g (τ j k).1 (τ j k).2 * (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) -
        ∫ x in P.x j..P.x (j + 1), ∫ y in Q.x k..Q.x (k + 1), g x y| ≤
      ε' * ((P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)) := by
    intro j hj k hk
    set t := g (τ j k).1 (τ j k).2
    have hPj := P.lt j hj
    have hQk := Q.lt k hk
    have e : t * (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) =
        ∫ x in P.x j..P.x (j + 1), ∫ y in Q.x k..Q.x (k + 1), t := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [e, abs_sub_comm, ← intervalIntegral.integral_sub ((hparam _ _).intervalIntegrable _ _)
      intervalIntegrable_const]
    have hb : ∀ x ∈ uIoc (P.x j) (P.x (j + 1)),
        ‖(∫ y in Q.x k..Q.x (k + 1), g x y) - ∫ y in Q.x k..Q.x (k + 1), t‖ ≤
          ε' * (Q.x (k + 1) - Q.x k) := by
      intro x hx
      rw [uIoc_of_le hPj.le] at hx
      rw [← intervalIntegral.integral_sub ((hgx x).intervalIntegrable _ _)
        intervalIntegrable_const]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε') (a := Q.x k)
        (b := Q.x (k + 1)) (f := fun y => g x y - t) fun y hy => by
          rw [uIoc_of_le hQk.le] at hy
          have hxK : (x, y) ∈ Icc a b ×ˢ Icc c d :=
            ⟨⟨(P.mem_Icc hj.le).1.trans hx.1.le, hx.2.trans (P.mem_Icc hj).2⟩,
              ⟨(Q.mem_Icc hk.le).1.trans hy.1.le, hy.2.trans (Q.mem_Icc hk).2⟩⟩
          have hτK : τ j k ∈ Icc a b ×ˢ Icc c d :=
            ⟨⟨(P.mem_Icc hj.le).1.trans (hτ j hj k hk).1.1,
                (hτ j hj k hk).1.2.trans (P.mem_Icc hj).2⟩,
              ⟨(Q.mem_Icc hk.le).1.trans (hτ j hj k hk).2.1,
                (hτ j hj k hk).2.2.trans (Q.mem_Icc hk).2⟩⟩
          have hd : dist (x, y) (τ j k) < δ := by
            have h1 := hτ j hj k hk
            have hm := hmesh j hj k hk
            rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt]
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
              linarith [hx.1, hx.2, hy.1, hy.2, h1.1.1, h1.1.2, h1.2.1, h1.2.2]
          have := hU _ hxK _ hτK hd
          rw [Real.dist_eq] at this
          rw [Real.norm_eq_abs]
          exact this.le
      rwa [abs_of_pos (sub_pos.2 hQk)] at this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [abs_of_pos (sub_pos.2 hPj), Real.norm_eq_abs] at this
    exact this.trans (le_of_eq (by ring))
  -- summing over the cells
  have hsum : |doubleRiemannSum g P Q τ - ∫ x in a..b, ∫ y in c..d, g x y| ≤
      ε' * ((b - a) * (d - c)) := by
    rw [doubleRiemannSum, hcol, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ j ∈ Finset.range P.n, |∑ k ∈ Finset.range Q.n,
          (g (τ j k).1 (τ j k).2 * (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)) -
            ∑ k ∈ Finset.range Q.n,
              ∫ x in P.x j..P.x (j + 1), ∫ y in Q.x k..Q.x (k + 1), g x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
          ε' * ((P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk =>
          hcell j (Finset.mem_range.mp hj) k (Finset.mem_range.mp hk))
      _ = ε' * ((b - a) * (d - c)) := by
        have hk : ∀ j, ∑ k ∈ Finset.range Q.n,
            ε' * ((P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)) =
            ε' * (P.x (j + 1) - P.x j) * (d - c) := fun j => by
          rw [← Q.sum_lengths, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        simp_rw [hk]
        rw [← Finset.sum_mul, ← Finset.mul_sum, P.sum_lengths]
        ring
  calc _ ≤ ε' * ((b - a) * (d - c)) := hsum
    _ < ε' * ((b - a) * (d - c) + 1) := by linarith
    _ = ε := div_mul_cancel₀ ε hA.ne'

/-- A function continuous on a closed rectangle extends to a continuous function on the plane. -/
theorem exists_continuous_extension_rect {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ Icc c d)) :
    ∃ g : ℝ → ℝ → ℝ, Continuous (uncurry g) ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, g x y = f x y := by
  refine ⟨fun x y => f (max a (min b x)) (max c (min d y)), ?_, fun x hx y hy => ?_⟩
  · exact hf.comp_continuous ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
      (continuous_const.max (continuous_const.min continuous_snd))) fun p =>
      ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩,
        ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩⟩
  · simp only [min_eq_right hx.2, max_eq_right hx.1, min_eq_right hy.2, max_eq_right hy.1]

/-- **DLMF 1.5.27**: if `f` is continuous on `R = [a, b] × [c, d]`, the double Riemann sums
converge, and the limit is the (Lebesgue) double integral `∬_R f dA`. -/
theorem dlmf_1_5_27 {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ Icc c d)) :
    HasDoubleRiemannIntegral f a b c d (∫ p in Icc a b ×ˢ Icc c d, f p.1 p.2) := by
  obtain ⟨g, hg, hgf⟩ := exists_continuous_extension_rect hab hcd hf
  have hR : Icc a b ×ˢ Icc c d = regionX a b (fun _ => c) (fun _ => d) := by
    ext ⟨x, y⟩
    simp only [regionX, mem_prod, mem_Icc, mem_ofPred_eq]
    tauto
  have hI : ∫ p in Icc a b ×ˢ Icc c d, f p.1 p.2 = ∫ x in a..b, ∫ y in c..d, g x y := by
    rw [hR, dlmf_1_5_31 hab continuous_const continuous_const (fun _ _ => hcd) (hR ▸ hf)]
    refine intervalIntegral.integral_congr fun x hx => intervalIntegral.integral_congr
      fun y hy => ?_
    rw [uIcc_of_le hab] at hx
    rw [uIcc_of_le hcd] at hy
    exact (hgf x hx y hy).symm
  rw [hI]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hasDoubleRiemannIntegral_of_continuous hab hcd hg ε hε
  refine ⟨δ, hδ, fun P Q τ hτ hmesh => ?_⟩
  have e : doubleRiemannSum f P Q τ = doubleRiemannSum g P Q τ := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have h1 := hτ j hj' k hk'
    rw [hgf _ ⟨(P.mem_Icc hj'.le).1.trans h1.1.1, h1.1.2.trans (P.mem_Icc hj').2⟩ _
      ⟨(Q.mem_Icc hk'.le).1.trans h1.2.1, h1.2.2.trans (Q.mem_Icc hk').2⟩]
  rw [e]
  exact h P Q τ hτ hmesh

/-! ### Piecewise continuous functions on a rectangle

DLMF defines piecewise continuity of `f(x, y)` slice-wise (§1.5(i)).  For the existence of the
double integral 1.5.27 we use the standard two-dimensional notion: `f` is bounded on the rectangle
and continuous there except along finitely many continuous curves `y = φᵢ(x)`, `x = ψⱼ(y)`
(the slice-wise definition alone does not control the set of discontinuities). -/

/-- The closed strip of half-width `r` around the curve `y = φ(x)`, `a ≤ x ≤ b`. -/
def stripY (φ : ℝ → ℝ) (a b r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ |p.2 - φ p.1| ≤ r}

/-- The closed strip of half-width `r` around the curve `x = ψ(y)`, `c ≤ y ≤ d`. -/
def stripX (ψ : ℝ → ℝ) (c d r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc c d ∧ |p.1 - ψ p.2| ≤ r}

theorem mem_stripY {φ : ℝ → ℝ} {a b r : ℝ} {p : ℝ × ℝ} :
    p ∈ stripY φ a b r ↔ p.1 ∈ Icc a b ∧ |p.2 - φ p.1| ≤ r := Iff.rfl

theorem mem_stripX {ψ : ℝ → ℝ} {c d r : ℝ} {p : ℝ × ℝ} :
    p ∈ stripX ψ c d r ↔ p.2 ∈ Icc c d ∧ |p.1 - ψ p.2| ≤ r := Iff.rfl

theorem isClosed_stripY {φ : ℝ → ℝ} (hφ : Continuous φ) (a b r : ℝ) :
    IsClosed (stripY φ a b r) := by
  simp only [stripY, mem_Icc, ofPred_and]
  exact ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst continuous_const)).inter
      (isClosed_le (continuous_snd.sub (hφ.comp continuous_fst)).abs continuous_const)

theorem stripX_eq_preimage_swap (ψ : ℝ → ℝ) (c d r : ℝ) :
    stripX ψ c d r = Prod.swap ⁻¹' stripY ψ c d r := by
  ext ⟨x, y⟩
  simp [stripX, stripY]

theorem isClosed_stripX {ψ : ℝ → ℝ} (hψ : Continuous ψ) (c d r : ℝ) :
    IsClosed (stripX ψ c d r) := by
  rw [stripX_eq_preimage_swap]
  exact (isClosed_stripY hψ c d r).preimage continuous_swap

/-- The strip around `y = φ(x)` has area at most `2r(b − a)`. -/
theorem volume_stripY_le {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (stripY φ a b r) ≤ ENNReal.ofReal (2 * r * (b - a)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (isClosed_stripY hφ a b r).measurableSet]
  have hsec : ∀ x, volume (Prod.mk x ⁻¹' stripY φ a b r) ≤
      (Icc a b).indicator (fun _ => ENNReal.ofReal (2 * r)) x := by
    intro x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
      calc volume (Prod.mk x ⁻¹' stripY φ a b r) ≤ volume (Icc (φ x - r) (φ x + r)) := by
            refine measure_mono fun y hy => ?_
            simp only [mem_preimage, stripY, mem_ofPred_eq] at hy
            rw [mem_Icc]
            constructor <;> linarith [abs_le.mp hy.2]
        _ = ENNReal.ofReal (2 * r) := by rw [Real.volume_Icc]; congr 1; ring
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' stripY φ a b r = ∅ := by
        ext y
        simp only [mem_preimage, stripY, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => (hx h).elim
      rw [this, measure_empty]
  calc ∫⁻ x, volume (Prod.mk x ⁻¹' stripY φ a b r) ≤
        ∫⁻ x, (Icc a b).indicator (fun _ => ENNReal.ofReal (2 * r)) x := lintegral_mono hsec
    _ = ENNReal.ofReal (2 * r) * volume (Icc a b) := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
    _ = ENNReal.ofReal (2 * r * (b - a)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]

/-- The strip around `x = ψ(y)` has area at most `2r(d − c)`. -/
theorem volume_stripX_le {ψ : ℝ → ℝ} (hψ : Continuous ψ) (c d : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (stripX ψ c d r) ≤ ENNReal.ofReal (2 * r * (d - c)) := by
  rw [stripX_eq_preimage_swap, Measure.volume_eq_prod,
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
      |>.measure_preimage (isClosed_stripY hψ c d r).measurableSet.nullMeasurableSet,
    ← Measure.volume_eq_prod]
  exact volume_stripY_le hψ c d hr

/-- `f` is piecewise continuous on the rectangle `R = [a, b] × [c, d]`: bounded on `R` and
continuous within `R` at every point of `R` off finitely many continuous curves `y = φᵢ(x)`,
`x = ψⱼ(y)`. -/
def IsPiecewiseContinuousRect (f : ℝ → ℝ → ℝ) (a b c d : ℝ) : Prop :=
  (∃ M, ∀ p ∈ Icc a b ×ˢ Icc c d, |f p.1 p.2| ≤ M) ∧
    ∃ (m : ℕ) (φ : Fin m → ℝ → ℝ) (m' : ℕ) (ψ : Fin m' → ℝ → ℝ), (∀ i, Continuous (φ i)) ∧
      (∀ j, Continuous (ψ j)) ∧ ∀ p ∈ Icc a b ×ˢ Icc c d, (∀ i, p.2 ≠ φ i p.1) →
        (∀ j, p.1 ≠ ψ j p.2) → ContinuousWithinAt (uncurry f) (Icc a b ×ˢ Icc c d) p

/-- A continuous function on a rectangle is piecewise continuous on it (no exceptional curves). -/
theorem ContinuousOn.isPiecewiseContinuousRect {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ Icc c d)) : IsPiecewiseContinuousRect f a b c d := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf
  exact ⟨⟨M, fun p hp => by have := hM p hp; rwa [Real.norm_eq_abs] at this⟩, 0, Fin.elim0, 0,
    Fin.elim0,
    fun i => i.elim0, fun j => j.elim0, fun p hp _ _ => hf p hp⟩

/-- A function continuous on a closed set and bounded by `M` there extends to a continuous
function on the plane bounded by `M` (Tietze extension, then clamping). -/
theorem exists_continuous_extension_of_isClosed {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f K) {M : ℝ} (hM : 0 ≤ M) (hfM : ∀ p ∈ K, |f p| ≤ M) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ (∀ p ∈ K, g p = f p) ∧ ∀ p, |g p| ≤ M := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK ⟨fun p : K => f p,
    continuousOn_iff_continuous_domRestrict.mp hf⟩
  refine ⟨fun p => max (-M) (min M (g p)), by fun_prop, fun p hp => ?_, fun p => ?_⟩
  · have : g p = f p := by
      have := congrArg (fun h : C(K, ℝ) => h ⟨p, hp⟩) hg
      exact this
    show max (-M) (min M (g p)) = f p
    rw [this, min_eq_right (abs_le.mp (hfM p hp)).2, max_eq_right (abs_le.mp (hfM p hp)).1]
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- A piecewise continuous function is (Lebesgue) integrable on the rectangle: the exceptional
curves have zero area, and `f` is bounded and continuous off them. -/
theorem IsPiecewiseContinuousRect.integrableOn {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : IsPiecewiseContinuousRect f a b c d) :
    IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc a b ×ˢ Icc c d) := by
  obtain ⟨⟨M, hM⟩, m, φ, m', ψ, hφ, hψ, hcont⟩ := hf
  set R := Icc a b ×ˢ Icc c d with hR
  set Z := (⋃ i, stripY (φ i) a b 0) ∪ ⋃ j, stripX (ψ j) c d 0 with hZ
  have hZ0 : volume Z = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc volume Z ≤ volume (⋃ i, stripY (φ i) a b 0) + volume (⋃ j, stripX (ψ j) c d 0) :=
          measure_union_le _ _
      _ ≤ (∑ i, volume (stripY (φ i) a b 0)) + ∑ j, volume (stripX (ψ j) c d 0) :=
          add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)
      _ ≤ (∑ _i : Fin m, ENNReal.ofReal (2 * 0 * (b - a))) +
            ∑ _j : Fin m', ENNReal.ofReal (2 * 0 * (d - c)) :=
          add_le_add (Finset.sum_le_sum fun i _ => volume_stripY_le (hφ i) a b le_rfl)
            (Finset.sum_le_sum fun j _ => volume_stripX_le (hψ j) c d le_rfl)
      _ = 0 := by simp
  have hZc : IsClosed Z :=
    (isClosed_iUnion_of_finite fun i => isClosed_stripY (hφ i) a b 0).union
      (isClosed_iUnion_of_finite fun j => isClosed_stripX (hψ j) c d 0)
  have hRc : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := hRc.isClosed.measurableSet
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (R \ Z) := by
    intro p hp
    have hp1 : p ∈ R := hp.1
    have h1 : ∀ i, p.2 ≠ φ i p.1 := fun i h =>
      hp.2 (Or.inl (mem_iUnion.mpr ⟨i, mem_stripY.mpr ⟨hp1.1, by rw [h, sub_self, abs_zero]⟩⟩))
    have h2 : ∀ j, p.1 ≠ ψ j p.2 := fun j h =>
      hp.2 (Or.inr (mem_iUnion.mpr ⟨j, mem_stripX.mpr ⟨hp1.2, by rw [h, sub_self, abs_zero]⟩⟩))
    exact (hcont p hp1 h1 h2).mono sdiff_subset
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2) (volume.restrict R) := by
    rw [← Measure.restrict_congr_set
      (sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right hZ0))]
    exact hcont'.aestronglyMeasurable (hRm.diff hZc.measurableSet)
  have : Fact (volume R < ⊤) := ⟨hRc.measure_lt_top⟩
  exact Integrable.of_bound hmeas M (ae_restrict_of_forall_mem hRm fun p hp => by
    rw [Real.norm_eq_abs]; exact hM p hp)

/-- Cells of a partition of mesh `< δ` that each contain a point within `r` of a fixed `m` have
total length at most `2r + 2δ`. -/
theorem TaggedPartition.sum_lengths_le_of_near {a b : ℝ} (P : TaggedPartition a b)
    {T : Finset ℕ} (hT : T ⊆ Finset.range P.n) {δ r m : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hmesh : ∀ k < P.n, P.x (k + 1) - P.x k < δ) {t : ℕ → ℝ}
    (ht : ∀ k ∈ T, t k ∈ Icc (P.x k) (P.x (k + 1)) ∧ |t k - m| ≤ r) :
    ∑ k ∈ T, (P.x (k + 1) - P.x k) ≤ 2 * r + 2 * δ := by
  have := P.sum_lengths_le hT (c := m - r - δ) (d := m + r + δ) (by linarith) fun k hk => by
    have hk' := Finset.mem_range.mp (hT hk)
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht k hk
    have hm := hmesh k hk'
    rw [abs_le] at h3
    intro y hy
    rw [Set.mem_Icc] at hy ⊢
    constructor <;> linarith
  linarith

theorem sum_sum_sum_comm {ι : Type*} [Fintype ι] (s t : Finset ℕ) (F : ι → ℕ → ℕ → ℝ) :
    ∑ j ∈ s, ∑ k ∈ t, ∑ i, F i j k = ∑ i, ∑ j ∈ s, ∑ k ∈ t, F i j k :=
  calc ∑ j ∈ s, ∑ k ∈ t, ∑ i, F i j k = ∑ j ∈ s, ∑ i, ∑ k ∈ t, F i j k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j ∈ s, ∑ k ∈ t, F i j k := Finset.sum_comm

/-- A partition of a degenerate interval `[a, a]` has no cells. -/
theorem TaggedPartition.n_eq_zero_of_eq {a : ℝ} (P : TaggedPartition a a) : P.n = 0 := by
  by_contra h
  have h1 := P.lt 0 (Nat.pos_of_ne_zero h)
  have h2 := P.le_of_le (Nat.one_le_iff_ne_zero.mpr h) le_rfl
  rw [P.first] at h1
  rw [P.last] at h2
  linarith

/-- On a degenerate rectangle (`a = b` or `c = d`) every double Riemann sum and the double integral
vanish. -/
theorem hasDoubleRiemannIntegral_of_degenerate (f : ℝ → ℝ → ℝ) {a b c d : ℝ}
    (h : a = b ∨ c = d) :
    HasDoubleRiemannIntegral f a b c d (∫ p in Icc a b ×ˢ Icc c d, f p.1 p.2) := by
  have hvol : volume (Icc a b ×ˢ Icc c d) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    rcases h with rfl | rfl <;> simp
  rw [Measure.restrict_eq_zero.mpr hvol, integral_zero_measure]
  intro ε hε
  refine ⟨1, one_pos, fun P Q τ _ _ => ?_⟩
  have : doubleRiemannSum f P Q τ = 0 := by
    rcases h with rfl | rfl
    · simp [doubleRiemannSum, P.n_eq_zero_of_eq]
    · simp [doubleRiemannSum, Q.n_eq_zero_of_eq]
  rw [this, sub_zero, abs_zero]
  exact hε

/-- **DLMF 1.5.27** for piecewise continuous `f`: if `f` is bounded on `R = [a, b] × [c, d]` and
continuous there off finitely many continuous curves, the double Riemann sums converge, with
limit the Lebesgue double integral `∬_R f dA`.  Proof: off closed strips of half-width `η` around
the curves, `f` agrees with a continuous `g` (Tietze); the sums and the integrals of `f` and `g`
differ by `O(M η)` (cells with a sample point in a strip have total area `O(η)`, the strips have
area `O(η)`), and `g` is handled by the continuous case. -/
theorem dlmf_1_5_27_piecewise {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : IsPiecewiseContinuousRect f a b c d) :
    HasDoubleRiemannIntegral f a b c d (∫ p in Icc a b ×ˢ Icc c d, f p.1 p.2) := by
  classical
  rcases eq_or_lt_of_le hab with rfl | hab'
  · exact hasDoubleRiemannIntegral_of_degenerate f (Or.inl rfl)
  rcases eq_or_lt_of_le hcd with rfl | hcd'
  · exact hasDoubleRiemannIntegral_of_degenerate f (Or.inr rfl)
  have hint := hf.integrableOn
  obtain ⟨⟨M₀, hM₀⟩, m, φ, m', ψ, hφ, hψ, hcont⟩ := hf
  set R := Icc a b ×ˢ Icc c d with hR
  set M := max M₀ 0 with hMdef
  have hM : ∀ p ∈ R, |f p.1 p.2| ≤ M := fun p hp => (hM₀ p hp).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hRc : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := hRc.isClosed.measurableSet
  have hRfin : volume R < ⊤ := hRc.measure_lt_top
  set B : ℝ := (b - a) * m + (d - c) * m' with hBdef
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg _))
    (mul_nonneg (sub_nonneg.2 hcd) (Nat.cast_nonneg _))
  intro ε hε
  set η := ε / (3 * (16 * M * B + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hηbound : 16 * M * η * B < ε / 3 := by
    have h1 : 0 < 16 * M * B + 1 := by positivity
    have h2 : 16 * M * η * B = ε / 3 * (16 * M * B / (16 * M * B + 1)) := by
      rw [hηdef]; field_simp
    rw [h2]
    have h3 : 16 * M * B / (16 * M * B + 1) < 1 := by
      rw [div_lt_one h1]; linarith
    have h4 : 0 ≤ 16 * M * B / (16 * M * B + 1) := by positivity
    nlinarith
  -- the closed set `K` off the strips, and the continuous replacement `g` of `f` on `K`
  set K : Set (ℝ × ℝ) :=
    R ∩ ({p | ∀ i, η ≤ |p.2 - φ i p.1|} ∩ {p | ∀ j, η ≤ |p.1 - ψ j p.2|}) with hKdef
  have hKc : IsClosed K := by
    refine hRc.isClosed.inter (IsClosed.inter ?_ ?_)
    · rw [ofPred_forall]
      exact isClosed_iInter fun i =>
        isClosed_le continuous_const (continuous_snd.sub ((hφ i).comp continuous_fst)).abs
    · rw [ofPred_forall]
      exact isClosed_iInter fun j =>
        isClosed_le continuous_const (continuous_fst.sub ((hψ j).comp continuous_snd)).abs
  have hfK : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) K := fun p hp =>
    (hcont p hp.1 (fun i h => by have := hp.2.1 i; rw [h, sub_self, abs_zero] at this; linarith)
      (fun j h => by have := hp.2.2 j; rw [h, sub_self, abs_zero] at this; linarith)).mono
      inter_subset_left
  obtain ⟨g, hg, hgf, hgM⟩ :=
    exists_continuous_extension_of_isClosed hKc hfK hM0 fun p hp => hM p hp.1
  obtain ⟨δg, hδg, hg'⟩ :=
    dlmf_1_5_27 (f := fun x y => g (x, y)) hab hcd (by exact hg.continuousOn) (ε / 3)
      (by positivity)
  -- uniform continuity of the curves
  obtain ⟨δφ, hδφ, hφu⟩ := Metric.uniformContinuousOn_iff_le.mp
    ((isCompact_Icc (a := a) (b := b)).uniformContinuousOn_of_continuous
      (continuous_pi fun i => hφ i).continuousOn) η hη
  obtain ⟨δψ, hδψ, hψu⟩ := Metric.uniformContinuousOn_iff_le.mp
    ((isCompact_Icc (a := c) (b := d)).uniformContinuousOn_of_continuous
      (continuous_pi fun j => hψ j).continuousOn) η hη
  have hφi : ∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| ≤ δφ → |φ i x - φ i y| ≤ η :=
    fun i x hx y hy hxy => by
      have := (dist_le_pi_dist (fun i => φ i x) (fun i => φ i y) i).trans
        (hφu x hx y hy (by rwa [Real.dist_eq]))
      rwa [Real.dist_eq] at this
  have hψj : ∀ j, ∀ x ∈ Icc c d, ∀ y ∈ Icc c d, |x - y| ≤ δψ → |ψ j x - ψ j y| ≤ η :=
    fun j x hx y hy hxy => by
      have := (dist_le_pi_dist (fun j => ψ j x) (fun j => ψ j y) j).trans
        (hψu x hx y hy (by rwa [Real.dist_eq]))
      rwa [Real.dist_eq] at this
  set δ := min (min δg η) (min δφ δψ) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδg hη) (lt_min hδφ hδψ)
  have hδg' : δ ≤ δg := min_le_of_left_le (min_le_left _ _)
  have hδη : δ ≤ η := min_le_of_left_le (min_le_right _ _)
  have hδφ' : δ ≤ δφ := min_le_of_right_le (min_le_left _ _)
  have hδψ' : δ ≤ δψ := min_le_of_right_le (min_le_right _ _)
  refine ⟨δ, hδ, fun P Q τ hτ hmesh => ?_⟩
  have hPn : 0 < P.n := Nat.pos_of_ne_zero fun h => by
    have h1 := P.first; have h2 := P.last; rw [h] at h2; linarith
  have hQn : 0 < Q.n := Nat.pos_of_ne_zero fun h => by
    have h1 := Q.first; have h2 := Q.last; rw [h] at h2; linarith
  have hmeshP : ∀ j < P.n, P.x (j + 1) - P.x j < δ := fun j hj => by
    have := hmesh j hj 0 hQn; have := Q.lt 0 hQn; linarith
  have hmeshQ : ∀ k < Q.n, Q.x (k + 1) - Q.x k < δ := fun k hk => by
    have := hmesh 0 hPn k hk; have := P.lt 0 hPn; linarith
  have hτR : ∀ j < P.n, ∀ k < Q.n, τ j k ∈ R := fun j hj k hk =>
    ⟨⟨(P.mem_Icc hj.le).1.trans (hτ j hj k hk).1.1, (hτ j hj k hk).1.2.trans (P.mem_Icc hj).2⟩,
      ⟨(Q.mem_Icc hk.le).1.trans (hτ j hj k hk).2.1, (hτ j hj k hk).2.2.trans (Q.mem_Icc hk).2⟩⟩
  have hΔ : ∀ j < P.n, ∀ k < Q.n, 0 ≤ (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) :=
    fun j hj k hk => mul_nonneg (sub_nonneg.2 (P.lt j hj).le) (sub_nonneg.2 (Q.lt k hk).le)
  -- cells whose sample point lies in a strip around `y = φᵢ(x)` have total area `≤ 6η(b − a)`
  have hcellY : ∀ i, ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
      (if τ j k ∈ stripY (φ i) a b η then (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)
        else 0) ≤ (b - a) * (6 * η) := by
    intro i
    calc _ = ∑ j ∈ Finset.range P.n, (P.x (j + 1) - P.x j) *
          ∑ k ∈ (Finset.range Q.n).filter (fun k => τ j k ∈ stripY (φ i) a b η),
            (Q.x (k + 1) - Q.x k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ j ∈ Finset.range P.n, (P.x (j + 1) - P.x j) * (6 * η) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 (P.lt j hj').le)
          have := Q.sum_lengths_le_of_near
            (Finset.filter_subset (fun k => τ j k ∈ stripY (φ i) a b η) _) (δ := δ) (r := 2 * η)
            (m := φ i (P.x j)) hδ.le (by positivity) hmeshQ (t := fun k => (τ j k).2)
            fun k hk => by
              obtain ⟨hk, hs⟩ := Finset.mem_filter.mp hk
              have hk' := Finset.mem_range.mp hk
              refine ⟨(hτ j hj' k hk').2, ?_⟩
              have h1 : |(τ j k).2 - φ i (τ j k).1| ≤ η := (mem_stripY.mp hs).2
              have h2 : |φ i (τ j k).1 - φ i (P.x j)| ≤ η :=
                hφi i _ (hτR j hj' k hk').1 _ (P.mem_Icc hj'.le) (by
                  rw [abs_le]
                  have hτ1 := (hτ j hj' k hk').1
                  have hm := hmeshP j hj'
                  constructor <;> linarith [hτ1.1, hτ1.2])
              calc |(τ j k).2 - φ i (P.x j)| =
                  |((τ j k).2 - φ i (τ j k).1) + (φ i (τ j k).1 - φ i (P.x j))| := by ring_nf
                _ ≤ |(τ j k).2 - φ i (τ j k).1| + |φ i (τ j k).1 - φ i (P.x j)| := abs_add_le _ _
                _ ≤ 2 * η := by linarith
          linarith
      _ = (b - a) * (6 * η) := by rw [← Finset.sum_mul, P.sum_lengths]
  -- and around `x = ψⱼ(y)`, total area `≤ 6η(d − c)`
  have hcellX : ∀ j', ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
      (if τ j k ∈ stripX (ψ j') c d η then (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)
        else 0) ≤ (d - c) * (6 * η) := by
    intro j'
    rw [Finset.sum_comm]
    calc _ = ∑ k ∈ Finset.range Q.n, (Q.x (k + 1) - Q.x k) *
          ∑ j ∈ (Finset.range P.n).filter (fun j => τ j k ∈ stripX (ψ j') c d η),
            (P.x (j + 1) - P.x j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp [mul_comm]
      _ ≤ ∑ k ∈ Finset.range Q.n, (Q.x (k + 1) - Q.x k) * (6 * η) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 (Q.lt k hk').le)
          have := P.sum_lengths_le_of_near
            (Finset.filter_subset (fun j => τ j k ∈ stripX (ψ j') c d η) _) (δ := δ)
            (r := 2 * η) (m := ψ j' (Q.x k)) hδ.le (by positivity) hmeshP
            (t := fun j => (τ j k).1) fun j hj => by
              obtain ⟨hj, hs⟩ := Finset.mem_filter.mp hj
              have hj' := Finset.mem_range.mp hj
              refine ⟨(hτ j hj' k hk').1, ?_⟩
              have h1 : |(τ j k).1 - ψ j' (τ j k).2| ≤ η := (mem_stripX.mp hs).2
              have h2 : |ψ j' (τ j k).2 - ψ j' (Q.x k)| ≤ η :=
                hψj j' _ (hτR j hj' k hk').2 _ (Q.mem_Icc hk'.le) (by
                  rw [abs_le]
                  have hτ2 := (hτ j hj' k hk').2
                  have hm := hmeshQ k hk'
                  constructor <;> linarith [hτ2.1, hτ2.2])
              calc |(τ j k).1 - ψ j' (Q.x k)| =
                  |((τ j k).1 - ψ j' (τ j k).2) + (ψ j' (τ j k).2 - ψ j' (Q.x k))| := by ring_nf
                _ ≤ |(τ j k).1 - ψ j' (τ j k).2| + |ψ j' (τ j k).2 - ψ j' (Q.x k)| :=
                  abs_add_le _ _
                _ ≤ 2 * η := by linarith
          linarith
      _ = (d - c) * (6 * η) := by rw [← Finset.sum_mul, Q.sum_lengths]
  -- the Riemann sums of `f` and `g` are close
  have hterm : ∀ j < P.n, ∀ k < Q.n, |f (τ j k).1 (τ j k).2 - g (τ j k)| ≤ 2 * M *
      ((∑ i, if τ j k ∈ stripY (φ i) a b η then (1 : ℝ) else 0) +
        ∑ j', if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ) else 0) := by
    intro j hj k hk
    have hnn : 0 ≤ (∑ i, if τ j k ∈ stripY (φ i) a b η then (1 : ℝ) else 0) +
        ∑ j', if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ) else 0 :=
      add_nonneg (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
        (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
    by_cases hK : τ j k ∈ K
    · rw [hgf _ hK, sub_self, abs_zero]
      exact mul_nonneg (by positivity) hnn
    · have hR' := hτR j hj k hk
      have h2M : |f (τ j k).1 (τ j k).2 - g (τ j k)| ≤ 2 * M := by
        calc _ ≤ |f (τ j k).1 (τ j k).2| + |g (τ j k)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hM _ hR') (hgM _)
          _ = 2 * M := by ring
      have hone : 1 ≤ (∑ i, if τ j k ∈ stripY (φ i) a b η then (1 : ℝ) else 0) +
          ∑ j', if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ) else 0 := by
        have hnot : ¬ ((∀ i, η ≤ |(τ j k).2 - φ i (τ j k).1|) ∧
            ∀ j', η ≤ |(τ j k).1 - ψ j' (τ j k).2|) := fun h => hK ⟨hR', h⟩
        rw [not_and_or] at hnot
        rcases hnot with h | h
        · push Not at h
          obtain ⟨i, hi⟩ := h
          have hmem : τ j k ∈ stripY (φ i) a b η := mem_stripY.mpr ⟨hR'.1, hi.le⟩
          calc (1 : ℝ) = if τ j k ∈ stripY (φ i) a b η then (1 : ℝ) else 0 := by
                simp only [hmem, ↓reduceIte]
            _ ≤ ∑ i, if τ j k ∈ stripY (φ i) a b η then (1 : ℝ) else 0 :=
                Finset.single_le_sum (f := fun i => if τ j k ∈ stripY (φ i) a b η then (1 : ℝ)
                  else 0) (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
            _ ≤ _ := le_add_of_nonneg_right
                (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
        · push Not at h
          obtain ⟨j', hj'⟩ := h
          have hmem : τ j k ∈ stripX (ψ j') c d η := mem_stripX.mpr ⟨hR'.2, hj'.le⟩
          calc (1 : ℝ) = if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ) else 0 := by
                simp only [hmem, ↓reduceIte]
            _ ≤ ∑ j', if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ) else 0 :=
                Finset.single_le_sum (f := fun j' => if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ)
                  else 0) (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ j')
            _ ≤ _ := le_add_of_nonneg_left
                (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
      calc |f (τ j k).1 (τ j k).2 - g (τ j k)| ≤ 2 * M := h2M
        _ = 2 * M * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hone (by positivity)
  have hSfg : |doubleRiemannSum f P Q τ - doubleRiemannSum (fun x y => g (x, y)) P Q τ| ≤
      12 * M * η * B := by
    calc |doubleRiemannSum f P Q τ - doubleRiemannSum (fun x y => g (x, y)) P Q τ|
        = |∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n, (f (τ j k).1 (τ j k).2 - g (τ j k)) *
            ((P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k))| := by
          simp only [doubleRiemannSum, ← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n, |f (τ j k).1 (τ j k).2 - g (τ j k)| *
            ((P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => by
              rw [abs_mul, abs_of_nonneg (hΔ j (Finset.mem_range.mp hj) k
                (Finset.mem_range.mp hk))]))
      _ ≤ ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n, 2 * M *
            ((∑ i, if τ j k ∈ stripY (φ i) a b η then (1 : ℝ) else 0) +
              ∑ j', if τ j k ∈ stripX (ψ j') c d η then (1 : ℝ) else 0) *
            ((P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k)) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_right (hterm j (Finset.mem_range.mp hj) k
              (Finset.mem_range.mp hk)) (hΔ j (Finset.mem_range.mp hj) k (Finset.mem_range.mp hk))
      _ = ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n, 2 * M *
            ((∑ i, if τ j k ∈ stripY (φ i) a b η then
                (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) else 0) +
              ∑ j', if τ j k ∈ stripX (ψ j') c d η then
                (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) else 0) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
            rw [mul_assoc, add_mul, Finset.sum_mul, Finset.sum_mul]
            simp only [boole_mul]
      _ = 2 * M * ((∑ i, ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
            if τ j k ∈ stripY (φ i) a b η then
              (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) else 0) +
            ∑ j', ∑ j ∈ Finset.range P.n, ∑ k ∈ Finset.range Q.n,
              if τ j k ∈ stripX (ψ j') c d η then
                (P.x (j + 1) - P.x j) * (Q.x (k + 1) - Q.x k) else 0) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
          rw [sum_sum_sum_comm, sum_sum_sum_comm]
      _ ≤ 2 * M * ((∑ _i : Fin m, (b - a) * (6 * η)) + ∑ _j' : Fin m', (d - c) * (6 * η)) :=
          mul_le_mul_of_nonneg_left (add_le_add (Finset.sum_le_sum fun i _ => hcellY i)
            (Finset.sum_le_sum fun j' _ => hcellX j')) (by positivity)
      _ = 12 * M * η * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hBdef]
          ring
  -- the integrals of `f` and `g` are close
  have hgint : IntegrableOn g R := hg.continuousOn.integrableOn_compact hRc
  have hIfg : |(∫ p in R, f p.1 p.2) - ∫ p in R, g p| ≤ 4 * M * η * B := by
    rw [← integral_sub hint hgint]
    have hsub : R \ K ⊆ (⋃ i, stripY (φ i) a b η) ∪ ⋃ j', stripX (ψ j') c d η := by
      intro p hp
      have hp1 := hp.1
      have hnot : ¬ ((∀ i, η ≤ |p.2 - φ i p.1|) ∧ ∀ j', η ≤ |p.1 - ψ j' p.2|) :=
        fun h => hp.2 ⟨hp1, h⟩
      rw [not_and_or] at hnot
      rcases hnot with h | h
      · push Not at h
        obtain ⟨i, hi⟩ := h
        exact Or.inl (mem_iUnion.mpr ⟨i, mem_stripY.mpr ⟨hp1.1, hi.le⟩⟩)
      · push Not at h
        obtain ⟨j', hj'⟩ := h
        exact Or.inr (mem_iUnion.mpr ⟨j', mem_stripX.mpr ⟨hp1.2, hj'.le⟩⟩)
    have hvol : volume (R \ K) ≤ ENNReal.ofReal (2 * η * B) := by
      calc volume (R \ K) ≤ volume ((⋃ i, stripY (φ i) a b η) ∪ ⋃ j', stripX (ψ j') c d η) :=
            measure_mono hsub
        _ ≤ volume (⋃ i, stripY (φ i) a b η) + volume (⋃ j', stripX (ψ j') c d η) :=
            measure_union_le _ _
        _ ≤ (∑ i, volume (stripY (φ i) a b η)) + ∑ j', volume (stripX (ψ j') c d η) :=
            add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)
        _ ≤ (∑ _i : Fin m, ENNReal.ofReal (2 * η * (b - a))) +
              ∑ _j' : Fin m', ENNReal.ofReal (2 * η * (d - c)) :=
            add_le_add (Finset.sum_le_sum fun i _ => volume_stripY_le (hφ i) a b hη.le)
              (Finset.sum_le_sum fun j _ => volume_stripX_le (hψ j) c d hη.le)
        _ = ENNReal.ofReal (2 * η * B) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (by positivity) (sub_nonneg.2 hab)))
                (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.2 hcd)))]
            congr 1
            rw [hBdef]
            ring
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := R \ K) hRm sdiff_subset
      fun p hp => by
        have hpK : p ∈ K := by
          rcases hp with ⟨hpR, hpn⟩
          by_contra hK
          exact hpn ⟨hpR, hK⟩
        show f p.1 p.2 - g p = 0
        rw [hgf p hpK, sub_self]]
    have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := R \ K)
      (f := fun p : ℝ × ℝ => f p.1 p.2 - g p) (C := 2 * M)
      ((measure_mono sdiff_subset).trans_lt hRfin) fun p hp => by
        rw [Real.norm_eq_abs]
        calc |f p.1 p.2 - g p| ≤ |f p.1 p.2| + |g p| := abs_sub _ _
          _ ≤ M + M := add_le_add (hM p hp.1) (hgM p)
          _ = 2 * M := by ring
    rw [Real.norm_eq_abs] at hbound
    refine hbound.trans ?_
    have hreal : volume.real (R \ K) ≤ 2 * η * B :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
    calc 2 * M * volume.real (R \ K) ≤ 2 * M * (2 * η * B) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = 4 * M * η * B := by ring
  -- conclusion
  have hSg : |doubleRiemannSum (fun x y => g (x, y)) P Q τ - ∫ p in R, g p| < ε / 3 :=
    hg' P Q τ hτ fun j hj k hk => (hmesh j hj k hk).trans_le hδg'
  calc |doubleRiemannSum f P Q τ - ∫ p in R, f p.1 p.2|
      = |(doubleRiemannSum f P Q τ - doubleRiemannSum (fun x y => g (x, y)) P Q τ) +
          (doubleRiemannSum (fun x y => g (x, y)) P Q τ - ∫ p in R, g p) +
          ((∫ p in R, g p) - ∫ p in R, f p.1 p.2)| := by ring_nf
    _ ≤ |doubleRiemannSum f P Q τ - doubleRiemannSum (fun x y => g (x, y)) P Q τ| +
          |doubleRiemannSum (fun x y => g (x, y)) P Q τ - ∫ p in R, g p| +
          |(∫ p in R, g p) - ∫ p in R, f p.1 p.2| := abs_add_three _ _ _
    _ < ε := by
        rw [abs_sub_comm (∫ p in R, g p)]
        linarith

/-- The extension by zero of a function continuous on the region `D` of 1.5.30 is piecewise
continuous on any rectangle `[a, b] × [c, d]`: its discontinuities lie along `y = φ₁(x)`,
`y = φ₂(x)`, `x = a` and `x = b`. -/
theorem isPiecewiseContinuousRect_extendByZero_regionX {f : ℝ → ℝ → ℝ} {a b : ℝ} (c d : ℝ)
    {φ₁ φ₂ : ℝ → ℝ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (hf : ContinuousOn (uncurry f) (regionX a b φ₁ φ₂)) :
    IsPiecewiseContinuousRect (extendByZero (regionX a b φ₁ φ₂) f) a b c d := by
  set D := regionX a b φ₁ φ₂ with hD
  obtain ⟨M, hM⟩ := (isCompact_regionX hφ₁ hφ₂).exists_bound_of_continuousOn hf
  have hext : uncurry (extendByZero D f) = D.indicator (uncurry f) := funext fun p => rfl
  refine ⟨⟨max M 0, fun p _ => ?_⟩, 2, ![φ₁, φ₂], 2, ![fun _ => a, fun _ => b],
    fun i => by fin_cases i <;> simp [hφ₁, hφ₂], fun j => by fin_cases j <;> exact continuous_const,
    ?_⟩
  · show |D.indicator (uncurry f) p| ≤ max M 0
    by_cases hp : p ∈ D
    · rw [indicator_of_mem hp]
      have := hM p hp
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [indicator_of_notMem hp, abs_zero]
      exact le_max_right _ _
  · intro p hp h1 h2
    have hφ1 : p.2 ≠ φ₁ p.1 := by simpa using h1 0
    have hφ2 : p.2 ≠ φ₂ p.1 := by simpa using h1 1
    have ha : p.1 ≠ a := by simpa using h2 0
    have hb : p.1 ≠ b := by simpa using h2 1
    rw [hext]
    refine ContinuousAt.continuousWithinAt ?_
    rcases lt_or_gt_of_ne hφ1 with hlt | hgt
    · -- below the graph of `φ₁`: `f* = 0` nearby
      have hW : IsOpen {q : ℝ × ℝ | q.2 < φ₁ q.1} :=
        isOpen_lt continuous_snd (hφ₁.comp continuous_fst)
      refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hW.mem_nhds hlt) fun q hq => ?_)
      exact indicator_of_notMem (fun hqD => absurd hq (not_lt.mpr hqD.2.2.1)) _
    rcases lt_or_gt_of_ne hφ2 with hlt2 | hgt2
    · -- strictly between the graphs with `a < x < b`: `f* = f` nearby
      have hpa : a < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm ha)
      have hpb : p.1 < b := lt_of_le_of_ne hp.1.2 hb
      set V := {q : ℝ × ℝ | a < q.1 ∧ q.1 < b ∧ φ₁ q.1 < q.2 ∧ q.2 < φ₂ q.1} with hV
      have hVo : IsOpen V := by
        simp only [hV, ofPred_and]
        exact (isOpen_lt continuous_const continuous_fst).inter
          ((isOpen_lt continuous_fst continuous_const).inter
            ((isOpen_lt (hφ₁.comp continuous_fst) continuous_snd).inter
              (isOpen_lt continuous_snd (hφ₂.comp continuous_fst))))
      have hpV : p ∈ V := ⟨hpa, hpb, hgt, hlt2⟩
      have hVD : V ⊆ D := fun q hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩
      have hcont : ContinuousAt (uncurry f) p :=
        (hf p (hVD hpV)).continuousAt (Filter.mem_of_superset (hVo.mem_nhds hpV) hVD)
      exact hcont.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hVo.mem_nhds hpV)
        fun q hq => indicator_of_mem (hVD hq) _)
    · -- above the graph of `φ₂`
      have hW : IsOpen {q : ℝ × ℝ | φ₂ q.1 < q.2} :=
        isOpen_lt (hφ₂.comp continuous_fst) continuous_snd
      refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hW.mem_nhds hgt2) fun q hq => ?_)
      exact indicator_of_notMem (fun hqD => absurd hq (not_lt.mpr hqD.2.2.2)) _

/-- Likewise for the region `D` of 1.5.33 (discontinuities along `x = ψ₁(y)`, `x = ψ₂(y)`,
`y = c`, `y = d`). -/
theorem isPiecewiseContinuousRect_extendByZero_regionY {f : ℝ → ℝ → ℝ} (a b : ℝ) {c d : ℝ}
    {ψ₁ ψ₂ : ℝ → ℝ} (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂)
    (hf : ContinuousOn (uncurry f) (regionY c d ψ₁ ψ₂)) :
    IsPiecewiseContinuousRect (extendByZero (regionY c d ψ₁ ψ₂) f) a b c d := by
  set D := regionY c d ψ₁ ψ₂ with hD
  obtain ⟨M, hM⟩ := (isCompact_regionY hψ₁ hψ₂).exists_bound_of_continuousOn hf
  have hext : uncurry (extendByZero D f) = D.indicator (uncurry f) := funext fun p => rfl
  refine ⟨⟨max M 0, fun p _ => ?_⟩, 2, ![fun _ => c, fun _ => d], 2, ![ψ₁, ψ₂],
    fun i => by fin_cases i <;> exact continuous_const, fun j => by fin_cases j <;> simp [hψ₁, hψ₂],
    ?_⟩
  · show |D.indicator (uncurry f) p| ≤ max M 0
    by_cases hp : p ∈ D
    · rw [indicator_of_mem hp]
      have := hM p hp
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [indicator_of_notMem hp, abs_zero]
      exact le_max_right _ _
  · intro p hp h1 h2
    have hc : p.2 ≠ c := by simpa using h1 0
    have hd : p.2 ≠ d := by simpa using h1 1
    have hψ1 : p.1 ≠ ψ₁ p.2 := by simpa using h2 0
    have hψ2 : p.1 ≠ ψ₂ p.2 := by simpa using h2 1
    rw [hext]
    refine ContinuousAt.continuousWithinAt ?_
    rcases lt_or_gt_of_ne hψ1 with hlt | hgt
    · have hW : IsOpen {q : ℝ × ℝ | q.1 < ψ₁ q.2} :=
        isOpen_lt continuous_fst (hψ₁.comp continuous_snd)
      refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hW.mem_nhds hlt) fun q hq => ?_)
      exact indicator_of_notMem (fun hqD => absurd hq (not_lt.mpr hqD.2.2.1)) _
    rcases lt_or_gt_of_ne hψ2 with hlt2 | hgt2
    · have hpc : c < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hc)
      have hpd : p.2 < d := lt_of_le_of_ne hp.2.2 hd
      set V := {q : ℝ × ℝ | c < q.2 ∧ q.2 < d ∧ ψ₁ q.2 < q.1 ∧ q.1 < ψ₂ q.2} with hV
      have hVo : IsOpen V := by
        simp only [hV, ofPred_and]
        exact (isOpen_lt continuous_const continuous_snd).inter
          ((isOpen_lt continuous_snd continuous_const).inter
            ((isOpen_lt (hψ₁.comp continuous_snd) continuous_fst).inter
              (isOpen_lt continuous_fst (hψ₂.comp continuous_snd))))
      have hpV : p ∈ V := ⟨hpc, hpd, hgt, hlt2⟩
      have hVD : V ⊆ D := fun q hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩
      have hcont : ContinuousAt (uncurry f) p :=
        (hf p (hVD hpV)).continuousAt (Filter.mem_of_superset (hVo.mem_nhds hpV) hVD)
      exact hcont.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hVo.mem_nhds hpV)
        fun q hq => indicator_of_mem (hVD hq) _)
    · have hW : IsOpen {q : ℝ × ℝ | ψ₂ q.2 < q.1} :=
        isOpen_lt (hψ₂.comp continuous_snd) continuous_fst
      refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hW.mem_nhds hgt2) fun q hq => ?_)
      exact indicator_of_notMem (fun hqD => absurd hq (not_lt.mpr hqD.2.2.2)) _

/-- **DLMF 1.5.29 and 1.5.31, Riemann form**: for `f` continuous on
`D = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` (`φ₁ ≤ φ₂` continuous) inside `R = [a, b] × [c, d]`, the
double Riemann integral `∬_R f* dA` exists, and equals `∬_D f dA = ∫_a^b ∫_{φ₁}^{φ₂} f dy dx`. -/
theorem dlmf_1_5_31_riemann {f : ℝ → ℝ → ℝ} {a b c d : ℝ} {φ₁ φ₂ : ℝ → ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hle : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x)
    (hc : ∀ x ∈ Icc a b, c ≤ φ₁ x) (hd : ∀ x ∈ Icc a b, φ₂ x ≤ d)
    (hf : ContinuousOn (uncurry f) (regionX a b φ₁ φ₂)) :
    HasDoubleRiemannIntegralOn (regionX a b φ₁ φ₂) f a b c d
        (∫ p in regionX a b φ₁ φ₂, f p.1 p.2) ∧
      ∫ p in regionX a b φ₁ φ₂, f p.1 p.2 = ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, f x y := by
  refine ⟨?_, dlmf_1_5_31 hab hφ₁ hφ₂ hle hf⟩
  have hDR : regionX a b φ₁ φ₂ ⊆ Icc a b ×ˢ Icc c d := fun p hp =>
    ⟨⟨hp.1, hp.2.1⟩, (hc _ ⟨hp.1, hp.2.1⟩).trans hp.2.2.1, hp.2.2.2.trans (hd _ ⟨hp.1, hp.2.1⟩)⟩
  have := dlmf_1_5_27_piecewise hab hcd
    (isPiecewiseContinuousRect_extendByZero_regionX c d hφ₁ hφ₂ hf)
  unfold HasDoubleRiemannIntegralOn
  rwa [dlmf_1_5_29 (isCompact_regionX hφ₁ hφ₂).isClosed.measurableSet hDR] at this

/-- **DLMF 1.5.29 and 1.5.34, Riemann form**: likewise for
`D = {c ≤ y ≤ d, ψ₁(y) ≤ x ≤ ψ₂(y)}` inside `[a, b] × [c, d]`. -/
theorem dlmf_1_5_34_riemann {f : ℝ → ℝ → ℝ} {a b c d : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂) (hle : ∀ y ∈ Icc c d, ψ₁ y ≤ ψ₂ y)
    (ha : ∀ y ∈ Icc c d, a ≤ ψ₁ y) (hb : ∀ y ∈ Icc c d, ψ₂ y ≤ b)
    (hf : ContinuousOn (uncurry f) (regionY c d ψ₁ ψ₂)) :
    HasDoubleRiemannIntegralOn (regionY c d ψ₁ ψ₂) f a b c d
        (∫ p in regionY c d ψ₁ ψ₂, f p.1 p.2) ∧
      ∫ p in regionY c d ψ₁ ψ₂, f p.1 p.2 = ∫ y in c..d, ∫ x in ψ₁ y..ψ₂ y, f x y := by
  refine ⟨?_, dlmf_1_5_34 hcd hψ₁ hψ₂ hle hf⟩
  have hDR : regionY c d ψ₁ ψ₂ ⊆ Icc a b ×ˢ Icc c d := fun p hp =>
    ⟨⟨(ha _ ⟨hp.1, hp.2.1⟩).trans hp.2.2.1, hp.2.2.2.trans (hb _ ⟨hp.1, hp.2.1⟩)⟩, hp.1, hp.2.1⟩
  have := dlmf_1_5_27_piecewise hab hcd
    (isPiecewiseContinuousRect_extendByZero_regionY a b hψ₁ hψ₂ hf)
  unfold HasDoubleRiemannIntegralOn
  rwa [dlmf_1_5_29 (isCompact_regionY hψ₁ hψ₂).isClosed.measurableSet hDR] at this

end MultipleIntegrals

end Azurite.DLMF
