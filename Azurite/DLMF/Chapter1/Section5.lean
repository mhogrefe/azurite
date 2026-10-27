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

end Azurite.DLMF
