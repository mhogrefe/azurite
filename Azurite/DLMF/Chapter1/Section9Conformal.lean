/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# DLMF §1.9(iv): Conformal Mapping

Formalizations of <https://dlmf.nist.gov/1.9.iv>.  The extended plane `ℂ ∪ {∞}` is Mathlib's
one-point compactification `OnePoint ℂ`; "`w → ∞`" in `ℂ` is the filter `cobounded ℂ`
(`tendsto_coe_nhds_infty_iff` links the two).

* 1.9.35: `diskAtInfty r = {|z| > 1/r} ∪ {∞}`; `dlmf_1_9_35` (the `S_r` form a neighbourhood
  basis of `∞`), `diskAtInfty_mem_nhds`.
* 1.9.36–1.9.39 (arithmetic with `∞`, read as limits): `dlmf_1_9_36` (`∞ ± z = z ± ∞ = ∞`),
  `dlmf_1_9_37` (`∞·z = z·∞ = ∞`, `z ≠ 0`), `dlmf_1_9_37_infty` (`∞·∞ = ∞`), `dlmf_1_9_38`
  (`z/∞ = 0`), `dlmf_1_9_39` (`z/0 = ∞`, `z ≠ 0`).
* Analyticity at `∞`: `invChart f f∞` (`g(z) = f(1/z)`, `g(0) = f(∞)`), `AnalyticAtInfty`,
  `derivInfty` (`f′(∞) = g′(0)`), `AnalyticAtInfty.tendsto` (`f → f(∞)` at `∞`).
* Conformal transformation: `tangentAngle` (signed angle between tangent directions, in
  `Real.Angle`), `dlmf_1_9_iv_conformal` (image tangents `f′(z₀) vᵢ`, signed angle preserved),
  `dlmf_1_9_iv_conformalAt` (Mathlib's `ConformalAt`), `dlmf_1_9_iv_linear` (`az + b`).
* Bilinear transformation: `mobius` (1.9.40), `mobiusExt` on `OnePoint ℂ`; `dlmf_1_9_41`
  (values and limits at the pole and at `∞`), `dlmf_1_9_42` (`f′`), `dlmf_1_9_43` (`f′(∞)`,
  analytic at `∞`), `dlmf_1_9_44` and `dlmf_1_9_44_left` (inverse), `dlmf_1_9_iv_bilinear`
  (bijective and continuous on `ℂ ∪ {∞}` with continuous inverse, conformal at finite non-pole
  points, at `∞`, and at the pole through the chart `1/w`).
* 1.9.45: `crossRatio`, `dlmf_1_9_45` (invariance under bilinear transformations, all four points
  finite with finite images), `dlmf_1_9_45_infty` (limiting form `(z₁ − z₂)/(z₃ − z₂)` as
  `z₄ → ∞`); invariance with points at `∞` (the limiting forms) is not formalized.
-/

open Complex Filter Topology Bornology Set Metric OnePoint

namespace Azurite.DLMF

/-! ### The extended complex plane -/

/-- The open disk `S_r = {z : |z| > 1/r} ∪ {∞}` around infinity. -/
def diskAtInfty (r : ℝ) : Set (OnePoint ℂ) := ((↑) '' {z : ℂ | 1 / r < ‖z‖}) ∪ {∞}

/-- **DLMF 1.9.35**: the disks `S_r`, `0 < r < ∞`, form a neighbourhood basis of `∞` in the
extended plane `ℂ ∪ {∞}` (Mathlib's one-point compactification `OnePoint ℂ`). -/
theorem dlmf_1_9_35 : (𝓝 (∞ : OnePoint ℂ)).HasBasis (fun r : ℝ => 0 < r) diskAtInfty := by
  refine hasBasis_nhds_infty.to_hasBasis (fun s ⟨_, hsk⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨R, hR⟩ := hsk.isBounded.subset_closedBall 0
    refine ⟨1 / (max R 0 + 1), by positivity, ?_⟩
    rintro p (⟨z, hz, rfl⟩ | hp)
    · refine Or.inl ⟨z, fun hzs => ?_, rfl⟩
      have h1 := hR hzs
      rw [mem_closedBall_zero_iff] at h1
      simp only [Set.mem_ofPred_eq, one_div_one_div] at hz
      linarith [le_max_left R 0]
    · exact Or.inr hp
  · refine ⟨closedBall 0 (1 / r), ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
    rintro p (⟨z, hz, rfl⟩ | hp)
    · refine Or.inl ⟨z, ?_, rfl⟩
      simpa [mem_closedBall_zero_iff, not_le] using hz
    · exact Or.inr hp

/-- Each `S_r` is a neighbourhood of `∞`. -/
theorem diskAtInfty_mem_nhds {r : ℝ} (hr : 0 < r) : diskAtInfty r ∈ 𝓝 (∞ : OnePoint ℂ) :=
  dlmf_1_9_35.mem_of_mem hr

/-- `g(x) → ∞` in `ℂ ∪ {∞}` iff `|g(x)| → ∞`. -/
theorem tendsto_coe_nhds_infty_iff {α : Type*} {l : Filter α} {g : α → ℂ} :
    Tendsto (fun x => (g x : OnePoint ℂ)) l (𝓝 ∞) ↔ Tendsto g l (cobounded ℂ) := by
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact, ← comap_coe_nhds_infty,
    tendsto_comap_iff]
  rfl

/-- **DLMF 1.9.36**: `∞ ± z = z ± ∞ = ∞` (as limits `w → ∞`). -/
theorem dlmf_1_9_36 (z : ℂ) :
    Tendsto (fun w : ℂ => ((w + z : ℂ) : OnePoint ℂ)) (cobounded ℂ) (𝓝 ∞) ∧
    Tendsto (fun w : ℂ => ((z + w : ℂ) : OnePoint ℂ)) (cobounded ℂ) (𝓝 ∞) ∧
    Tendsto (fun w : ℂ => ((w - z : ℂ) : OnePoint ℂ)) (cobounded ℂ) (𝓝 ∞) ∧
    Tendsto (fun w : ℂ => ((z - w : ℂ) : OnePoint ℂ)) (cobounded ℂ) (𝓝 ∞) := by
  simp only [tendsto_coe_nhds_infty_iff]
  exact ⟨tendsto_add_const_cobounded z, tendsto_const_add_cobounded z,
    tendsto_sub_const_cobounded z, tendsto_const_sub_cobounded z⟩

/-- **DLMF 1.9.37**: `∞ · z = z · ∞ = ∞` for `z ≠ 0`. -/
theorem dlmf_1_9_37 {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun w : ℂ => ((w * z : ℂ) : OnePoint ℂ)) (cobounded ℂ) (𝓝 ∞) ∧
    Tendsto (fun w : ℂ => ((z * w : ℂ) : OnePoint ℂ)) (cobounded ℂ) (𝓝 ∞) := by
  simp only [tendsto_coe_nhds_infty_iff]
  exact ⟨tendsto_mul_right_cobounded hz, tendsto_mul_left_cobounded hz⟩

/-- DLMF 1.9.37 with `z = ∞`: `∞ · ∞ = ∞`. -/
theorem dlmf_1_9_37_infty :
    Tendsto (fun p : ℂ × ℂ => ((p.1 * p.2 : ℂ) : OnePoint ℂ)) (cobounded ℂ ×ˢ cobounded ℂ)
      (𝓝 ∞) := by
  rw [tendsto_coe_nhds_infty_iff, ← tendsto_norm_atTop_iff_cobounded]
  simp only [norm_mul]
  exact (tendsto_norm_cobounded_atTop.comp tendsto_fst).atTop_mul_atTop₀
    (tendsto_norm_cobounded_atTop.comp tendsto_snd)

/-- **DLMF 1.9.38**: `z/∞ = 0`. -/
theorem dlmf_1_9_38 (z : ℂ) : Tendsto (fun w : ℂ => z / w) (cobounded ℂ) (𝓝 0) := by
  have := (tendsto_inv₀_cobounded (α := ℂ)).const_mul z
  rw [mul_zero] at this
  exact this.congr fun w => (div_eq_mul_inv z w).symm

/-- **DLMF 1.9.39**: `z/0 = ∞` for `z ≠ 0`. -/
theorem dlmf_1_9_39 {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun w : ℂ => ((z / w : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
  rw [tendsto_coe_nhds_infty_iff]
  exact ((tendsto_mul_left_cobounded hz).comp tendsto_inv₀_nhdsNE_zero).congr fun w =>
    (div_eq_mul_inv z w).symm

/-! ### Analyticity at infinity -/

/-- The chart `g(z) = f(1/z)` at `∞`, with `g(0) = f(∞)`. -/
noncomputable def invChart (f : ℂ → ℂ) (fInf : ℂ) (z : ℂ) : ℂ := if z = 0 then fInf else f z⁻¹

/-- `f` (with value `f(∞) = fInf`) is analytic at `∞` if `g(z) = f(1/z)` is analytic at `0`. -/
def AnalyticAtInfty (f : ℂ → ℂ) (fInf : ℂ) : Prop := AnalyticAt ℂ (invChart f fInf) 0

/-- `f′(∞) = g′(0)`. -/
noncomputable def derivInfty (f : ℂ → ℂ) (fInf : ℂ) : ℂ := deriv (invChart f fInf) 0

theorem eventually_ne_zero_cobounded : ∀ᶠ w in cobounded ℂ, w ≠ 0 := by
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with w hw
  exact norm_pos_iff.mp hw

/-- An analytic function at `∞` has limit `f(∞)` at `∞`. -/
theorem AnalyticAtInfty.tendsto {f : ℂ → ℂ} {fInf : ℂ} (h : AnalyticAtInfty f fInf) :
    Tendsto f (cobounded ℂ) (𝓝 fInf) := by
  have h1 : Tendsto (fun w => invChart f fInf w⁻¹) (cobounded ℂ) (𝓝 fInf) := by
    have := h.continuousAt.tendsto.comp (tendsto_inv₀_cobounded (α := ℂ))
    have h0 : invChart f fInf 0 = fInf := by simp [invChart]
    rw [h0] at this
    exact this
  refine h1.congr' ?_
  filter_upwards [eventually_ne_zero_cobounded] with w hw
  simp [invChart, hw]

/-! ### Conformal transformations -/

/-- The signed angle from the direction `v` to the direction `w`. -/
noncomputable def tangentAngle (v w : ℂ) : Real.Angle := (arg w : Real.Angle) - arg v

/-- **Conformal transformation** (DLMF §1.9(iv)): if `f′(z₀) ≠ 0`, arcs `C₁`, `C₂` through `z₀`
with tangents `v₁`, `v₂` are mapped to arcs with tangents `f′(z₀) vᵢ`, and the signed angle
between the tangents is preserved (magnitude and sense). -/
theorem dlmf_1_9_iv_conformal {f : ℂ → ℂ} {z₀ : ℂ} (hf : DifferentiableAt ℂ f z₀)
    (hf' : deriv f z₀ ≠ 0) {γ₁ γ₂ : ℝ → ℂ} {t₁ t₂ : ℝ} {v₁ v₂ : ℂ} (h₁ : HasDerivAt γ₁ v₁ t₁)
    (h₂ : HasDerivAt γ₂ v₂ t₂) (hγ₁ : γ₁ t₁ = z₀) (hγ₂ : γ₂ t₂ = z₀) (hv₁ : v₁ ≠ 0)
    (hv₂ : v₂ ≠ 0) :
    HasDerivAt (f ∘ γ₁) (deriv f z₀ * v₁) t₁ ∧ HasDerivAt (f ∘ γ₂) (deriv f z₀ * v₂) t₂ ∧
      tangentAngle (deriv f z₀ * v₁) (deriv f z₀ * v₂) = tangentAngle v₁ v₂ := by
  have hf₁ : HasDerivAt f (deriv f z₀) (γ₁ t₁) := by rw [hγ₁]; exact hf.hasDerivAt
  have hf₂ : HasDerivAt f (deriv f z₀) (γ₂ t₂) := by rw [hγ₂]; exact hf.hasDerivAt
  refine ⟨hf₁.comp t₁ h₁, hf₂.comp t₂ h₂, ?_⟩
  unfold tangentAngle
  rw [arg_mul_coe_angle hf' hv₂, arg_mul_coe_angle hf' hv₁]
  abel

/-- `f′(z₀) ≠ 0` makes `f` conformal at `z₀` in Mathlib's sense. -/
theorem dlmf_1_9_iv_conformalAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : DifferentiableAt ℂ f z₀)
    (hf' : deriv f z₀ ≠ 0) : ConformalAt f z₀ :=
  hf.conformalAt hf'

/-- The linear transformation `f(z) = az + b`, `a ≠ 0`: `f′ = a`, and `f` maps `ℂ` bijectively
and conformally onto `ℂ`. -/
theorem dlmf_1_9_iv_linear {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (∀ z, HasDerivAt (fun z => a * z + b) a z) ∧ Function.Bijective (fun z => a * z + b) ∧
      ∀ z, ConformalAt (fun z => a * z + b) z := by
  have hd : ∀ z, HasDerivAt (fun z => a * z + b) a z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul a).add_const b
  refine ⟨hd, Function.bijective_iff_has_inverse.mpr ⟨fun w => (w - b) / a, fun z => ?_,
    fun w => ?_⟩, fun z => (hd z).differentiableAt.conformalAt (by rw [(hd z).deriv]; exact ha)⟩
  · field_simp
    ring
  · field_simp
    ring

/-! ### Bilinear transformations -/

/-- **DLMF 1.9.40**: the bilinear (Möbius) transformation `w = (az + b)/(cz + d)`. -/
noncomputable def mobius (a b c d z : ℂ) : ℂ := (a * z + b) / (c * z + d)

/-- The bilinear transformation on the extended plane: `f(−d/c) = ∞`, `f(∞) = a/c`. -/
noncomputable def mobiusExt (a b c d : ℂ) (p : OnePoint ℂ) : OnePoint ℂ :=
  OnePoint.elim p ((a / c : ℂ) : OnePoint ℂ) fun z =>
    if c * z + d = 0 then ∞ else ((mobius a b c d z : ℂ) : OnePoint ℂ)

@[simp] theorem mobiusExt_infty (a b c d : ℂ) : mobiusExt a b c d ∞ = ((a / c : ℂ) : OnePoint ℂ) :=
  rfl

theorem mobiusExt_coe (a b c d z : ℂ) : mobiusExt a b c d z =
    if c * z + d = 0 then ∞ else ((mobius a b c d z : ℂ) : OnePoint ℂ) :=
  rfl

theorem mobiusExt_coe_of_ne {a b c d z : ℂ} (h : c * z + d ≠ 0) :
    mobiusExt a b c d z = ((mobius a b c d z : ℂ) : OnePoint ℂ) := by
  simp only [mobiusExt_coe, h, ↓reduceIte]

variable {a b c d : ℂ}

theorem mul_neg_div_add {c d : ℂ} (hc : c ≠ 0) : c * (-d / c) + d = 0 := by
  field_simp
  ring

theorem eq_neg_div_of_mul_add_eq_zero (hc : c ≠ 0) {z : ℂ} (h : c * z + d = 0) : z = -d / c := by
  field_simp
  linear_combination h

/-- The bilinear transformation tends to `∞` at its pole `−d/c`. -/
theorem tendsto_mobius_pole (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Tendsto (fun z => ((mobius a b c d z : ℂ) : OnePoint ℂ)) (𝓝[≠] (-d / c)) (𝓝 ∞) := by
  rw [tendsto_coe_nhds_infty_iff, ← tendsto_norm_atTop_iff_cobounded]
  have hnum : a * (-d / c) + b ≠ 0 := by
    intro h
    apply hdet
    field_simp at h
    linear_combination -h
  have hden : Tendsto (fun z => c * z + d) (𝓝[≠] (-d / c)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((by fun_prop : Continuous fun z : ℂ => c * z + d).tendsto (-d / c)).mono_left
        (nhdsWithin_le_nhds (s := {-d / c}ᶜ))
      simpa [mul_neg_div_add hc] using this
    · filter_upwards [self_mem_nhdsWithin] with z hz h0
      exact hz (eq_neg_div_of_mul_add_eq_zero hc h0)
  have h1 : Tendsto (fun z => ‖a * z + b‖) (𝓝[≠] (-d / c)) (𝓝 ‖a * (-d / c) + b‖) :=
    (((by fun_prop : Continuous fun z : ℂ => a * z + b)).norm.tendsto _).mono_left
      nhdsWithin_le_nhds
  have h2 : Tendsto (fun z => ‖(c * z + d)⁻¹‖) (𝓝[≠] (-d / c)) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp hden)
  have := h1.pos_mul_atTop (norm_pos_iff.mpr hnum) h2
  simpa [mobius, div_eq_mul_inv, norm_mul] using this

/-- The bilinear transformation tends to `a/c` at `∞`. -/
theorem tendsto_mobius_infty (hc : c ≠ 0) :
    Tendsto (mobius a b c d) (cobounded ℂ) (𝓝 (a / c)) := by
  have h : Tendsto (fun z => (a + b * z⁻¹) / (c + d * z⁻¹)) (cobounded ℂ) (𝓝 (a / c)) := by
    have hi := tendsto_inv₀_cobounded (α := ℂ)
    have := ((tendsto_const_nhds (x := a)).add (hi.const_mul b)).div
      ((tendsto_const_nhds (x := c)).add (hi.const_mul d)) (by simpa using hc)
    simp only [mul_zero, add_zero] at this
    exact this
  refine h.congr' ?_
  filter_upwards [eventually_ne_zero_cobounded] with z hz
  rw [mobius, show a + b * z⁻¹ = (a * z + b) / z by field_simp,
    show c + d * z⁻¹ = (c * z + d) / z by field_simp, div_div_div_cancel_right₀ hz]

/-- **DLMF 1.9.41**: `f(−d/c) = ∞`, `f(∞) = a/c`, both as values of the extended map and as
limits. -/
theorem dlmf_1_9_41 (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) :
    mobiusExt a b c d ((-d / c : ℂ) : OnePoint ℂ) = ∞ ∧
    mobiusExt a b c d ∞ = ((a / c : ℂ) : OnePoint ℂ) ∧
    Tendsto (fun z => ((mobius a b c d z : ℂ) : OnePoint ℂ)) (𝓝[≠] (-d / c)) (𝓝 ∞) ∧
    Tendsto (mobius a b c d) (cobounded ℂ) (𝓝 (a / c)) :=
  ⟨by simp only [mobiusExt_coe, mul_neg_div_add hc, ↓reduceIte], rfl, tendsto_mobius_pole hc hdet,
    tendsto_mobius_infty hc⟩

/-- **DLMF 1.9.42**: `f′(z) = (ad − bc)/(cz + d)²`, `z ≠ −d/c`. -/
theorem dlmf_1_9_42 {z : ℂ} (hz : c * z + d ≠ 0) :
    HasDerivAt (mobius a b c d) ((a * d - b * c) / (c * z + d) ^ 2) z := by
  have h := (((hasDerivAt_id z).const_mul a).add_const b).div
    (((hasDerivAt_id z).const_mul c).add_const d) hz
  exact h.congr_deriv (by simp only [id]; ring)

/-- `f(1/z) = (a + bz)/(c + dz)`, with value `a/c` at `0`. -/
theorem invChart_mobius (a b c d : ℂ) :
    invChart (mobius a b c d) (a / c) = fun z => (a + b * z) / (c + d * z) := by
  funext z
  by_cases hz : z = 0
  · simp [invChart, hz]
  · simp only [invChart, hz, ↓reduceIte]
    rw [mobius, show a * z⁻¹ + b = (a + b * z) / z by field_simp,
      show c * z⁻¹ + d = (c + d * z) / z by field_simp, div_div_div_cancel_right₀ hz]

/-- **DLMF 1.9.43**: `f` is analytic at `∞` and `f′(∞) = (bc − ad)/c²`. -/
theorem dlmf_1_9_43 (hc : c ≠ 0) :
    HasDerivAt (invChart (mobius a b c d) (a / c)) ((b * c - a * d) / c ^ 2) 0 ∧
      AnalyticAtInfty (mobius a b c d) (a / c) ∧
      derivInfty (mobius a b c d) (a / c) = (b * c - a * d) / c ^ 2 := by
  have hden : c + d * 0 ≠ 0 := by simpa using hc
  have h := ((((hasDerivAt_id (0 : ℂ)).const_mul b).const_add a).div
    (((hasDerivAt_id (0 : ℂ)).const_mul d).const_add c) hden)
  have hd : HasDerivAt (invChart (mobius a b c d) (a / c)) ((b * c - a * d) / c ^ 2) 0 := by
    rw [invChart_mobius]
    exact h.congr_deriv (by simp only [id]; ring)
  refine ⟨hd, ?_, hd.deriv⟩
  unfold AnalyticAtInfty
  rw [invChart_mobius]
  have hden' : ∀ᶠ z in 𝓝 (0 : ℂ), c + d * z ≠ 0 :=
    (by fun_prop : Continuous fun z : ℂ => c + d * z).continuousAt.eventually_ne hden
  refine (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) hden

/-- **DLMF 1.9.44**: the inverse transformation `z = (dw − b)/(−cw + a)`. -/
theorem dlmf_1_9_44 (hdet : a * d - b * c ≠ 0) {w : ℂ} (hw : -c * w + a ≠ 0) :
    c * ((d * w - b) / (-c * w + a)) + d ≠ 0 ∧
      mobius a b c d ((d * w - b) / (-c * w + a)) = w := by
  have e : -c * w + a = a - c * w := by ring
  have hw' : a - c * w ≠ 0 := e ▸ hw
  rw [e]
  have h1 : c * ((d * w - b) / (a - c * w)) + d = (a * d - b * c) / (a - c * w) := by
    field_simp
    ring
  have hden : c * ((d * w - b) / (a - c * w)) + d ≠ 0 := by
    rw [h1]
    exact div_ne_zero hdet hw'
  refine ⟨hden, ?_⟩
  rw [mobius, div_eq_iff hden, h1, mul_div_assoc', mul_div_assoc', div_add' _ _ _ hw',
    div_left_inj' hw']
  ring

/-- DLMF 1.9.44, the other composition. -/
theorem dlmf_1_9_44_left (hdet : a * d - b * c ≠ 0) {z : ℂ} (hz : c * z + d ≠ 0) :
    -c * mobius a b c d z + a ≠ 0 ∧
      (d * mobius a b c d z - b) / (-c * mobius a b c d z + a) = z := by
  have h1 : -c * mobius a b c d z + a = (a * d - b * c) / (c * z + d) := by
    rw [mobius]
    field_simp
    ring
  have hne : -c * mobius a b c d z + a ≠ 0 := by
    rw [h1]
    exact div_ne_zero hdet hz
  refine ⟨hne, ?_⟩
  rw [div_eq_iff hne, h1, mobius, mul_div_assoc', mul_div_assoc', eq_div_iff hz, sub_mul,
    div_mul_cancel₀ _ hz]
  ring

/-- The extended bilinear transformation with coefficients `(d, −b, −c, a)` undoes `f`. -/
theorem mobiusExt_leftInverse (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Function.LeftInverse (mobiusExt d (-b) (-c) a) (mobiusExt a b c d) := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    have h0 : -c * (a / c) + a = 0 := by field_simp; ring
    simp only [mobiusExt_infty, mobiusExt_coe, h0, ↓reduceIte]
  | coe z =>
    by_cases hz : c * z + d = 0
    · simp only [mobiusExt_coe, hz, ↓reduceIte, mobiusExt_infty]
      rw [eq_neg_div_of_mul_add_eq_zero hc hz, div_neg, neg_div]
    · rw [mobiusExt_coe_of_ne hz]
      obtain ⟨hne, heq⟩ := dlmf_1_9_44_left hdet hz
      rw [mobiusExt_coe_of_ne (by simpa using hne)]
      exact congrArg _ heq

theorem continuous_mobiusExt (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Continuous (mobiusExt a b c d) := by
  have hmc : ∀ z, c * z + d ≠ 0 → ContinuousAt (mobius a b c d) z := fun z hz =>
    (by fun_prop : Continuous fun z : ℂ => a * z + b).continuousAt.div
      (by fun_prop : Continuous fun z : ℂ => c * z + d).continuousAt hz
  rw [OnePoint.continuous_iff]
  refine ⟨?_, continuous_iff_continuousAt.mpr fun z => ?_⟩
  · rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact, mobiusExt_infty]
    have hev : ∀ᶠ x in cobounded ℂ, c * x + d ≠ 0 := by
      have := tendsto_add_const_cobounded (R := ℂ) d |>.comp (tendsto_mul_left_cobounded hc)
      exact this.eventually eventually_ne_zero_cobounded
    refine ((continuous_coe.tendsto _).comp (tendsto_mobius_infty (b := b) (d := d) hc)).congr' ?_
    filter_upwards [hev] with x hx
    rw [Function.comp_apply, mobiusExt_coe_of_ne hx]
  · by_cases hz : c * z + d = 0
    · have hv : mobiusExt a b c d z = ∞ := by
        simp only [mobiusExt_coe, hz, ↓reduceIte]
      rw [continuousAt_iff_punctured_nhds, hv]
      have hz' := eq_neg_div_of_mul_add_eq_zero hc hz
      subst hz'
      refine (tendsto_mobius_pole hc hdet).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [mobiusExt_coe_of_ne fun h => hx (eq_neg_div_of_mul_add_eq_zero hc h)]
    · have hev : ∀ᶠ x in 𝓝 z, c * x + d ≠ 0 :=
        (by fun_prop : Continuous fun z : ℂ => c * z + d).continuousAt.eventually_ne hz
      refine ((continuous_coe.continuousAt).comp (hmc z hz)).congr ?_
      filter_upwards [hev] with x hx
      rw [Function.comp_apply, mobiusExt_coe_of_ne hx]

/-- DLMF §1.9(iv): the bilinear transformation is a one-to-one continuous map of `ℂ ∪ {∞}` onto
itself (a homeomorphism, with inverse the bilinear transformation of 1.9.44), conformal at every
finite non-pole point (`f′ ≠ 0`, 1.9.42), at `∞` (`f′(∞) ≠ 0`, 1.9.43) and at the pole (where
`1/f`, a bilinear transformation, has nonzero derivative). -/
theorem dlmf_1_9_iv_bilinear (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Function.Bijective (mobiusExt a b c d) ∧ Continuous (mobiusExt a b c d) ∧
    Continuous (mobiusExt d (-b) (-c) a) ∧
    (∀ z, c * z + d ≠ 0 → ConformalAt (mobius a b c d) z) ∧
    derivInfty (mobius a b c d) (a / c) ≠ 0 ∧
    HasDerivAt (fun z => (mobius a b c d z)⁻¹)
      ((c * b - d * a) / (a * (-d / c) + b) ^ 2) (-d / c) ∧
    (c * b - d * a) / (a * (-d / c) + b) ^ 2 ≠ 0 := by
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  have hdet' : d * a - -b * -c ≠ 0 := by
    intro h
    apply hdet
    linear_combination h
  have hL := mobiusExt_leftInverse hc hdet
  have hR : Function.RightInverse (mobiusExt d (-b) (-c) a) (mobiusExt a b c d) := by
    intro p
    have := mobiusExt_leftInverse hc' hdet' p
    simpa only [neg_neg] using this
  have hnum : a * (-d / c) + b ≠ 0 := by
    intro h
    apply hdet
    field_simp at h
    linear_combination -h
  refine ⟨⟨hL.injective, hR.surjective⟩, continuous_mobiusExt hc hdet,
    continuous_mobiusExt hc' hdet', fun z hz => ?_, ?_, ?_, ?_⟩
  · exact (dlmf_1_9_42 hz).differentiableAt.conformalAt
      (by rw [(dlmf_1_9_42 hz).deriv]; exact div_ne_zero hdet (pow_ne_zero _ hz))
  · rw [(dlmf_1_9_43 hc).2.2]
    refine div_ne_zero (fun h => hdet ?_) (pow_ne_zero _ hc)
    linear_combination -h
  · have hinv : (fun z => (mobius a b c d z)⁻¹) = mobius c d a b := by
      funext z
      rw [mobius, mobius, inv_div]
    rw [hinv]
    exact dlmf_1_9_42 hnum
  · refine div_ne_zero (fun h => hdet ?_) (pow_ne_zero _ hnum)
    linear_combination -h

/-! ### Cross ratio -/

/-- **DLMF 1.9.45**: the cross ratio `(z₁ − z₂)(z₃ − z₄)/((z₁ − z₄)(z₃ − z₂))`. -/
noncomputable def crossRatio (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  (z₁ - z₂) * (z₃ - z₄) / ((z₁ - z₄) * (z₃ - z₂))

theorem mobius_sub_mobius {z w : ℂ} (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    mobius a b c d z - mobius a b c d w =
      (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  rw [mobius, mobius, div_sub_div _ _ hz hw]
  congr 1
  ring

/-- DLMF §1.9(iv): the cross ratio is invariant under bilinear transformations. -/
theorem dlmf_1_9_45 (hdet : a * d - b * c ≠ 0) {z₁ z₂ z₃ z₄ : ℂ} (h₁ : c * z₁ + d ≠ 0)
    (h₂ : c * z₂ + d ≠ 0) (h₃ : c * z₃ + d ≠ 0) (h₄ : c * z₄ + d ≠ 0) :
    crossRatio (mobius a b c d z₁) (mobius a b c d z₂) (mobius a b c d z₃) (mobius a b c d z₄) =
      crossRatio z₁ z₂ z₃ z₄ := by
  set K := (a * d - b * c) ^ 2 / ((c * z₁ + d) * (c * z₂ + d) * (c * z₃ + d) * (c * z₄ + d))
    with hKdef
  have hK : K ≠ 0 := div_ne_zero (pow_ne_zero _ hdet)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h₁ h₂) h₃) h₄)
  have hn : (mobius a b c d z₁ - mobius a b c d z₂) * (mobius a b c d z₃ - mobius a b c d z₄) =
      K * ((z₁ - z₂) * (z₃ - z₄)) := by
    rw [mobius_sub_mobius h₁ h₂, mobius_sub_mobius h₃ h₄, div_mul_div_comm, hKdef,
      div_mul_eq_mul_div]
    congr 1 <;> ring
  have hd : (mobius a b c d z₁ - mobius a b c d z₄) * (mobius a b c d z₃ - mobius a b c d z₂) =
      K * ((z₁ - z₄) * (z₃ - z₂)) := by
    rw [mobius_sub_mobius h₁ h₄, mobius_sub_mobius h₃ h₂, div_mul_div_comm, hKdef,
      div_mul_eq_mul_div]
    congr 1 <;> ring
  rw [crossRatio, crossRatio, hn, hd, mul_div_mul_left _ _ hK]

/-- The limiting form of the cross ratio as `z₄ → ∞`: `(z₁ − z₂)/(z₃ − z₂)`. -/
theorem dlmf_1_9_45_infty (z₁ z₂ z₃ : ℂ) :
    Tendsto (fun z₄ => crossRatio z₁ z₂ z₃ z₄) (cobounded ℂ) (𝓝 ((z₁ - z₂) / (z₃ - z₂))) := by
  have h : Tendsto (fun z₄ : ℂ => (z₁ - z₂) / (z₃ - z₂) * ((z₃ * z₄⁻¹ - 1) / (z₁ * z₄⁻¹ - 1)))
      (cobounded ℂ) (𝓝 ((z₁ - z₂) / (z₃ - z₂))) := by
    have hi := tendsto_inv₀_cobounded (α := ℂ)
    have := tendsto_const_nhds (x := (z₁ - z₂) / (z₃ - z₂)) |>.mul
      (((hi.const_mul z₃).sub_const 1).div ((hi.const_mul z₁).sub_const 1) (by simp))
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_ne_zero_cobounded] with z₄ hz
  rw [crossRatio, show z₃ * z₄⁻¹ - 1 = (z₃ - z₄) / z₄ by field_simp,
    show z₁ * z₄⁻¹ - 1 = (z₁ - z₄) / z₄ by field_simp, div_div_div_cancel_right₀ hz,
    div_mul_div_comm, mul_comm (z₃ - z₂)]

end Azurite.DLMF
