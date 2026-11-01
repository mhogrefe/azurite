/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18L2
import Azurite.DLMF.Chapter1.Section18Plemelj
import Azurite.DLMF.Chapter1.Section14HilbertLebesgue

/-!
# DLMF §1.18(vi): Continuous spectra — general results

https://dlmf.nist.gov/1.18.vi

The "General Results" subsection. DLMF's eigenfunctions `φ_λ` of the continuous spectrum
`σ_c = [0, ∞)` are not in `L²`, so its formulas are formal. They are made rigorous through the
generalized eigenfunction transform `U : V ≃ₗᵢ L²(σ_c, dλ)`, `f̂ = U f = ⟨f, φ_λ⟩` (`contCoeff`,
1.18.47). Here `T` is multiplication by `λ` in this spectral representation (`opT` on `InDomT`,
1.18.49): it is symmetric (`opT_symmetric`) and has no point spectrum (`opT_no_eigenvalue`).

* 1.18.44–1.18.45: orthonormality and completeness in weak form,
  `⟨U⁻¹a, U⁻¹b⟩ = ∫ a conj b` and `⟨f, g⟩ = ∫ f̂ conj ĝ`.
* 1.18.46: the inversion `U⁻¹ f̂ = f`. 1.18.48: Parseval (`dlmf_1_18_48`, `dlmf_1_18_48_L2`).
* 1.18.50–1.18.51: `F(T) = U⁻¹ M_F U` for `F` bounded on `σ_c` (`spectralOp`, via the
  multiplication operator `multOp`), with `(F(T)f)^ = F f̂` and `⟨F(T)f, f⟩ = ∫ F |f̂|²`.
* 1.18.52: the resolvent `(z − T)⁻¹` for `z ∉ [0, ∞)` (`resolvent`), with
  `⟨(z − T)⁻¹f, f⟩ = ∫ |f̂(λ)|² dλ/(z − λ)`. It really is the inverse of `z − T`
  (`resolvent_sub_opT`, `inDomT_resolvent`).
* 1.18.53: Stieltjes inversion holds for almost every `μ` (`dlmf_1_18_53`), the difference
  quotient being the Poisson integral of `|f̂|²` (extended by `0`). Since `f̂` is an `L²` class,
  "gives `|f̂(μ)|²`" can only hold a.e.
* 1.18.54 (Sokhotski–Plemelj) is in `Section18Plemelj.lean`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace ComplexConjugate Real

namespace Azurite.DLMF

/-- `L²(σ_c, dλ)` with `σ_c = [0, ∞)`. -/
noncomputable abbrev L2sigma := Lp ℂ 2 (volume.restrict (Ici (0 : ℝ)))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : V ≃ₗᵢ[ℂ] L2sigma)

/-! ### Expansion and Parseval (1.18.44–1.18.48) -/

/-- DLMF 1.18.47: `f̂(λ) = ⟨f, φ_λ⟩`, the generalized eigenfunction transform `U f`. -/
noncomputable def contCoeff (f : V) : L2sigma := U f

theorem dlmfInner_map (f g : V) : dlmfInner (U f) (U g) = dlmfInner f g := by
  simp only [dlmfInner]
  exact U.toLinearIsometry.inner_map_map g f

/-- DLMF 1.18.45, the completeness relation `δ(x − y) = ∫ φ_λ(x) conj φ_λ(y) dλ`, in weak form:
`⟨f, g⟩ = ∫_0^∞ f̂(λ) conj ĝ(λ) dλ`. -/
theorem dlmf_1_18_45 (f g : V) :
    dlmfInner f g = ∫ l in Ici 0, contCoeff U f l * conj (contCoeff U g l) := by
  rw [← dlmfInner_map U, dlmfInner_Lp_eq]
  rfl

/-- DLMF 1.18.44, the orthonormality `∫ φ_λ conj φ_λ′ = δ(λ − λ′)`, in weak form: superposing
eigenfunctions with `L²` weights `a`, `b` gives `⟨U⁻¹a, U⁻¹b⟩ = ∫_0^∞ a conj b dλ`. -/
theorem dlmf_1_18_44 (a b : L2sigma) :
    dlmfInner (U.symm a) (U.symm b) = ∫ l in Ici 0, a l * conj (b l) := by
  rw [← dlmfInner_map U, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply, dlmfInner_Lp_eq]

/-- DLMF 1.18.46: `f = ∫ φ_λ f̂(λ) dλ`, i.e. `f = U⁻¹ f̂`. -/
theorem dlmf_1_18_46 (f : V) : U.symm (contCoeff U f) = f := U.symm_apply_apply f

/-- DLMF 1.18.48: Parseval, `‖f‖² = ∫_0^∞ |f̂(λ)|² dλ`. -/
theorem dlmf_1_18_48 (f : V) : ‖f‖ ^ 2 = ∫ l in Ici 0, ‖contCoeff U f l‖ ^ 2 := by
  rw [integral_norm_sq_Lp, contCoeff, U.norm_map]

/-- DLMF 1.18.48 for `V = L²(X)`: `∫_X |f|² dx = ∫_0^∞ |f̂(λ)|² dλ`. -/
theorem dlmf_1_18_48_L2 {X : Set ℝ} (U : Lp ℂ 2 (volume.restrict X) ≃ₗᵢ[ℂ] L2sigma)
    (f : Lp ℂ 2 (volume.restrict X)) :
    ∫ x in X, ‖f x‖ ^ 2 = ∫ l in Ici 0, ‖contCoeff U f l‖ ^ 2 := by
  rw [integral_norm_sq_Lp, dlmf_1_18_48]

/-! ### Multiplication operators on `L²(σ_c)` -/

/-- `F` truncated to `|F| ≤ C`. -/
noncomputable def truncMul (F : ℝ → ℂ) (C : ℝ) (l : ℝ) : ℂ := if ‖F l‖ ≤ C then F l else 0

theorem measurable_truncMul {F : ℝ → ℂ} (hF : Measurable F) (C : ℝ) :
    Measurable (truncMul F C) :=
  Measurable.ite (measurableSet_le hF.norm measurable_const) hF measurable_const

theorem norm_truncMul_le (F : ℝ → ℂ) (C l : ℝ) : ‖truncMul F C l‖ ≤ max C 0 := by
  unfold truncMul
  split_ifs with h
  · exact h.trans (le_max_left _ _)
  · simp

theorem memLp_truncMul_mul {F : ℝ → ℂ} (hF : Measurable F) (C : ℝ) (a : L2sigma) :
    MemLp (fun l => truncMul F C l * a l) 2 (volume.restrict (Ici (0 : ℝ))) :=
  (Lp.memLp a).of_le_mul ((measurable_truncMul hF C).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable a)) (ae_of_all _ fun l => by
      rw [norm_mul]; gcongr; exact norm_truncMul_le F C l)

/-- Multiplication by the (truncated) function `F` on `L²(σ_c)`. -/
noncomputable def multOp (F : ℝ → ℂ) (hF : Measurable F) (C : ℝ) : L2sigma →L[ℂ] L2sigma :=
  LinearMap.mkContinuous
    { toFun := fun a => (memLp_truncMul_mul hF C a).toLp _
      map_add' := fun a b => by
        refine Lp.ext_iff.mpr ?_
        filter_upwards [(memLp_truncMul_mul hF C (a + b)).coeFn_toLp,
          (memLp_truncMul_mul hF C a).coeFn_toLp, (memLp_truncMul_mul hF C b).coeFn_toLp,
          Lp.coeFn_add a b, Lp.coeFn_add ((memLp_truncMul_mul hF C a).toLp _)
            ((memLp_truncMul_mul hF C b).toLp _)] with l h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        refine Lp.ext_iff.mpr ?_
        filter_upwards [(memLp_truncMul_mul hF C (c • a)).coeFn_toLp,
          (memLp_truncMul_mul hF C a).coeFn_toLp, Lp.coeFn_smul c a,
          Lp.coeFn_smul c ((memLp_truncMul_mul hF C a).toLp _)] with l h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    (max C 0) fun a => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_truncMul_mul hF C a).coeFn_toLp] with l hl
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hl, norm_mul]
      gcongr
      exact norm_truncMul_le F C l

theorem coeFn_multOp {F : ℝ → ℂ} (hF : Measurable F) {C : ℝ} (hb : ∀ l, 0 ≤ l → ‖F l‖ ≤ C)
    (a : L2sigma) :
    (multOp F hF C a : ℝ → ℂ) =ᵐ[volume.restrict (Ici (0 : ℝ))] fun l => F l * a l := by
  filter_upwards [(memLp_truncMul_mul hF C a).coeFn_toLp,
    ae_restrict_mem measurableSet_Ici] with l hl (hl0 : 0 ≤ l)
  change (memLp_truncMul_mul hF C a).toLp _ l = _
  rw [hl, truncMul]
  simp only [hb l hl0, ite_true]

/-! ### Functions of `T` (1.18.49–1.18.51) -/

/-- DLMF 1.18.50: `F(T) = U⁻¹ M_F U` for a measurable `F`, bounded on `σ_c` by `C`. -/
noncomputable def spectralOp (F : ℝ → ℂ) (hF : Measurable F) (C : ℝ) : V →L[ℂ] V :=
  U.symm.toLinearIsometry.toContinuousLinearMap ∘L multOp F hF C ∘L
    U.toLinearIsometry.toContinuousLinearMap

/-- DLMF 1.18.50: `(F(T)f)^(λ) = F(λ) f̂(λ)`. -/
theorem dlmf_1_18_50 {F : ℝ → ℂ} (hF : Measurable F) {C : ℝ} (hb : ∀ l, 0 ≤ l → ‖F l‖ ≤ C)
    (f : V) : (contCoeff U (spectralOp U F hF C f) : ℝ → ℂ) =ᵐ[volume.restrict (Ici (0 : ℝ))]
      fun l => F l * contCoeff U f l := by
  have : contCoeff U (spectralOp U F hF C f) = multOp F hF C (U f) := by
    simp [contCoeff, spectralOp]
  rw [this]
  exact coeFn_multOp hF hb (U f)

/-- DLMF 1.18.51: `⟨F(T)f, f⟩ = ∫_0^∞ F(λ) |f̂(λ)|² dλ`. -/
theorem dlmf_1_18_51 {F : ℝ → ℂ} (hF : Measurable F) {C : ℝ} (hb : ∀ l, 0 ≤ l → ‖F l‖ ≤ C)
    (f : V) : dlmfInner (spectralOp U F hF C f) f =
      ∫ l in Ici 0, F l * ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ) := by
  rw [dlmf_1_18_45]
  refine integral_congr_ae ?_
  filter_upwards [dlmf_1_18_50 U hF hb f] with l hl
  rw [hl, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ### The operator `T` (1.18.49) -/

/-- The domain of `T`: `f` with `λ f̂(λ) ∈ L²(σ_c)`. -/
def InDomT (f : V) : Prop :=
  MemLp (fun l : ℝ => (l : ℂ) * contCoeff U f l) 2 (volume.restrict (Ici (0 : ℝ)))

/-- DLMF 1.18.49: `T f = U⁻¹(λ f̂)` (`T` is multiplication by `λ` in the spectral
representation). -/
noncomputable def opT (f : V) (hf : InDomT U f) : V := U.symm (hf.toLp _)

theorem dlmf_1_18_49 (f : V) (hf : InDomT U f) :
    (contCoeff U (opT U f hf) : ℝ → ℂ) =ᵐ[volume.restrict (Ici (0 : ℝ))]
      fun l => (l : ℂ) * contCoeff U f l := by
  simp only [contCoeff, opT, LinearIsometryEquiv.apply_symm_apply]
  exact hf.coeFn_toLp

/-- `T` is symmetric. -/
theorem opT_symmetric (f g : V) (hf : InDomT U f) (hg : InDomT U g) :
    dlmfInner (opT U f hf) g = dlmfInner f (opT U g hg) := by
  rw [dlmf_1_18_45, dlmf_1_18_45]
  refine integral_congr_ae ?_
  filter_upwards [dlmf_1_18_49 U f hf, dlmf_1_18_49 U g hg] with l h1 h2
  rw [h1, h2, map_mul, Complex.conj_ofReal]
  ring

/-- `T` has no point spectrum: no eigenfunctions in `V`. -/
theorem opT_no_eigenvalue (f : V) (hf : InDomT U f) (c : ℂ) (h : opT U f hf = c • f) :
    f = 0 := by
  have h1 := dlmf_1_18_49 U f hf
  rw [h] at h1
  have h2 : (contCoeff U (c • f) : ℝ → ℂ) =ᵐ[volume.restrict (Ici (0 : ℝ))]
      fun l => c * contCoeff U f l := by
    have := Lp.coeFn_smul c (U f)
    simp only [contCoeff, map_smul]
    filter_upwards [this] with l hl
    rw [hl, Pi.smul_apply, smul_eq_mul]
  have hne : ∀ᵐ l ∂(volume.restrict (Ici (0 : ℝ))), l ≠ c.re :=
    ae_restrict_of_ae ((Set.countable_singleton c.re).ae_notMem volume)
  have hz : (U f : ℝ → ℂ) =ᵐ[volume.restrict (Ici (0 : ℝ))] 0 := by
    filter_upwards [h1, h2, hne] with l hl1 hl2 hl3
    rw [hl2] at hl1
    have hlc : (l : ℂ) ≠ c := fun e => hl3 (by rw [← e, Complex.ofReal_re])
    have : ((l : ℂ) - c) * contCoeff U f l = 0 := by rw [sub_mul, hl1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlc)
  have : U f = 0 := Lp.eq_zero_iff_ae_eq_zero.mpr hz
  exact (map_eq_zero_iff U U.injective).mp this

/-! ### The resolvent (1.18.52) -/

/-- The distance `max(|Im z|, −Re z)` of `z ∉ [0, ∞)` from `[0, ∞)` (a lower bound for it). -/
noncomputable def resDist (z : ℂ) : ℝ := max |z.im| (-z.re)

theorem resDist_pos {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) : 0 < resDist z := by
  rcases hz with h | h
  · exact lt_max_of_lt_left (abs_pos.mpr h)
  · exact lt_max_of_lt_right (by linarith)

theorem resDist_le_norm (z : ℂ) {l : ℝ} (hl : 0 ≤ l) : resDist z ≤ ‖z - l‖ := by
  refine max_le ?_ ?_
  · calc |z.im| = |(z - l).im| := by simp
      _ ≤ ‖z - l‖ := Complex.abs_im_le_norm _
  · calc -z.re ≤ |(z - l).re| := by
          rw [Complex.sub_re, Complex.ofReal_re]
          exact (by linarith : -z.re ≤ -(z.re - l)).trans (neg_le_abs _)
      _ ≤ ‖z - l‖ := Complex.abs_re_le_norm _

theorem measurable_resolventFun (z : ℂ) : Measurable fun l : ℝ => (z - l)⁻¹ :=
  (measurable_const.sub Complex.measurable_ofReal).inv

theorem norm_resolventFun_le {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) (l : ℝ) (hl : 0 ≤ l) :
    ‖(z - l)⁻¹‖ ≤ (resDist z)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (resDist_pos hz) (resDist_le_norm z hl)

/-- The resolvent `(z − T)⁻¹ = F(T)` with `F(λ) = (z − λ)⁻¹`. -/
noncomputable def resolvent (z : ℂ) : V →L[ℂ] V :=
  spectralOp U (fun l : ℝ => (z - l)⁻¹) (measurable_resolventFun z) (resDist z)⁻¹

/-- DLMF 1.18.52: `⟨(z − T)⁻¹f, f⟩ = ∫_{σ} |f̂(λ)|² dλ/(z − λ)` for `z ∉ σ_c`. -/
theorem dlmf_1_18_52 {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) (f : V) :
    dlmfInner (resolvent U z f) f = ∫ l in Ici 0, ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ) / (z - l) := by
  rw [resolvent, dlmf_1_18_51 U _ (norm_resolventFun_le hz)]
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  simp only
  rw [div_eq_mul_inv, mul_comm]

/-- `(z − T)⁻¹` inverts `z − T`: `(z − T)⁻¹(z f − T f) = f` for `f ∈ 𝒟(T)`. -/
theorem resolvent_sub_opT {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) (f : V) (hf : InDomT U f) :
    resolvent U z (z • f - opT U f hf) = f := by
  refine U.injective (Lp.ext_iff.mpr ?_)
  have h1 := dlmf_1_18_50 U (measurable_resolventFun z) (norm_resolventFun_le hz)
    (z • f - opT U f hf)
  have h2 : (contCoeff U (z • f - opT U f hf) : ℝ → ℂ) =ᵐ[volume.restrict (Ici (0 : ℝ))]
      fun l => z * contCoeff U f l - (l : ℂ) * contCoeff U f l := by
    simp only [contCoeff, map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (z • U f) (U (opT U f hf)), Lp.coeFn_smul z (U f),
      dlmf_1_18_49 U f hf] with l ha hb hc
    rw [ha, Pi.sub_apply, hb, Pi.smul_apply, smul_eq_mul]
    simp only [contCoeff] at hc
    rw [hc]
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ici] with l ha hb (hl : 0 ≤ l)
  simp only [contCoeff, resolvent] at ha hb ⊢
  rw [ha, hb]
  have hzl : z - l ≠ 0 := fun e => by
    have := (resDist_pos hz).trans_le (resDist_le_norm z hl)
    rw [e, norm_zero] at this; exact lt_irrefl 0 this
  field_simp

/-- `(z − T)⁻¹ g ∈ 𝒟(T)` and `(z − T)(z − T)⁻¹ g = g`. -/
theorem inDomT_resolvent {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) (g : V) :
    ∃ h : InDomT U (resolvent U z g), z • resolvent U z g - opT U _ h = g := by
  have hd := resDist_pos hz
  have h1 := dlmf_1_18_50 U (measurable_resolventFun z) (norm_resolventFun_le hz) g
  have hdom : InDomT U (resolvent U z g) := by
    refine (Lp.memLp (U g)).of_le_mul (c := 1 + ‖z‖ * (resDist z)⁻¹)
      ((Complex.measurable_ofReal.aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [h1, ae_restrict_mem measurableSet_Ici] with l hl (hl0 : 0 ≤ l)
    simp only [contCoeff, resolvent] at hl ⊢
    rw [hl, ← mul_assoc, norm_mul]
    gcongr
    have hzl : z - l ≠ 0 := fun e => by
      have := hd.trans_le (resDist_le_norm z hl0)
      rw [e, norm_zero] at this; exact lt_irrefl 0 this
    have : (l : ℂ) * (z - l)⁻¹ = z * (z - l)⁻¹ - 1 := by field_simp; ring
    rw [this]
    calc ‖z * (z - l)⁻¹ - 1‖ ≤ ‖z * (z - l)⁻¹‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖z‖ * (resDist z)⁻¹ + 1 := by
        rw [norm_mul, norm_one]
        gcongr
        exact norm_resolventFun_le hz l hl0
      _ = 1 + ‖z‖ * (resDist z)⁻¹ := by ring
  refine ⟨hdom, U.injective (Lp.ext_iff.mpr ?_)⟩
  filter_upwards [Lp.coeFn_sub (z • U (resolvent U z g)) (U (opT U _ hdom)),
    Lp.coeFn_smul z (U (resolvent U z g)), dlmf_1_18_49 U _ hdom, h1,
    ae_restrict_mem measurableSet_Ici] with l ha hb hc he (hl0 : 0 ≤ l)
  simp only [map_sub, map_smul]
  rw [ha, Pi.sub_apply, hb, Pi.smul_apply, smul_eq_mul]
  simp only [contCoeff] at hc he
  rw [hc]
  simp only [resolvent] at he ⊢
  rw [he]
  have hzl : z - l ≠ 0 := fun e => by
    have := hd.trans_le (resDist_le_norm z hl0)
    rw [e, norm_zero] at this; exact lt_irrefl 0 this
  field_simp

/-! ### Stieltjes inversion (1.18.53) -/

theorem integrable_sq_contCoeff (f : V) :
    Integrable (fun l => ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ)) (volume.restrict (Ici (0 : ℝ))) :=
  ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)).ofReal

theorem sub_resolventFun (μ : ℝ) {ν : ℝ} (hν : 0 < ν) (l : ℝ) :
    (2 * π * I)⁻¹ * (((μ : ℂ) - ν * I - l)⁻¹ - ((μ : ℂ) + ν * I - l)⁻¹) =
      ((pK ν (l - μ) : ℝ) : ℂ) := by
  have h1 := one_div_sokhotski (x := μ) (y := l) hν (-1) (Or.inr rfl)
  have h2 := one_div_sokhotski (x := μ) (y := l) hν 1 (Or.inl rfl)
  simp only [one_div, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul] at h1 h2
  rw [show (μ : ℂ) - ν * I - l = (μ : ℂ) + -(ν * I) - l by ring, h1, h2, pK]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hD : (((l - μ) ^ 2 + ν ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < _).ne'
  push_cast at hD ⊢
  field_simp
  ring

/-- DLMF 1.18.53 (Stieltjes inversion): for almost every `μ`,
`(2πi)⁻¹ (⟨(μ − iν − T)⁻¹f, f⟩ − ⟨(μ + iν − T)⁻¹f, f⟩) → |f̂(μ)|²` for `μ ∈ σ_c` and `→ 0`
otherwise, as `ν → 0+`. (`f̂ ∈ L²` is an a.e. class, so the statement is necessarily a.e.) -/
theorem dlmf_1_18_53 (f : V) : ∀ᵐ μ : ℝ, Tendsto (fun ν : ℝ => (2 * π * I)⁻¹ *
    (dlmfInner (resolvent U ((μ : ℂ) - ν * I) f) f -
      dlmfInner (resolvent U ((μ : ℂ) + ν * I) f) f)) (𝓝[>] 0)
    (𝓝 ((Ici 0).indicator (fun l => ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ)) μ)) := by
  have hπ := Real.pi_pos
  set h : ℝ → ℂ := (Ici 0).indicator (fun l => ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ))
  have hint : Integrable h := (integrable_indicator_iff measurableSet_Ici).mpr
    (integrable_sq_contCoeff U f)
  have hm : AEStronglyMeasurable (fun t => ‖h t‖ / (1 + t ^ 2)) volume :=
    hint.norm.aestronglyMeasurable.div₀
      (by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2).aestronglyMeasurable
  have hw : Integrable fun t => ‖h t‖ / (1 + t ^ 2) :=
    hint.norm.mono' hm
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact div_le_self (norm_nonneg _) (by nlinarith [sq_nonneg t]))
  filter_upwards [ae_tendsto_poissonKernel hint.aestronglyMeasurable hw] with μ hμ
  -- the expression is the Poisson integral of `h` at `μ`
  have hexpr : ∀ ν : ℝ, 0 < ν → (2 * π * I)⁻¹ *
      (dlmfInner (resolvent U ((μ : ℂ) - ν * I) f) f -
        dlmfInner (resolvent U ((μ : ℂ) + ν * I) f) f) =
      ∫ s, ((pK ν s : ℝ) : ℂ) * h (μ + s) := fun ν hν => by
    have hz1 : ((μ : ℂ) - ν * I).im ≠ 0 ∨ ((μ : ℂ) - ν * I).re < 0 := Or.inl (by simp [hν.ne'])
    have hz2 : ((μ : ℂ) + ν * I).im ≠ 0 ∨ ((μ : ℂ) + ν * I).re < 0 := Or.inl (by simp [hν.ne'])
    have hi : ∀ (z : ℂ), (z.im ≠ 0 ∨ z.re < 0) → Integrable
        (fun l => ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ) / (z - l))
          (volume.restrict (Ici (0 : ℝ))) :=
      fun z hz => by
        refine ((integrable_sq_contCoeff U f).bdd_mul (c := (resDist z)⁻¹)
          (measurable_resolventFun z).aestronglyMeasurable
          (ae_restrict_of_forall_mem measurableSet_Ici fun l hl =>
            norm_resolventFun_le hz l hl)).congr (ae_of_all _ fun l => ?_)
        simp only [div_eq_mul_inv]; ring
    rw [dlmf_1_18_52 U hz1, dlmf_1_18_52 U hz2, ← integral_sub (hi _ hz1) (hi _ hz2),
      ← integral_const_mul]
    have e1 : ∫ l in Ici 0, (2 * π * I)⁻¹ * (((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ) /
        ((μ : ℂ) - ν * I - l) - ((‖contCoeff U f l‖ ^ 2 : ℝ) : ℂ) / ((μ : ℂ) + ν * I - l)) =
        ∫ l, ((pK ν (l - μ) : ℝ) : ℂ) * h l := by
      rw [← integral_indicator measurableSet_Ici]
      congr 1
      funext l
      by_cases hl : l ∈ Ici (0 : ℝ)
      · rw [indicator_of_mem hl]
        show _ = _ * (Ici 0).indicator _ l
        rw [indicator_of_mem hl, ← sub_resolventFun μ hν l]
        simp only [div_eq_mul_inv]; ring
      · simp [indicator_of_notMem hl, h]
    rw [e1, ← integral_add_left_eq_self (fun l => ((pK ν (l - μ) : ℝ) : ℂ) * h l) μ]
    simp only [add_sub_cancel_left]
  -- the Poisson estimate
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound := hμ.const_mul π⁻¹
  rw [mul_zero] at hbound
  refine squeeze_zero' (Eventually.of_forall fun ν => norm_nonneg _) ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with ν (hν : 0 < ν)
  rw [hexpr ν hν]
  have hc : h μ = ∫ s, ((pK ν s : ℝ) : ℂ) * h μ := by
    rw [integral_mul_const, integral_complex_ofReal, integral_pK hν, Complex.ofReal_one, one_mul]
  have hA : Integrable fun s => ((pK ν s : ℝ) : ℂ) * h (μ + s) :=
    (hint.comp_add_left μ).bdd_mul (c := 1 / (π * ν))
      (Complex.continuous_ofReal.comp (continuous_pK hν)).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Complex.norm_real,
        Real.norm_of_nonneg (pK_nonneg hν s)]; exact pK_le hν s)
  have hB : Integrable fun s => ((pK ν s : ℝ) : ℂ) * h μ :=
    (integrable_pK hν).ofReal.mul_const _
  have e : (∫ s, ((pK ν s : ℝ) : ℂ) * h (μ + s)) - h μ =
      ∫ s, (((pK ν s : ℝ) : ℂ) * h (μ + s) - ((pK ν s : ℝ) : ℂ) * h μ) := by
    rw [integral_sub hA hB, ← hc]
  rw [e]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hν s), pK]
  field_simp
  ring

end Azurite.DLMF
