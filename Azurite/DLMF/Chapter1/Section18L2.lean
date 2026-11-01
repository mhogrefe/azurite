/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# DLMF §1.18(ii): `L²` spaces on intervals in `ℝ`

https://dlmf.nist.gov/1.18.ii

`L²(X, dα)` is Mathlib's `Lp ℂ 2 (α.measure.restrict X)` for a Stieltjes function `α` (the
Lebesgue–Stieltjes measure `dα` of §1.4(v)) and any set `X ⊆ ℝ`, in particular any interval.
Mathlib's `Lp` consists of a.e. classes of a.e. strongly measurable functions. Every
Lebesgue–Stieltjes measurable function agrees a.e. with a Borel one, so the space is the same.

* 1.18.11: square integrability (`dlmf_1_18_11`). Functions with `⟨f − g, f − g⟩ = 0` are
  identified, which is equality a.e. (`dlmf_1_18_ii_identify`, `dlmf_1_18_ii_identify_Lp`).
* `L²(X, dα)` is a separable Hilbert space, also in DLMF's sense of §1.18(i)
  (`dlmf_1_18_ii_separable`, from Mathlib's second countability of `Lp` for separable measures).
* 1.18.12: `⟨f, g⟩ = ∫ f conj(g) dα` (`dlmf_1_18_12`). `dα = dx` for `α(x) = x`
  (`dlmf_1_18_ii_dx`). The absolutely continuous case `dα = w dx` is 1.4.23_1 (`dlmf_1_4_23_1`).
* For an orthonormal basis `{φₙ}` of `L²(X)` (`b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict X))`):
  * 1.18.13: the coefficients.
  * 1.18.14: Parseval.
  * 1.18.15–1.18.16: convergence in the mean (`dlmf_1_18_16`).
  * 1.18.17–1.18.18: the formal kernel expansion, rigorous with the partial kernels
    `Kₘ(x, y) = ∑_{n=0}^{m} φₙ(x) conj(φₙ(y))` (`kernelPartial`, `dlmf_1_18_17_partial`,
    `dlmf_1_18_17`).
  * 1.18.19: the completeness relation in weak form,
    `∑ₙ ⟨f, φₙ⟩ conj⟨g, φₙ⟩ = ⟨f, g⟩` (`dlmf_1_18_19`).
  * 1.18.20: orthonormality.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace Azurite.DLMF

/-! ### `L²(X, dα)` (1.18.11–1.18.12) -/

theorem dlmfInner_Lp_eq {μ : Measure ℝ} (f g : Lp ℂ 2 μ) :
    dlmfInner f g = ∫ x, f x * conj (g x) ∂μ := by
  rw [dlmfInner, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [RCLike.inner_apply, mul_comm]

section Stieltjes

variable (α : StieltjesFunction ℝ) (X : Set ℝ)

/-- DLMF 1.18.11: `f ∈ L²(X, dα)` iff `f` is measurable with `∫_X |f|² dα < ∞`. -/
theorem dlmf_1_18_11 {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (α.measure.restrict X)) :
    MemLp f 2 (α.measure.restrict X) ↔
      Integrable (fun x => ‖f x‖ ^ 2) (α.measure.restrict X) :=
  memLp_two_iff_integrable_sq_norm hf

/-- DLMF §1.18(ii): functions with `⟨f − g, f − g⟩ = 0` are identified; for square-integrable
functions this is equality almost everywhere, the identification made in `Lp`. -/
theorem dlmf_1_18_ii_identify {f g : ℝ → ℂ} (hf : MemLp f 2 (α.measure.restrict X))
    (hg : MemLp g 2 (α.measure.restrict X)) :
    ∫ x in X, ‖f x - g x‖ ^ 2 ∂α.measure = 0 ↔ f =ᵐ[α.measure.restrict X] g := by
  have hi : Integrable (fun x => ‖f x - g x‖ ^ 2) (α.measure.restrict X) :=
    (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)).mp
      (hf.sub hg)
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi]
  constructor
  · intro h
    filter_upwards [h] with x hx
    simpa [sub_eq_zero] using hx
  · intro h
    filter_upwards [h] with x hx
    simp [hx]

theorem dlmf_1_18_ii_identify_Lp (f g : Lp ℂ 2 (α.measure.restrict X)) :
    dlmfInner (f - g) (f - g) = 0 ↔ f = g := by
  rw [dlmfInner, inner_self_eq_zero, sub_eq_zero]

/-- DLMF §1.18(ii): `L²(X, dα)` is a separable Hilbert space, also in DLMF's sense of §1.18(i). -/
theorem dlmf_1_18_ii_separable :
    CompleteSpace (Lp ℂ 2 (α.measure.restrict X)) ∧
      TopologicalSpace.SeparableSpace (Lp ℂ 2 (α.measure.restrict X)) ∧
      IsSeparableDLMF (Lp ℂ 2 (α.measure.restrict X)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  exact ⟨inferInstance, inferInstance, isSeparableDLMF_iff.mpr inferInstance⟩

/-- DLMF 1.18.12: `⟨f, g⟩ = ∫_X f(x) conj(g(x)) dα(x)`. -/
theorem dlmf_1_18_12 (f g : Lp ℂ 2 (α.measure.restrict X)) :
    dlmfInner f g = ∫ x in X, f x * conj (g x) ∂α.measure :=
  dlmfInner_Lp_eq f g

/-- DLMF §1.18(ii): for `α(x) = x`, `dα = dx` (`L²(X) = L²(X, dx)`). -/
theorem dlmf_1_18_ii_dx : StieltjesFunction.id.measure.restrict X = volume.restrict X := by
  rw [← Real.volume_eq_stieltjes_id]

end Stieltjes

/-! ### Orthonormal bases of `L²(X)` (1.18.13–1.18.20) -/

section Basis

variable {X : Set ℝ}

theorem integral_norm_sq_Lp {μ : Measure ℝ} (f : Lp ℂ 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h1 := dlmfInner_self f
  rw [dlmfInner, L2.inner_def] at h1
  have h2 : ∫ x, ⟪f x, f x⟫_ℂ ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h2] at h1
  exact_mod_cast h1

theorem coeFn_finsetSum_Lp {μ : Measure ℝ} {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simpa using hx
  | insert i s hi ih =>
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hx hs
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hx, Pi.add_apply, hs]

variable (b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict X)))

/-- DLMF 1.18.13: `cₙ = ⟨f, φₙ⟩ = ∫_X f(x) conj(φₙ(x)) dx`. -/
theorem dlmf_1_18_13 (f : Lp ℂ 2 (volume.restrict X)) (n : ℕ) :
    dlmfInner f (b n) = ∫ x in X, f x * conj (b n x) :=
  dlmfInner_Lp_eq f (b n)

/-- DLMF 1.18.14: Parseval, `∫_X |f|² dx = ∑ₙ |cₙ|²`. -/
theorem dlmf_1_18_14 (f : Lp ℂ 2 (volume.restrict X)) :
    ∫ x in X, ‖f x‖ ^ 2 = ∑' n, ‖dlmfInner f (b n)‖ ^ 2 := by
  rw [integral_norm_sq_Lp, tsum_norm_sq_hilbertBasis]

/-- DLMF 1.18.15–1.18.16: `f = lim ∑_{n=0}^{m} cₙ φₙ` in the mean:
`∫_X |f(x) − ∑_{n=0}^{m} cₙ φₙ(x)|² dx → 0`. -/
theorem dlmf_1_18_16 (f : Lp ℂ 2 (volume.restrict X)) :
    Tendsto (fun m : ℕ => ∫ x in X,
      ‖f x - ∑ n ∈ Finset.range (m + 1), dlmfInner f (b n) * b n x‖ ^ 2) atTop (𝓝 0) := by
  set S : ℕ → Lp ℂ 2 (volume.restrict X) := fun m =>
    ∑ n ∈ Finset.range (m + 1), dlmfInner f (b n) • b n
  have hS : HasSum (fun n => dlmfInner f (b n) • b n) f := by
    have := b.hasSum_repr f
    convert this using 1
    funext n
    rw [b.repr_apply_apply]
    rfl
  have h := (hS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have h2 := ((tendsto_iff_norm_sub_tendsto_zero.mp h).pow 2)
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun m => ?_
  simp only [Function.comp]
  rw [norm_sub_rev, ← integral_norm_sq_Lp]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f (S m), coeFn_finsetSum_Lp (Finset.range (m + 1))
    (fun n => dlmfInner f (b n) • b n),
    ae_all_iff.mpr fun n : ℕ => Lp.coeFn_smul (dlmfInner f (b n)) (b n)] with x hx hs hsm
  rw [hx, Pi.sub_apply, hs]
  simp only [hsm, Pi.smul_apply, smul_eq_mul]

/-- The partial kernel `Kₘ(x, y) = ∑_{n=0}^{m} φₙ(x) conj(φₙ(y))` of 1.18.18. -/
noncomputable def kernelPartial (m : ℕ) (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), b n x * conj (b n y)

/-- DLMF 1.18.17 (partial sums): `∑_{n=0}^{m} ⟨f, φₙ⟩ φₙ(x) = ∫_X Kₘ(x, y) f(y) dy`. -/
theorem dlmf_1_18_17_partial (f : Lp ℂ 2 (volume.restrict X)) (m : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range (m + 1), dlmfInner f (b n) * b n x =
      ∫ y in X, kernelPartial b m x y * f y := by
  simp only [kernelPartial, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [dlmf_1_18_13, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  · intro n _
    have := (L2.integrable_inner (𝕜 := ℂ) (b n) f).const_mul (b n x)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [RCLike.inner_apply]
    ring

/-- DLMF 1.18.17, `f(x) = ∫_X K(x, y) f(y) dy`, made rigorous: with the partial kernels,
`∫_X |f(x) − ∫_X Kₘ(x, y) f(y) dy|² dx → 0`. -/
theorem dlmf_1_18_17 (f : Lp ℂ 2 (volume.restrict X)) :
    Tendsto (fun m : ℕ => ∫ x in X, ‖f x - ∫ y in X, kernelPartial b m x y * f y‖ ^ 2)
      atTop (𝓝 0) := by
  simpa only [dlmf_1_18_17_partial] using dlmf_1_18_16 b f

/-- DLMF 1.18.19, the completeness relation `δ(x − y) = ∑ φₙ(x) conj(φₙ(y))`, in its weak
form: for `f, g ∈ L²(X)`,
`∑ₙ (∫_X f conj φₙ) conj(∫_X g conj φₙ) = ∫_X f(x) conj(g(x)) dx`. -/
theorem dlmf_1_18_19 (f g : Lp ℂ 2 (volume.restrict X)) :
    HasSum (fun n => (∫ x in X, f x * conj (b n x)) * conj (∫ x in X, g x * conj (b n x)))
      (∫ x in X, f x * conj (g x)) := by
  have h := b.hasSum_inner_mul_inner g f
  simp only [← dlmf_1_18_13 b]
  have e : ∫ x in X, f x * conj (g x) = dlmfInner f g := (dlmfInner_Lp_eq f g).symm
  rw [e]
  refine h.congr_fun fun n => ?_
  simp only [dlmfInner]
  rw [← inner_conj_symm (b n) g, mul_comm, Complex.conj_conj]

/-- DLMF 1.18.20: orthonormality, `∫_X φₙ(x) conj(φₘ(x)) dx = δ_{n,m}`. -/
theorem dlmf_1_18_20 (n m : ℕ) :
    ∫ x in X, b n x * conj (b m x) = if n = m then 1 else 0 := by
  rw [← dlmf_1_18_13, dlmfInner, orthonormal_iff_ite.mp b.orthonormal]
  simp only [eq_comm]

end Basis

end Azurite.DLMF
