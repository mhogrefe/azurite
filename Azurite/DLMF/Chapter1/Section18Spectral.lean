/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18L2
import Azurite.DLMF.Chapter1.Section18Operators

/-!
# DLMF §1.18(v): Point spectra and eigenfunction expansions — general results

https://dlmf.nist.gov/1.18.v

The "General Results" subsection. The complete orthonormal set of eigenfunctions `{φₙ}` is a
Hilbert basis `b : HilbertBasis ℕ ℂ V`, abstractly or for `V = L²(X)`, with real eigenvalues `λₙ`.

* 1.18.29: orthonormality. 1.18.30: the completeness relation in weak form,
  `∑ₙ ⟨f, φₙ⟩ conj⟨g, φₙ⟩ = ⟨f, g⟩`.
* 1.18.31–1.18.33: the expansion `f = ∑ₙ f̂(λₙ) φₙ` in norm, `f̂(λₙ) = ⟨f, φₙ⟩` (`eigenCoeff`), and
  Parseval. This holds for every `f ∈ L²(X)`, not only `f ∈ C(X) ∩ L²(X) ∩ 𝒟(T)`. For `L²(X)`
  the expansion and its kernel form converge in the mean (`dlmf_1_18_16`, `dlmf_1_18_17`).
* 1.18.34: if `T` is symmetric on `𝒟(T)` with `Tφₙ = λₙφₙ`, then `Tf = ∑ₙ λₙ f̂(λₙ) φₙ` for
  `f ∈ 𝒟(T)` (`dlmf_1_18_34`). In `L²(X)`, `Tf = ∫_X (∑ₙ λₙ φₙ(x) conj φₙ(y)) f(y) dy` in the
  mean with the partial kernels (`kernelWeighted`, `dlmf_1_18_34_kernel`).
* 1.18.35: for `F` bounded on the spectrum, `F(T) = ∑ₙ F(λₙ) ⟨·, φₙ⟩ φₙ` is a bounded operator
  (`spectralCalculus`, via the multiplier `multLp` on `ℓ²`) with `F(T)φₙ = F(λₙ)φₙ`,
  `‖F(T)‖ ≤ sup |F(λₙ)|`, the expansion `dlmf_1_18_35`, and the kernel form
  `dlmf_1_18_35_kernel`.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate lp

namespace Azurite.DLMF

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (b : HilbertBasis ℕ ℂ V)

/-- DLMF 1.18.32: the coefficients `f̂(λₙ) = ⟨f, φₙ⟩`. -/
noncomputable def eigenCoeff (f : V) (n : ℕ) : ℂ := dlmfInner f (b n)

theorem eigenCoeff_eq_repr (f : V) (n : ℕ) : eigenCoeff b f n = b.repr f n := by
  rw [eigenCoeff, dlmfInner, b.repr_apply_apply]

/-- DLMF 1.18.29: orthonormality `⟨φₙ, φₘ⟩ = δ_{n,m}`. -/
theorem dlmf_1_18_29 (n m : ℕ) : dlmfInner (b n) (b m) = if n = m then 1 else 0 := by
  rw [dlmfInner, orthonormal_iff_ite.mp b.orthonormal]
  simp only [eq_comm]

/-- DLMF 1.18.30, the completeness relation, in weak form:
`∑ₙ ⟨f, φₙ⟩ conj⟨g, φₙ⟩ = ⟨f, g⟩`. -/
theorem dlmf_1_18_30 (f g : V) :
    HasSum (fun n => eigenCoeff b f n * conj (eigenCoeff b g n)) (dlmfInner f g) := by
  have h := b.hasSum_inner_mul_inner g f
  refine h.congr_fun fun n => ?_
  simp only [eigenCoeff, dlmfInner]
  rw [← inner_conj_symm (b n) g, mul_comm, Complex.conj_conj]

/-- DLMF 1.18.31: `f = ∑ₙ f̂(λₙ) φₙ`, convergent in norm. -/
theorem dlmf_1_18_31 (f : V) : HasSum (fun n => eigenCoeff b f n • b n) f := by
  have := b.hasSum_repr f
  convert this using 1
  funext n
  rw [eigenCoeff_eq_repr]

/-- DLMF 1.18.33: Parseval, `‖f‖² = ∑ₙ |f̂(λₙ)|²`. -/
theorem dlmf_1_18_33 (f : V) :
    Summable (fun n => ‖eigenCoeff b f n‖ ^ 2) ∧ ∑' n, ‖eigenCoeff b f n‖ ^ 2 = ‖f‖ ^ 2 :=
  ⟨b.orthonormal.inner_products_summable f, tsum_norm_sq_hilbertBasis b f⟩

/-- DLMF 1.18.34: if `T` is symmetric on `𝒟(T)` with eigenfunctions `Tφₙ = λₙφₙ`, `λₙ` real,
then `(Tf)^(λₙ) = λₙ f̂(λₙ)` and `Tf = ∑ₙ λₙ f̂(λₙ) φₙ`. -/
theorem dlmf_1_18_34 {D : Submodule ℂ V} {T : D →ₗ[ℂ] V} (hT : IsSymmetricOn T) (lam : ℕ → ℝ)
    (hb : ∀ n, ∃ h : b n ∈ D, T ⟨b n, h⟩ = (lam n : ℂ) • b n) (f : D) :
    (∀ n, eigenCoeff b (T f) n = lam n * eigenCoeff b f n) ∧
      HasSum (fun n => ((lam n : ℂ) * eigenCoeff b f n) • b n) (T f) := by
  have hc : ∀ n, eigenCoeff b (T f) n = lam n * eigenCoeff b f n := fun n => by
    obtain ⟨h, e⟩ := hb n
    have := hT f ⟨b n, h⟩
    rw [e, dlmfInner_smul_right, Complex.conj_ofReal] at this
    exact this
  refine ⟨hc, ?_⟩
  have := dlmf_1_18_31 b (T f)
  simpa only [hc] using this

/-! ### Functions of `T` (1.18.35) -/

theorem summable_norm_sq_lp (c : ℓ²(ℕ, ℂ)) : Summable fun n => ‖c n‖ ^ 2 := by
  have hs := (lp.memℓp c).summable (p := 2) (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

theorem norm_sq_lp (c : ℓ²(ℕ, ℂ)) : ‖c‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) c
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem memℓp_mul_of_bound {w : ℕ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C) (c : ℓ²(ℕ, ℂ)) :
    Memℓp (fun n => w n * c n) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine ((summable_norm_sq_lp c).mul_left (C ^ 2)).of_nonneg_of_le (fun n => by positivity)
    fun n => ?_
  rw [norm_mul, mul_pow]
  gcongr
  exact hw n

theorem norm_mul_lp_le {w : ℕ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C) (c : ℓ²(ℕ, ℂ)) :
    ‖(⟨fun n => w n * c n, memℓp_mul_of_bound hw c⟩ : ℓ²(ℕ, ℂ))‖ ≤ C * ‖c‖ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  have hsq : ‖(⟨fun n => w n * c n, memℓp_mul_of_bound hw c⟩ : ℓ²(ℕ, ℂ))‖ ^ 2 ≤
      (C * ‖c‖) ^ 2 := by
    rw [norm_sq_lp, mul_pow, norm_sq_lp, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ ((summable_norm_sq_lp c).mul_left _)
    · change ‖w n * c n‖ ^ 2 ≤ C ^ 2 * ‖c n‖ ^ 2
      rw [norm_mul, mul_pow]
      gcongr
      exact hw n
    · exact summable_norm_sq_lp ⟨fun n => w n * c n, memℓp_mul_of_bound hw c⟩
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Multiplication by a bounded sequence `w` on `ℓ²`. -/
noncomputable def multLp (w : ℕ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) :
    ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨fun n => w n * c n, memℓp_mul_of_bound hw c⟩
      map_add' := fun c d => by
        ext n
        simp only [lp.coeFn_add, Pi.add_apply]
        exact mul_add _ _ _
      map_smul' := fun r c => by
        ext n
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact mul_left_comm _ _ _ }
    C (norm_mul_lp_le hw)

theorem multLp_apply (w : ℕ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) (c : ℓ²(ℕ, ℂ)) (n : ℕ) :
    multLp w C hw c n = w n * c n := rfl

/-- DLMF 1.18.35: `F(T)` for a function `F` bounded on the spectrum `{λₙ}`,
`F(T) f = ∑ₙ F(λₙ) f̂(λₙ) φₙ`. -/
noncomputable def spectralCalculus (lam : ℕ → ℝ) (F : ℝ → ℂ) (C : ℝ)
    (hF : ∀ n, ‖F (lam n)‖ ≤ C) : V →L[ℂ] V :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap ∘L multLp (fun n => F (lam n)) C hF ∘L
    b.repr.toLinearIsometry.toContinuousLinearMap

variable {b}

theorem eigenCoeff_spectralCalculus (lam : ℕ → ℝ) (F : ℝ → ℂ) (C : ℝ)
    (hF : ∀ n, ‖F (lam n)‖ ≤ C) (f : V) (n : ℕ) :
    eigenCoeff b (spectralCalculus b lam F C hF f) n = F (lam n) * eigenCoeff b f n := by
  rw [eigenCoeff_eq_repr, eigenCoeff_eq_repr]
  simp [spectralCalculus, multLp_apply]

/-- DLMF 1.18.35: `F(T) f = ∑ₙ F(λₙ) f̂(λₙ) φₙ`, convergent in norm. -/
theorem dlmf_1_18_35 (lam : ℕ → ℝ) (F : ℝ → ℂ) (C : ℝ) (hF : ∀ n, ‖F (lam n)‖ ≤ C) (f : V) :
    HasSum (fun n => (F (lam n) * eigenCoeff b f n) • b n) (spectralCalculus b lam F C hF f) := by
  have := dlmf_1_18_31 b (spectralCalculus b lam F C hF f)
  simpa only [eigenCoeff_spectralCalculus] using this

theorem eq_of_eigenCoeff_eq {f g : V} (h : ∀ n, eigenCoeff b f n = eigenCoeff b g n) : f = g := by
  refine b.repr.injective (lp.ext (funext fun n => ?_))
  rw [← eigenCoeff_eq_repr, ← eigenCoeff_eq_repr, h]

/-- `F(T) φₙ = F(λₙ) φₙ`. -/
theorem spectralCalculus_basis (lam : ℕ → ℝ) (F : ℝ → ℂ) (C : ℝ) (hF : ∀ n, ‖F (lam n)‖ ≤ C)
    (n : ℕ) : spectralCalculus b lam F C hF (b n) = F (lam n) • b n := by
  refine eq_of_eigenCoeff_eq (b := b) fun m => ?_
  rw [eigenCoeff_spectralCalculus, eigenCoeff, eigenCoeff, dlmf_1_18_29, dlmfInner_smul_left,
    dlmf_1_18_29]
  split_ifs with h
  · rw [h]
  · simp

/-- `‖F(T)‖ ≤ sup |F(λₙ)|`. -/
theorem norm_spectralCalculus_le (lam : ℕ → ℝ) (F : ℝ → ℂ) (C : ℝ)
    (hF : ∀ n, ‖F (lam n)‖ ≤ C) : ‖spectralCalculus b lam F C hF‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => ?_
  have h1 := norm_mul_lp_le hF (b.repr f)
  rw [LinearIsometryEquiv.norm_map] at h1
  simp only [spectralCalculus, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.norm_map]
  exact h1

end Abstract

/-! ### Kernel forms in `L²(X)` -/

section Kernel

variable {X : Set ℝ} (b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict X)))

/-- Expansions converge in the mean: if `g = ∑ cₙ φₙ` in `L²(X)` then
`∫_X |g(x) − ∑_{n=0}^{m} cₙ φₙ(x)|² dx → 0`. -/
theorem tendsto_integral_sub_partialSum {c : ℕ → ℂ} {g : Lp ℂ 2 (volume.restrict X)}
    (h : HasSum (fun n => c n • b n) g) :
    Tendsto (fun m : ℕ => ∫ x in X, ‖g x - ∑ n ∈ Finset.range (m + 1), c n * b n x‖ ^ 2)
      atTop (𝓝 0) := by
  set S : ℕ → Lp ℂ 2 (volume.restrict X) := fun m => ∑ n ∈ Finset.range (m + 1), c n • b n
  have h1 := (h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have h2 := ((tendsto_iff_norm_sub_tendsto_zero.mp h1).pow 2)
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun m => ?_
  simp only [Function.comp]
  rw [norm_sub_rev, ← integral_norm_sq_Lp]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub g (S m), coeFn_finsetSum_Lp (Finset.range (m + 1))
    (fun n => c n • b n), ae_all_iff.mpr fun n : ℕ => Lp.coeFn_smul (c n) (b n)] with x hx hs hsm
  rw [hx, Pi.sub_apply, hs]
  simp only [hsm, Pi.smul_apply, smul_eq_mul]

/-- The weighted partial kernel `∑_{n=0}^{m} wₙ φₙ(x) conj(φₙ(y))` of 1.18.34–1.18.35. -/
noncomputable def kernelWeighted (w : ℕ → ℂ) (m : ℕ) (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), w n * b n x * conj (b n y)

theorem sum_eq_integral_kernelWeighted (w : ℕ → ℂ) (f : Lp ℂ 2 (volume.restrict X)) (m : ℕ)
    (x : ℝ) : ∑ n ∈ Finset.range (m + 1), (w n * eigenCoeff b f n) * b n x =
      ∫ y in X, kernelWeighted b w m x y * f y := by
  simp only [kernelWeighted, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [eigenCoeff, dlmf_1_18_13, mul_assoc, ← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  · intro n _
    have := (L2.integrable_inner (𝕜 := ℂ) (b n) f).const_mul (w n * b n x)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [RCLike.inner_apply]
    ring

/-- DLMF 1.18.34 (kernel form): `(Tf)(x) = ∫_X (∑ₙ λₙ φₙ(x) conj(φₙ(y))) f(y) dy`, in the mean
with the partial kernels. -/
theorem dlmf_1_18_34_kernel {D : Submodule ℂ (Lp ℂ 2 (volume.restrict X))}
    {T : D →ₗ[ℂ] Lp ℂ 2 (volume.restrict X)} (hT : IsSymmetricOn T) (lam : ℕ → ℝ)
    (hb : ∀ n, ∃ h : b n ∈ D, T ⟨b n, h⟩ = (lam n : ℂ) • b n) (f : D) :
    Tendsto (fun m : ℕ => ∫ x in X,
      ‖(T f : ℝ → ℂ) x - ∫ y in X, kernelWeighted b (fun n => lam n) m x y * (f : ℝ → ℂ) y‖ ^ 2)
      atTop (𝓝 0) := by
  have h := tendsto_integral_sub_partialSum b (dlmf_1_18_34 b hT lam hb f).2
  simpa only [sum_eq_integral_kernelWeighted] using h

/-- DLMF 1.18.35 (kernel form): `(F(T)f)(x) = ∫_X (∑ₙ F(λₙ) φₙ(x) conj(φₙ(y))) f(y) dy`, in the
mean with the partial kernels. -/
theorem dlmf_1_18_35_kernel (lam : ℕ → ℝ) (F : ℝ → ℂ) (C : ℝ) (hF : ∀ n, ‖F (lam n)‖ ≤ C)
    (f : Lp ℂ 2 (volume.restrict X)) :
    Tendsto (fun m : ℕ => ∫ x in X,
      ‖(spectralCalculus b lam F C hF f : ℝ → ℂ) x -
        ∫ y in X, kernelWeighted b (fun n => F (lam n)) m x y * f y‖ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_integral_sub_partialSum b (dlmf_1_18_35 lam F C hF f)
  simpa only [sum_eq_integral_kernelWeighted] using h

end Kernel

end Azurite.DLMF
