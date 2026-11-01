/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Continuous
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# DLMF §1.18(viii): Mixed spectra and eigenfunction expansions

https://dlmf.nist.gov/1.18.viii

Up to (not including) Example 1. A mixed spectrum, continuous `σ_c = [0, ∞)` plus a point spectrum
`{λₙ}` indexed by any type `ι`, is a unitary spectral representation
`U : V ≃ₗᵢ L²(σ_c) ⊕ ℓ²(ι)` (the `L²` direct sum `WithLp 2 (L2sigma × ℓ²(ι, ℂ))`). The coefficients
are `f̂(λ) = (Uf)_c` (`hatC`, 1.18.47) and `f̂(λₙ) = (Uf)_p(n) = ⟨f, φ_{λₙ}⟩` (`hatP`, `hatP_eq`,
1.18.32). The `L²` eigenfunctions are `φ_{λₙ} = U⁻¹(0, eₙ)` (`pointFun`). Superpositions of the
non-`L²` continuum eigenfunctions are `contSuper`.

* 1.18.60–1.18.62: normalization and orthogonality, 1.18.60 and 1.18.62 in weak form.
* 1.18.63: the completeness relation in weak form,
  `⟨f, g⟩ = ∫ f̂ conj ĝ + ∑ f̂(λₙ) conj ĝ(λₙ)`.
* 1.18.64: `f = ∫_{σ_c} f̂ φ_λ dλ + ∑ f̂(λₙ) φ_{λₙ}`, the sum converging in norm, for every `f`
  (DLMF assumes `f ∈ C(X) ∩ L²(X)`, which is not needed).
* 1.18.65: Parseval for the mixed spectrum.
* The analogs of 1.18.49–1.18.52: `F(T)` for bounded `F` (`mixedSpectralOp`, with the diagonal
  operator `diagOp` on `ℓ²`) and `⟨F(T)f, f⟩` (`dlmfInner_mixedSpectralOp`). 1.18.66 is the
  resolvent case (`mixedResolvent`, `dlmf_1_18_66`).
* The poles of 1.18.66: at an isolated eigenvalue `λₘ < 0`, `(z − λₘ)` times the right-hand side
  tends to `|f̂(λₘ)|²` (`dlmf_1_18_66_residue`, by Tannery's theorem and dominated convergence).
  The branch-cut discontinuity is that of the continuous part, 1.18.53. The remarks on
  resonances and dilatation transformations are descriptive and not formalized.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory Complex WithLp
open scoped InnerProductSpace ComplexConjugate Real lp

namespace Azurite.DLMF

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
  (U : V ≃ₗᵢ[ℂ] WithLp 2 (L2sigma × ℓ²(ι, ℂ)))

/-! ### The mixed spectral representation -/

/-- DLMF 1.18.47: the continuous-spectrum coefficients `f̂(λ)`, `λ ∈ σ_c`. -/
noncomputable def hatC (f : V) : L2sigma := (U f).fst

/-- DLMF 1.18.32: the point-spectrum coefficients `f̂(λₙ)`. -/
noncomputable def hatP (f : V) (n : ι) : ℂ := (U f).snd n

/-- The `L²` eigenfunction `φ_{λₙ}` of the point spectrum. -/
noncomputable def pointFun [DecidableEq ι] (n : ι) : V := U.symm (toLp 2 (0, lp.single 2 n 1))

/-- Superposition `∫ a(λ) φ_λ dλ` of continuum eigenfunctions with an `L²` weight `a`. -/
noncomputable def contSuper (a : L2sigma) : V := U.symm (toLp 2 (a, 0))

theorem dlmfInner_U (f g : V) : dlmfInner f g = dlmfInner (U f) (U g) := by
  simp only [dlmfInner]
  exact (U.toLinearIsometry.inner_map_map g f).symm

theorem dlmfInner_withLp (x y : WithLp 2 (L2sigma × ℓ²(ι, ℂ))) :
    dlmfInner x y = dlmfInner x.fst y.fst + dlmfInner x.snd y.snd := by
  simp only [dlmfInner, prod_inner_apply, ofLp_fst, ofLp_snd]

theorem dlmfInner_lp (c d : ℓ²(ι, ℂ)) : dlmfInner c d = ∑' n, c n * conj (d n) := by
  rw [dlmfInner, lp.inner_eq_tsum]
  congr 1

/-- `f̂(λₙ) = ⟨f, φ_{λₙ}⟩`. -/
theorem hatP_eq [DecidableEq ι] (f : V) (n : ι) : hatP U f n = dlmfInner f (pointFun U n) := by
  rw [dlmfInner_U, pointFun, LinearIsometryEquiv.apply_symm_apply, dlmfInner_withLp]
  simp only [toLp_fst, toLp_snd, dlmfInner, inner_zero_left, zero_add, lp.inner_single_left,
    RCLike.inner_apply, map_one, mul_one]
  rfl

/-- DLMF 1.18.61: `∫_X φ_{λₙ} conj φ_{λₘ} = δ_{n,m}`. -/
theorem dlmf_1_18_61 [DecidableEq ι] (n m : ι) :
    dlmfInner (pointFun U n) (pointFun U m) = if n = m then 1 else 0 := by
  rw [← hatP_eq, hatP, pointFun, LinearIsometryEquiv.apply_symm_apply, toLp_snd,
    lp.single_apply, Pi.single_apply]
  by_cases h : n = m
  · subst h; simp
  · simp [h, Ne.symm h]

/-- DLMF 1.18.60, `∫_X φ_λ conj φ_λ′ = δ(λ − λ′)`, in weak form. -/
theorem dlmf_1_18_60 (a b : L2sigma) :
    dlmfInner (contSuper U a) (contSuper U b) = ∫ l in Ici 0, a l * conj (b l) := by
  rw [dlmfInner_U, contSuper, contSuper, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply, dlmfInner_withLp]
  simp only [toLp_fst, toLp_snd, dlmfInner, inner_zero_left, add_zero]
  exact dlmfInner_Lp_eq a b

/-- DLMF 1.18.62, `∫_X φ_{λₙ} conj φ_λ = 0`, in weak form. -/
theorem dlmf_1_18_62 [DecidableEq ι] (n : ι) (a : L2sigma) :
    dlmfInner (pointFun U n) (contSuper U a) = 0 := by
  rw [dlmfInner_U, contSuper, pointFun, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply, dlmfInner_withLp]
  simp [dlmfInner]

/-- DLMF 1.18.63, the completeness relation, in weak form:
`⟨f, g⟩ = ∫_{σ_c} f̂ conj ĝ dλ + ∑_{σ_p} f̂(λₙ) conj ĝ(λₙ)`. -/
theorem dlmf_1_18_63 (f g : V) :
    dlmfInner f g = (∫ l in Ici 0, hatC U f l * conj (hatC U g l)) +
      ∑' n, hatP U f n * conj (hatP U g n) := by
  rw [dlmfInner_U, dlmfInner_withLp, dlmfInner_Lp_eq, dlmfInner_lp]
  rfl

/-- DLMF 1.18.64: `f = ∫_{σ_c} f̂(λ) φ_λ dλ + ∑_{σ_p} f̂(λₙ) φ_{λₙ}`, the sum converging in norm. -/
theorem dlmf_1_18_64 [DecidableEq ι] (f : V) :
    HasSum (fun n => hatP U f n • pointFun U n) (f - contSuper U (hatC U f)) := by
  have h := (lp.hasSum_single (p := 2) (E := fun _ : ι => ℂ) (by norm_num) (U f).snd)
  set L : ℓ²(ι, ℂ) →L[ℂ] V := (U.symm.toLinearIsometry.toContinuousLinearMap).comp
    ((prodContinuousLinearEquiv 2 ℂ L2sigma ℓ²(ι, ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℂ L2sigma ℓ²(ι, ℂ)))
  have hL : ∀ c : ℓ²(ι, ℂ), L c = U.symm (toLp 2 (0, c)) := fun c => rfl
  have h2 := h.mapL L
  have e1 : ∀ n, L (lp.single 2 n ((U f).snd n)) = hatP U f n • pointFun U n := fun n => by
    rw [hL, pointFun, ← map_smul]
    congr 1
    rw [← toLp_smul, Prod.smul_mk, smul_zero, ← lp.single_smul, smul_eq_mul, mul_one]
    rfl
  have e2 : L (U f).snd = f - contSuper U (hatC U f) := by
    rw [hL, contSuper, hatC, eq_sub_iff_add_eq, ← map_add, ← toLp_add, Prod.mk_add_mk, zero_add,
      add_zero]
    rw [show toLp 2 ((U f).fst, (U f).snd) = U f from WithLp.toLp_ofLp (p := 2) (U f),
      U.symm_apply_apply]
  simp only [e1, e2] at h2
  exact h2

/-- DLMF 1.18.65: `∫_X |f|² = ∫_{σ_c} |f̂(λ)|² dλ + ∑_{σ_p} |f̂(λₙ)|²`. -/
theorem dlmf_1_18_65 (f : V) :
    ‖f‖ ^ 2 = (∫ l in Ici 0, ‖hatC U f l‖ ^ 2) + ∑' n, ‖hatP U f n‖ ^ 2 := by
  rw [← U.norm_map, prod_norm_sq_eq_of_L2, ← integral_norm_sq_Lp]
  congr 1
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (U f).snd
  simp only [hatP]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-! ### Diagonal operators on `ℓ²` -/

/-- `w` truncated to `|w| ≤ C`. -/
noncomputable def truncW (w : ι → ℂ) (C : ℝ) (n : ι) : ℂ := if ‖w n‖ ≤ C then w n else 0

theorem norm_truncW_le (w : ι → ℂ) (C : ℝ) (n : ι) : ‖truncW w C n‖ ≤ max C 0 := by
  unfold truncW
  split_ifs with h
  · exact h.trans (le_max_left _ _)
  · simp

theorem summable_norm_sq_lpι (c : ℓ²(ι, ℂ)) : Summable fun n => ‖c n‖ ^ 2 := by
  have hs := (lp.memℓp c).summable (p := 2) (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

theorem norm_sq_lpι (c : ℓ²(ι, ℂ)) : ‖c‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) c
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem memℓp_truncW_mul (w : ι → ℂ) (C : ℝ) (c : ℓ²(ι, ℂ)) :
    Memℓp (fun n => truncW w C n * c n) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine ((summable_norm_sq_lpι c).mul_left (max C 0 ^ 2)).of_nonneg_of_le (fun n => by positivity)
    fun n => ?_
  rw [norm_mul, mul_pow]
  gcongr
  exact norm_truncW_le w C n

theorem norm_truncW_mul_le (w : ι → ℂ) (C : ℝ) (c : ℓ²(ι, ℂ)) :
    ‖(⟨fun n => truncW w C n * c n, memℓp_truncW_mul w C c⟩ : ℓ²(ι, ℂ))‖ ≤ max C 0 * ‖c‖ := by
  have hsq : ‖(⟨fun n => truncW w C n * c n, memℓp_truncW_mul w C c⟩ : ℓ²(ι, ℂ))‖ ^ 2 ≤
      (max C 0 * ‖c‖) ^ 2 := by
    rw [norm_sq_lpι, mul_pow, norm_sq_lpι, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ ((summable_norm_sq_lpι c).mul_left _)
    · change ‖truncW w C n * c n‖ ^ 2 ≤ max C 0 ^ 2 * ‖c n‖ ^ 2
      rw [norm_mul, mul_pow]
      gcongr
      exact norm_truncW_le w C n
    · exact summable_norm_sq_lpι ⟨fun n => truncW w C n * c n, memℓp_truncW_mul w C c⟩
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The diagonal operator `(cₙ) ↦ (wₙ cₙ)` (with `w` truncated to `|w| ≤ C`). -/
noncomputable def diagOp (w : ι → ℂ) (C : ℝ) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨fun n => truncW w C n * c n, memℓp_truncW_mul w C c⟩
      map_add' := fun c d => by
        ext n
        simp only [lp.coeFn_add, Pi.add_apply]
        exact mul_add _ _ _
      map_smul' := fun r c => by
        ext n
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact mul_left_comm _ _ _ }
    (max C 0) (norm_truncW_mul_le w C)

theorem diagOp_apply {w : ι → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C) (c : ℓ²(ι, ℂ)) (n : ι) :
    diagOp w C c n = w n * c n := by
  change truncW w C n * c n = _
  rw [truncW]
  simp only [hw n, ite_true]

/-! ### Functions of `T` and the resolvent (1.18.66) -/

/-- `F(T)` for the mixed spectrum: multiplication by `F(λ)` on `σ_c` and by `F(λₙ)` on `σ_p`. -/
noncomputable def mixedSpectralOp (F : ℝ → ℂ) (hF : Measurable F) (Cc : ℝ) (lam : ι → ℝ)
    (Cp : ℝ) (f : V) : V :=
  U.symm (toLp 2 (multOp F hF Cc (U f).fst, diagOp (fun n => F (lam n)) Cp (U f).snd))

/-- DLMF §1.18(viii): the analog of 1.18.51,
`⟨F(T)f, f⟩ = ∫_{σ_c} F(λ) |f̂(λ)|² dλ + ∑_{σ_p} F(λₙ) |f̂(λₙ)|²`. -/
theorem dlmfInner_mixedSpectralOp {F : ℝ → ℂ} (hF : Measurable F) {Cc : ℝ}
    (hb : ∀ l, 0 ≤ l → ‖F l‖ ≤ Cc) (lam : ι → ℝ) {Cp : ℝ} (hbp : ∀ n, ‖F (lam n)‖ ≤ Cp)
    (f : V) : dlmfInner (mixedSpectralOp U F hF Cc lam Cp f) f =
      (∫ l in Ici 0, F l * ((‖hatC U f l‖ ^ 2 : ℝ) : ℂ)) +
        ∑' n, F (lam n) * ((‖hatP U f n‖ ^ 2 : ℝ) : ℂ) := by
  rw [dlmfInner_U, mixedSpectralOp, LinearIsometryEquiv.apply_symm_apply, dlmfInner_withLp]
  simp only [toLp_fst, toLp_snd]
  congr 1
  · rw [dlmfInner_Lp_eq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_multOp hF hb (U f).fst] with l hl
    rw [hl, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  · rw [dlmfInner_lp]
    congr 1
    funext n
    rw [diagOp_apply hbp, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl

/-- The resolvent `(z − T)⁻¹` for the mixed spectrum (`Cp` bounds `|z − λₙ|⁻¹`). -/
noncomputable def mixedResolvent (lam : ι → ℝ) (z : ℂ) (Cp : ℝ) (f : V) : V :=
  mixedSpectralOp U (fun l : ℝ => (z - l)⁻¹) (measurable_resolventFun z) (resDist z)⁻¹ lam Cp f

/-- DLMF 1.18.66: for `z ∉ σ`,
`⟨(z − T)⁻¹f, f⟩ = ∑_{σ_p} |f̂(λₙ)|²/(z − λₙ) + ∫_{σ_c} |f̂(λ)|² dλ/(z − λ)`. -/
theorem dlmf_1_18_66 (lam : ι → ℝ) {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) {Cp : ℝ}
    (hCp : ∀ n, ‖(z - lam n)⁻¹‖ ≤ Cp) (f : V) :
    dlmfInner (mixedResolvent U lam z Cp f) f =
      (∑' n, ((‖hatP U f n‖ ^ 2 : ℝ) : ℂ) / (z - lam n)) +
        ∫ l in Ici 0, ((‖hatC U f l‖ ^ 2 : ℝ) : ℂ) / (z - l) := by
  rw [mixedResolvent, dlmfInner_mixedSpectralOp U _ (norm_resolventFun_le hz) lam hCp, add_comm]
  congr 1
  · congr 1; funext n; rw [div_eq_mul_inv, mul_comm]
  · refine integral_congr_ae (ae_of_all _ fun l => ?_)
    simp only
    rw [div_eq_mul_inv, mul_comm]

/-! ### Poles at isolated eigenvalues -/

theorem norm_sub_ofReal_ge {z : ℂ} {a b r : ℝ} (hz : ‖z - a‖ < r) (hab : 2 * r ≤ |a - b|) :
    r ≤ ‖z - b‖ := by
  have h1 : ‖((a : ℂ) - b)‖ ≤ ‖z - b‖ + ‖z - a‖ := by
    calc ‖((a : ℂ) - b)‖ = ‖(z - b) - (z - a)‖ := by ring_nf
      _ ≤ ‖z - b‖ + ‖z - a‖ := norm_sub_le _ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

theorem tendsto_sub_ofReal_nhdsNE (c b : ℝ) :
    Tendsto (fun z : ℂ => z - b) (𝓝[≠] (c : ℂ)) (𝓝 ((c : ℂ) - b)) :=
  ((by fun_prop : Continuous fun z : ℂ => z - (b : ℂ)).tendsto (c : ℂ)).mono_left
    nhdsWithin_le_nhds

/-- DLMF §1.18(viii): the representation 1.18.66 has a pole with residue `|f̂(λₘ)|²` at an
isolated eigenvalue `λₘ < 0` (one at distance `δ > 0` from the other eigenvalues): as
`z → λₘ`, `(z − λₘ)` times the right-hand side of 1.18.66 tends to `|f̂(λₘ)|²`. -/
theorem dlmf_1_18_66_residue (lam : ι → ℝ) {m : ι} (hm : lam m < 0) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ n, n ≠ m → δ ≤ |lam n - lam m|) (f : V) :
    Tendsto (fun z : ℂ => (z - lam m) * ((∑' n, ((‖hatP U f n‖ ^ 2 : ℝ) : ℂ) / (z - lam n)) +
      ∫ l in Ici 0, ((‖hatC U f l‖ ^ 2 : ℝ) : ℂ) / (z - l)))
      (𝓝[≠] (lam m : ℂ)) (𝓝 ((‖hatP U f m‖ ^ 2 : ℝ) : ℂ)) := by
  classical
  set a : ι → ℝ := fun n => ‖hatP U f n‖ ^ 2
  set b : ℝ → ℝ := fun l => ‖hatC U f l‖ ^ 2
  have ha : Summable a := summable_norm_sq_lpι (U f).snd
  have hb : Integrable (fun l => ((b l : ℝ) : ℂ)) (volume.restrict (Ici (0 : ℝ))) :=
    integrable_sq_contCoeff (V := L2sigma) (LinearIsometryEquiv.refl ℂ L2sigma) (U f).fst
  set r := min (δ / 2) (-lam m / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] (lam m : ℂ), ‖z - (lam m : ℂ)‖ < r ∧ z ≠ (lam m : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hr), self_mem_nhdsWithin]
      with z hz hz'
    exact ⟨by rwa [Metric.mem_ball, dist_eq_norm] at hz, hz'⟩
  -- the point-spectrum sum
  have hsum : Tendsto (fun z : ℂ => ∑' n, (z - lam m) * (((a n : ℝ) : ℂ) / (z - lam n)))
      (𝓝[≠] (lam m : ℂ)) (𝓝 (∑' n, if n = m then ((a m : ℝ) : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := a) ha (fun k => ?_) ?_
    · by_cases hk : k = m
      · subst hk
        simp only [ite_true]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ lam k)
        field_simp [sub_ne_zero.mpr hz]
      · simp only [hk, ite_false]
        have hne : ((lam m : ℂ) - lam k) ≠ 0 := by
          rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero, sub_ne_zero]
          intro h
          have := hgap k hk
          rw [h, sub_self, abs_zero] at this
          linarith
        have h1 : Tendsto (fun z : ℂ => z - lam m) (𝓝[≠] (lam m : ℂ)) (𝓝 0) := by
          simpa using tendsto_sub_ofReal_nhdsNE (lam m) (lam m)
        have h2 : Tendsto (fun z : ℂ => ((a k : ℝ) : ℂ) / (z - lam k)) (𝓝[≠] (lam m : ℂ))
            (𝓝 (((a k : ℝ) : ℂ) / ((lam m : ℂ) - lam k))) :=
          tendsto_const_nhds.div (tendsto_sub_ofReal_nhdsNE (lam m) (lam k)) hne
        simpa using h1.mul h2
    · filter_upwards [hnear] with z ⟨hz, hz'⟩ k
      by_cases hk : k = m
      · subst hk
        rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (sub_ne_zero.mpr hz'), mul_one,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      · have hk' : r ≤ ‖z - lam k‖ :=
          norm_sub_ofReal_ge hz (by
            rw [abs_sub_comm]
            linarith [hgap k hk, min_le_left (δ / 2) (-lam m / 2)])
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ a k)]
        have hpos : 0 < ‖z - lam k‖ := hr.trans_le hk'
        rw [mul_div_assoc', div_le_iff₀ hpos]
        have : 0 ≤ a k := by positivity
        nlinarith [hz.le]
  -- the continuous-spectrum integral
  have hint : Tendsto (fun z : ℂ => ∫ l in Ici 0, (z - lam m) * (((b l : ℝ) : ℂ) / (z - l)))
      (𝓝[≠] (lam m : ℂ)) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun l => ‖((b l : ℝ) : ℂ)‖)
      (l := 𝓝[≠] (lam m : ℂ)) (μ := volume.restrict (Ici (0 : ℝ)))
      (F := fun z l => (z - lam m) * (((b l : ℝ) : ℂ) / (z - l))) (f := fun _ => 0)
      (Eventually.of_forall fun z => ((hb.aestronglyMeasurable.mul
        (measurable_resolventFun z).aestronglyMeasurable).const_mul (z - lam m)).congr
          (ae_of_all _ fun l => by simp only [Pi.mul_apply, div_eq_mul_inv]))
      (by
        filter_upwards [hnear] with z ⟨hz, _⟩
        refine ae_restrict_of_forall_mem measurableSet_Ici fun l (hl : 0 ≤ l) => ?_
        have hk' : r ≤ ‖z - l‖ := norm_sub_ofReal_ge hz (by
          rw [abs_of_neg (by linarith)]; linarith [min_le_right (δ / 2) (-lam m / 2)])
        have hpos : 0 < ‖z - l‖ := hr.trans_le hk'
        rw [norm_mul, norm_div, mul_div_assoc', div_le_iff₀ hpos]
        nlinarith [hz.le, norm_nonneg (((b l : ℝ) : ℂ))])
      hb.norm
      (ae_restrict_of_forall_mem measurableSet_Ici fun l (hl : 0 ≤ l) => by
        have hne : ((lam m : ℂ) - l) ≠ 0 := by
          rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero, sub_ne_zero]; intro h; linarith
        have h1 : Tendsto (fun z : ℂ => z - lam m) (𝓝[≠] (lam m : ℂ)) (𝓝 0) := by
          simpa using tendsto_sub_ofReal_nhdsNE (lam m) (lam m)
        have hc : Tendsto (fun _ : ℂ => ((b l : ℝ) : ℂ)) (𝓝[≠] (lam m : ℂ))
            (𝓝 ((b l : ℝ) : ℂ)) := tendsto_const_nhds
        have h2 := hc.div (tendsto_sub_ofReal_nhdsNE (lam m) l) hne
        simpa using h1.mul h2)
    simpa using h
  have hcomb := hsum.add hint
  rw [tsum_ite_eq, add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z _
  rw [mul_add, ← tsum_mul_left, ← integral_const_mul]

end Azurite.DLMF
