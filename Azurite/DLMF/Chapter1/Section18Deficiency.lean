/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18OpSpectrum
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# DLMF §1.18(ix): deficiency spaces of a symmetric operator

https://dlmf.nist.gov/1.18.ix

`N_z = {v ∈ D(T*) | T*v = zv}` (`deficiencySpace`), closed, equal to `R(z̄ − T)^⊥`
(`deficiencySpace_eq_orthogonal`).

* `dlmf_1_18_ix_deficiency_const`: `dim N_z` is constant for `ℑz > 0` and for `ℑz < 0`. The key
  estimate (`eq_zero_of_mem_deficiencySpace_of_orthogonal`): for `|z − w| < |ℑw|`, no nonzero
  vector of `N_z` is orthogonal to `N_w`. So orthogonal projection `N_z → N_w` is injective,
  `dim` is locally constant, and each half-plane is connected.
* `deficiencyIndices`: `(n₊, n₋) = (dim N_i, dim N_{−i})`.
-/

open LinearPMap Topology Filter
open scoped ComplexConjugate InnerProductSpace

namespace Azurite.DLMF

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- DLMF §1.18(ix): the deficiency space `N_z = {v ∈ D(T*) | T*v = zv}`. -/
noncomputable def deficiencySpace (T : V →ₗ.[ℂ] V) (z : ℂ) : Submodule ℂ V :=
  eigenspaceDLMF T† z

theorem isClosed_deficiencySpace {T : V →ₗ.[ℂ] V} (hT : Dense (T.domain : Set V)) (z : ℂ) :
    IsClosed (deficiencySpace T z : Set V) :=
  isClosed_eigenspaceDLMF (adjoint_isClosed hT) z

instance {T : V →ₗ.[ℂ] V} [Fact (Dense (T.domain : Set V))] (z : ℂ) :
    CompleteSpace (deficiencySpace T z) :=
  have : IsClosed (deficiencySpace T z : Set V) :=
    isClosed_deficiencySpace (Fact.out) z
  IsClosed.completeSpace_coe

/-- `N_z = R(z̄ − T)^⊥`. -/
theorem mem_deficiencySpace_iff {T : V →ₗ.[ℂ] V} (hT : Dense (T.domain : Set V)) (z : ℂ)
    (v : V) : v ∈ deficiencySpace T z ↔ ∀ x : T.domain, ⟪v, shiftOp T (conj z) x⟫_ℂ = 0 := by
  rw [orthogonal_range_shiftOp hT, Complex.conj_conj, deficiencySpace, mem_eigenspaceDLMF]

theorem deficiencySpace_eq_orthogonal {T : V →ₗ.[ℂ] V} (hT : Dense (T.domain : Set V)) (z : ℂ) :
    deficiencySpace T z = (LinearMap.range (shiftOp T (conj z)))ᗮ := by
  ext v
  rw [mem_deficiencySpace_iff hT, Submodule.mem_orthogonal]
  simp only [LinearMap.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact ⟨fun h x => by rw [inner_eq_zero_symm]; exact h x,
    fun h x => by rw [inner_eq_zero_symm]; exact h x⟩

/-- The key estimate: if `|z − w| < |ℑw|`, a vector of `N_z` orthogonal to `N_w` vanishes. -/
theorem eq_zero_of_mem_deficiencySpace_of_orthogonal {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T)
    {z w : ℂ} (hzw : ‖z - w‖ < |w.im|) {v : V} (hv : v ∈ deficiencySpace T z)
    (hvw : v ∈ (deficiencySpace T w)ᗮ) : v = 0 := by
  have hwim : 0 < |w.im| := (norm_nonneg _).trans_lt hzw
  set q := ‖z - w‖ / |w.im|
  have hq : q < 1 := (div_lt_one hwim).mpr hzw
  have hq0 : 0 ≤ q := by positivity
  -- `v` lies in the closure of `R(w̄ − T)`
  rw [deficiencySpace_eq_orthogonal hT.1, Submodule.orthogonal_orthogonal_eq_closure] at hvw
  have hcl : v ∈ closure (LinearMap.range (shiftOp T (conj w)) : Set V) := hvw
  -- `v ∈ D(T*)` with `T*v = zv`
  obtain ⟨hvd, hTv⟩ := mem_eigenspaceDLMF.mp hv
  have hinner : ∀ x : T.domain, ⟪v, shiftOp T (conj w) x⟫_ℂ = (conj w - conj z) * ⟪v, (x : V)⟫_ℂ :=
    fun x => by
      have h1 := (adjoint_isFormalAdjoint hT.1) ⟨v, hvd⟩ x
      rw [hTv, inner_smul_left] at h1
      rw [shiftOp_apply, inner_sub_right, inner_smul_right, ← h1]
      ring
  have hbound : ∀ ε > 0, ‖v‖ ^ 2 ≤ q * ‖v‖ * (‖v‖ + ε) + ‖v‖ * ε := by
    intro ε hε
    obtain ⟨y, hy, hyv⟩ := Metric.mem_closure_iff.mp hcl ε hε
    obtain ⟨x, rfl⟩ := hy
    have hx := hT.norm_shiftOp_ge (conj w) x
    rw [Complex.conj_im, abs_neg] at hx
    have hy' : ‖shiftOp T (conj w) x‖ ≤ ‖v‖ + ε := by
      have := norm_sub_norm_le (shiftOp T (conj w) x) v
      rw [← dist_eq_norm, dist_comm] at this
      linarith
    have h1 : ‖⟪v, shiftOp T (conj w) x⟫_ℂ‖ ≤ q * ‖v‖ * (‖v‖ + ε) := by
      rw [hinner, norm_mul, ← _root_.map_sub, Complex.norm_conj, ← norm_neg, neg_sub]
      have h2 : ‖(x : V)‖ ≤ (‖v‖ + ε) / |w.im| := by
        rw [le_div_iff₀ hwim, mul_comm]; exact hx.trans hy'
      calc ‖z - w‖ * ‖⟪v, (x : V)⟫_ℂ‖ ≤ ‖z - w‖ * (‖v‖ * ‖(x : V)‖) :=
            mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
        _ ≤ ‖z - w‖ * (‖v‖ * ((‖v‖ + ε) / |w.im|)) := by gcongr
        _ = q * ‖v‖ * (‖v‖ + ε) := by simp only [q]; ring
    have h3 : ‖⟪v, v - shiftOp T (conj w) x⟫_ℂ‖ ≤ ‖v‖ * ε := by
      refine (norm_inner_le_norm _ _).trans ?_
      gcongr
      rw [← dist_eq_norm]; exact hyv.le
    have h4 : ‖v‖ ^ 2 = ‖⟪v, v⟫_ℂ‖ := by
      rw [show ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) from dlmfInner_self v, Complex.norm_real,
        Real.norm_of_nonneg (sq_nonneg _)]
    have h5 : ⟪v, v⟫_ℂ = ⟪v, shiftOp T (conj w) x⟫_ℂ + ⟪v, v - shiftOp T (conj w) x⟫_ℂ := by
      rw [inner_sub_right]; ring
    rw [h4, h5]
    exact (norm_add_le _ _).trans (add_le_add h1 h3)
  have hle : ‖v‖ ^ 2 * (1 - q) ≤ 0 := by
    by_contra hc
    push Not at hc
    have hv0 : 0 < ‖v‖ := by
      by_contra h0
      push Not at h0
      have : ‖v‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [this] at hc
      simp at hc
    set ε := ‖v‖ ^ 2 * (1 - q) / (2 * (‖v‖ * (q + 1)))
    have hε : 0 < ε := by positivity
    have := hbound ε hε
    have hεeq : ‖v‖ * (q + 1) * ε = ‖v‖ ^ 2 * (1 - q) / 2 := by
      simp only [ε]; field_simp
    nlinarith
  have h1q : 0 < 1 - q := by linarith
  have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))

/-- `dim N_z ≤ dim N_w` when `|z − w| < |ℑw|`. -/
theorem rank_deficiencySpace_le {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) {z w : ℂ}
    (hzw : ‖z - w‖ < |w.im|) :
    Module.rank ℂ (deficiencySpace T z) ≤ Module.rank ℂ (deficiencySpace T w) := by
  have : Fact (Dense (T.domain : Set V)) := ⟨hT.1⟩
  refine LinearMap.rank_le_of_injective (((deficiencySpace T w).orthogonalProjectionOnto
    : V →L[ℂ] deficiencySpace T w).toLinearMap.comp (deficiencySpace T z).subtype) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h : (v : V) ∈ (deficiencySpace T w)ᗮ :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hv
  have h2 : (v : V) = 0 := eq_zero_of_mem_deficiencySpace_of_orthogonal hT hzw v.2 h
  exact (Submodule.coe_eq_zero).mp h2

/-- `dim N_z = dim N_w` for `z, w` close in the same half-plane. -/
theorem rank_deficiencySpace_eq_of_near {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) {z w : ℂ}
    (hz : ‖z - w‖ < |z.im|) (hw : ‖z - w‖ < |w.im|) :
    Module.rank ℂ (deficiencySpace T z) = Module.rank ℂ (deficiencySpace T w) :=
  le_antisymm (rank_deficiencySpace_le hT hw)
    (rank_deficiencySpace_le hT (by rw [← norm_neg, neg_sub]; exact hz))

theorem rank_deficiencySpace_const {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) {H : Set ℂ}
    (hH : IsPreconnected H) (hHim : ∀ z ∈ H, ∀ w ∈ H, z.im * w.im > 0) {z w : ℂ} (hz : z ∈ H)
    (hw : w ∈ H) :
    Module.rank ℂ (deficiencySpace T z) = Module.rank ℂ (deficiencySpace T w) := by
  have : PreconnectedSpace H := isPreconnected_iff_preconnectedSpace.mp hH
  have hlc : IsLocallyConstant fun u : H => Module.rank ℂ (deficiencySpace T u) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    have him : 0 < |(u : ℂ).im| := by
      have := hHim u u.2 u u.2
      exact abs_pos.mpr fun h => by rw [h, zero_mul] at this; exact lt_irrefl _ this
    have hball : Metric.ball (u : ℂ) (|(u : ℂ).im| / 2) ∈ 𝓝 (u : ℂ) :=
      Metric.ball_mem_nhds _ (by positivity)
    have hev : ∀ᶠ y : H in 𝓝 u, (y : ℂ) ∈ Metric.ball (u : ℂ) (|(u : ℂ).im| / 2) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hball
    filter_upwards [hev] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hyim : |(u : ℂ).im| / 2 < |(y : ℂ).im| := by
      have h1 : |(u : ℂ).im - (y : ℂ).im| ≤ ‖(y : ℂ) - u‖ := by
        rw [← Complex.sub_im, ← norm_neg ((y : ℂ) - u), neg_sub]
        exact Complex.abs_im_le_norm _
      have := abs_sub_abs_le_abs_sub (u : ℂ).im (y : ℂ).im
      linarith
    refine rank_deficiencySpace_eq_of_near hT ?_ ?_
    · linarith
    · have : ‖(u : ℂ) - y‖ = ‖(y : ℂ) - u‖ := by rw [← norm_neg, neg_sub]
      linarith
  exact hlc.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨w, hw⟩

/-- **DLMF §1.18(ix)**: `dim N_z` is constant for `ℑz > 0` and constant for `ℑz < 0`. -/
theorem dlmf_1_18_ix_deficiency_const {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T) {z w : ℂ}
    (hzw : (0 < z.im ∧ 0 < w.im) ∨ (z.im < 0 ∧ w.im < 0)) :
    Module.rank ℂ (deficiencySpace T z) = Module.rank ℂ (deficiencySpace T w) := by
  rcases hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · refine rank_deficiencySpace_const hT (H := {u | 0 < u.im})
      (convex_halfSpace_gt Complex.imLm.isLinear 0).isPreconnected
      (fun a ha b hb => mul_pos ha hb) hz hw
  · refine rank_deficiencySpace_const hT (H := {u | u.im < 0})
      (convex_halfSpace_lt Complex.imLm.isLinear 0).isPreconnected
      (fun a ha b hb => mul_pos_of_neg_of_neg ha hb) hz hw

/-- The deficiency indices `n₊ = dim N_i` and `n₋ = dim N_{−i}`. -/
noncomputable def deficiencyIndices (T : V →ₗ.[ℂ] V) : Cardinal × Cardinal :=
  (Module.rank ℂ (deficiencySpace T Complex.I), Module.rank ℂ (deficiencySpace T (-Complex.I)))

end Azurite.DLMF
