/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylReg
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# DLMF §1.18(ix): deficiency spaces of (1.18.28) are spaces of `L²` solutions

* `ode2c_eq_zero_on`: uniqueness for complex `w″ = W w` on an open interval.
* `dlmf_1_18_ix_deficiency_iff`: `f ∈ N_z` iff `f` is a.e. an ordinary `C²` solution of
  `ℒf = zf` in `L²(X)` (`IsSolution`). Proved via `isSolution_of_weak` (regularity) and
  `weak_of_isSolution` (integration by parts).
* `dlmf_1_18_ix_finrank_le`: `dim N_z ∈ {0, 1, 2}`, via the injective map `solData`
  `v ↦ (u(c), u′(c))`.
* `dlmf_1_18_ix_conj_iff`, `dlmf_1_18_ix_deficiency_eq`: `f ∈ N_z` iff `f̄ ∈ N_{z̄}`, so
  `dim N_z = dim N_{z̄}`.
* `dlmf_1_18_ix_exists_selfAdjoint`: `ℒ` has self-adjoint extensions, with
  `n₊ = n₋ ∈ {0, 1, 2}`.
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-! ### Complex second-order linear ODEs: uniqueness on intervals -/

/-- Uniqueness to the right on `[x₁, x₂]` for `w″ = W w` with `W` bounded there. -/
theorem ode2c_eq_zero_Icc {W w w' : ℝ → ℂ} {K x1 x2 : ℝ}
    (hK : ∀ x ∈ Icc x1 x2, ‖W x‖ ≤ K) (hw : ∀ x ∈ Icc x1 x2, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Icc x1 x2, HasDerivAt w' (W x * w x) x) (h0 : w x1 = 0) (h1 : w' x1 = 0) :
    ∀ x ∈ Icc x1 x2, w x = 0 := by
  intro x hx
  set Y : ℝ → ℂ × ℂ := fun s => (w s, w' s)
  have hY : ∀ s ∈ Icc x1 x2, HasDerivAt Y (w' s, W s * w s) s := fun s hs =>
    (hw s hs).prodMk (hw' s hs)
  have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := Y)
    (f' := fun s => (w' s, W s * w s)) (K := max 1 K) (a := x1) (b := x2)
    (fun s hs => (hY s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hY s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simp [Y, h0, h1])
    fun s hs => by
      have hKs := hK s (Ico_subset_Icc_self hs)
      simp only [Prod.norm_def, Y]
      refine max_le ?_ ?_
      · calc ‖w' s‖ ≤ max ‖w s‖ ‖w' s‖ := le_max_right _ _
          _ ≤ max 1 K * max ‖w s‖ ‖w' s‖ :=
            le_mul_of_one_le_left (by positivity) (le_max_left _ _)
      · rw [norm_mul]
        calc ‖W s‖ * ‖w s‖ ≤ K * max ‖w s‖ ‖w' s‖ := by
              gcongr
              · exact (norm_nonneg _).trans hKs
              · exact le_max_left _ _
          _ ≤ max 1 K * max ‖w s‖ ‖w' s‖ := by gcongr; exact le_max_right _ _
  exact congrArg Prod.fst (h x hx)

/-- Uniqueness on an open interval `X` for `w″ = W w` with `W` continuous on `X`. -/
theorem ode2c_eq_zero_on {X : Set ℝ} (hXc : X.OrdConnected) {W w w' : ℝ → ℂ}
    (hW : ContinuousOn W X) (hw : ∀ x ∈ X, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ X, HasDerivAt w' (W x * w x) x) {c : ℝ} (hc : c ∈ X) (h0 : w c = 0)
    (h1 : w' c = 0) : ∀ x ∈ X, w x = 0 := by
  intro x hx
  rcases le_total c x with hcx | hxc
  · have hsub : Icc c x ⊆ X := hXc.out hc hx
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.mono hsub)
    exact ode2c_eq_zero_Icc hK (fun s hs => hw s (hsub hs)) (fun s hs => hw' s (hsub hs)) h0 h1
      x ⟨hcx, le_rfl⟩
  · have hsub : Icc x c ⊆ X := hXc.out hx hc
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.mono hsub)
    have hm : ∀ s ∈ Icc (-c) (-x), -s ∈ X := fun s hs =>
      hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := ode2c_eq_zero_Icc (W := fun s => W (-s)) (w := fun s => w (-s))
      (w' := fun s => -w' (-s)) (K := K) (x1 := -c) (x2 := -x)
      (fun s hs => hK (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (fun s hs => ((hw (-s) (hm s hs)).scomp s (hasDerivAt_neg s)).congr_deriv (by simp))
      (fun s hs => (((hw' (-s) (hm s hs)).scomp s (hasDerivAt_neg s)).neg).congr_deriv
        (by simp))
      (by simpa using h0) (by simp [h1]) (-x) ⟨by linarith, le_rfl⟩
    simpa using this

/-! ### Classical solutions -/

/-- `u` is a classical solution of `ℒu = zu`, i.e. `u″ = (q − z)u`, on `X`. -/
def IsSolution (X : Set ℝ) (q : ℝ → ℝ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ u' : ℝ → ℂ, ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x

variable {X : Set ℝ} {q : ℝ → ℝ}

theorem IsSolution.continuousOn {z : ℂ} {u : ℝ → ℂ} (hu : IsSolution X q z u) :
    ContinuousOn u X := by
  obtain ⟨u', hu'⟩ := hu
  exact fun x hx => (hu' x hx).1.continuousAt.continuousWithinAt

theorem L2X.locallyIntegrableOn (hX : IsOpen X) (v : L2X X) :
    LocallyIntegrableOn (v : ℝ → ℂ) X volume := by
  rw [locallyIntegrableOn_iff hX.isLocallyClosed]
  intro k hk hkc
  have hm : MemLp (v : ℝ → ℂ) 2 (volume.restrict k) :=
    (Lp.memLp v).mono_measure (Measure.restrict_mono hk le_rfl)
  have : IsFiniteMeasure (volume.restrict k) := ⟨by simpa using hkc.measure_lt_top⟩
  exact MemLp.integrable (by norm_num) hm

/-- A distributional solution of `ℒw = zw` is (a.e.) a classical `C²` solution. -/
theorem isSolution_of_weak (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {w : ℝ → ℂ} (hw : LocallyIntegrableOn w X) {z : ℂ}
    (h : ∀ φ : ℝ → ℂ, IsC2c X φ →
      ∫ x in X, w x * schrodingerOp q φ x = ∫ x in X, z * w x * φ x) :
    ∃ u, IsSolution X q z u ∧ w =ᵐ[volume.restrict X] u := by
  have hg : LocallyIntegrableOn (fun x => z * w x) X :=
    hw.continuousOn_mul continuousOn_const hX.isLocallyClosed
  obtain ⟨F, F', hwF, hF, hF'⟩ := weak_regularity hX hXc hne hq hw hg h
  obtain ⟨c, hc⟩ := hne
  have hFc : ContinuousOn F X := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  set G : ℝ → ℂ := fun t => ((q t : ℂ) - z) * F t
  have hGc : ContinuousOn G X :=
    ((Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const).mul hFc
  have hae : ∀ᵐ t ∂volume, t ∈ X → w t = F t := (ae_restrict_iff' hX.measurableSet).mp hwF
  have hF'eq : ∀ x ∈ X, F' x = F' c + ∫ t in c..x, G t := fun x hx => by
    rw [hF' c hc x hx]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht htI
    have htX : t ∈ X := hXc.uIcc_subset hc hx (uIoc_subset_uIcc htI)
    simp only [G, ht htX]
    ring
  refine ⟨F, ⟨F', fun x hx => ⟨hF x hx, ?_⟩⟩, hwF⟩
  have hd : HasDerivAt (fun y => F' c + ∫ t in c..y, G t) (G x) x :=
    (intervalIntegral.integral_hasDerivAt_right
      ((hGc.mono (hXc.uIcc_subset hc hx)).intervalIntegrable)
      (hGc.stronglyMeasurableAtFilter hX x hx) (hGc.continuousAt (hX.mem_nhds hx))).const_add _
  exact hd.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hX.mem_nhds hx) hF'eq)

/-- A classical solution satisfies the distributional equation (two integrations by parts). -/
theorem weak_of_isSolution (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {z : ℂ} {u : ℝ → ℂ} (hu : IsSolution X q z u) {φ : ℝ → ℂ}
    (hφ : IsC2c X φ) :
    ∫ x in X, u x * schrodingerOp q φ x = ∫ x in X, z * u x * φ x := by
  obtain ⟨u', hu'⟩ := hu
  obtain ⟨c, hc⟩ := hne
  obtain ⟨α, β, hα, hβ, hαβ, hK, -⟩ := exists_Ioo_of_isCompact hX hφ.2.1.isCompact hφ.2.2 hc
  have hIcc : Icc α β ⊆ X := hXc.out hα hβ
  have hI : ∀ x ∈ uIcc α β, x ∈ X := fun x hx => hIcc (by rwa [uIcc_of_le hαβ.le] at hx)
  have hφz : ∀ x ∉ Ioo α β, φ x = 0 := fun x hx =>
    ((notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hK h)).eq_of_nhds
  have hφ'z : ∀ x ∉ Ioo α β, deriv φ x = 0 := fun x hx => deriv_eq_zero_of_notMem' hK hx
  have hφ''z : ∀ x ∉ Ioo α β, deriv (deriv φ) x = 0 := fun x hx =>
    deriv_deriv_eq_zero_of_notMem hK hx
  have hφd := fun x => (hasDerivAt_deriv_of_contDiff_two hφ.1 x).1
  have hφdd := fun x => (hasDerivAt_deriv_of_contDiff_two hφ.1 x).2
  have hφ'' : Continuous (deriv (deriv φ)) := continuous_deriv_deriv hφ.1
  have hφ' : Continuous (deriv φ) := continuous_deriv' hφ.1
  have huc : ContinuousOn u (Icc α β) := fun x hx =>
    (hu' x (hIcc hx)).1.continuousAt.continuousWithinAt
  have hu'c : ContinuousOn u' (Icc α β) := fun x hx =>
    (hu' x (hIcc hx)).2.continuousAt.continuousWithinAt
  have hqc : ContinuousOn (fun x => (q x : ℂ)) (Icc α β) :=
    Complex.continuous_ofReal.comp_continuousOn (hq.mono hIcc)
  have ii : ∀ f : ℝ → ℂ, ContinuousOn f (Icc α β) → IntervalIntegrable f volume α β :=
    fun f hf => hf.intervalIntegrable_of_Icc hαβ.le
  -- `∫ u φ″ = −∫ u′ φ′ = ∫ (q − z) u φ`
  have e1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (u := u) (u' := u') (v := deriv φ) (v' := deriv (deriv φ))
    (fun x hx => (hu' x (hI x hx)).1) (fun x _ => hφdd x) (ii _ hu'c) (hφ''.intervalIntegrable _ _)
  have e2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (u := u') (u' := fun x => ((q x : ℂ) - z) * u x) (v := φ) (v' := deriv φ)
    (fun x hx => (hu' x (hI x hx)).2) (fun x _ => hφd x)
    (ii _ ((hqc.sub continuousOn_const).mul huc)) (hφ'.intervalIntegrable _ _)
  rw [hφ'z α (fun h => lt_irrefl _ h.1), hφ'z β (fun h => lt_irrefl _ h.2)] at e1
  rw [hφz α (fun h => lt_irrefl _ h.1), hφz β (fun h => lt_irrefl _ h.2)] at e2
  simp only [mul_zero, sub_zero, zero_sub] at e1 e2
  rw [setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by
      simp [schrodingerOp, hφz x hx, hφ''z x hx],
    setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by simp [hφz x hx]]
  have e3 : ∫ x in α..β, u x * schrodingerOp q φ x =
      -(∫ x in α..β, u x * deriv (deriv φ) x) + ∫ x in α..β, (q x : ℂ) * u x * φ x := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_add
      (f := fun x => -(u x * deriv (deriv φ) x)) (g := fun x => (q x : ℂ) * u x * φ x)
      (ii _ (huc.mul hφ''.continuousOn)).neg
      (ii _ ((hqc.mul huc).mul hφ.1.continuous.continuousOn))]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [schrodingerOp]; ring
  have e4 : ∫ x in α..β, ((q x : ℂ) - z) * u x * φ x =
      (∫ x in α..β, (q x : ℂ) * u x * φ x) - ∫ x in α..β, z * u x * φ x := by
    rw [← intervalIntegral.integral_sub (f := fun x => (q x : ℂ) * u x * φ x)
      (g := fun x => z * u x * φ x) (ii _ ((hqc.mul huc).mul hφ.1.continuous.continuousOn))
      (ii _ ((continuousOn_const.mul huc).mul hφ.1.continuous.continuousOn))]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [e3, e1, e2, e4]
  ring

/-- **DLMF §1.18(ix)**: `f ∈ N_z` iff `f` is (a.e.) an ordinary `C²` solution of `ℒf = zf` lying
in `L²(X)`. -/
theorem dlmf_1_18_ix_deficiency_iff (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) (z : ℂ) (v : L2X X) :
    v ∈ deficiencySpace (minOp X q) z ↔
      ∃ u, IsSolution X q z u ∧ (v : ℝ → ℂ) =ᵐ[volume.restrict X] u := by
  have hd := dense_minOp_domain hX hq
  have hsm : ∀ φ : ℝ → ℂ, ∫ x in X, ((z • v : L2X X) : ℝ → ℂ) x * φ x =
      ∫ x in X, z * (v : ℝ → ℂ) x * φ x := fun φ => integral_congr_ae (by
    filter_upwards [Lp.coeFn_smul z v] with x hx
    rw [hx]; rfl)
  constructor
  · intro hv
    obtain ⟨h, hT⟩ := mem_eigenspaceDLMF.mp hv
    have hw := (weak_schrodinger_iff hX hq v ((minOp X q)† ⟨v, h⟩)).mpr
      ((adjoint_isFormalAdjoint hd) ⟨v, h⟩)
    rw [hT] at hw
    exact isSolution_of_weak hX hXc hne hq (L2X.locallyIntegrableOn hX v) fun φ hφ => by
      rw [hw φ hφ, hsm]
  · rintro ⟨u, hu, hvu⟩
    have hweak : ∀ φ : ℝ → ℂ, IsC2c X φ → ∫ x in X, (v : ℝ → ℂ) x * schrodingerOp q φ x =
        ∫ x in X, ((z • v : L2X X) : ℝ → ℂ) x * φ x := fun φ hφ => by
      rw [hsm]
      have e1 : ∫ x in X, (v : ℝ → ℂ) x * schrodingerOp q φ x =
          ∫ x in X, u x * schrodingerOp q φ x :=
        integral_congr_ae (by filter_upwards [hvu] with x hx; rw [hx])
      have e2 : ∫ x in X, z * (v : ℝ → ℂ) x * φ x = ∫ x in X, z * u x * φ x :=
        integral_congr_ae (by filter_upwards [hvu] with x hx; rw [hx])
      rw [e1, e2, weak_of_isSolution hX hXc hne hq hu hφ]
    have hmem := (dlmf_1_18_ix_maxDomain hX hq v).mpr ⟨_, hweak⟩
    exact mem_eigenspaceDLMF.mpr ⟨hmem, minOp_adjoint_apply hX hq ⟨v, hmem⟩ _ hweak⟩

/-! ### `dim N_z ≤ 2` -/

theorem eqOn_of_ae_eq_of_continuousOn (hX : IsOpen X) {u1 u2 : ℝ → ℂ} (h1 : ContinuousOn u1 X)
    (h2 : ContinuousOn u2 X) (h : u1 =ᵐ[volume.restrict X] u2) : EqOn u1 u2 X :=
  Measure.eqOn_open_of_ae_eq h hX h1 h2

theorem IsSolution.differentiableAt {z : ℂ} {u : ℝ → ℂ} (hu : IsSolution X q z u) {x : ℝ}
    (hx : x ∈ X) : DifferentiableAt ℝ u x := by
  obtain ⟨u', hu'⟩ := hu; exact (hu' x hx).1.differentiableAt

section Dim

variable (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) (hq : ContinuousOn q X)
  (z : ℂ)

/-- The classical representative of `v ∈ N_z`. -/
noncomputable def solRep (v : deficiencySpace (minOp X q) z) : ℝ → ℂ :=
  ((dlmf_1_18_ix_deficiency_iff hX hXc hne hq z v).mp v.2).choose

theorem solRep_spec (v : deficiencySpace (minOp X q) z) :
    IsSolution X q z (solRep hX hXc hne hq z v) ∧
      ((v : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict X] solRep hX hXc hne hq z v :=
  ((dlmf_1_18_ix_deficiency_iff hX hXc hne hq z v).mp v.2).choose_spec

/-- `v ↦ (u(c), u′(c))` for the classical representative `u`. -/
noncomputable def solData {c : ℝ} (hc : c ∈ X) : deficiencySpace (minOp X q) z →ₗ[ℂ] ℂ × ℂ where
  toFun v := (solRep hX hXc hne hq z v c, deriv (solRep hX hXc hne hq z v) c)
  map_add' v w := by
    obtain ⟨hv, hva⟩ := solRep_spec hX hXc hne hq z v
    obtain ⟨hw, hwa⟩ := solRep_spec hX hXc hne hq z w
    obtain ⟨hvw, hvwa⟩ := solRep_spec hX hXc hne hq z (v + w)
    have heq : EqOn (solRep hX hXc hne hq z (v + w))
        (solRep hX hXc hne hq z v + solRep hX hXc hne hq z w) X := by
      refine eqOn_of_ae_eq_of_continuousOn hX hvw.continuousOn
        (hv.continuousOn.add hw.continuousOn) (hvwa.symm.trans ?_)
      rw [Submodule.coe_add]
      exact (Lp.coeFn_add _ _).trans (hva.add hwa)
    have hev : solRep hX hXc hne hq z (v + w) =ᶠ[𝓝 c]
        solRep hX hXc hne hq z v + solRep hX hXc hne hq z w :=
      Filter.eventuallyEq_of_mem (hX.mem_nhds hc) heq
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨heq hc, ?_⟩
    rw [hev.deriv_eq, deriv_add (hv.differentiableAt hc) (hw.differentiableAt hc)]
  map_smul' a v := by
    obtain ⟨hv, hva⟩ := solRep_spec hX hXc hne hq z v
    obtain ⟨hav, hava⟩ := solRep_spec hX hXc hne hq z (a • v)
    have heq : EqOn (solRep hX hXc hne hq z (a • v)) (a • solRep hX hXc hne hq z v) X := by
      refine eqOn_of_ae_eq_of_continuousOn hX hav.continuousOn
        (continuousOn_const.smul hv.continuousOn) (hava.symm.trans ?_)
      rw [Submodule.coe_smul]
      exact (Lp.coeFn_smul _ _).trans (hva.const_smul a)
    have hev : solRep hX hXc hne hq z (a • v) =ᶠ[𝓝 c] a • solRep hX hXc hne hq z v :=
      Filter.eventuallyEq_of_mem (hX.mem_nhds hc) heq
    simp only [RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
    refine ⟨heq hc, ?_⟩
    rw [hev.deriv_eq, deriv_const_smul _ (hv.differentiableAt hc)]

theorem solData_injective {c : ℝ} (hc : c ∈ X) :
    Function.Injective (solData hX hXc hne hq z hc) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨hs, hva⟩ := solRep_spec hX hXc hne hq z v
  have hs' := hs
  obtain ⟨u', hu'⟩ := hs'
  simp only [solData, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero] at hv
  have hu'c : u' c = 0 := by rw [← (hu' c hc).1.deriv]; exact hv.2
  have hW : ContinuousOn (fun x => (q x : ℂ) - z) X :=
    (Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const
  have h0 := ode2c_eq_zero_on hXc hW (fun x hx => (hu' x hx).1) (fun x hx => (hu' x hx).2) hc
    hv.1 hu'c
  have hv0 : ((v : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict X] 0 := by
    refine hva.trans ?_
    exact (ae_restrict_iff' hX.measurableSet).mpr (ae_of_all _ fun x hx => h0 x hx)
  exact Subtype.ext (Lp.eq_zero_iff_ae_eq_zero.mpr hv0)

include hX hXc hne hq in
/-- **DLMF §1.18(ix)**: `N_z` has dimension `0`, `1` or `2`. -/
theorem dlmf_1_18_ix_finrank_le :
    FiniteDimensional ℂ (deficiencySpace (minOp X q) z) ∧
      Module.finrank ℂ (deficiencySpace (minOp X q) z) ≤ 2 := by
  obtain ⟨c, hc⟩ := hne
  have hinj := solData_injective hX hXc ⟨c, hc⟩ hq z hc
  have : FiniteDimensional ℂ (deficiencySpace (minOp X q) z) :=
    Module.Finite.of_injective _ hinj
  refine ⟨this, ?_⟩
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end Dim

/-! ### Conjugation: `f ∈ N_z` iff `f̄ ∈ N_{z̄}` -/

theorem memLp_conj (v : L2X X) :
    MemLp (fun x => conj ((v : ℝ → ℂ) x)) 2 (volume.restrict X) :=
  (Lp.memLp v).of_le (Complex.continuous_conj.comp_aestronglyMeasurable
    (Lp.memLp v).aestronglyMeasurable) (ae_of_all _ fun x => by simp)

/-- Complex conjugation on `L²(X)`. -/
noncomputable def conjL2 (v : L2X X) : L2X X := (memLp_conj v).toLp

theorem coeFn_conjL2 (v : L2X X) :
    (conjL2 v : ℝ → ℂ) =ᵐ[volume.restrict X] fun x => conj ((v : ℝ → ℂ) x) :=
  (memLp_conj v).coeFn_toLp

theorem conjL2_conjL2 (v : L2X X) : conjL2 (conjL2 v) = v := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjL2 (conjL2 v), coeFn_conjL2 v] with x h1 h2
  rw [h1, h2, Complex.conj_conj]

theorem conjL2_add (v w : L2X X) : conjL2 (v + w) = conjL2 v + conjL2 w := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjL2 (v + w), Lp.coeFn_add (conjL2 v) (conjL2 w), coeFn_conjL2 v,
    coeFn_conjL2 w, Lp.coeFn_add v w] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, _root_.map_add]

theorem conjL2_smul (a : ℂ) (v : L2X X) : conjL2 (a • v) = conj a • conjL2 v := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjL2 (a • v), Lp.coeFn_smul (conj a) (conjL2 v), coeFn_conjL2 v,
    Lp.coeFn_smul a v] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply]
  simp [map_mul]

theorem IsSolution.conj {z : ℂ} {u : ℝ → ℂ} (hu : IsSolution X q z u) :
    IsSolution X q (conj z) fun x => conj (u x) := by
  obtain ⟨u', hu'⟩ := hu
  refine ⟨fun x => conj (u' x), fun x hx => ⟨(hu' x hx).1.star, ?_⟩⟩
  have := (hu' x hx).2.star
  refine this.congr_deriv ?_
  show conj (((q x : ℂ) - z) * u x) = _
  simp [_root_.map_sub, Complex.conj_ofReal]

theorem conjL2_mem (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {z : ℂ} {v : L2X X} (hv : v ∈ deficiencySpace (minOp X q) z) :
    conjL2 v ∈ deficiencySpace (minOp X q) (conj z) := by
  obtain ⟨u, hu, hvu⟩ := (dlmf_1_18_ix_deficiency_iff hX hXc hne hq z v).mp hv
  refine (dlmf_1_18_ix_deficiency_iff hX hXc hne hq _ _).mpr ⟨_, hu.conj, ?_⟩
  filter_upwards [coeFn_conjL2 v, hvu] with x h1 h2
  rw [h1, h2]

/-- Conjugation `N_z ≃ N_{z̄}`, additive and conjugate-linear. -/
noncomputable def conjDeficiency (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) (z : ℂ) :
    deficiencySpace (minOp X q) z ≃+ deficiencySpace (minOp X q) (conj z) where
  toFun v := ⟨conjL2 v, conjL2_mem hX hXc hne hq v.2⟩
  invFun v := ⟨conjL2 v, by
    have := conjL2_mem hX hXc hne hq v.2
    rwa [Complex.conj_conj] at this⟩
  map_add' v w := Subtype.ext (by simp only [Submodule.coe_add]; exact conjL2_add _ _)
  left_inv v := Subtype.ext (conjL2_conjL2 _)
  right_inv v := Subtype.ext (conjL2_conjL2 _)

/-- **DLMF §1.18(ix)**: since `q` is real, `dim N_z = dim N_{z̄}`; so `ℒ` has self-adjoint
extensions, with deficiency indices `n₊ = n₋ ∈ {0, 1, 2}`. -/
theorem dlmf_1_18_ix_deficiency_eq (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) (z : ℂ) :
    Module.finrank ℂ (deficiencySpace (minOp X q) z) =
      Module.finrank ℂ (deficiencySpace (minOp X q) (conj z)) := by
  have h := rank_eq_of_equiv_equiv (fun a : ℂ => conj a) (conjDeficiency hX hXc hne hq z)
    (Function.Involutive.bijective fun a => Complex.conj_conj a) fun a v => Subtype.ext (by
      simp only [Submodule.coe_smul]; exact conjL2_smul a (v : L2X X))
  unfold Module.finrank
  rw [h]

theorem dlmf_1_18_ix_exists_selfAdjoint (hX : IsOpen X) (hXc : X.OrdConnected)
    (hne : X.Nonempty) (hq : ContinuousOn q X) :
    (∃ A : L2X X →ₗ.[ℂ] L2X X, IsSelfAdjoint A ∧ minOp X q ≤ A) ∧
      Module.finrank ℂ (deficiencySpace (minOp X q) Complex.I) =
        Module.finrank ℂ (deficiencySpace (minOp X q) (-Complex.I)) ∧
      Module.finrank ℂ (deficiencySpace (minOp X q) Complex.I) ≤ 2 := by
  have h1 := dlmf_1_18_ix_finrank_le hX hXc hne hq Complex.I
  have h2 := dlmf_1_18_ix_finrank_le hX hXc hne hq (-Complex.I)
  have : FiniteDimensional ℂ (deficiencySpace (minOp X q) Complex.I) := h1.1
  have : FiniteDimensional ℂ (deficiencySpace (minOp X q) (-Complex.I)) := h2.1
  have heq : Module.finrank ℂ (deficiencySpace (minOp X q) Complex.I) =
      Module.finrank ℂ (deficiencySpace (minOp X q) (-Complex.I)) := by
    rw [dlmf_1_18_ix_deficiency_eq hX hXc hne hq, Complex.conj_I]
  exact ⟨((isSymmetricDLMF_minOp hX hq).exists_selfAdjoint_ext_iff_finrank).mpr heq, heq, h1.2⟩

/-- **DLMF §1.18(ix)**: since `q` is real, `f ∈ N_z` iff `f̄ ∈ N_{z̄}`. -/
theorem dlmf_1_18_ix_conj_iff (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) (z : ℂ) (v : L2X X) :
    v ∈ deficiencySpace (minOp X q) z ↔ conjL2 v ∈ deficiencySpace (minOp X q) (conj z) := by
  refine ⟨conjL2_mem hX hXc hne hq, fun h => ?_⟩
  have := conjL2_mem hX hXc hne hq h
  rwa [conjL2_conjL2, Complex.conj_conj] at this

end Azurite.DLMF
