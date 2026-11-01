/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Schrodinger
import Azurite.DLMF.Chapter1.Section18VonNeumann

/-!
# DLMF §1.18(ix): the minimal operator of (1.18.28) and its adjoint

https://dlmf.nist.gov/1.18.ix

`minOp X q` is `ℒ = −d²/dx² + q` on `𝒟 = C²_c(X) ⊂ L²(X)`, as a partially defined operator.
It is built from its graph (`minGraph`), is densely defined, and is symmetric
(`isSymmetricDLMF_minOp`).

`dlmf_1_18_ix_maxDomain` gives DLMF's description of `𝒟(ℒ*)`: the `w ∈ L²(X)` for which the
distribution `ℒw` is a function `g ∈ L²(X)`, i.e. `∫_X w ℒφ = ∫_X g φ` for all `φ ∈ C²_c(X)`.
Then `ℒ*w = g` (`minOp_adjoint_apply`).
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-! ### Calculus facts for `ℒ = −d²/dx² + q` -/

theorem deriv_add_of_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    deriv (f + g) = deriv f + deriv g := by
  funext x
  exact deriv_add (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x)

theorem schrodingerOp_add (q : ℝ → ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    schrodingerOp q (f + g) = schrodingerOp q f + schrodingerOp q g := by
  have h1 := deriv_add_of_contDiff (hf.of_le (by norm_num)) (hg.of_le (by norm_num))
  have h2 := deriv_add_of_contDiff (ContDiff.deriv' (n := 1) (by convert hf; norm_num))
    (ContDiff.deriv' (n := 1) (by convert hg; norm_num))
  funext x
  simp only [schrodingerOp, Pi.add_apply, h1, h2]
  ring

theorem schrodingerOp_smul (q : ℝ → ℝ) (c : ℂ) (f : ℝ → ℂ) :
    schrodingerOp q (c • f) = c • schrodingerOp q f := by
  have h1 : deriv (c • f) = c • deriv f := by
    have := deriv_const_mul_field' (𝕜 := ℝ) c (v := f)
    funext x; exact congrFun this x
  have h2 : deriv (c • deriv f) = c • deriv (deriv f) := by
    have := deriv_const_mul_field' (𝕜 := ℝ) c (v := deriv f)
    funext x; exact congrFun this x
  funext x
  simp only [schrodingerOp, h1, h2, Pi.smul_apply, smul_eq_mul]
  ring

theorem schrodingerOp_zero (q : ℝ → ℝ) : schrodingerOp q 0 = 0 := by
  funext x; simp [schrodingerOp]

theorem deriv_conj {f : ℝ → ℂ} (hf : Differentiable ℝ f) :
    deriv (fun x => conj (f x)) = fun x => conj (deriv f x) := by
  funext x
  exact ((hf x).hasDerivAt.star).deriv

/-- `ℒ conj f = conj ℒf` since `q` is real. -/
theorem schrodingerOp_conj (q : ℝ → ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) :
    schrodingerOp q (fun x => conj (f x)) = fun x => conj (schrodingerOp q f x) := by
  have h1 := deriv_conj (hf.differentiable (by norm_num))
  have h2 := deriv_conj ((ContDiff.deriv' (n := 1) (by convert hf; norm_num)).differentiable
    one_ne_zero)
  funext x
  simp only [schrodingerOp, h1, h2, _root_.map_add, _root_.map_neg, map_mul, Complex.conj_ofReal]

theorem IsC2c.conj {X : Set ℝ} {f : ℝ → ℂ} (hf : IsC2c X f) : IsC2c X fun x => conj (f x) := by
  refine ⟨?_, hf.2.1.comp_left (_root_.map_zero _), ?_⟩
  · exact (Complex.conjCLE.restrictScalars ℝ).contDiff.comp hf.1
  · exact (tsupport_comp_subset (_root_.map_zero _) _).trans hf.2.2

theorem support_schrodingerOp_subset (q : ℝ → ℝ) (f : ℝ → ℂ) :
    Function.support (schrodingerOp q f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  have hz : f =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp h
  have hd : deriv f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hz.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq]; simp
  simp [schrodingerOp, hd.deriv_eq, hz.eq_of_nhds]

theorem IsC2c.memLp {X : Set ℝ} {f : ℝ → ℂ} (hf : IsC2c X f) :
    MemLp f 2 (volume.restrict X) :=
  (hf.1.continuous.memLp_of_hasCompactSupport hf.2.1).restrict X

theorem IsC2c.memLp_schrodingerOp {X : Set ℝ} (hX : IsOpen X) {q : ℝ → ℝ}
    (hq : ContinuousOn q X) {f : ℝ → ℂ} (hf : IsC2c X f) :
    MemLp (schrodingerOp q f) 2 (volume.restrict X) :=
  ((continuous_schrodingerOp hX hq hf).memLp_of_hasCompactSupport
    (hf.2.1.mono' (support_schrodingerOp_subset q f))).restrict X

/-- Two `C²_c(X)` functions equal a.e. on open `X` have equal `ℒ` on `X`. -/
theorem schrodingerOp_eqOn_of_ae_eq {X : Set ℝ} (hX : IsOpen X) (q : ℝ → ℝ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[volume.restrict X] g) :
    EqOn (schrodingerOp q f) (schrodingerOp q g) X := by
  have heq : EqOn f g X := Measure.eqOn_open_of_ae_eq h hX hf.continuousOn hg.continuousOn
  intro x hx
  have hev : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hX.mem_nhds hx) heq
  have hd : deriv f =ᶠ[𝓝 x] deriv g := by
    filter_upwards [hev.eventuallyEq_nhds] with y hy
    exact hy.deriv_eq
  simp [schrodingerOp, hd.deriv_eq, heq hx]

/-! ### The minimal operator -/

/-- `L²(X)`. -/
noncomputable abbrev L2X (X : Set ℝ) := Lp ℂ 2 (volume.restrict X)

variable {X : Set ℝ} {q : ℝ → ℝ}

variable (X q) in
/-- The graph `{(f, ℒf) | f ∈ C²_c(X)}` in `L²(X) × L²(X)`. -/
def minGraph : Submodule ℂ (L2X X × L2X X) where
  carrier := {p | ∃ f, IsC2c X f ∧ (p.1 : ℝ → ℂ) =ᵐ[volume.restrict X] f ∧
    (p.2 : ℝ → ℂ) =ᵐ[volume.restrict X] schrodingerOp q f}
  add_mem' := by
    rintro p p' ⟨f, hf, h1, h2⟩ ⟨g, hg, h1', h2'⟩
    refine ⟨f + g, hf.add hg, (Lp.coeFn_add _ _).trans (h1.add h1'), ?_⟩
    rw [schrodingerOp_add q hf.1 hg.1]
    exact (Lp.coeFn_add _ _).trans (h2.add h2')
  zero_mem' := ⟨0, isC2c_zero X, Lp.coeFn_zero ℂ 2 _, by
    rw [schrodingerOp_zero]; exact Lp.coeFn_zero ℂ 2 _⟩
  smul_mem' := by
    rintro c p ⟨f, hf, h1, h2⟩
    refine ⟨c • f, hf.smul c, (Lp.coeFn_smul c _).trans (h1.const_smul c), ?_⟩
    rw [schrodingerOp_smul]
    exact (Lp.coeFn_smul c _).trans (h2.const_smul c)

theorem minGraph_zero (hX : IsOpen X) :
    ∀ p ∈ minGraph X q, p.1 = 0 → p.2 = 0 := by
  rintro p ⟨f, hf, h1, h2⟩ hp
  have hf0 : f =ᵐ[volume.restrict X] 0 := by
    rw [hp] at h1; exact h1.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have heq := schrodingerOp_eqOn_of_ae_eq hX q (g := 0) hf.1.continuous continuous_const hf0
  rw [schrodingerOp_zero] at heq
  refine Lp.eq_zero_iff_ae_eq_zero.mpr (h2.trans ?_)
  exact (ae_restrict_iff' hX.measurableSet).mpr (ae_of_all _ fun x hx => heq hx)

variable (X q) in
/-- DLMF §1.18(ix): the operator `ℒ` of (1.18.28) on `𝒟 = C²_c(X) ⊂ L²(X)`. -/
noncomputable def minOp : L2X X →ₗ.[ℂ] L2X X := (minGraph X q).toLinearPMap

theorem minOp_domain (hX : IsOpen X) (hq : ContinuousOn q X) :
    (minOp X q).domain = c2cSubmodule X := by
  ext F
  rw [minOp, Submodule.toLinearPMap_domain, Submodule.mem_map]
  constructor
  · rintro ⟨p, ⟨f, hf, h1, -⟩, rfl⟩
    exact ⟨f, hf, h1⟩
  · rintro ⟨f, hf, h1⟩
    exact ⟨(F, (hf.memLp_schrodingerOp hX hq).toLp),
      ⟨f, hf, h1, MemLp.coeFn_toLp (hf.memLp_schrodingerOp hX hq)⟩, rfl⟩

/-- `T F = ℒf` a.e. for `F = f ∈ C²_c(X)`. -/
theorem minOp_apply (hX : IsOpen X) (F : (minOp X q).domain) {f : ℝ → ℂ} (hf : IsC2c X f)
    (hF : (F : ℝ → ℂ) =ᵐ[volume.restrict X] f) :
    (minOp X q F : ℝ → ℂ) =ᵐ[volume.restrict X] schrodingerOp q f := by
  obtain ⟨g, hg, h1, h2⟩ := Submodule.mem_graph_toLinearPMap (minGraph_zero hX) F
  have heq := schrodingerOp_eqOn_of_ae_eq hX q hg.1.continuous hf.1.continuous
    (h1.symm.trans hF)
  refine h2.trans ?_
  exact (ae_restrict_iff' hX.measurableSet).mpr (ae_of_all _ fun x hx => heq hx)

theorem dense_minOp_domain (hX : IsOpen X) (hq : ContinuousOn q X) :
    Dense ((minOp X q).domain : Set (L2X X)) := by
  rw [minOp_domain hX hq]; exact dlmf_1_18_iv_dense hX

theorem exists_c2c_of_mem (hX : IsOpen X) (hq : ContinuousOn q X) (F : (minOp X q).domain) :
    ∃ f, IsC2c X f ∧ (F : ℝ → ℂ) =ᵐ[volume.restrict X] f := by
  exact (SetLike.ext_iff.mp (minOp_domain hX hq) (F : L2X X)).mp F.2

/-- DLMF §1.18(iv) in operator form: the minimal operator is symmetric. -/
theorem isSymmetricDLMF_minOp (hX : IsOpen X) (hq : ContinuousOn q X) :
    IsSymmetricDLMF (minOp X q) := by
  refine ⟨dense_minOp_domain hX hq, fun F G => ?_⟩
  obtain ⟨f, hf, hF⟩ := exists_c2c_of_mem hX hq F
  obtain ⟨g, hg, hG⟩ := exists_c2c_of_mem hX hq G
  have hTF := minOp_apply hX F hf hF
  have hTG := minOp_apply hX G hg hG
  rw [dlmfInner_Lp_eq, dlmfInner_Lp_eq]
  have e1 : ∫ x in X, (minOp X q F : ℝ → ℂ) x * conj ((G : ℝ → ℂ) x) =
      ∫ x in X, schrodingerOp q f x * conj (g x) :=
    integral_congr_ae (by filter_upwards [hTF, hG] with x h1 h2; rw [h1, h2])
  have e2 : ∫ x in X, (F : ℝ → ℂ) x * conj ((minOp X q G : ℝ → ℂ) x) =
      ∫ x in X, f x * conj (schrodingerOp q g x) :=
    integral_congr_ae (by filter_upwards [hF, hTG] with x h1 h2; rw [h1, h2])
  rw [e1, e2]
  exact dlmf_1_18_iv_symmetric hX hq hf hg

/-! ### The adjoint is the maximal operator -/

theorem inner_L2X (F G : L2X X) :
    ⟪F, G⟫_ℂ = ∫ x in X, conj ((F : ℝ → ℂ) x) * (G : ℝ → ℂ) x := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- The distributional identity `ℒw = g` in inner-product form. -/
theorem weak_schrodinger_iff (hX : IsOpen X) (hq : ContinuousOn q X) (w g : L2X X) :
    (∀ φ : ℝ → ℂ, IsC2c X φ →
      ∫ x in X, (w : ℝ → ℂ) x * schrodingerOp q φ x = ∫ x in X, (g : ℝ → ℂ) x * φ x) ↔
      ∀ F : (minOp X q).domain, ⟪g, (F : L2X X)⟫_ℂ = ⟪w, minOp X q F⟫_ℂ := by
  constructor
  · intro h F
    obtain ⟨f, hf, hF⟩ := exists_c2c_of_mem hX hq F
    have hTF := minOp_apply hX F hf hF
    have h1 := congrArg conj (h _ hf.conj)
    rw [schrodingerOp_conj q hf.1, ← integral_conj, ← integral_conj] at h1
    rw [inner_L2X, inner_L2X]
    have e1 : ∫ x in X, conj ((g : ℝ → ℂ) x) * (F : ℝ → ℂ) x =
        ∫ x in X, conj ((g : ℝ → ℂ) x * conj (f x)) := integral_congr_ae (by
      filter_upwards [hF] with x hx; rw [hx, map_mul, Complex.conj_conj])
    have e2 : ∫ x in X, conj ((w : ℝ → ℂ) x) * (minOp X q F : ℝ → ℂ) x =
        ∫ x in X, conj ((w : ℝ → ℂ) x * conj (schrodingerOp q f x)) := integral_congr_ae (by
      filter_upwards [hTF] with x hx; rw [hx, map_mul, Complex.conj_conj])
    rw [e1, e2, ← h1]
  · intro h φ hφ
    set Φ : L2X X := hφ.conj.memLp.toLp
    have hΦ : Φ ∈ (minOp X q).domain := by
      rw [minOp_domain hX hq]; exact ⟨_, hφ.conj, MemLp.coeFn_toLp hφ.conj.memLp⟩
    have hTΦ := minOp_apply hX ⟨Φ, hΦ⟩ hφ.conj (MemLp.coeFn_toLp hφ.conj.memLp)
    have h1 := congrArg conj (h ⟨Φ, hΦ⟩)
    rw [inner_L2X, inner_L2X, ← integral_conj, ← integral_conj] at h1
    have e1 : ∫ x in X, conj (conj ((g : ℝ → ℂ) x) * (Φ : ℝ → ℂ) x) =
        ∫ x in X, (g : ℝ → ℂ) x * φ x := integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp hφ.conj.memLp] with x hx
      rw [hx, map_mul, Complex.conj_conj, Complex.conj_conj])
    have e2 : ∫ x in X, conj (conj ((w : ℝ → ℂ) x) * (minOp X q ⟨Φ, hΦ⟩ : ℝ → ℂ) x) =
        ∫ x in X, (w : ℝ → ℂ) x * schrodingerOp q φ x := integral_congr_ae (by
      filter_upwards [hTΦ] with x hx
      rw [hx, schrodingerOp_conj q hφ.1, map_mul, Complex.conj_conj, Complex.conj_conj])
    rw [e1, e2] at h1
    exact h1.symm

/-- **DLMF §1.18(ix)**: `𝒟(ℒ*)` consists of the `w ∈ L²(X)` whose distribution `ℒw` is a
function `g ∈ L²(X)`: `∫_X w ℒφ = ∫_X g φ` for all `φ ∈ C²_c(X)`; then `ℒ*w = g`. -/
theorem dlmf_1_18_ix_maxDomain (hX : IsOpen X) (hq : ContinuousOn q X) (w : L2X X) :
    w ∈ (minOp X q)†.domain ↔ ∃ g : L2X X, ∀ φ : ℝ → ℂ, IsC2c X φ →
      ∫ x in X, (w : ℝ → ℂ) x * schrodingerOp q φ x = ∫ x in X, (g : ℝ → ℂ) x * φ x := by
  have hconj := weak_schrodinger_iff hX hq w
  constructor
  · intro hw
    refine ⟨(minOp X q)† ⟨w, hw⟩, (hconj _).mpr fun F => ?_⟩
    exact (adjoint_isFormalAdjoint (dense_minOp_domain hX hq)) ⟨w, hw⟩ F
  · rintro ⟨g, hg⟩
    exact mem_adjoint_domain_of_exists w ⟨g, (hconj g).mp hg⟩

/-- The value: `ℒ*w = g`. -/
theorem minOp_adjoint_apply (hX : IsOpen X) (hq : ContinuousOn q X) (w : (minOp X q)†.domain)
    (g : L2X X) (hg : ∀ φ : ℝ → ℂ, IsC2c X φ →
      ∫ x in X, (w : ℝ → ℂ) x * schrodingerOp q φ x = ∫ x in X, (g : ℝ → ℂ) x * φ x) :
    (minOp X q)† w = g := by
  exact adjoint_apply_eq (dense_minOp_domain hX hq) w ((weak_schrodinger_iff hX hq w g).mp hg)
