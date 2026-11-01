/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18L2
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# DLMF §1.18(iv): Formally self-adjoint second-order differential operators

https://dlmf.nist.gov/1.18.iv

* 1.18.28: the Schrödinger operator `ℒ = −d²/dx² + q(x)` with `q` real (`schrodingerOp`).
* `ℒ` is formally self-adjoint. The Lagrange identity says `(ℒf) conj g − f conj(ℒg)` is the
  derivative of the Wronskian `W(f, conj g) = f conj(g′) − f′ conj(g)`
  (`schrodinger_lagrange_identity`, `hasDerivAt_wronskianConj`), which gives Green's formula
  (`dlmf_1_18_iv_green`).
* `𝒟(T) = C²_c(X)` (`IsC2c`, `c2cSubmodule`): `ℒ` is symmetric there for any open `X` and `q` real
  and continuous on `X` (`dlmf_1_18_iv_symmetric`), and `C²_c(X)` is dense in `L²(X)`
  (`dlmf_1_18_iv_dense`). Density follows from Mathlib's fundamental lemma of the calculus of
  variations via orthogonal complements.
* Eigenvalues are real and eigenfunctions for distinct eigenvalues are orthogonal. This is stated
  for `C²` eigenfunctions on `[α, β]` whose Wronskian boundary terms cancel (e.g. Dirichlet
  conditions): `schrodinger_eigen_relation`, `schrodinger_eigenvalue_real`,
  `schrodinger_eigen_orthogonal`. A nonzero eigenfunction cannot lie in `C²_c(X)` itself, by
  uniqueness for the ODE.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-- DLMF 1.18.28: the Schrödinger operator `ℒ = −d²/dx² + q(x)` with real potential `q`. -/
noncomputable def schrodingerOp (q : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv f) x + q x * f x

/-- The Wronskian `W(f, conj g) = f conj(g′) − f′ conj(g)`. -/
noncomputable def wronskianConj (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x * conj (deriv g x) - deriv f x * conj (g x)

theorem hasDerivAt_deriv_of_contDiff_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  ⟨(hf.differentiable (by norm_num) x).hasDerivAt,
    ((ContDiff.deriv' (n := 1) (by convert hf; norm_num)).differentiable one_ne_zero x).hasDerivAt⟩

theorem continuous_deriv_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : Continuous (deriv (deriv f)) :=
  (ContDiff.deriv' (n := 1) (by convert hf; norm_num)).continuous_deriv le_rfl

theorem continuous_deriv' {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : Continuous (deriv f) :=
  hf.continuous_deriv (by norm_num)

/-- The derivative of the Wronskian. -/
theorem hasDerivAt_wronskianConj {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : ℝ) : HasDerivAt (wronskianConj f g)
      (f x * conj (deriv (deriv g) x) - deriv (deriv f) x * conj (g x)) x := by
  obtain ⟨hf1, hf2⟩ := hasDerivAt_deriv_of_contDiff_two hf x
  obtain ⟨hg1, hg2⟩ := hasDerivAt_deriv_of_contDiff_two hg x
  have h := (hf1.mul hg2.star).sub (hf2.mul hg1.star)
  convert h using 1
  · rfl
  · simp only [show ∀ z : ℂ, star z = conj z from fun _ => rfl]
    ring

/-- The Lagrange identity: `(ℒf) conj g − f conj(ℒg) = W(f, conj g)′` (`q` real). -/
theorem schrodinger_lagrange_identity (q : ℝ → ℝ) (f g : ℝ → ℂ) (x : ℝ) :
    schrodingerOp q f x * conj (g x) - f x * conj (schrodingerOp q g x) =
      f x * conj (deriv (deriv g) x) - deriv (deriv f) x * conj (g x) := by
  simp only [schrodingerOp, map_add, map_neg, map_mul, Complex.conj_ofReal]
  ring

/-- DLMF §1.18(iv): `ℒ` is formally self-adjoint (Green's formula):
`∫_α^β ((ℒf) conj g − f conj(ℒg)) = [W(f, conj g)]_α^β`. -/
theorem dlmf_1_18_iv_green (q : ℝ → ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (α β : ℝ) :
    ∫ x in α..β, (schrodingerOp q f x * conj (g x) - f x * conj (schrodingerOp q g x)) =
      wronskianConj f g β - wronskianConj f g α := by
  simp only [schrodinger_lagrange_identity]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_wronskianConj hf hg x)
    (Continuous.intervalIntegrable ?_ _ _)
  exact (hf.continuous.mul (Complex.continuous_conj.comp (continuous_deriv_deriv hg))).sub
    ((continuous_deriv_deriv hf).mul (Complex.continuous_conj.comp hg.continuous))

/-! ### The domain `C²_c(X)` -/

/-- `C²` functions with compact support in `X`. -/
def IsC2c (X : Set ℝ) (f : ℝ → ℂ) : Prop := ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ tsupport f ⊆ X

theorem continuous_mul_of_tsupport {X : Set ℝ} (hX : IsOpen X) {q : ℝ → ℝ}
    (hq : ContinuousOn q X) {f : ℝ → ℂ} (hf : Continuous f) (hs : tsupport f ⊆ X) :
    Continuous fun x => (q x : ℂ) * f x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ X
  · exact ((Complex.continuous_ofReal.continuousAt).comp
      (hq.continuousAt (hX.mem_nhds hx))).mul hf.continuousAt
  · have hz : f =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hs h)
    have : (fun x => (q x : ℂ) * f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hz] with y hy
      simp [hy]
    rw [continuousAt_congr this]
    exact continuousAt_const

theorem continuous_schrodingerOp {X : Set ℝ} (hX : IsOpen X) {q : ℝ → ℝ}
    (hq : ContinuousOn q X) {f : ℝ → ℂ} (hf : IsC2c X f) : Continuous (schrodingerOp q f) :=
  (continuous_deriv_deriv hf.1).neg.add (continuous_mul_of_tsupport hX hq hf.1.continuous hf.2.2)

/-- DLMF §1.18(iv): on `𝒟(T) = C²_c(X)`, `ℒ` is symmetric: `⟨ℒf, g⟩ = ⟨f, ℒg⟩`, i.e.
`∫_X (ℒf) conj g = ∫_X f conj(ℒg)`, for any open `X` and `q` real and continuous on `X`. -/
theorem dlmf_1_18_iv_symmetric {X : Set ℝ} (hX : IsOpen X) {q : ℝ → ℝ}
    (hq : ContinuousOn q X) {f g : ℝ → ℂ} (hf : IsC2c X f) (hg : IsC2c X g) :
    ∫ x in X, schrodingerOp q f x * conj (g x) = ∫ x in X, f x * conj (schrodingerOp q g x) := by
  have hgc : HasCompactSupport fun x => conj (g x) := hg.2.1.comp_left (map_zero _)
  have hcg : Continuous fun x => conj (g x) := Complex.continuous_conj.comp hg.1.continuous
  have hA : Integrable fun x => schrodingerOp q f x * conj (g x) :=
    ((continuous_schrodingerOp hX hq hf).mul hcg).integrable_of_hasCompactSupport hgc.mul_left
  have hB : Integrable fun x => f x * conj (schrodingerOp q g x) :=
    (hf.1.continuous.mul (Complex.continuous_conj.comp (continuous_schrodingerOp hX hq hg))
      ).integrable_of_hasCompactSupport hf.2.1.mul_right
  have hW : Integrable (wronskianConj f g) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hf.1.continuous.mul (Complex.continuous_conj.comp (continuous_deriv' hg.1))).sub
        ((continuous_deriv' hf.1).mul hcg)
    · exact (hf.2.1.mul_right).sub (hf.2.1.deriv.mul_right)
  have hW' : Integrable fun x =>
      f x * conj (deriv (deriv g) x) - deriv (deriv f) x * conj (g x) := by
    refine (hA.sub hB).congr (ae_of_all _ fun x => ?_)
    exact schrodinger_lagrange_identity q f g x
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => hasDerivAt_wronskianConj hf.1 hg.1 x) hW' hW
  simp only [← schrodinger_lagrange_identity q] at h0
  rw [integral_sub hA hB, sub_eq_zero] at h0
  have hfz : ∀ x, x ∉ X → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
    fun h => hx (hf.2.2 h)
  have hgz : ∀ x, x ∉ X → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
    fun h => hx (hg.2.2 h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hgz x hx],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hfz x hx]]
  exact h0

theorem IsC2c.add {X : Set ℝ} {f g : ℝ → ℂ} (hf : IsC2c X f) (hg : IsC2c X g) :
    IsC2c X (f + g) :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩

theorem IsC2c.smul {X : Set ℝ} {f : ℝ → ℂ} (c : ℂ) (hf : IsC2c X f) : IsC2c X (c • f) := by
  have e : c • f = fun x => c * f x := rfl
  rw [e]
  exact ⟨contDiff_const.mul hf.1, hf.2.1.mul_left, tsupport_mul_subset_right.trans hf.2.2⟩

theorem isC2c_zero (X : Set ℝ) : IsC2c X 0 :=
  ⟨contDiff_const, HasCompactSupport.zero, by rw [tsupport_zero]; exact empty_subset _⟩

/-- `C²_c(X)` as a subspace of `L²(X)`. -/
def c2cSubmodule (X : Set ℝ) : Submodule ℂ (Lp ℂ 2 (volume.restrict X)) where
  carrier := {F | ∃ f, IsC2c X f ∧ (F : ℝ → ℂ) =ᵐ[volume.restrict X] f}
  add_mem' := by
    rintro F G ⟨f, hf, hF⟩ ⟨g, hg, hG⟩
    exact ⟨f + g, hf.add hg, (Lp.coeFn_add F G).trans (hF.add hG)⟩
  zero_mem' := ⟨0, isC2c_zero X, Lp.coeFn_zero ℂ 2 _⟩
  smul_mem' := by
    rintro c F ⟨f, hf, hF⟩
    exact ⟨c • f, hf.smul c, (Lp.coeFn_smul c F).trans (hF.const_smul c)⟩

/-- DLMF §1.18(iv): `C²_c(X)` is dense in `L²(X)` for open `X`. -/
theorem dlmf_1_18_iv_dense {X : Set ℝ} (hX : IsOpen X) :
    Dense (c2cSubmodule X : Set (Lp ℂ 2 (volume.restrict X))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro h hh
  rw [Submodule.mem_orthogonal] at hh
  have hmem : MemLp (X.indicator (h : ℝ → ℂ)) 2 volume :=
    (memLp_indicator_iff_restrict hX.measurableSet).mpr (Lp.memLp h)
  have hloc : LocallyIntegrableOn (X.indicator (h : ℝ → ℂ)) X volume :=
    (hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn X
  have key := hX.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun φ hφ hφc hφs => by
    have hc : Continuous fun x => (φ x : ℂ) := Complex.continuous_ofReal.comp hφ.continuous
    have hcs : HasCompactSupport fun x => (φ x : ℂ) := hφc.comp_left Complex.ofReal_zero
    have hm : MemLp (fun x => (φ x : ℂ)) 2 (volume.restrict X) :=
      (hc.memLp_of_hasCompactSupport hcs).restrict X
    have hu : hm.toLp _ ∈ c2cSubmodule X :=
      ⟨_, ⟨(Complex.ofRealCLM.contDiff.comp hφ).of_le
        (WithTop.coe_le_coe.mpr le_top), hcs,
        (tsupport_comp_subset Complex.ofReal_zero _).trans hφs⟩, hm.coeFn_toLp⟩
    have h0 := hh _ hu
    rw [L2.inner_def] at h0
    have e1 : (fun x => φ x • X.indicator (h : ℝ → ℂ) x) =
        X.indicator (fun x => φ x • (h : ℝ → ℂ) x) :=
      funext fun x => by by_cases hx : x ∈ X <;> simp [hx]
    rw [e1, integral_indicator hX.measurableSet, ← h0]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, Complex.real_smul]
    simp [mul_comm]
  have hz : (h : ℝ → ℂ) =ᵐ[volume.restrict X] 0 :=
    (ae_restrict_iff' hX.measurableSet).mpr (key.mono fun x hx hxX => by
      simpa [indicator_of_mem hxX] using hx hxX)
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr hz

/-! ### Real eigenvalues and orthogonal eigenfunctions -/

/-- For eigenfunctions `ℒf = λf`, `ℒg = μg` on `[α, β]` whose Wronskian boundary terms cancel,
`(λ − conj μ) ∫_α^β f conj g = 0`. -/
theorem schrodinger_eigen_relation (q : ℝ → ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) {α β : ℝ} {l m : ℂ}
    (hfe : ∀ x ∈ uIcc α β, schrodingerOp q f x = l * f x)
    (hge : ∀ x ∈ uIcc α β, schrodingerOp q g x = m * g x)
    (hW : wronskianConj f g β = wronskianConj f g α) :
    (l - conj m) * ∫ x in α..β, f x * conj (g x) = 0 := by
  have h := dlmf_1_18_iv_green q hf hg α β
  rw [hW, sub_self] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  simp only [hfe x hx, hge x hx, map_mul]
  ring

/-- Dirichlet conditions `f = g = 0` at `α` and `β` make the Wronskian boundary terms vanish. -/
theorem wronskianConj_dirichlet {f g : ℝ → ℂ} {α β : ℝ} (hfα : f α = 0) (hfβ : f β = 0)
    (hgα : g α = 0) (hgβ : g β = 0) : wronskianConj f g β = wronskianConj f g α := by
  simp [wronskianConj, hfα, hfβ, hgα, hgβ]

/-- DLMF §1.18(iv): eigenvalues are real. -/
theorem schrodinger_eigenvalue_real (q : ℝ → ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {α β : ℝ}
    {l : ℂ} (hfe : ∀ x ∈ uIcc α β, schrodingerOp q f x = l * f x)
    (hW : wronskianConj f f β = wronskianConj f f α) (h0 : ∫ x in α..β, f x * conj (f x) ≠ 0) :
    conj l = l := by
  have h := schrodinger_eigen_relation q hf hf hfe hfe hW
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right h0)).symm

/-- DLMF §1.18(iv): eigenfunctions for distinct real eigenvalues are orthogonal. -/
theorem schrodinger_eigen_orthogonal (q : ℝ → ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) {α β : ℝ} {l m : ℝ}
    (hfe : ∀ x ∈ uIcc α β, schrodingerOp q f x = l * f x)
    (hge : ∀ x ∈ uIcc α β, schrodingerOp q g x = m * g x)
    (hW : wronskianConj f g β = wronskianConj f g α) (hlm : l ≠ m) :
    ∫ x in α..β, f x * conj (g x) = 0 := by
  have h := schrodinger_eigen_relation q hf hg hfe hge hW
  rw [Complex.conj_ofReal] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hlm))

end Azurite.DLMF
