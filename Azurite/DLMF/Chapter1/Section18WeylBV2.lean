/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylBV

/-!
# DLMF §1.18(ix): boundary values at limit-point endpoints

* `mem_adjoint_cutoff_of_weak`, `mem_adjoint_cutoff`: multiplication by a smooth cut-off `χ`
  preserves `𝒟(ℒ*)`, with `ℒ*(χf) = χℒ*f − 2χ′f′ − χ″f`.
* `restrict_mem_adjoint`, `IsBoundaryValue.eq_zero_of_restrict`: restriction to a half-interval,
  and the transfer of `𝒟(ℒ**)`-membership back to `X`.
* `mem_adjoint_adjoint_of_boundary_zero`: on a limit-point side, vanishing of the boundary form
  against test functions near `c` gives membership in `𝒟(ℒ**)`.
* `dlmf_1_18_ix_boundary_values_LP_left`, `dlmf_1_18_ix_boundary_values_LP_right`: if `n₁ = 1`
  (resp. `n₂ = 1`) there are no nonzero boundary values at `a` (resp. `b`).
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

variable {X : Set ℝ} {q : ℝ → ℝ}

/-! ### Multiplication by a smooth cut-off -/

section Cutoff

variable {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ)
include hχ

theorem cutoff_derivs (x : ℝ) :
    HasDerivAt (fun x => (χ x : ℂ)) ((deriv χ x : ℝ) : ℂ) x ∧
      HasDerivAt (fun x => ((deriv χ x : ℝ) : ℂ)) ((deriv (deriv χ) x : ℝ) : ℂ) x := by
  have h1 : HasDerivAt χ (deriv χ x) x := (hχ.differentiable (by norm_num) x).hasDerivAt
  have h2 : HasDerivAt (deriv χ) (deriv (deriv χ) x) x :=
    ((ContDiff.deriv' (n := 1) (by convert hχ; norm_num)).differentiable one_ne_zero x).hasDerivAt
  exact ⟨h1.ofReal_comp, h2.ofReal_comp⟩

theorem cutoff_continuous :
    Continuous (fun x => ((deriv χ x : ℝ) : ℂ)) ∧
      Continuous (fun x => ((deriv (deriv χ) x : ℝ) : ℂ)) :=
  ⟨Complex.continuous_ofReal.comp (hχ.continuous_deriv (by norm_num)),
    Complex.continuous_ofReal.comp
      ((ContDiff.deriv' (n := 1) (by convert hχ; norm_num)).continuous_deriv le_rfl)⟩

/-- `ℒ(χφ) = χ ℒφ − 2χ′φ′ − χ″φ`. -/
theorem schrodingerOp_cutoff_mul (q : ℝ → ℝ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (x : ℝ) :
    schrodingerOp q (fun x => (χ x : ℂ) * φ x) x = (χ x : ℂ) * schrodingerOp q φ x -
      2 * ((deriv χ x : ℝ) : ℂ) * deriv φ x - ((deriv (deriv χ) x : ℝ) : ℂ) * φ x := by
  have hd1 : deriv (fun x => (χ x : ℂ) * φ x) =
      fun x => ((deriv χ x : ℝ) : ℂ) * φ x + (χ x : ℂ) * deriv φ x := by
    funext y
    exact ((cutoff_derivs hχ y).1.mul (hasDerivAt_deriv_of_contDiff_two hφ y).1).deriv
  have hd2 : deriv (fun x => ((deriv χ x : ℝ) : ℂ) * φ x + (χ x : ℂ) * deriv φ x) x =
      ((deriv (deriv χ) x : ℝ) : ℂ) * φ x + ((deriv χ x : ℝ) : ℂ) * deriv φ x +
        (((deriv χ x : ℝ) : ℂ) * deriv φ x + (χ x : ℂ) * deriv (deriv φ) x) :=
    (((cutoff_derivs hχ x).2.mul (hasDerivAt_deriv_of_contDiff_two hφ x).1).add
      ((cutoff_derivs hχ x).1.mul (hasDerivAt_deriv_of_contDiff_two hφ x).2)).deriv
  simp only [schrodingerOp, hd1, hd2]
  ring

end Cutoff

section CutoffMem

variable (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) (hq : ContinuousOn q X)

theorem continuousOn_maxRepD (f : (minOp X q)†.domain) :
    ContinuousOn (maxRepD hX hXc hne hq f) X := by
  intro x hx
  obtain ⟨ε, hε, hJ⟩ := exists_Icc_ball hX hx
  obtain ⟨-, -, hD⟩ := maxRep_spec hX hXc hne hq f
  set h : ℝ → ℂ := fun t => (q t : ℂ) * maxRep hX hXc hne hq f t -
    (((minOp X q)† f : L2X X) : ℝ → ℂ) t
  have hloc : LocallyIntegrableOn h X :=
    (((Complex.continuous_ofReal.comp_continuousOn hq).mul
      (continuousOn_maxRep hX hXc hne hq f)).locallyIntegrableOn hX.measurableSet).sub
      (L2X.locallyIntegrableOn hX _)
  have hint : IntervalIntegrable h volume (x - ε) (x + ε) :=
    (hloc.integrableOn_compact_subset (by rwa [uIcc_of_le (by linarith)]) isCompact_uIcc)
      |>.intervalIntegrable
  have hprim := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := x) hint
    (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
  rw [uIcc_of_le (by linarith)] at hprim
  have heq : EqOn (maxRepD hX hXc hne hq f) (fun s => maxRepD hX hXc hne hq f x +
      ∫ t in x..s, h t) (Icc (x - ε) (x + ε)) := fun s hs => hD x hx s (hJ hs)
  exact (((continuousOn_const.add hprim).congr heq).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

end CutoffMem

/-- The weak identity `∫ f ℒψ = ∫ (ℒ*f) ψ` for `f ∈ 𝒟(ℒ*)`. -/
theorem weak_of_mem_adjoint (hX : IsOpen X) (hq : ContinuousOn q X) (f : (minOp X q)†.domain)
    {ψ : ℝ → ℂ} (hψ : IsC2c X ψ) :
    ∫ x in X, ((f : L2X X) : ℝ → ℂ) x * schrodingerOp q ψ x =
      ∫ x in X, (((minOp X q)† f : L2X X) : ℝ → ℂ) x * ψ x :=
  (weak_schrodinger_iff hX hq (f : L2X X) ((minOp X q)† f)).mpr
    ((adjoint_isFormalAdjoint (dense_minOp_domain hX hq)) f) ψ hψ

section CutoffMem2

variable (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) (hq : ContinuousOn q X)

include hX hXc hne hq in
/-- **Cut-off multiplication**, general form: if `F` is `C¹` on `X` and weakly `ℒF = g`, and `χF`,
`χg` are square integrable for a smooth `χ` constant outside a compact `[α, β] ⊆ X`, then
`χF ∈ 𝒟(ℒ*)` with `ℒ*(χF) = χg − 2χ′F′ − χ″F`. -/
theorem mem_adjoint_cutoff_of_weak {F F' g : ℝ → ℂ} (hF : ∀ x ∈ X, HasDerivAt F (F' x) x)
    (hF'c : ContinuousOn F' X) (hg : LocallyIntegrableOn g X)
    (hA : ∀ ψ : ℝ → ℂ, IsC2c X ψ →
      ∫ x in X, F x * schrodingerOp q ψ x = ∫ x in X, g x * ψ x)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) {α β : ℝ} (hIcc : Icc α β ⊆ X)
    (hχc : ∀ x ∉ Ioo α β, deriv χ =ᶠ[𝓝 x] 0)
    (h1 : MemLp (fun x => (χ x : ℂ) * F x) 2 (volume.restrict X))
    (hg2 : MemLp (fun x => (χ x : ℂ) * g x) 2 (volume.restrict X)) :
    ∃ (h2 : MemLp (fun x => (χ x : ℂ) * g x - 2 * ((deriv χ x : ℝ) : ℂ) * F' x -
        ((deriv (deriv χ) x : ℝ) : ℂ) * F x) 2 (volume.restrict X)),
      ∃ hm : h1.toLp ∈ (minOp X q)†.domain, (minOp X q)† ⟨_, hm⟩ = h2.toLp := by
  set χc : ℝ → ℂ := fun x => (χ x : ℂ)
  set χ1 : ℝ → ℂ := fun x => ((deriv χ x : ℝ) : ℂ)
  set χ2 : ℝ → ℂ := fun x => ((deriv (deriv χ) x : ℝ) : ℂ)
  have hχcc : Continuous χc := Complex.continuous_ofReal.comp hχ.continuous
  obtain ⟨hχ1c, hχ2c⟩ := cutoff_continuous hχ
  have hχz : ∀ x ∉ Ioo α β, χ1 x = 0 ∧ χ2 x = 0 := fun x hx => by
    refine ⟨by simp [χ1, (hχc x hx).eq_of_nhds], ?_⟩
    simp [χ2, (hχc x hx).deriv_eq]
  have hFc : ContinuousOn F X := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  set P : ℝ → ℂ := fun x => 2 * χ1 x * F' x + χ2 x * F x
  have hPc : ContinuousOn P X :=
    ((continuousOn_const.mul hχ1c.continuousOn).mul hF'c).add (hχ2c.continuousOn.mul hFc)
  have hPz : ∀ x ∉ Ioo α β, P x = 0 := fun x hx => by simp [P, (hχz x hx).1, (hχz x hx).2]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hPc.mono hIcc)
  have hP2 : MemLp P 2 (volume.restrict X) := by
    refine (memLp_indicator_const 2 (measurableSet_Icc (a := α) (b := β)) M (Or.inr ?_)).of_le
      (hPc.aestronglyMeasurable hX.measurableSet) (ae_of_all _ fun x => ?_)
    · rw [Measure.restrict_apply measurableSet_Icc]
      exact ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
    · by_cases hx : x ∈ Icc α β
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        exact (hM x hx).trans (le_abs_self M)
      · rw [hPz x fun h => hx (Ioo_subset_Icc_self h), indicator_of_notMem hx]; simp
  have h2 : MemLp (fun x => χc x * g x - 2 * χ1 x * F' x - χ2 x * F x) 2 (volume.restrict X) :=
    (hg2.sub hP2).ae_eq (ae_of_all _ fun x => by simp only [P, Pi.sub_apply]; ring)
  refine ⟨h2, ?_⟩
  -- the weak identity
  have hweak : ∀ φ : ℝ → ℂ, IsC2c X φ →
      ∫ x in X, (h1.toLp : ℝ → ℂ) x * schrodingerOp q φ x =
        ∫ x in X, (h2.toLp : ℝ → ℂ) x * φ x := by
    intro φ hφ
    obtain ⟨c, hc⟩ := hne
    obtain ⟨α', β', hα', hβ', hαβ', hK, -⟩ := exists_Ioo_of_isCompact hX
      (hφ.2.1.isCompact.union isCompact_Icc) (union_subset hφ.2.2 hIcc) hc
    have hI' : Icc α' β' ⊆ X := hXc.out hα' hβ'
    have hφK : tsupport φ ⊆ Ioo α' β' := subset_union_left.trans hK
    have hIK : Icc α β ⊆ Ioo α' β' := subset_union_right.trans hK
    have hφz : ∀ x ∉ Ioo α' β', φ x = 0 := fun x hx =>
      ((notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hφK h)).eq_of_nhds
    have hLφz : ∀ x ∉ Ioo α' β', schrodingerOp q φ x = 0 := fun x hx => by
      by_contra h; exact hx (hφK (support_schrodingerOp_subset q φ h))
    have hχz' : ∀ x ∉ Ioo α' β', χ1 x = 0 ∧ χ2 x = 0 := fun x hx =>
      hχz x fun h => hx (hIK (Ioo_subset_Icc_self h))
    have hφd := fun x => (hasDerivAt_deriv_of_contDiff_two hφ.1 x).1
    have hφ' : Continuous (deriv φ) := continuous_deriv' hφ.1
    have hLφ : Continuous (schrodingerOp q φ) := continuous_schrodingerOp hX hq hφ
    -- the test function `χφ`
    have hχφ : IsC2c X fun x => χc x * φ x :=
      ⟨(Complex.ofRealCLM.contDiff.comp hχ).mul hφ.1, hφ.2.1.mul_left,
        tsupport_mul_subset_right.trans hφ.2.2⟩
    have hA := hA _ hχφ
    have ii : ∀ u : ℝ → ℂ, ContinuousOn u (Icc α' β') → IntervalIntegrable u volume α' β' :=
      fun u hu => hu.intervalIntegrable_of_Icc hαβ'.le
    have hFc' := hFc.mono hI'
    have hF'c' := hF'c.mono hI'
    have ig : ∀ u : ℝ → ℂ, Continuous u → IntervalIntegrable (fun x => g x * u x) volume α' β' :=
      fun u hu => intervalIntegrable_mul_of_locallyIntegrableOn hg hu hαβ'.le hI'
    -- move everything to `[α', β']`
    have eL : ∫ x in X, (h1.toLp : ℝ → ℂ) x * schrodingerOp q φ x =
        ∫ x in α'..β', χc x * F x * schrodingerOp q φ x := by
      rw [← setIntegral_eq_intervalIntegral_of_vanish hαβ'.le hI' fun x hx => by
        simp [hLφz x hx]]
      exact integral_congr_ae (by filter_upwards [h1.coeFn_toLp] with x hx; rw [hx])
    have eR : ∫ x in X, (h2.toLp : ℝ → ℂ) x * φ x =
        ∫ x in α'..β', (χc x * g x - 2 * χ1 x * F' x - χ2 x * F x) * φ x := by
      rw [← setIntegral_eq_intervalIntegral_of_vanish hαβ'.le hI' fun x hx => by
        simp [hφz x hx]]
      exact integral_congr_ae (by filter_upwards [h2.coeFn_toLp] with x hx; rw [hx])
    have eA1 : ∫ x in X, F x * schrodingerOp q (fun x => χc x * φ x) x =
        ∫ x in α'..β', F x * schrodingerOp q (fun x => χc x * φ x) x :=
      setIntegral_eq_intervalIntegral_of_vanish hαβ'.le hI' fun x hx => by
        rw [schrodingerOp_cutoff_mul hχ q hφ.1]; simp [hLφz x hx, hφz x hx]
        exact Or.inr (Or.inr (deriv_eq_zero_of_notMem' hφK hx))
    have eA2 : ∫ x in X, g x * (χc x * φ x) = ∫ x in α'..β', g x * (χc x * φ x) :=
      setIntegral_eq_intervalIntegral_of_vanish hαβ'.le hI' fun x hx => by simp [hφz x hx]
    rw [eA1, eA2] at hA
    -- integration by parts for `∫ 2χ′F φ′`
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α') (b := β')
      (u := fun x => 2 * χ1 x * F x) (u' := fun x => 2 * χ2 x * F x + 2 * χ1 x * F' x)
      (v := φ) (v' := deriv φ)
      (fun x hx => by
        have hxX : x ∈ X := hI' (by rwa [uIcc_of_le hαβ'.le] at hx)
        exact (((cutoff_derivs hχ x).2.const_mul 2).mul (hF x hxX)).congr_deriv (by ring))
      (fun x _ => hφd x)
      (ii _ (((continuousOn_const.mul hχ2c.continuousOn).mul hFc').add
        ((continuousOn_const.mul hχ1c.continuousOn).mul hF'c')))
      (hφ'.intervalIntegrable _ _)
    rw [hφz α' (fun h => lt_irrefl _ h.1), hφz β' (fun h => lt_irrefl _ h.2)] at hIBP
    simp only [mul_zero, sub_zero] at hIBP
    -- assemble
    have hpt : ∀ x, χc x * F x * schrodingerOp q φ x =
        F x * schrodingerOp q (fun x => χc x * φ x) x + 2 * χ1 x * F x * deriv φ x +
          χ2 x * F x * φ x := fun x => by
      rw [schrodingerOp_cutoff_mul hχ q hφ.1]; ring
    have c1 : ContinuousOn (fun x => F x * schrodingerOp q (fun x => χc x * φ x) x)
        (Icc α' β') := hFc'.mul (continuous_schrodingerOp hX hq hχφ).continuousOn
    have c2 : ContinuousOn (fun x => 2 * χ1 x * F x * deriv φ x) (Icc α' β') :=
      ((continuousOn_const.mul hχ1c.continuousOn).mul hFc').mul hφ'.continuousOn
    have c3 : ContinuousOn (fun x => χ2 x * F x * φ x) (Icc α' β') :=
      (hχ2c.continuousOn.mul hFc').mul hφ.1.continuous.continuousOn
    have c4 : ContinuousOn (fun x => (2 * χ2 x * F x + 2 * χ1 x * F' x) * φ x) (Icc α' β') :=
      (((continuousOn_const.mul hχ2c.continuousOn).mul hFc').add
        ((continuousOn_const.mul hχ1c.continuousOn).mul hF'c')).mul hφ.1.continuous.continuousOn
    rw [eL, eR, intervalIntegral.integral_congr (g := fun x =>
      F x * schrodingerOp q (fun x => χc x * φ x) x + 2 * χ1 x * F x * deriv φ x +
        χ2 x * F x * φ x) fun x _ => hpt x,
      intervalIntegral.integral_add ((ii _ c1).add (ii _ c2)) (ii _ c3),
      intervalIntegral.integral_add (ii _ c1) (ii _ c2), hA, hIBP]
    have e5 : ∫ x in α'..β', (χc x * g x - 2 * χ1 x * F' x - χ2 x * F x) * φ x =
        (∫ x in α'..β', g x * (χc x * φ x)) -
          ∫ x in α'..β', ((2 * χ2 x * F x + 2 * χ1 x * F' x) * φ x - χ2 x * F x * φ x) := by
      rw [← intervalIntegral.integral_sub (f := fun x => g x * (χc x * φ x))
        (g := fun x => (2 * χ2 x * F x + 2 * χ1 x * F' x) * φ x - χ2 x * F x * φ x)
        (ig _ (hχcc.mul hφ.1.continuous)) ((ii _ c4).sub (ii _ c3))]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [e5, intervalIntegral.integral_sub (ii _ c4) (ii _ c3)]
    ring
  have hmem := (dlmf_1_18_ix_maxDomain hX hq _).mpr ⟨_, hweak⟩
  exact ⟨hmem, minOp_adjoint_apply hX hq ⟨_, hmem⟩ _ hweak⟩


include hX hXc hne hq in
/-- **Cut-off multiplication**: for `f ∈ 𝒟(ℒ*)` and a smooth `χ`, `|χ| ≤ 1`, constant outside a
compact `[α, β] ⊆ X`, `χf ∈ 𝒟(ℒ*)` with `ℒ*(χf) = χ ℒ*f − 2χ′f′ − χ″f`. -/
theorem mem_adjoint_cutoff (f : (minOp X q)†.domain) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ x, |χ x| ≤ 1) {α β : ℝ} (hIcc : Icc α β ⊆ X)
    (hχc : ∀ x ∉ Ioo α β, deriv χ =ᶠ[𝓝 x] 0) :
    ∃ (h1 : MemLp (fun x => (χ x : ℂ) * maxRep hX hXc hne hq f x) 2 (volume.restrict X))
      (h2 : MemLp (fun x => (χ x : ℂ) * (((minOp X q)† f : L2X X) : ℝ → ℂ) x -
        2 * ((deriv χ x : ℝ) : ℂ) * maxRepD hX hXc hne hq f x -
        ((deriv (deriv χ) x : ℝ) : ℂ) * maxRep hX hXc hne hq f x) 2 (volume.restrict X)),
      ∃ hm : h1.toLp ∈ (minOp X q)†.domain, (minOp X q)† ⟨_, hm⟩ = h2.toLp := by
  obtain ⟨hwF, hF, -⟩ := maxRep_spec hX hXc hne hq f
  have hχcc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hbd : ∀ x, ‖(χ x : ℂ)‖ ≤ 1 := fun x => by simp [Complex.norm_real, hχb x]
  have hmul : ∀ v : L2X X, MemLp (fun x => (χ x : ℂ) * (v : ℝ → ℂ) x) 2 (volume.restrict X) :=
    fun v => (Lp.memLp v).of_le (hχcc.aestronglyMeasurable.mul (Lp.memLp v).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hbd x))
  have h1 : MemLp (fun x => (χ x : ℂ) * maxRep hX hXc hne hq f x) 2 (volume.restrict X) :=
    (hmul f).ae_eq (by filter_upwards [hwF] with x hx; rw [hx])
  obtain ⟨h2, hm, hT⟩ := mem_adjoint_cutoff_of_weak hX hXc hne hq hF
    (continuousOn_maxRepD hX hXc hne hq f) (L2X.locallyIntegrableOn hX _)
    (fun ψ hψ => by
      rw [← weak_of_mem_adjoint hX hq f hψ]
      exact integral_congr_ae (by filter_upwards [hwF] with x hx; rw [hx]))
    hχ hIcc hχc h1 (hmul _)
  exact ⟨h1, h2, hm, hT⟩

end CutoffMem2

/-! ### A standard cut-off -/

theorem exists_cutoff {d₁ d₂ : ℝ} (h : d₁ < d₂) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 2 χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ≤ d₁, χ x = 1) ∧
      (∀ x, d₂ ≤ x → χ x = 0) ∧
      ∀ α β, α < d₁ → d₂ < β → ∀ x ∉ Ioo α β, deriv χ =ᶠ[𝓝 x] 0 := by
  set χ : ℝ → ℝ := fun x => Real.smoothTransition ((d₂ - x) / (d₂ - d₁))
  have hd : 0 < d₂ - d₁ := by linarith
  have h1 : ∀ x ≤ d₁, χ x = 1 := fun x hx =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hd]; linarith)
  have h0 : ∀ x, d₂ ≤ x → χ x = 0 := fun x hx =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  refine ⟨χ, Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _),
    fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    h1, h0, fun α β hα hβ x hx => ?_⟩
  rcases le_or_gt x α with hxa | hxa
  · have hev : χ =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds (show x < d₁ by linarith)] with y hy using h1 y hy.le
    filter_upwards [hev.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq]; simp
  · have hxb : β ≤ x := by
      by_contra hb; push Not at hb; exact hx ⟨hxa, hb⟩
    have hev : χ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (show d₂ < x by linarith)] with y hy using h0 y hy.le
    filter_upwards [hev.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq]; simp

/-! ### Restriction to a subinterval -/

theorem memLp_restrict_sub {Y : Set ℝ} (hYX : Y ⊆ X) (v : L2X X) :
    MemLp ((v : L2X X) : ℝ → ℂ) 2 (volume.restrict Y) := by
  have := (Lp.memLp v).restrict Y
  rwa [Measure.restrict_restrict_of_subset hYX] at this

/-- The restriction of `w ∈ 𝒟(ℒ_X*)` to an open `Y ⊆ X` lies in `𝒟(ℒ_Y*)`. -/
theorem restrict_mem_adjoint (hX : IsOpen X) (hq : ContinuousOn q X) {Y : Set ℝ} (hY : IsOpen Y)
    (hYX : Y ⊆ X) (w : (minOp X q)†.domain) :
    ∃ h : (memLp_restrict_sub hYX (w : L2X X)).toLp ∈ (minOp Y q)†.domain,
      (minOp Y q)† ⟨_, h⟩ = (memLp_restrict_sub hYX ((minOp X q)† w)).toLp := by
  have hqY : ContinuousOn q Y := hq.mono hYX
  have hweak : ∀ φ : ℝ → ℂ, IsC2c Y φ →
      ∫ x in Y, ((memLp_restrict_sub hYX (w : L2X X)).toLp : ℝ → ℂ) x * schrodingerOp q φ x =
        ∫ x in Y, ((memLp_restrict_sub hYX ((minOp X q)† w)).toLp : ℝ → ℂ) x * φ x := by
    intro φ hφ
    have hφX : IsC2c X φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hYX⟩
    have hφz : ∀ x ∉ Y, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
      fun h => hx (hφ.2.2 h)
    have hLφz : ∀ x ∉ Y, schrodingerOp q φ x = 0 := fun x hx => by
      by_contra h; exact hx (hφ.2.2 (support_schrodingerOp_subset q φ h))
    have hA := weak_of_mem_adjoint hX hq w hφX
    have e1 : ∫ x in Y, ((memLp_restrict_sub hYX (w : L2X X)).toLp : ℝ → ℂ) x *
        schrodingerOp q φ x = ∫ x in X, ((w : L2X X) : ℝ → ℂ) x * schrodingerOp q φ x := by
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hX.measurableSet hYX
        fun x hx => by simp [hLφz x hx.2]]
      exact integral_congr_ae (by
        filter_upwards [(memLp_restrict_sub hYX (w : L2X X)).coeFn_toLp] with x hx; rw [hx])
    have e2 : ∫ x in Y, ((memLp_restrict_sub hYX ((minOp X q)† w)).toLp : ℝ → ℂ) x * φ x =
        ∫ x in X, (((minOp X q)† w : L2X X) : ℝ → ℂ) x * φ x := by
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hX.measurableSet hYX
        fun x hx => by simp [hφz x hx.2]]
      exact integral_congr_ae (by
        filter_upwards [(memLp_restrict_sub hYX ((minOp X q)† w)).coeFn_toLp] with x hx
        rw [hx])
    rw [e1, e2, hA]
  have hmem := (dlmf_1_18_ix_maxDomain hY hqY _).mpr ⟨_, hweak⟩
  exact ⟨hmem, minOp_adjoint_apply hY hqY ⟨_, hmem⟩ _ hweak⟩

/-! ### Transfer from a subinterval -/

theorem norm_eq_of_restrict {Y : Set ℝ} (hY : MeasurableSet Y) (hYX : Y ⊆ X) (U : L2X X)
    (W : L2X Y) (h1 : (U : ℝ → ℂ) =ᵐ[volume.restrict Y] W)
    (h2 : (U : ℝ → ℂ) =ᵐ[volume.restrict (X \ Y)] 0) : ‖U‖ = ‖W‖ := by
  have hU : IntegrableOn (fun x => ‖(U : ℝ → ℂ) x‖ ^ 2) X :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp U).aestronglyMeasurable).mp (Lp.memLp U)
  have hs := integral_inter_add_sdiff (μ := volume) hY hU
  rw [inter_eq_right.mpr hYX] at hs
  have hz : ∫ x in X \ Y, ‖(U : ℝ → ℂ) x‖ ^ 2 = 0 :=
    integral_eq_zero_of_ae (by filter_upwards [h2] with x hx; simp [hx])
  have hY' : ∫ x in Y, ‖(U : ℝ → ℂ) x‖ ^ 2 = ∫ x in Y, ‖(W : ℝ → ℂ) x‖ ^ 2 :=
    integral_congr_ae (by filter_upwards [h1] with x hx; rw [hx])
  rw [hz, add_zero, hY', integral_norm_sq_Lp, integral_norm_sq_Lp] at hs
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs).symm

section Transfer

variable (hX : IsOpen X) (hq : ContinuousOn q X)

include hX hq in
/-- If `g ∈ 𝒟(ℒ_X*)` and `ℒ_X* g` vanish on `X ∖ Y`, and `g|_Y ∈ 𝒟(ℒ_Y**)`, then every
boundary value for `ℒ` on `X` vanishes at `g`. -/
theorem IsBoundaryValue.eq_zero_of_restrict {B : (minOp X q)†.domain →ₗ[ℂ] ℂ}
    (hB : IsBoundaryValue X q B) {Y : Set ℝ} (hY : IsOpen Y) (hYX : Y ⊆ X)
    (g : (minOp X q)†.domain) (hg0 : ((g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X \ Y)] 0)
    (hTg0 : (((minOp X q)† g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X \ Y)] 0)
    (hYm : (memLp_restrict_sub hYX (g : L2X X)).toLp ∈ (minOp Y q)††.domain) : B g = 0 := by
  have hqY : ContinuousOn q Y := hq.mono hYX
  have hTY := isSymmetricDLMF_minOp hY hqY
  have hTX := isSymmetricDLMF_minOp hX hq
  obtain ⟨hr, hTr⟩ := restrict_mem_adjoint hX hq hY hYX g
  set r := (memLp_restrict_sub hYX (g : L2X X)).toLp
  obtain ⟨C, hC⟩ := hB.1
  by_contra hne
  have hpos : 0 < ‖B g‖ := norm_pos_iff.mpr hne
  set ε := ‖B g‖ / (2 * (|C| + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨φ, h1, h2⟩ := hTY.approx_adjoint_adjoint ⟨r, hYm⟩ hε
  obtain ⟨ψ, hψ, hφψ⟩ := (SetLike.ext_iff.mp (minOp_domain hY hqY) (φ : L2X Y)).mp φ.2
  have hψX : IsC2c X ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hYX⟩
  set Ψ : L2X X := hψX.memLp.toLp
  have hΨ : Ψ ∈ (minOp X q).domain := by
    rw [minOp_domain hX hq]; exact ⟨ψ, hψX, hψX.memLp.coeFn_toLp⟩
  set Ψ' : (minOp X q)†.domain := ⟨Ψ, hTX.le_adjoint.1 hΨ⟩
  have hBΨ : B Ψ' = 0 := hB.2 Ψ' hΨ
  have hTΨ : (minOp X q)† Ψ' = minOp X q ⟨Ψ, hΨ⟩ := (hTX.le_adjoint.2 rfl).symm
  have hψz : ∀ x ∉ Y, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
    fun h => hx (hψ.2.2 h)
  have hLψz : ∀ x ∉ Y, schrodingerOp q ψ x = 0 := fun x hx => by
    by_contra h; exact hx (hψ.2.2 (support_schrodingerOp_subset q ψ h))
  have hdiff : ∀ {Z : Set ℝ}, MeasurableSet Z → Z ⊆ X \ Y → ∀ᵐ x ∂(volume.restrict Z), x ∉ Y :=
    fun hZ hZsub => (ae_restrict_iff' hZ).mpr (ae_of_all _ fun x hx => (hZsub hx).2)
  -- the two norms
  have hn1 : ‖(g : L2X X) - Ψ‖ = ‖r - (φ : L2X Y)‖ := by
    refine norm_eq_of_restrict hY.measurableSet hYX _ _ ?_ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hYX (Lp.coeFn_sub (g : L2X X) Ψ),
        ae_restrict_of_ae_restrict_of_subset hYX hψX.memLp.coeFn_toLp,
        Lp.coeFn_sub r (φ : L2X Y), (memLp_restrict_sub hYX (g : L2X X)).coeFn_toLp, hφψ]
        with x h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply, h4, h5]
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset
          (Lp.coeFn_sub (g : L2X X) Ψ),
        hg0, ae_restrict_of_ae_restrict_of_subset sdiff_subset hψX.memLp.coeFn_toLp,
        hdiff (hX.measurableSet.diff hY.measurableSet) subset_rfl] with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, hψz x h4]; simp
  have hn2 : ‖((minOp X q)† g : L2X X) - minOp X q ⟨Ψ, hΨ⟩‖ =
      ‖(minOp Y q)†† ⟨r, hYm⟩ - minOp Y q φ‖ := by
    have hTTr : (minOp Y q)†† ⟨r, hYm⟩ = (minOp Y q)† ⟨r, hr⟩ :=
      hTY.le_adjoint_adjoint.2.2 rfl
    rw [hTTr, hTr]
    have hTφ := minOp_apply hY φ hψ hφψ
    have hTΨ' := minOp_apply hX ⟨Ψ, hΨ⟩ hψX hψX.memLp.coeFn_toLp
    refine norm_eq_of_restrict hY.measurableSet hYX _ _ ?_ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hYX
          (Lp.coeFn_sub ((minOp X q)† g) (minOp X q ⟨Ψ, hΨ⟩)),
        ae_restrict_of_ae_restrict_of_subset hYX hTΨ',
        Lp.coeFn_sub (memLp_restrict_sub hYX ((minOp X q)† g)).toLp (minOp Y q φ),
        (memLp_restrict_sub hYX ((minOp X q)† g)).coeFn_toLp, hTφ] with x h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply, h4, h5]
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset
        (Lp.coeFn_sub ((minOp X q)† g) (minOp X q ⟨Ψ, hΨ⟩)), hTg0,
        ae_restrict_of_ae_restrict_of_subset sdiff_subset hTΨ',
        hdiff (hX.measurableSet.diff hY.measurableSet) subset_rfl] with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, hLψz x h4]; simp
  have hb := hC (g - Ψ')
  rw [_root_.map_sub, hBΨ, sub_zero, LinearPMap.map_sub, hTΨ] at hb
  have hb' : ‖B g‖ ≤ |C| * (ε + ε) := by
    refine hb.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (abs_nonneg _)
    · change ‖(g : L2X X) - Ψ‖ ≤ ε; rw [hn1]; exact h1.le
    · rw [hn2]; exact h2.le
  have : |C| * (ε + ε) < ‖B g‖ := by
    simp only [ε]
    rw [show |C| * (‖B g‖ / (2 * (|C| + 1)) + ‖B g‖ / (2 * (|C| + 1))) =
      ‖B g‖ * (|C| / (|C| + 1)) by field_simp; ring]
    exact mul_lt_of_lt_one_right hpos ((div_lt_one (by positivity)).mpr (by linarith))
  linarith

end Transfer

/-- On a limit-point side `Y`, an `F ∈ 𝒟(ℒ_Y*)` whose boundary form against all test functions
supported near `c` vanishes lies in `𝒟(ℒ_Y**)`. -/
theorem mem_adjoint_adjoint_of_boundary_zero (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) {Y : Set ℝ} (s : ℂ)
    (hside : (Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1))
    (h1 : Module.finrank ℂ (deficiencySpace (minOp Y q) z) = 1) {r : ℝ} (hr : 0 < r)
    (hIcc : Icc (c - r) (c + r) ⊆ X) (F : (minOp Y q)†.domain)
    (hF : ∀ (e : ℝ → ℂ) (he : IsC2c X e), tsupport e ⊆ Ioo (c - r) (c + r) →
      ∀ hE : (he.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
        ⟪(minOp Y q)† F, (he.memLp_on Y).toLp⟫_ℂ - ⟪(F : L2X Y), (minOp Y q)† ⟨_, hE⟩⟫_ℂ = 0) :
    (F : L2X Y) ∈ (minOp Y q)††.domain := by
  have hside' : Y = X ∩ Iio c ∨ Y = X ∩ Ioi c := by
    rcases hside with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hs0 : s ≠ 0 := by rcases hside with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  obtain ⟨hY, hYc, hYne, hYX⟩ := halfInterval_props hX hXc hc hside'
  have hqY : ContinuousOn q Y := hq.mono hYX
  have hT := isSymmetricDLMF_minOp hY hqY
  have : ∀ w : ℂ, FiniteDimensional ℂ (deficiencySpace (minOp Y q) w) := fun w =>
    (dlmf_1_18_ix_finrank_le hY hYc hYne hqY w).1
  have hI : Module.finrank ℂ (deficiencySpace (minOp Y q) Complex.I) = 1 := by
    rw [← finrank_deficiency_eq_I hY hYc hYne hqY hz, h1]
  have hmI : Module.finrank ℂ (deficiencySpace (minOp Y q) (-Complex.I)) = 1 := by
    rw [← Complex.conj_I, ← dlmf_1_18_ix_deficiency_eq hY hYc hYne hqY, hI]
  obtain ⟨e₁, e₂, he₁, he₂, hs₁, hs₂, he₁c, he₁d, he₂c, he₂d⟩ := exists_boundary_pair hr hIcc
  obtain ⟨hE₁, hTE₁⟩ := mem_adjoint_of_isC2c hX hq hY hYX he₁
  obtain ⟨hE₂, hTE₂⟩ := mem_adjoint_of_isC2c hX hq hY hYX he₂
  set E₁ : (minOp Y q)†.domain := ⟨_, hE₁⟩
  set E₂ : (minOp Y q)†.domain := ⟨_, hE₂⟩
  set B : (minOp Y q)†.domain → (minOp Y q)†.domain → ℂ := fun x y =>
    ⟪(minOp Y q)† x, (y : L2X Y)⟫_ℂ - ⟪(x : L2X Y), (minOp Y q)† y⟫_ℂ
  have Badd : ∀ x y w, B (x + y) w = B x w + B y w := fun x y w => by
    simp only [B, LinearPMap.map_add, Submodule.coe_add, inner_add_left]; ring
  have Bconj : ∀ x y, B x y = -conj (B y x) := fun x y => by
    simp only [B, _root_.map_sub, inner_conj_symm]; ring
  have Bzero : ∀ x y : (minOp Y q)†.domain, ((x : L2X Y) ∈ (minOp Y q)††.domain) →
      B x y = 0 := fun x y hx =>
    hT.boundary_eq_zero_of_mem x y hx
  -- linear combinations of test functions
  set ê : ℂ → ℂ → ℝ → ℂ := fun α β => α • e₁ + β • e₂
  have hê : ∀ α β, IsC2c X (ê α β) := fun α β => (he₁.smul α).add (he₂.smul β)
  have hsm : ∀ (a : ℂ) (e : ℝ → ℂ), tsupport (a • e) ⊆ tsupport e := fun a e => by
    have := tsupport_smul_subset_right (fun _ : ℝ => a) e
    exact this
  have hês : ∀ α β, tsupport (ê α β) ⊆ Ioo (c - r) (c + r) := fun α β =>
    (tsupport_add _ _).trans (union_subset ((hsm α e₁).trans hs₁) ((hsm β e₂).trans hs₂))
  have hêc : ∀ α β, ê α β c = β := fun α β => by simp [ê, he₁c, he₂c]
  have hêd : ∀ α β, deriv (ê α β) c = α := fun α β => by
    have d1 : DifferentiableAt ℝ e₁ c := he₁.1.differentiable (by norm_num) c
    have d2 : DifferentiableAt ℝ e₂ c := he₂.1.differentiable (by norm_num) c
    simp only [ê]
    rw [deriv_add (d1.const_smul α) (d2.const_smul β), deriv_const_smul _ d1,
      deriv_const_smul _ d2, he₁d, he₂d]
    simp
  have hêL : ∀ α β, ((α • E₁ + β • E₂ : (minOp Y q)†.domain) : L2X Y) =
      ((hê α β).memLp_on Y).toLp := fun α β => by
    refine Lp.ext ?_
    simp only [Submodule.coe_add, Submodule.coe_smul, E₁, E₂]
    filter_upwards [Lp.coeFn_add (α • (he₁.memLp_on Y).toLp) (β • (he₂.memLp_on Y).toLp),
      Lp.coeFn_smul α (he₁.memLp_on Y).toLp, Lp.coeFn_smul β (he₂.memLp_on Y).toLp,
      (he₁.memLp_on Y).coeFn_toLp, (he₂.memLp_on Y).coeFn_toLp,
      ((hê α β).memLp_on Y).coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, h6]
    simp [ê]
  -- the boundary form of a combination against the test functions
  have hBcomb : ∀ α β, ∀ (g : ℝ → ℂ) (hg : IsC2c X g), tsupport g ⊆ Ioo (c - r) (c + r) →
      ∀ hG : (hg.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
      B (α • E₁ + β • E₂) ⟨_, hG⟩ = s * conj (wronskianConj (ê α β) g c) := by
    intro α β g hg hgs hG
    obtain ⟨hF', hG', hB'⟩ := boundaryForm_testFunctions hX hq hr hIcc (hê α β) hg (hês α β) hgs
      hY hYX s hside
    have he : (α • E₁ + β • E₂ : (minOp Y q)†.domain) = ⟨_, hF'⟩ := Subtype.ext (hêL α β)
    rw [he]
    exact hB'
  have hind : ∀ α β : ℂ, ((α • E₁ + β • E₂ : (minOp Y q)†.domain) : L2X Y) ∈
      (minOp Y q)††.domain → α = 0 ∧ β = 0 := by
    intro α β hm
    have h₁ := hBcomb α β e₁ he₁ hs₁ hE₁
    have h₂ := hBcomb α β e₂ he₂ hs₂ hE₂
    rw [Bzero _ _ hm] at h₁ h₂
    have w₁ : wronskianConj (ê α β) e₁ c = β := by
      simp [wronskianConj, hêc, hêd, he₁c, he₁d]
    have w₂ : wronskianConj (ê α β) e₂ c = -α := by
      simp [wronskianConj, hêc, hêd, he₂c, he₂d]
    rw [w₁] at h₁
    rw [w₂] at h₂
    have hb : conj β = 0 := (mul_eq_zero.mp h₁.symm).resolve_left hs0
    have ha : conj (-α) = 0 := (mul_eq_zero.mp h₂.symm).resolve_left hs0
    simp only [map_eq_zero, neg_eq_zero] at hb ha
    exact ⟨ha, hb⟩
  obtain ⟨α, β, hdec⟩ := hT.exists_decomp_of_finrank_one hI hmI E₁ E₂ hind F
  set Ê : (minOp Y q)†.domain := α • E₁ + β • E₂
  set h : (minOp Y q)†.domain := F - α • E₁ - β • E₂
  have hFeq : F = h + Ê := by simp only [h, Ê]; abel
  have hsplit : ∀ w, B F w = B Ê w := fun w => by rw [hFeq, Badd, Bzero h w hdec, zero_add]
  have hz1 : B F E₁ = 0 := hF e₁ he₁ hs₁ hE₁
  have hz2 : B F E₂ = 0 := hF e₂ he₂ hs₂ hE₂
  rw [hsplit, hBcomb α β e₁ he₁ hs₁ hE₁] at hz1
  rw [hsplit, hBcomb α β e₂ he₂ hs₂ hE₂] at hz2
  have w₁ : wronskianConj (ê α β) e₁ c = β := by
    simp [wronskianConj, hêc, hêd, he₁c, he₁d]
  have w₂ : wronskianConj (ê α β) e₂ c = -α := by
    simp [wronskianConj, hêc, hêd, he₂c, he₂d]
  rw [w₁] at hz1
  rw [w₂] at hz2
  have hb : conj β = 0 := (mul_eq_zero.mp hz1).resolve_left hs0
  have ha : conj (-α) = 0 := (mul_eq_zero.mp hz2).resolve_left hs0
  simp only [map_eq_zero, neg_eq_zero] at hb ha
  have hF' : F = h := by rw [hFeq]; simp [Ê, ha, hb]
  rw [hF']
  exact hdec

/-- On a limit-point side `Y`, every boundary value vanishes at a `g ∈ 𝒟(ℒ*)` such that `g` and
`ℒ*g` vanish off `Y` and near `c`. -/
theorem IsBoundaryValue.eq_zero_of_vanish (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) {Y : Set ℝ} (s : ℂ)
    (hside : (Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1))
    (h1 : Module.finrank ℂ (deficiencySpace (minOp Y q) z) = 1) {r : ℝ} (hr : 0 < r)
    (hIcc : Icc (c - r) (c + r) ⊆ X) {B : (minOp X q)†.domain →ₗ[ℂ] ℂ}
    (hB : IsBoundaryValue X q B) (g : (minOp X q)†.domain)
    (hg : ∀ᵐ x ∂(volume.restrict X), x ∉ Y ∨ x ∈ Ioo (c - r) (c + r) →
      ((g : L2X X) : ℝ → ℂ) x = 0)
    (hTg : ∀ᵐ x ∂(volume.restrict X), x ∉ Y ∨ x ∈ Ioo (c - r) (c + r) →
      (((minOp X q)† g : L2X X) : ℝ → ℂ) x = 0) : B g = 0 := by
  have hside' : Y = X ∩ Iio c ∨ Y = X ∩ Ioi c := by
    rcases hside with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨hY, -, -, hYX⟩ := halfInterval_props hX hXc hc hside'
  obtain ⟨hr', hTr⟩ := restrict_mem_adjoint hX hq hY hYX g
  have hdiff : MeasurableSet (X \ Y) := hX.measurableSet.diff hY.measurableSet
  have hgY := ae_restrict_of_ae_restrict_of_subset hYX hg
  have hTgY := ae_restrict_of_ae_restrict_of_subset hYX hTg
  refine hB.eq_zero_of_restrict hX hq hY hYX g ?_ ?_ ?_
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hg, ae_restrict_mem hdiff]
      with x h1 h2 using h1 (Or.inl h2.2)
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hTg, ae_restrict_mem hdiff]
      with x h1 h2 using h1 (Or.inl h2.2)
  refine mem_adjoint_adjoint_of_boundary_zero hX hXc hq hc hz s hside h1 hr hIcc ⟨_, hr'⟩ ?_
  intro e he hts hE
  obtain ⟨hE', hTE⟩ := mem_adjoint_of_isC2c hX hq hY hYX he
  have hTE' : (minOp Y q)† ⟨_, hE⟩ = (he.memLp_schrodingerOp_on hX hq Y).toLp := hTE
  rw [hTr, hTE', inner_L2X, inner_L2X]
  have he0 : ∀ x ∉ Ioo (c - r) (c + r), e x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hts h)
  have hLe0 : ∀ x ∉ Ioo (c - r) (c + r), schrodingerOp q e x = 0 := fun x hx => by
    by_contra h; exact hx (hts (support_schrodingerOp_subset q e h))
  rw [integral_eq_zero_of_ae, integral_eq_zero_of_ae, sub_zero]
  · filter_upwards [(memLp_restrict_sub hYX (g : L2X X)).coeFn_toLp,
      (he.memLp_schrodingerOp_on hX hq Y).coeFn_toLp, hgY, ae_restrict_mem hY.measurableSet]
      with x h1 h2 h3 h4
    simp only [Pi.zero_apply]
    rw [h1, h2]
    by_cases hx : x ∈ Ioo (c - r) (c + r)
    · rw [h3 (Or.inr hx)]; simp
    · rw [hLe0 x hx]; simp
  · filter_upwards [(memLp_restrict_sub hYX ((minOp X q)† g)).coeFn_toLp,
      (he.memLp_on Y).coeFn_toLp, hTgY, ae_restrict_mem hY.measurableSet] with x h1 h2 h3 h4
    simp only [Pi.zero_apply]
    rw [h1, h2]
    by_cases hx : x ∈ Ioo (c - r) (c + r)
    · rw [h3 (Or.inr hx)]; simp
    · rw [he0 x hx]; simp

/-- Cut-off step of the limit-point argument: if `χ` vanishes near every point of `X` off `Y` or
near `c`, every boundary value vanishes at `χ f`. -/
theorem IsBoundaryValue.exists_cutoff_eq_zero (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) {Y : Set ℝ} (s : ℂ)
    (hside : (Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1))
    (h1 : Module.finrank ℂ (deficiencySpace (minOp Y q) z) = 1) {r : ℝ} (hr : 0 < r)
    (hIcc : Icc (c - r) (c + r) ⊆ X) {B : (minOp X q)†.domain →ₗ[ℂ] ℂ}
    (hB : IsBoundaryValue X q B) (f : (minOp X q)†.domain) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ x, |χ x| ≤ 1) {α β : ℝ} (hαβ : Icc α β ⊆ X)
    (hχc : ∀ x ∉ Ioo α β, deriv χ =ᶠ[𝓝 x] 0)
    (hχ0 : ∀ x ∈ X, x ∉ Y ∨ x ∈ Ioo (c - r) (c + r) → χ =ᶠ[𝓝 x] 0) :
    ∃ g : (minOp X q)†.domain, ((g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict X]
      (fun x => (χ x : ℂ) * maxRep hX hXc ⟨c, hc⟩ hq f x) ∧ B g = 0 := by
  obtain ⟨m1, m2, hm, hTg⟩ := mem_adjoint_cutoff hX hXc ⟨c, hc⟩ hq f hχ hχb hαβ hχc
  have hflat : ∀ x ∈ X, x ∉ Y ∨ x ∈ Ioo (c - r) (c + r) →
      χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0 := fun x hx hx' => by
    have hev := hχ0 x hx hx'
    have hev' : deriv χ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hev.eventuallyEq_nhds] with y hy
      rw [hy.deriv_eq]; simp
    refine ⟨hev.eq_of_nhds, hev'.eq_of_nhds, ?_⟩
    rw [hev'.deriv_eq]; simp
  refine ⟨⟨_, hm⟩, m1.coeFn_toLp,
    hB.eq_zero_of_vanish hX hXc hq hc hz s hside h1 hr hIcc ⟨_, hm⟩ ?_ ?_⟩
  · filter_upwards [m1.coeFn_toLp, ae_restrict_mem hX.measurableSet] with x h hx hx'
    rw [h, (hflat x hx hx').1]; simp
  · rw [hTg]
    filter_upwards [m2.coeFn_toLp, ae_restrict_mem hX.measurableSet] with x h hx hx'
    obtain ⟨e1, e2, e3⟩ := hflat x hx hx'
    rw [h]; simp [e1, e2, e3]

/-- **DLMF §1.18(ix), (1.18.71)**: if `n₁ = 1` (limit point at the left end `a`), there are no
nonzero boundary values at `a`. -/
theorem dlmf_1_18_ix_boundary_values_LP_left (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1)
    {B : (minOp X q)†.domain →ₗ[ℂ] ℂ} (hB : IsBoundaryValue X q B)
    (hBa : ∀ f, VanishesNear X q (fun d => X ∩ Iio d) f → B f = 0) : B = 0 := by
  obtain ⟨R, hR, hIccR⟩ := exists_Icc_ball hX hc
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ :=
    exists_cutoff (show c - 3 * R / 4 < c - R / 2 by linarith)
  have hIcc : Icc (c - R / 4) (c + R / 4) ⊆ X := fun x hx =>
    hIccR ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hαβ : Icc (c - R) (c - R / 4) ⊆ X := fun x hx => hIccR ⟨hx.1, by linarith [hx.2]⟩
  ext f
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc ⟨c, hc⟩ hq f
  obtain ⟨g, hg, hBg⟩ := hB.exists_cutoff_eq_zero hX hXc hq hc hz 1 (Or.inl ⟨rfl, rfl⟩) h1
    (by positivity : (0 : ℝ) < R / 4) hIcc f hχ
    (fun x => abs_le.mpr ⟨by linarith [(hχb x).1], (hχb x).2⟩) hαβ
    (hχc _ _ (by linarith) (by linarith)) fun x hx hx' => by
      have : c - R / 2 < x := by
        rcases hx' with h | h
        · have : c ≤ x := by by_contra h'; exact h ⟨hx, lt_of_not_ge h'⟩
          linarith
        · linarith [h.1]
      filter_upwards [Ioi_mem_nhds this] with y hy using hχ0 y hy.le
  have hd : c - 3 * R / 4 ∈ X := hIccR ⟨by linarith, by linarith⟩
  have hfg : B (f - g) = 0 := hBa _ ⟨_, hd, by
    show (((f : L2X X) - (g : L2X X) : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Iio _)] 0
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (Lp.coeFn_sub (f : L2X X) (g : L2X X)),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hwF,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hg,
      ae_restrict_mem (hX.inter isOpen_Iio).measurableSet] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, hχ1 x h4.2.le]; simp⟩
  rw [_root_.map_sub, hBg, sub_zero] at hfg
  simpa using hfg

/-- **DLMF §1.18(ix), (1.18.71)**: if `n₂ = 1` (limit point at the right end `b`), there are no
nonzero boundary values at `b`. -/
theorem dlmf_1_18_ix_boundary_values_LP_right (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1)
    {B : (minOp X q)†.domain →ₗ[ℂ] ℂ} (hB : IsBoundaryValue X q B)
    (hBb : ∀ f, VanishesNear X q (fun d => X ∩ Ioi d) f → B f = 0) : B = 0 := by
  obtain ⟨R, hR, hIccR⟩ := exists_Icc_ball hX hc
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ :=
    exists_cutoff (show c + R / 2 < c + 3 * R / 4 by linarith)
  set η : ℝ → ℝ := fun x => 1 - χ x
  have hIcc : Icc (c - R / 4) (c + R / 4) ⊆ X := fun x hx =>
    hIccR ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hαβ : Icc (c + R / 4) (c + R) ⊆ X := fun x hx => hIccR ⟨by linarith [hx.1], hx.2⟩
  have hηc : ∀ x ∉ Ioo (c + R / 4) (c + R), deriv η =ᶠ[𝓝 x] 0 := fun x hx => by
    filter_upwards [hχc _ _ (by linarith) (by linarith) x hx] with y hy
    simp only [η, deriv_const_sub, hy, Pi.zero_apply, neg_zero]
  ext f
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc ⟨c, hc⟩ hq f
  obtain ⟨g, hg, hBg⟩ := hB.exists_cutoff_eq_zero hX hXc hq hc hz (-1) (Or.inr ⟨rfl, rfl⟩) h1
    (by positivity : (0 : ℝ) < R / 4) hIcc f (contDiff_const.sub hχ)
    (fun x => abs_le.mpr ⟨by linarith [(hχb x).2], by linarith [(hχb x).1]⟩) hαβ hηc
    fun x hx hx' => by
      have : x < c + R / 2 := by
        rcases hx' with h | h
        · have : x ≤ c := by by_contra h'; exact h ⟨hx, lt_of_not_ge h'⟩
          linarith
        · linarith [h.2]
      filter_upwards [Iio_mem_nhds this] with y hy
      simp [hχ1 y hy.le]
  have hd : c + 3 * R / 4 ∈ X := hIccR ⟨by linarith, by linarith⟩
  have hfg : B (f - g) = 0 := hBb _ ⟨_, hd, by
    show (((f : L2X X) - (g : L2X X) : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Ioi _)] 0
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (Lp.coeFn_sub (f : L2X X) (g : L2X X)),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hwF,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hg,
      ae_restrict_mem (hX.inter isOpen_Ioi).measurableSet] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3]
    simp [hχ0 x h4.2.le]⟩
  rw [_root_.map_sub, hBg, sub_zero] at hfg
  simpa using hfg

end Azurite.DLMF
