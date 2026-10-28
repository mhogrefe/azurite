/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section6Surfaces
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# DLMF 1.6.58–1.6.60 for general regions: Gauss's theorem via the solid angle

Gauss's (divergence) theorem 1.6.58 and Green's theorem for volume 1.6.59–1.6.60 for a bounded
region `V` whose boundary is a closed piecewise smooth surface `S` (companion to
`Section6Surfaces.lean`, where the box versions are).

* **Surfaces.**  `SurfacePiece`: `Φ` of class `C²` near the closure of a parameter region `D`
  bounded by a positively oriented closed piecewise-`C¹` curve (the setting of Stokes 1.6.57).
  `ClosedSurface`: finitely many pieces whose boundary curves cancel
  (`Σⱼ ∫_{∂Sⱼ} A · ds = 0` for every `C¹` field `A`); `ClosedSurface.flux`, `image`.
* **Solid angle.**  `ClosedSurface.windingNumber y = ∬_S (x − y)/(4π |x − y|³) · dS`, the flux
  of the field `newtonKernel` of a unit point source at `y` (the solid angle of `S` seen from
  `y`, divided by `4π`).
* **Newton kernel** (`integral_newton_euclid`, `integral_newton`): `∫ ∇ψ(x − z) · K(z) dz = ψ(x)`
  for `ψ ∈ C¹_c`, by Mathlib's generalized polar coordinates (`homeomorphUnitSphereProd`,
  `Measure.toSphere`, `EuclideanSpace.volume_ball_fin_three`) and the FTC in `r`; the Newton
  field `newtonField ψ = K ⋆ ψ` is `C¹` with `∇ · (K ⋆ ψ) = ψ` (`div3_newtonField`).
* **Poincaré lemma** (`curl3_vectorPotential`): a `C¹` divergence-free field `H` equals
  `∇ × A` for `A(x) = ∫₀¹ t H(t x) × x dt` (differentiation under `∫₀¹`:
  `hasFDerivAt_intervalIntegral_param`, `contDiff_intervalIntegral_param`).
* **Gauss with the solid angle** (`ClosedSurface.flux_eq_integral`):
  `∬_S F · dS = ∭ (∇ · F)(y) W(y) dy` for `F ∈ C¹_c`.  For `F ∈ C²_c`
  (`flux_eq_integral_of_contDiff_two`): `F − K ⋆ (∇ · F)` is divergence-free, hence a curl,
  whose flux vanishes by Stokes on each piece and the cancellation of the boundary curves;
  the flux of `K ⋆ (∇ · F)` is `∫ (∇ · F) W` by Fubini (`SurfacePiece.flux_newtonField`).
  `C¹` by mollification (`mollifier`, `div3_mollify`, `norm_mollify_le`, dominated
  convergence).
* **DLMF.**  `ClosedSurface.BoundsOutward S V`: `W = 1` a.e. on `V` and `0` a.e. off `V` (the
  solid-angle form of "`S` is the complete boundary of `V`, oriented by the outward normal").
  `dlmf_1_6_58_general`, `dlmf_1_6_59_general`, `dlmf_1_6_60_general` for `F` (resp. `f`, `g`)
  of class `C¹` (resp. `C²`) on an open set containing `V̄ ∪ S` (smooth cutoff
  `exists_contDiff_eqOn_nhds_fin3`).  `Section6GaussOrientation` derives `BoundsOutward` from
  a geometric outward normal (the 3D analogue of `JordanCurve/Orientation`).
-/

namespace Azurite.DLMF

open Matrix MeasureTheory Set Metric Filter Topology
open scoped Real Convolution Pointwise

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ### The Newton kernel identity -/

/-- In `ℝ³` (Euclidean), `∫ ∇ψ(x − z) · z / (4π |z|³) dz = ψ(x)` for `ψ` of class `C¹` with compact
support: in polar coordinates `z = r ω` the integrand is `−(1/4π) d/dr ψ(x − r ω)`. -/
theorem integral_newton_euclid {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) (x : EuclideanSpace ℝ (Fin 3)) :
    ∫ z, fderiv ℝ ψ (x - z) z / (4 * π * ‖z‖ ^ 3) = ψ x := by
  set f : 𝔼 → ℝ := fun z => fderiv ℝ ψ (x - z) z / (4 * π * ‖z‖ ^ 3) with hfdef
  have hdim : Module.finrank ℝ 𝔼 = 3 := by simp
  have hψd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  set R' := max R 0 + ‖x‖ + 1 with hR'
  have hψ0 : ∀ y, max R 0 < ‖y‖ → ψ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h
      rw [mem_closedBall_zero_iff] at this
      linarith [le_max_left R 0]
  have hdψ0 : ∀ y, max R 0 < ‖y‖ → fderiv ℝ ψ y = 0 := by
    intro y hy
    have hev : ψ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with w hw
      exact hψ0 w hw
    rw [hev.fderiv_eq, fderiv_const_apply]
  -- integrability of `f`
  have hfm : AEStronglyMeasurable f volume :=
    ((hψd.comp (continuous_const.sub continuous_id)).clm_apply continuous_id).measurable.div
      (measurable_const.mul (continuous_norm.measurable.pow_const 3)) |>.aestronglyMeasurable
  obtain ⟨M, hM⟩ := (hs.fderiv (𝕜 := ℝ)).isCompact.exists_bound_of_continuousOn
    hψd.continuousOn
  set M' := max M 0
  have hfint : Integrable f := by
    have hball : IntegrableOn f (ball 0 R') := by
      refine integrableOn_ball_of_norm_le_rpow (C := M' / (4 * π)) (α := 2)
        (by rw [hdim]; norm_num) (by rw [hdim]; norm_num) ?_ hfm
      refine ae_of_all _ fun z => ?_
      by_cases hz : z = 0
      · simp [hfdef, hz]
      have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hb : ‖fderiv ℝ ψ (x - z)‖ ≤ M' := by
        by_cases hm : x - z ∈ tsupport (fderiv ℝ ψ)
        · exact (hM _ hm).trans (le_max_left _ _)
        · rw [image_eq_zero_of_notMem_tsupport hm, norm_zero]; exact le_max_right _ _
      have h1 : ‖fderiv ℝ ψ (x - z) z‖ ≤ M' * ‖z‖ := (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two, hfdef, norm_div, Real.norm_of_nonneg
        (by positivity : (0 : ℝ) ≤ 4 * π * ‖z‖ ^ 3)]
      rw [div_le_iff₀ (by positivity)]
      calc ‖fderiv ℝ ψ (x - z) z‖ ≤ M' * ‖z‖ := h1
        _ = M' / (4 * π) * (‖z‖ ^ 2)⁻¹ * (4 * π * ‖z‖ ^ 3) := by field_simp
    refine hball.integrable_of_forall_notMem_eq_zero fun z hz => ?_
    rw [mem_ball_zero_iff, not_lt] at hz
    have : max R 0 < ‖x - z‖ := by
      have := norm_sub_norm_le z x
      rw [norm_sub_rev] at this
      linarith
    simp [hfdef, hdψ0 _ this]
  -- polar coordinates
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  set h := homeomorphUnitSphereProd 𝔼
  set g : sphere (0 : 𝔼) 1 × Ioi (0 : ℝ) → ℝ := fun p => f (p.2.1 • (p.1 : 𝔼)) with hgdef
  have hfg : ∀ z : ({0}ᶜ : Set 𝔼), f z = g (h z) := by
    intro z
    have hz : (z : 𝔼) ≠ 0 := z.2
    simp only [hgdef, h, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have h0 : ∫ z, f z = ∫ p, g p ∂((volume : Measure 𝔼).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1))) := by
    have e1 : ∫ z, f z = ∫ z in ({0}ᶜ : Set 𝔼), f z := by rw [restrict_compl_singleton]
    rw [e1, ← integral_subtype_comap (measurableSet_singleton 0).compl]
    simp_rw [hfg]
    exact hmp.integral_comp h.measurableEmbedding g
  have hgint : Integrable g ((volume : Measure 𝔼).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1))) := by
    rw [← hmp.integrable_comp_emb h.measurableEmbedding]
    have : g ∘ h = f ∘ Subtype.val := funext fun z => (hfg z).symm
    rw [this]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton 0).compl).mp
      hfint.integrableOn
  rw [h0, integral_prod g hgint, hdim]
  -- the radial integral
  have hrad : ∀ ω : sphere (0 : 𝔼) 1,
      ∫ r, g (ω, r) ∂(Measure.volumeIoiPow (3 - 1)) = ψ x / (4 * π) := by
    intro ω
    have hω : ‖(ω : 𝔼)‖ = 1 := norm_eq_of_mem_sphere ω
    rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (ae_of_all _ fun r => ENNReal.ofReal_lt_top),
      integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (ENNReal.ofReal (r ^ (3 - 1))).toReal
        • f (r • (ω : 𝔼)))]
    have hpt : ∀ r ∈ Ioi (0 : ℝ), (ENNReal.ofReal (r ^ (3 - 1))).toReal • f (r • (ω : 𝔼)) =
        fderiv ℝ ψ (x - r • (ω : 𝔼)) (ω : 𝔼) / (4 * π) := by
      intro r hr
      have hr' : (0 : ℝ) < r := hr
      rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul, hfdef]
      simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hr'.le, hω, mul_one]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    set G : ℝ → ℝ := fun r => -ψ (x - r • (ω : 𝔼)) / (4 * π) with hGdef
    have hG : ∀ r, HasDerivAt G (fderiv ℝ ψ (x - r • (ω : 𝔼)) (ω : 𝔼) / (4 * π)) r := by
      intro r
      have h1 : HasDerivAt (fun r : ℝ => x - r • (ω : 𝔼)) (-(ω : 𝔼)) r := by
        simpa using ((hasDerivAt_id r).smul_const (ω : 𝔼)).const_sub x
      have h2 := ((hψ.differentiable one_ne_zero) (x - r • (ω : 𝔼))).hasFDerivAt.comp_hasDerivAt
        r h1
      have h3 := (h2.neg).div_const (4 * π)
      simp only [map_neg, neg_neg] at h3
      exact h3
    have hzero : ∀ r, max R 0 + ‖x‖ < r → G r = 0 := by
      intro r hr
      have : max R 0 < ‖x - r • (ω : 𝔼)‖ := by
        have := norm_sub_norm_le (r • (ω : 𝔼)) x
        rw [norm_sub_rev, norm_smul, hω, mul_one, Real.norm_of_nonneg (by
          linarith [le_max_right R 0, norm_nonneg x])] at this
        linarith
      simp [hGdef, hψ0 _ this]
    have hint : IntegrableOn (fun r => fderiv ℝ ψ (x - r • (ω : 𝔼)) (ω : 𝔼) / (4 * π))
        (Ioi (0 : ℝ)) := by
      have hc : Continuous fun r : ℝ => fderiv ℝ ψ (x - r • (ω : 𝔼)) (ω : 𝔼) / (4 * π) :=
        ((hψd.comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
          continuous_const).div_const _
      refine (hc.continuousOn.integrableOn_compact
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max R 0 + ‖x‖ + 1)))).of_forall_sdiff_eq_zero
        measurableSet_Ioi fun r hr => ?_
      simp only [Set.mem_sdiff, mem_Ioi, mem_Icc, not_and, not_le] at hr
      have hr2 := hr.2 hr.1.le
      have : max R 0 < ‖x - r • (ω : 𝔼)‖ := by
        have := norm_sub_norm_le (r • (ω : 𝔼)) x
        rw [norm_sub_rev, norm_smul, hω, mul_one, Real.norm_of_nonneg hr.1.le] at this
        linarith
      simp [hdψ0 _ this]
    have hlim : Tendsto G atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (max R 0 + ‖x‖)] with r hr
      exact (hzero r hr).symm
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ => hG r) hint hlim]
    simp [hGdef]
    ring
  simp_rw [hrad]
  rw [integral_const, smul_eq_mul, measureReal_def, Measure.toSphere_apply_univ, hdim,
    EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp
  field_simp

/-- The Newton kernel `K(z) = z / (4π |z|³)` (the field of a unit point source). -/
noncomputable def newtonKernel (z : Fin 3 → ℝ) : Fin 3 → ℝ := (4 * π * vnorm z ^ 3)⁻¹ • z

theorem vnorm_ofLp (w : 𝔼) : vnorm (WithLp.ofLp w) = ‖w‖ := by
  rw [dlmf_1_6_3]

/-- **Newton kernel identity**: `∫ ∇ψ(x − z) · K(z) dz = ψ(x)` for `ψ` of class `C¹` with compact
support. -/
theorem integral_newton {ψ : (Fin 3 → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ)
    (x : Fin 3 → ℝ) : ∫ z, fderiv ℝ ψ (x - z) (newtonKernel z) = ψ x := by
  set L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ) with hLdef
  have hLw : ∀ w : 𝔼, L w = WithLp.ofLp w := fun _ => rfl
  have hE := integral_newton_euclid (ψ := ψ ∘ L) (hψ.comp L.contDiff)
    (hs.comp_homeomorph L.toHomeomorph) (L.symm x)
  have hd : ∀ w, fderiv ℝ (ψ ∘ L) w = (fderiv ℝ ψ (L w)).comp (L : 𝔼 →L[ℝ] (Fin 3 → ℝ)) :=
    fun w => ((hψ.differentiable one_ne_zero (L w)).hasFDerivAt.comp w L.hasFDerivAt).fderiv
  simp only [hd, ContinuousLinearMap.comp_apply, Function.comp_apply, map_sub,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.coe_coe] at hE
  rw [← hE, ← (PiLp.volume_preserving_ofLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).symm.measurableEmbedding]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [newtonKernel, map_smul, smul_eq_mul, vnorm_ofLp, hLw]
  ring

theorem norm_le_vnorm (v : Fin 3 → ℝ) : ‖v‖ ≤ vnorm v := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  show √(v i ^ 2) ≤ √(v ⬝ᵥ v)
  refine Real.sqrt_le_sqrt ?_
  have : v i ^ 2 = v i * v i := sq _
  rw [this, dotProduct]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i)

theorem vnorm_nonneg (v : Fin 3 → ℝ) : 0 ≤ vnorm v := Real.sqrt_nonneg _

theorem norm_newtonKernel_le (z : Fin 3 → ℝ) : ‖newtonKernel z‖ ≤ (4 * π)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
  by_cases hz : z = 0
  · simp [newtonKernel, hz]
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hv : ‖z‖ ≤ vnorm z := norm_le_vnorm z
  have hv' : 0 < vnorm z := hz'.trans_le hv
  rw [newtonKernel, norm_smul, Real.norm_of_nonneg (by positivity), Real.rpow_neg hz'.le,
    Real.rpow_two]
  calc (4 * π * vnorm z ^ 3)⁻¹ * ‖z‖ ≤ (4 * π * vnorm z ^ 3)⁻¹ * vnorm z :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ = (4 * π)⁻¹ * (vnorm z ^ 2)⁻¹ := by field_simp
    _ ≤ (4 * π)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
        gcongr

theorem measurable_newtonKernel : Measurable newtonKernel := by
  unfold newtonKernel
  exact ((measurable_const.mul (continuous_vnorm.measurable.pow_const 3)).inv).smul
    measurable_id

theorem locallyIntegrable_newtonKernel : LocallyIntegrable newtonKernel := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr⟩ := hk.isBounded.subset_ball 0
  refine IntegrableOn.mono_set ?_ hr
  refine integrableOn_ball_of_norm_le_rpow (C := (4 * π)⁻¹) (α := 2)
    (by norm_num [Module.finrank_fin_fun]) (by norm_num [Module.finrank_fin_fun])
    (ae_of_all _ norm_newtonKernel_le) measurable_newtonKernel.aestronglyMeasurable

theorem locallyIntegrable_norm_newtonKernel : LocallyIntegrable fun t => ‖newtonKernel t‖ :=
  locallyIntegrableOn_univ.mp (locallyIntegrableOn_univ.mpr locallyIntegrable_newtonKernel).norm

/-- The bilinear map `(v, s) ↦ s • v` used to convolve the kernel with a scalar density. -/
noncomputable def smulFlip : (Fin 3 → ℝ) →L[ℝ] ℝ →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

/-- The Newton field `G(x) = ∫ ψ(x − t) K(t) dt` of a density `ψ`. -/
noncomputable def newtonField (ψ : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∫ t, ψ (x - t) • newtonKernel t

theorem newtonField_eq_convolution (ψ : (Fin 3 → ℝ) → ℝ) :
    newtonField ψ = newtonKernel ⋆[smulFlip, volume] ψ := by
  funext x
  rfl

theorem contDiff_newtonField {ψ : (Fin 3 → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) : ContDiff ℝ 1 (newtonField ψ) := by
  rw [newtonField_eq_convolution]
  exact hs.contDiff_convolution_right smulFlip locallyIntegrable_newtonKernel hψ

/-- **The Newton field has divergence `ψ`.** -/
theorem div3_newtonField {ψ : (Fin 3 → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) (x : Fin 3 → ℝ) : div3 (newtonField ψ) x = ψ x := by
  have hD := hs.hasFDerivAt_convolution_right smulFlip locallyIntegrable_newtonKernel hψ x
  rw [← newtonField_eq_convolution] at hD
  have hψd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hex := (hs.fderiv (𝕜 := ℝ)).convolutionExists_right (smulFlip.precompR (Fin 3 → ℝ))
    locallyIntegrable_newtonKernel hψd x
  have hint : ∀ v : Fin 3 → ℝ, Integrable fun t => fderiv ℝ ψ (x - t) v • newtonKernel t := by
    intro v
    have := (hs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right smulFlip
      locallyIntegrable_newtonKernel (hψd.clm_apply continuous_const) x
    exact this
  have hcomp : ∀ i : Fin 3, pd i (fun q => newtonField ψ q i) x =
      ∫ t, fderiv ℝ ψ (x - t) (Pi.single i 1) * newtonKernel t i := by
    intro i
    rw [pd_component_eq hD.differentiableAt i, hD.fderiv, convolution_def,
      ContinuousLinearMap.integral_apply hex]
    have e : ∀ t, (smulFlip.precompR (Fin 3 → ℝ) (newtonKernel t) (fderiv ℝ ψ (x - t)))
        (Pi.single i 1) = fderiv ℝ ψ (x - t) (Pi.single i 1) • newtonKernel t := by
      intro t
      simp [smulFlip]
    simp_rw [e]
    have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
      (hint (Pi.single i 1))
    simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2]
  rw [div3]
  simp_rw [hcomp]
  rw [← integral_finsetSum _ fun i _ => ?_]
  · rw [← integral_newton hψ hs x]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show _ = fderiv ℝ ψ (x - t) (newtonKernel t)
    conv_rhs => rw [← dlmf_1_6_13 (newtonKernel t)]
    simp only [map_sum, map_smul, smul_eq_mul, unitE]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · have := ((ContinuousLinearMap.proj (R := ℝ) i).integrable_comp (hint (Pi.single i 1)))
    refine this.congr (ae_of_all _ fun t => ?_)
    simp [mul_comm]

/-! ### Differentiation under `∫₀¹` and the Poincaré lemma -/

theorem fderiv_slice_eq {φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ)} (hφ : ContDiff ℝ 1 φ)
    (x : Fin 3 → ℝ) (t : ℝ) :
    fderiv ℝ (fun y => φ (y, t)) x =
      (fderiv ℝ φ (x, t)).comp ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod 0) :=
  ((hφ.differentiable one_ne_zero (x, t)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))).fderiv

/-- Differentiation under `∫₀¹` for a jointly `C¹` integrand. -/
theorem hasFDerivAt_intervalIntegral_param {φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ)}
    (hφ : ContDiff ℝ 1 φ) (x₀ : Fin 3 → ℝ) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, φ (x, t))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => φ (y, t)) x₀) x₀ := by
  set ι : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) × ℝ := (ContinuousLinearMap.id ℝ _).prod 0
  have hφd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hF'c : Continuous fun p : (Fin 3 → ℝ) × ℝ => (fderiv ℝ φ p).comp ι :=
    hφd.clm_comp continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod
    (isCompact_uIcc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn hF'c.continuousOn
  simp_rw [fderiv_slice_eq hφ]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (s := ball x₀ 1)
    (F := fun x t => φ (x, t)) (F' := fun x t => (fderiv ℝ φ (x, t)).comp ι)
    (bound := fun _ => C) (ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun x =>
      (hφ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hφ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx => ?_
    exact hC (x, t) ⟨ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩
  · refine ae_of_all _ fun t x _ => ?_
    exact (hφ.differentiable one_ne_zero (x, t)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))

/-- `x ↦ ∫₀¹ φ(x, t) dt` is `C¹` for a jointly `C¹` integrand. -/
theorem contDiff_intervalIntegral_param {φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ)}
    (hφ : ContDiff ℝ 1 φ) : ContDiff ℝ 1 fun x => ∫ t in (0 : ℝ)..1, φ (x, t) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_intervalIntegral_param hφ x).differentiableAt, ?_⟩
  have e : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, φ (x, t)) =
      fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => φ (y, t)) x :=
    funext fun x => (hasFDerivAt_intervalIntegral_param hφ x).fderiv
  rw [e]
  simp_rw [fderiv_slice_eq hφ]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun x t => (fderiv ℝ φ (x, t)).comp ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod 0))
    ((hφ.continuous_fderiv one_ne_zero).clm_comp continuous_const) continuous_const

theorem contDiff_cross {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {f g : α → Fin 3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun p => f p ⨯₃ g p := by
  have hf' := contDiff_pi.mp hf
  have hg' := contDiff_pi.mp hg
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i
  · simp only [cross_apply]
    exact ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1))
  · simp only [cross_apply]
    exact ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2))
  · simp only [cross_apply]
    exact ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0))

theorem continuous_cross {α : Type*} [TopologicalSpace α] {f g : α → Fin 3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun p => f p ⨯₃ g p := by
  have hf' : ∀ i, Continuous fun p => f p i := fun i => (continuous_apply i).comp hf
  have hg' : ∀ i, Continuous fun p => g p i := fun i => (continuous_apply i).comp hg
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [cross_apply]
    exact ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1))
  · simp only [cross_apply]
    exact ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2))
  · simp only [cross_apply]
    exact ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0))

theorem hasDerivAt_cross {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun r => f r ⨯₃ g r) (f' ⨯₃ g s + f s ⨯₃ g') s := by
  have hf' := hasDerivAt_pi.mp hf
  have hg' := hasDerivAt_pi.mp hg
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · convert ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1)) using 1
    · funext r
      simp [cross_apply]
    · simp [cross_apply]
      ring
  · convert ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2)) using 1
    · funext r
      simp [cross_apply]
    · simp [cross_apply]
      ring
  · convert ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0)) using 1
    · funext r
      simp [cross_apply]
    · simp [cross_apply]
      ring

theorem pd_apply_component {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (j k : Fin 3) :
    pd j (fun q => F q k) x = fderiv ℝ F x (unitE j) k := by
  show fderiv ℝ (fun q => F q k) x (unitE j) = _
  rw [((hasFDerivAt_pi'.mp hF.hasFDerivAt) k).fderiv]
  rfl

/-- The vector potential `A(x) = ∫₀¹ t H(t x) × x dt` of a field `H`. -/
noncomputable def vectorPotential (H : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  ∫ t in (0 : ℝ)..1, t • (H (t • x) ⨯₃ x)

theorem contDiff_potentialIntegrand {H : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 fun p : (Fin 3 → ℝ) × ℝ => p.2 • (H (p.2 • p.1) ⨯₃ p.1) :=
  contDiff_snd.smul (contDiff_cross (hH.comp (contDiff_snd.smul contDiff_fst)) contDiff_fst)

theorem contDiff_vectorPotential {H : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 (vectorPotential H) :=
  contDiff_intervalIntegral_param (contDiff_potentialIntegrand hH)

/-- **Poincaré lemma**: a `C¹` divergence-free field on `ℝ³` is the curl of its vector
potential, `∇ × A = H`. -/
theorem curl3_vectorPotential {H : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hH : ContDiff ℝ 1 H)
    (hdiv : ∀ x, div3 H x = 0) (x : Fin 3 → ℝ) : curl3 (vectorPotential H) x = H x := by
  have hφ := contDiff_potentialIntegrand hH
  have hHd := hH.differentiable one_ne_zero
  have hD : HasFDerivAt (vectorPotential H)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => t • (H (t • y) ⨯₃ y)) x) x :=
    hasFDerivAt_intervalIntegral_param hφ x
  set D : ℝ → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := fun t => fderiv ℝ H (t • x) with hDdef
  -- the directional derivatives of the integrand
  have hdir : ∀ t (j : Fin 3), fderiv ℝ (fun y => t • (H (t • y) ⨯₃ y)) x (Pi.single j 1) =
      t • ((t • D t (Pi.single j 1)) ⨯₃ x + H (t • x) ⨯₃ Pi.single j 1) := by
    intro t j
    have hdiff : Differentiable ℝ fun y => t • (H (t • y) ⨯₃ y) :=
      ((contDiff_const (c := t)).smul (contDiff_cross (hH.comp
        ((contDiff_const (c := t)).smul contDiff_id)) contDiff_id)).differentiable one_ne_zero
    have hline : HasDerivAt (fun s : ℝ => x + s • (Pi.single j 1 : Fin 3 → ℝ))
        (Pi.single j 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j 1 : Fin 3 → ℝ)).const_add x
    have h1 := (hdiff (x + (0 : ℝ) • (Pi.single j 1 : Fin 3 → ℝ))).hasFDerivAt.comp_hasDerivAt
      0 hline
    have hs : HasDerivAt (fun s : ℝ => t • (x + s • (Pi.single j 1 : Fin 3 → ℝ)))
        (t • (Pi.single j 1 : Fin 3 → ℝ)) 0 := hline.const_smul t
    have h2 : HasDerivAt (fun s : ℝ => H (t • (x + s • (Pi.single j 1 : Fin 3 → ℝ))))
        (fderiv ℝ H (t • (x + (0 : ℝ) • (Pi.single j 1 : Fin 3 → ℝ)))
          (t • (Pi.single j 1 : Fin 3 → ℝ))) 0 :=
      (hHd _).hasFDerivAt.comp_hasDerivAt 0 hs
    have h3 := (hasDerivAt_cross h2 hline).const_smul t
    have := h1.unique h3
    simp only [zero_smul, add_zero] at this
    rw [ContinuousLinearMap.map_smul] at this
    exact this
  -- `∂ⱼ Aₖ = ∫₀¹ (∂ⱼ φ)ₖ dt`
  have hpd : ∀ j k : Fin 3, pd j (fun q => vectorPotential H q k) x =
      ∫ t in (0 : ℝ)..1,
        (t • ((t • D t (Pi.single j 1)) ⨯₃ x + H (t • x) ⨯₃ Pi.single j 1)) k := by
    intro j k
    have hc : Continuous fun t : ℝ => fderiv ℝ (fun y => t • (H (t • y) ⨯₃ y)) x := by
      have := (hφ.continuous_fderiv one_ne_zero).clm_comp
        (continuous_const (y := (ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod 0))
      have e : (fun t : ℝ => fderiv ℝ (fun y => t • (H (t • y) ⨯₃ y)) x) =
          fun t => (fderiv ℝ (fun p : (Fin 3 → ℝ) × ℝ => p.2 • (H (p.2 • p.1) ⨯₃ p.1)) (x, t)).comp
            ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod 0) :=
        funext fun t => fderiv_slice_eq hφ x t
      rw [e]
      exact this.comp (continuous_const.prodMk continuous_id)
    have hint := hc.intervalIntegrable (μ := volume) 0 1
    rw [pd_apply_component hD.differentiableAt, hD.fderiv,
      ContinuousLinearMap.intervalIntegral_apply hint]
    have hint2 : IntervalIntegrable
        (fun t => fderiv ℝ (fun y => t • (H (t • y) ⨯₃ y)) x (unitE j)) volume 0 1 :=
      (hc.clm_apply continuous_const).intervalIntegrable _ _
    have h2 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k).intervalIntegral_comp_comm
        hint2
    simp only [ContinuousLinearMap.proj_apply] at h2
    rw [← h2]
    exact intervalIntegral.integral_congr fun t _ => by simp only [unitE, hdir]
  -- the integrand of `t² H(t x)`
  have hftc : ∀ l : Fin 3,
      ∫ t in (0 : ℝ)..1, (2 * t * H (t • x) l + t ^ 2 * D t x l) = H x l := by
    intro l
    have hderiv : ∀ t, HasDerivAt (fun t : ℝ => t ^ 2 * H (t • x) l)
        (2 * t * H (t • x) l + t ^ 2 * D t x l) t := by
      intro t
      have hs : HasDerivAt (fun t : ℝ => t • x) x t := by
        simpa using (hasDerivAt_id t).smul_const x
      have h1 := (hHd (t • x)).hasFDerivAt.comp_hasDerivAt t hs
      have h2 := (hasDerivAt_pi.mp h1) l
      convert (hasDerivAt_pow 2 t).mul h2 using 1
      · funext t
        simp
      · simp [hDdef]
    have hcont : Continuous fun t : ℝ => 2 * t * H (t • x) l + t ^ 2 * D t x l := by
      have hc1 : Continuous fun t : ℝ => H (t • x) l :=
        (continuous_apply l).comp (hH.continuous.comp (continuous_id.smul continuous_const))
      have hc2 : Continuous fun t : ℝ => D t x l :=
        (continuous_apply l).comp (((hH.continuous_fderiv one_ne_zero).comp
          (continuous_id.smul continuous_const)).clm_apply continuous_const)
      exact ((continuous_const.mul continuous_id).mul hc1).add
        ((continuous_id.pow 2).mul hc2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable _ _)]
    simp
  -- linear algebra for each `t`
  have hlin : ∀ t, D t x = x 0 • D t (Pi.single 0 1) + x 1 • D t (Pi.single 1 1) +
      x 2 • D t (Pi.single 2 1) := by
    intro t
    conv_lhs => rw [← dlmf_1_6_13 x]
    simp [Fin.sum_univ_three, map_add, map_smul, unitE]
  have htr : ∀ t, D t (Pi.single 0 1) 0 + D t (Pi.single 1 1) 1 + D t (Pi.single 2 1) 2 = 0 := by
    intro t
    have h := hdiv (t • x)
    rw [dlmf_1_6_21, pd_apply_component (hHd _), pd_apply_component (hHd _),
      pd_apply_component (hHd _)] at h
    exact h
  have hcomp : ∀ j k : Fin 3, IntervalIntegrable (fun t : ℝ =>
      (t • ((t • D t (Pi.single j 1)) ⨯₃ x + H (t • x) ⨯₃ Pi.single j 1)) k) volume 0 1 := by
    intro j k
    have hDc : Continuous fun t : ℝ => D t (Pi.single j 1) :=
      ((hH.continuous_fderiv one_ne_zero).comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const
    have hHc : Continuous fun t : ℝ => H (t • x) :=
      hH.continuous.comp (continuous_id.smul continuous_const)
    have : Continuous fun t : ℝ =>
        t • ((t • D t (Pi.single j 1)) ⨯₃ x + H (t • x) ⨯₃ Pi.single j 1) :=
      continuous_id.smul ((continuous_cross (continuous_id.smul hDc) continuous_const).add
        (continuous_cross hHc continuous_const))
    exact ((continuous_apply k).comp this).intervalIntegrable _ _
  ext l
  fin_cases l
  · show pd 1 (fun q => vectorPotential H q 2) x - pd 2 (fun q => vectorPotential H q 1) x =
      H x 0
    rw [hpd, hpd, ← intervalIntegral.integral_sub (hcomp _ _) (hcomp _ _), ← hftc 0]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hlin t]
    simp [cross_apply]
    linear_combination (-(t ^ 2 * x 0)) * htr t
  · show pd 2 (fun q => vectorPotential H q 0) x - pd 0 (fun q => vectorPotential H q 2) x =
      H x 1
    rw [hpd, hpd, ← intervalIntegral.integral_sub (hcomp _ _) (hcomp _ _), ← hftc 1]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hlin t]
    simp [cross_apply]
    linear_combination (-(t ^ 2 * x 1)) * htr t
  · show pd 0 (fun q => vectorPotential H q 1) x - pd 1 (fun q => vectorPotential H q 0) x =
      H x 2
    rw [hpd, hpd, ← intervalIntegral.integral_sub (hcomp _ _) (hcomp _ _), ← hftc 2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hlin t]
    simp [cross_apply]
    linear_combination (-(t ^ 2 * x 2)) * htr t

/-! ### Closed piecewise smooth surfaces and the solid-angle winding number -/

theorem continuousOn_cross {α : Type*} [TopologicalSpace α] {f g : α → Fin 3 → ℝ} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun p => f p ⨯₃ g p) s := by
  have hf' : ∀ i, ContinuousOn (fun p => f p i) s := fun i =>
    (continuous_apply i).comp_continuousOn hf
  have hg' : ∀ i, ContinuousOn (fun p => g p i) s := fun i =>
    (continuous_apply i).comp_continuousOn hg
  refine continuousOn_pi.mpr fun i => ?_
  fin_cases i
  · simp only [cross_apply]
    exact ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1))
  · simp only [cross_apply]
    exact ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2))
  · simp only [cross_apply]
    exact ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0))

theorem continuousOn_dotProduct {α : Type*} [TopologicalSpace α] {f g : α → Fin 3 → ℝ}
    {s : Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun p => f p ⬝ᵥ g p) s := by
  have hf' : ∀ i, ContinuousOn (fun p => f p i) s := fun i =>
    (continuous_apply i).comp_continuousOn hf
  have hg' : ∀ i, ContinuousOn (fun p => g p i) s := fun i =>
    (continuous_apply i).comp_continuousOn hg
  simp only [dotProduct, Fin.sum_univ_three]
  exact (((hf' 0).mul (hg' 0)).add ((hf' 1).mul (hg' 1))).add ((hf' 2).mul (hg' 2))

theorem abs_dotProduct_le (w v : Fin 3 → ℝ) : |w ⬝ᵥ v| ≤ 3 * (‖w‖ * ‖v‖) := by
  simp only [dotProduct, Fin.sum_univ_three]
  have h : ∀ i, |w i * v i| ≤ ‖w‖ * ‖v‖ := fun i => by
    rw [abs_mul]
    exact mul_le_mul (norm_le_pi_norm w i) (norm_le_pi_norm v i) (abs_nonneg _) (norm_nonneg _)
  calc |w 0 * v 0 + w 1 * v 1 + w 2 * v 2| ≤ |w 0 * v 0| + |w 1 * v 1| + |w 2 * v 2| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _ ≤ _ := by linarith [h 0, h 1, h 2]

/-- `w ↦ w · v` as a continuous linear functional. -/
noncomputable def dotCLM (v : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => w ⬝ᵥ v
      map_add' := fun a b => add_dotProduct a b v
      map_smul' := fun c a => by simp [smul_dotProduct] }

@[simp] theorem dotCLM_apply (v w : Fin 3 → ℝ) : dotCLM v w = w ⬝ᵥ v := rfl

/-- A piece of a surface: `Φ` of class `C²` near the closure of the parameter region `D` bounded
by a positively oriented closed piecewise-`C¹` curve `γ`. -/
structure SurfacePiece where
  γ : ℝ → ℝ × ℝ
  a : ℝ
  b : ℝ
  P : JordanCurve.ClosedPiecewiseC1 (toComplexPath γ) a b
  hpos : P.IsPositivelyOriented
  Φ : ℝ × ℝ → Fin 3 → ℝ
  U : Set (ℝ × ℝ)
  hU : IsOpen U
  hSU : planeInterior γ a b ∪ γ '' Icc a b ⊆ U
  hΦ : ContDiffOn ℝ 2 Φ U

namespace SurfacePiece

variable (S : SurfacePiece)

/-- The parameter region. -/
def D : Set (ℝ × ℝ) := planeInterior S.γ S.a S.b

/-- The normal `T_u × T_v`. -/
noncomputable def normal (p : ℝ × ℝ) : Fin 3 → ℝ := tangentU S.Φ p ⨯₃ tangentV S.Φ p

/-- The flux `∬ F · dS` through the piece. -/
noncomputable def flux (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : ℝ := fluxIntegral F S.Φ S.D

/-- The line integral `∫ A · ds` along the boundary curve `Φ ∘ γ`. -/
noncomputable def boundaryIntegral (A : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : ℝ :=
  lineIntegral A (fun t => S.Φ (S.γ t)) S.a S.b

theorem flux_curl {A : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hA : ContDiff ℝ 1 A) :
    S.flux (curl3 A) = S.boundaryIntegral A :=
  dlmf_1_6_57 S.P S.hpos S.hU S.hSU S.hΦ hA

theorem measurableSet_D : MeasurableSet S.D := (isOpen_planeInterior S.P).measurableSet

theorem isCompact_closure_D : IsCompact (closure S.D) :=
  (isCompact_closure_planeInterior_union S.P).1.of_isClosed_subset isClosed_closure
    subset_union_left

theorem closure_D_subset_U : closure S.D ⊆ S.U := fun _ hp =>
  S.hSU ((isCompact_closure_planeInterior_union S.P).2 hp)

theorem continuousOn_normal : ContinuousOn S.normal S.U := by
  have hT : ContDiffOn ℝ 1 (fun p => fderiv ℝ S.Φ p) S.U :=
    S.hΦ.fderiv_of_isOpen S.hU (by norm_num)
  exact continuousOn_cross (hT.clm_apply contDiffOn_const).continuousOn
    (hT.clm_apply contDiffOn_const).continuousOn

theorem continuousOn_flux_integrand {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : Continuous F) :
    ContinuousOn (fun p => F (S.Φ p) ⬝ᵥ S.normal p) (closure S.D) :=
  (continuousOn_dotProduct (hF.comp_continuousOn S.hΦ.continuousOn) S.continuousOn_normal).mono
    S.closure_D_subset_U

theorem integrableOn_flux {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : Continuous F) :
    IntegrableOn (fun p => F (S.Φ p) ⬝ᵥ S.normal p) S.D :=
  ((S.continuousOn_flux_integrand hF).integrableOn_compact S.isCompact_closure_D).mono_set
    subset_closure

theorem flux_sub {F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : Continuous F) (hG : Continuous G) :
    S.flux (fun x => F x - G x) = S.flux F - S.flux G := by
  have e := integral_sub (S.integrableOn_flux hF) (S.integrableOn_flux hG)
  simp only [normal] at e
  unfold flux fluxIntegral
  rw [← e]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [sub_dotProduct]

theorem volume_D_lt_top : volume S.D < ⊤ :=
  (measure_mono subset_closure).trans_lt S.isCompact_closure_D.measure_lt_top

/-- Fubini for the Newton field: the flux of the Newton field of `ψ` is
`∫ ψ(y) · (flux of K(· − y)) dy`. -/
theorem flux_newtonField {ψ : (Fin 3 → ℝ) → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun y => ψ y * S.flux (fun x => newtonKernel (x - y))) ∧
      S.flux (newtonField ψ) = ∫ y, ψ y * S.flux (fun x => newtonKernel (x - y)) := by
  set N := S.normal with hN
  -- the convolution of `|ψ|` with `‖K‖` is continuous
  set ρ : (Fin 3 → ℝ) → ℝ :=
    (fun t => ‖newtonKernel t‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => |ψ y|) with hρ
  have hρc : Continuous ρ :=
    (hs.comp_left abs_zero).continuous_convolution_right _ locallyIntegrable_norm_newtonKernel
      hψ.abs
  have hρint : ∀ x, Integrable fun y => |ψ y| * ‖newtonKernel (x - y)‖ := by
    intro x
    have h := ((hs.comp_left abs_zero).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      locallyIntegrable_norm_newtonKernel hψ.abs) x
    have h2 := h.comp_sub_left x
    refine h2.congr (ae_of_all _ fun y => ?_)
    simp [mul_comm]
  have hρeq : ∀ x, ∫ y, |ψ y| * ‖newtonKernel (x - y)‖ = ρ x := by
    intro x
    rw [hρ, convolution_def, ← integral_sub_left_eq_self _ volume x]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [mul_comm]
  have hconv : ∀ x, Integrable fun y => ψ y • newtonKernel (x - y) := by
    intro x
    have h := (hs.convolutionExists_right smulFlip locallyIntegrable_newtonKernel hψ) x
    have h2 := h.comp_sub_left x
    refine h2.congr (ae_of_all _ fun y => ?_)
    simp [smulFlip]
  have hG : ∀ x, newtonField ψ x = ∫ y, ψ y • newtonKernel (x - y) := by
    intro x
    rw [newtonField, ← integral_sub_left_eq_self _ volume x]
    simp
  -- the kernel on `D × ℝ³`
  set κ : (ℝ × ℝ) × (Fin 3 → ℝ) → ℝ :=
    fun q => ψ q.2 * (newtonKernel (S.Φ q.1 - q.2) ⬝ᵥ N q.1) with hκ
  obtain ⟨L, hL⟩ := S.isCompact_closure_D.exists_bound_of_continuousOn
    (S.continuousOn_normal.mono S.closure_D_subset_U)
  obtain ⟨Mρ, hMρ⟩ := S.isCompact_closure_D.exists_bound_of_continuousOn
    (hρc.comp_continuousOn (S.hΦ.continuousOn.mono S.closure_D_subset_U))
  have hmeas : AEStronglyMeasurable κ ((volume.restrict S.D).prod volume) := by
    have hΦm : AEMeasurable S.Φ (volume.restrict S.D) :=
      (S.hΦ.continuousOn.mono (subset_closure.trans S.closure_D_subset_U)).aemeasurable
        S.measurableSet_D
    have hNm : AEMeasurable N (volume.restrict S.D) :=
      (S.continuousOn_normal.mono (subset_closure.trans S.closure_D_subset_U)).aemeasurable
        S.measurableSet_D
    have h1 : AEMeasurable (fun q : (ℝ × ℝ) × (Fin 3 → ℝ) => S.Φ q.1)
        ((volume.restrict S.D).prod volume) := hΦm.comp_fst
    have h2 : AEMeasurable (fun q : (ℝ × ℝ) × (Fin 3 → ℝ) => N q.1)
        ((volume.restrict S.D).prod volume) := hNm.comp_fst
    refine AEMeasurable.aestronglyMeasurable ?_
    have hdot : Measurable fun w : (Fin 3 → ℝ) × (Fin 3 → ℝ) => w.1 ⬝ᵥ w.2 :=
      (continuous_fst.dotProduct continuous_snd).measurable
    exact (hψ.measurable.comp measurable_snd).aemeasurable.mul
      (hdot.comp_aemeasurable
        ((measurable_newtonKernel.comp_aemeasurable (h1.sub measurable_snd.aemeasurable)).prodMk
          h2))
  have hκint : Integrable κ ((volume.restrict S.D).prod volume) := by
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · refine ae_of_all _ fun p => ?_
      have := (dotCLM (N p)).integrable_comp (hconv (S.Φ p))
      refine this.congr (ae_of_all _ fun y => ?_)
      simp [hκ]
    · have : IsFiniteMeasure (volume.restrict S.D) := ⟨by
        rw [Measure.restrict_apply_univ]; exact S.volume_D_lt_top⟩
      refine Integrable.of_bound hmeas.norm.integral_prod_right' (3 * max L 0 * max Mρ 0) ?_
      · filter_upwards [ae_restrict_mem S.measurableSet_D] with p hp
        have hLp : ‖N p‖ ≤ max L 0 := (hL p (subset_closure hp)).trans (le_max_left _ _)
        have hMp : ρ (S.Φ p) ≤ max Mρ 0 :=
          (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
            ((hMρ p (subset_closure hp)).trans (le_max_left _ _)))
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        calc ∫ y, ‖κ (p, y)‖ ≤ ∫ y, 3 * ‖N p‖ * (|ψ y| * ‖newtonKernel (S.Φ p - y)‖) := by
              refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
                ((hρint (S.Φ p)).const_mul _) (ae_of_all _ fun y => ?_)
              simp only [hκ, Real.norm_eq_abs, abs_mul]
              have := abs_dotProduct_le (newtonKernel (S.Φ p - y)) (N p)
              nlinarith [abs_nonneg (ψ y), norm_nonneg (newtonKernel (S.Φ p - y)),
                norm_nonneg (N p)]
          _ = 3 * ‖N p‖ * ρ (S.Φ p) := by rw [integral_const_mul, hρeq]
          _ ≤ 3 * max L 0 * max Mρ 0 := by
              have h0 : 0 ≤ ρ (S.Φ p) := by
                rw [← hρeq]; exact integral_nonneg fun _ => by positivity
              exact mul_le_mul (mul_le_mul_of_nonneg_left hLp (by norm_num)) hMp h0
                (by positivity)
  refine ⟨?_, ?_⟩
  · refine hκint.integral_prod_right.congr (ae_of_all _ fun y => ?_)
    simp only [hκ, flux, fluxIntegral]
    rw [integral_const_mul]
    rfl
  · unfold flux fluxIntegral
    calc ∫ p in S.D, newtonField ψ (S.Φ p) ⬝ᵥ (tangentU S.Φ p ⨯₃ tangentV S.Φ p)
        = ∫ p in S.D, ∫ y, κ (p, y) := by
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          show newtonField ψ (S.Φ p) ⬝ᵥ _ = ∫ y, κ (p, y)
          rw [hG, ← dotCLM_apply, ← (dotCLM _).integral_comp_comm (hconv _)]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp [hκ, hN, normal]
      _ = ∫ y, ∫ p in S.D, κ (p, y) := integral_integral_swap hκint
      _ = _ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [hκ]
          rw [integral_const_mul]
          rfl

end SurfacePiece

/-- A closed piecewise smooth surface: finitely many pieces whose boundary curves cancel,
`Σⱼ ∫_{∂Sⱼ} A · ds = 0` for every `C¹` field `A` (each edge is traversed once in each
direction). -/
structure ClosedSurface where
  m : ℕ
  piece : Fin m → SurfacePiece
  closed : ∀ A : (Fin 3 → ℝ) → (Fin 3 → ℝ), ContDiff ℝ 1 A →
    ∑ j, (piece j).boundaryIntegral A = 0

namespace ClosedSurface

variable (S : ClosedSurface)

/-- The flux `∬_S F · dS = Σⱼ ∬_{Sⱼ} F · dS`. -/
noncomputable def flux (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : ℝ := ∑ j, (S.piece j).flux F

/-- The solid-angle winding number `W(y) = ∬_S (x − y)/(4π |x − y|³) · dS`: the flux of the
field of a unit point source at `y`, i.e. the (signed) solid angle of `S` seen from `y`
divided by `4π`. -/
noncomputable def windingNumber (y : Fin 3 → ℝ) : ℝ := S.flux fun x => newtonKernel (x - y)

/-- The flux of a curl through a closed surface vanishes (Stokes on each piece). -/
theorem flux_curl {A : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hA : ContDiff ℝ 1 A) :
    S.flux (curl3 A) = 0 := by
  unfold flux
  simp_rw [(S.piece _).flux_curl hA]
  exact S.closed A hA

end ClosedSurface

theorem div3_eq_sum (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    div3 F = fun x => pd 0 (fun q => F q 0) x + pd 1 (fun q => F q 1) x +
      pd 2 (fun q => F q 2) x :=
  funext fun x => dlmf_1_6_21 F x

theorem contDiff_div3 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (div3 F) := by
  have hc := contDiff_pi.mp hF
  rw [div3_eq_sum]
  exact ((contDiff_pd (hc 0) 0).add (contDiff_pd (hc 1) 1)).add (contDiff_pd (hc 2) 2)

theorem hasCompactSupport_div3 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hs : HasCompactSupport F) :
    HasCompactSupport (div3 F) := by
  have hcomp : ∀ i : Fin 3, HasCompactSupport fun q => F q i := fun i =>
    hs.comp_left (g := fun w : Fin 3 → ℝ => w i) rfl
  rw [div3_eq_sum]
  exact (((hcomp 0).fderiv_apply (𝕜 := ℝ) (unitE 0)).add
    ((hcomp 1).fderiv_apply (𝕜 := ℝ) (unitE 1))).add ((hcomp 2).fderiv_apply (𝕜 := ℝ) (unitE 2))

theorem div3_sub {F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    div3 (fun q => F q - G q) x = div3 F x - div3 G x := by
  have hF' := differentiableAt_pi.mp hF
  have hG' := differentiableAt_pi.mp hG
  simp only [div3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pd_sub (hF' i) (hG' i) i

namespace ClosedSurface

variable (S : ClosedSurface)

/-- **Gauss's theorem with the solid-angle winding number**: for a closed piecewise smooth
surface `S` and a compactly supported `C²` field `F`, `∬_S F · dS = ∭ (∇ · F)(y) W(y) dy`.
Proof: `G` = Newton field of `∇ · F` has the same divergence, so `F − G = ∇ × A` (Poincaré)
has zero flux (Stokes on each piece, boundaries cancel); the flux of `G` is
`∫ (∇ · F) W` by Fubini. -/
theorem flux_eq_integral_of_contDiff_two {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 2 F)
    (hs : HasCompactSupport F) :
    S.flux F = ∫ y, div3 F y * S.windingNumber y := by
  set ψ := div3 F with hψdef
  have hψ : ContDiff ℝ 1 ψ := contDiff_div3 hF
  have hψs : HasCompactSupport ψ := hasCompactSupport_div3 hs
  set G := newtonField ψ with hGdef
  have hG : ContDiff ℝ 1 G := contDiff_newtonField hψ hψs
  have hF1 : ContDiff ℝ 1 F := hF.of_le one_le_two
  set H : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x => F x - G x with hHdef
  have hH : ContDiff ℝ 1 H := hF1.sub hG
  have hdivH : ∀ x, div3 H x = 0 := by
    intro x
    rw [hHdef, div3_sub ((hF1.differentiable one_ne_zero) x) ((hG.differentiable one_ne_zero) x),
      hGdef, div3_newtonField hψ hψs, sub_self]
  have hcurl : curl3 (vectorPotential H) = H := funext (curl3_vectorPotential hH hdivH)
  have h1 : S.flux F = S.flux G + S.flux H := by
    unfold flux
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(S.piece j).flux_sub hF1.continuous hG.continuous]
    ring
  have h2 : S.flux H = 0 := by
    rw [← hcurl]
    exact S.flux_curl (contDiff_vectorPotential hH)
  have h3 : S.flux G = ∫ y, ψ y * S.windingNumber y := by
    unfold flux windingNumber flux
    rw [Finset.sum_congr rfl fun j _ => ((S.piece j).flux_newtonField hψ.continuous hψs).2,
      ← integral_finsetSum _ fun j _ => ((S.piece j).flux_newtonField hψ.continuous hψs).1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    rw [Finset.mul_sum]
  rw [h1, h2, add_zero, h3]

end ClosedSurface

/-! ### From `C²` to `C¹`: mollification -/

/-- Mollifiers: normed smooth bumps supported in the ball of radius `1/(n+1)`. -/
noncomputable def mollifier (n : ℕ) : ContDiffBump (0 : Fin 3 → ℝ) :=
  ⟨1 / (2 * (n + 1)), 1 / (n + 1), by positivity, by
    have : (0 : ℝ) < n + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]
    linarith⟩

theorem tendsto_mollifier_rOut : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem mollifier_rOut_le (n : ℕ) : (mollifier n).rOut ≤ 1 := by
  show 1 / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- `‖(φ ⋆ g)(x)‖ ≤ C` for a normed bump `φ` and `‖g‖ ≤ C`. -/
theorem norm_mollify_le {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    (φ : ContDiffBump (0 : Fin 3 → ℝ)) {g : (Fin 3 → ℝ) → E'} {C : ℝ} (hg : ∀ y, ‖g y‖ ≤ C)
    (x : Fin 3 → ℝ) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ C := by
  rw [convolution_def]
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume t) (g (x - t))‖
      ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume t) (g (x - t))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, φ.normed volume t * C := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          (φ.integrable_normed.mul_const C) (ae_of_all _ fun t => ?_)
        simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg
          (φ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hg _) (φ.nonneg_normed t)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The divergence of a mollified `C¹` field is the mollified divergence. -/
theorem div3_mollify (φ : ContDiffBump (0 : Fin 3 → ℝ)) {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) (x : Fin 3 → ℝ) :
    div3 (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] div3 F) x := by
  have hφl : LocallyIntegrable (φ.normed volume) volume := φ.integrable_normed.locallyIntegrable
  have hD := hs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφl hF x
  have hFd : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hex := (hs.fderiv (𝕜 := ℝ)).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin 3 → ℝ)) hφl hFd x
  have hint : ∀ v : Fin 3 → ℝ,
      Integrable fun t => φ.normed volume t • fderiv ℝ F (x - t) v := by
    intro v
    have := (hs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hφl (hFd.clm_apply continuous_const) x
    exact this
  have hcomp : ∀ i : Fin 3, pd i (fun q => (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] F) q i) x = ∫ t, φ.normed volume t * pd i (fun q => F q i) (x - t) := by
    intro i
    rw [pd_apply_component hD.differentiableAt, hD.fderiv, convolution_def,
      ContinuousLinearMap.integral_apply hex]
    have e : ∀ t, ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin 3 → ℝ) (φ.normed volume t)
        (fderiv ℝ F (x - t))) (unitE i) = φ.normed volume t • fderiv ℝ F (x - t) (unitE i) := by
      intro t
      simp
    simp_rw [e]
    have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
      (hint (unitE i))
    simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show _ = φ.normed volume t * pd i (fun q => F q i) (x - t)
    rw [pd_apply_component ((hF.differentiable one_ne_zero) _)]
  have hint2 : ∀ i : Fin 3,
      Integrable fun t => φ.normed volume t * pd i (fun q => F q i) (x - t) := by
    intro i
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integrable_comp
      (hint (unitE i))
    refine this.congr (ae_of_all _ fun t => ?_)
    simp [pd_apply_component ((hF.differentiable one_ne_zero) _)]
  rw [div3, convolution_def]
  simp_rw [hcomp]
  rw [← integral_finsetSum _ fun i _ => hint2 i]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp [div3]

namespace ClosedSurface

variable (S : ClosedSurface)

/-- `ψ W` is integrable for continuous compactly supported `ψ`. -/
theorem integrable_mul_windingNumber {ψ : (Fin 3 → ℝ) → ℝ} (hψ : Continuous ψ)
    (hs : HasCompactSupport ψ) : Integrable fun y => ψ y * S.windingNumber y := by
  have := integrable_finsetSum Finset.univ fun j _ => ((S.piece j).flux_newtonField hψ hs).1
  refine this.congr (ae_of_all _ fun y => ?_)
  simp [windingNumber, flux, Finset.mul_sum]

theorem tendsto_flux_piece (j : Fin S.m) {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {Fn : ℕ → (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hFn : ∀ n, Continuous (Fn n)) {C : ℝ}
    (hC : ∀ n y, ‖Fn n y‖ ≤ C) (hlim : ∀ y, Tendsto (fun n => Fn n y) atTop (𝓝 (F y))) :
    Tendsto (fun n => (S.piece j).flux (Fn n)) atTop (𝓝 ((S.piece j).flux F)) := by
  set P := S.piece j
  obtain ⟨L, hL⟩ := P.isCompact_closure_D.exists_bound_of_continuousOn
    (P.continuousOn_normal.mono P.closure_D_subset_U)
  have : IsFiniteMeasure (volume.restrict P.D) := ⟨by
    rw [Measure.restrict_apply_univ]; exact P.volume_D_lt_top⟩
  unfold SurfacePiece.flux fluxIntegral
  refine tendsto_integral_of_dominated_convergence (fun _ => 3 * (C * max L 0)) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact ((P.continuousOn_flux_integrand (hFn n)).mono subset_closure).aestronglyMeasurable
      P.measurableSet_D
  · filter_upwards [ae_restrict_mem P.measurableSet_D] with p hp
    rw [Real.norm_eq_abs]
    refine (abs_dotProduct_le _ _).trans ?_
    have hN : ‖tangentU P.Φ p ⨯₃ tangentV P.Φ p‖ ≤ max L 0 :=
      (hL p (subset_closure hp)).trans (le_max_left _ _)
    gcongr
    · exact (norm_nonneg _).trans (hC 0 0)
    · exact hC n _
  · refine ae_of_all _ fun p => ?_
    exact ((continuous_id.dotProduct continuous_const).tendsto _).comp (hlim (P.Φ p))

/-- **Gauss's theorem with the solid-angle winding number** for a compactly supported `C¹`
field: `∬_S F · dS = ∭ (∇ · F)(y) W(y) dy` (from the `C²` case by mollification). -/
theorem flux_eq_integral {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport F) :
    S.flux F = ∫ y, div3 F y * S.windingNumber y := by
  set Fn : ℕ → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun n =>
    (mollifier n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F with hFndef
  have hFn2 : ∀ n, ContDiff ℝ 2 (Fn n) := fun n =>
    (mollifier n).hasCompactSupport_normed.contDiff_convolution_left _
      (mollifier n).contDiff_normed hF.continuous.locallyIntegrable
  have hFns : ∀ n, HasCompactSupport (Fn n) := fun n =>
    (mollifier n).hasCompactSupport_normed.convolution _ hs
  have heq : ∀ n, S.flux (Fn n) = ∫ y, div3 (Fn n) y * S.windingNumber y := fun n =>
    S.flux_eq_integral_of_contDiff_two (hFn2 n) (hFns n)
  set ψ := div3 F with hψdef
  have hψc : Continuous ψ := continuous_div3 hF
  have hψs : HasCompactSupport ψ := by
    have hcomp : ∀ i : Fin 3, HasCompactSupport fun q => F q i := fun i =>
      hs.comp_left (g := fun w : Fin 3 → ℝ => w i) rfl
    rw [hψdef, div3_eq_sum]
    exact (((hcomp 0).fderiv_apply (𝕜 := ℝ) (unitE 0)).add
      ((hcomp 1).fderiv_apply (𝕜 := ℝ) (unitE 1))).add
      ((hcomp 2).fderiv_apply (𝕜 := ℝ) (unitE 2))
  have hdivn : ∀ n y, div3 (Fn n) y =
      ((mollifier n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y :=
    fun n y => div3_mollify _ hF hs y
  obtain ⟨MF, hMF⟩ := hF.continuous.bounded_above_of_compact_support hs
  obtain ⟨Mψ, hMψ⟩ := hψc.bounded_above_of_compact_support hψs
  -- the left-hand sides converge
  have hL : Tendsto (fun n => S.flux (Fn n)) atTop (𝓝 (S.flux F)) := by
    unfold flux
    refine tendsto_finsetSum _ fun j _ => S.tendsto_flux_piece j
      (fun n => (hFn2 n).continuous) (fun n y => norm_mollify_le _ hMF y) fun y => ?_
    exact ContDiffBump.convolution_tendsto_right_of_continuous tendsto_mollifier_rOut
      hF.continuous y
  -- a bump equal to `1` on a neighbourhood of all the supports
  obtain ⟨R, hR⟩ := (hψs.isCompact.add (isCompact_closedBall (0 : Fin 3 → ℝ) 1)).isBounded
    |>.subset_closedBall 0
  set R' := max R 0 + 1 with hR'
  let β : ContDiffBump (0 : Fin 3 → ℝ) := ⟨R', R' + 1, by positivity, by linarith⟩
  have hβ1 : ∀ y ∈ tsupport ψ + closedBall (0 : Fin 3 → ℝ) 1, β y = 1 := fun y hy =>
    β.one_of_mem_closedBall (by
      have := hR hy
      rw [mem_closedBall] at this ⊢
      show dist y 0 ≤ R'
      linarith [le_max_left R 0])
  have hint₀ : Integrable fun y => β y * S.windingNumber y :=
    S.integrable_mul_windingNumber β.continuous β.hasCompactSupport
  have hsupp : ∀ n y, y ∉ tsupport ψ + closedBall (0 : Fin 3 → ℝ) 1 → div3 (Fn n) y = 0 := by
    intro n y hy
    rw [hdivn]
    by_contra hne
    have hmem := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hne
    rw [(mollifier n).support_normed_eq] at hmem
    obtain ⟨a, ha, c, hc, rfl⟩ := hmem
    refine hy ⟨c, subset_tsupport _ hc, a, ?_, add_comm _ _⟩
    exact ball_subset_closedBall (ball_subset_ball (mollifier_rOut_le n) ha)
  have hψ0 : ∀ y, y ∉ tsupport ψ + closedBall (0 : Fin 3 → ℝ) 1 → ψ y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨y, h, 0, mem_closedBall_self zero_le_one,
      add_zero y⟩
  have hrw : ∀ g : (Fin 3 → ℝ) → ℝ, (∀ y, y ∉ tsupport ψ + closedBall (0 : Fin 3 → ℝ) 1 →
      g y = 0) → ∀ y, g y * S.windingNumber y = g y * (β y * S.windingNumber y) := by
    intro g hg y
    by_cases hy : y ∈ tsupport ψ + closedBall (0 : Fin 3 → ℝ) 1
    · rw [hβ1 y hy, one_mul]
    · rw [hg y hy, zero_mul, zero_mul]
  -- the right-hand sides converge
  have hR2 : Tendsto (fun n => ∫ y, div3 (Fn n) y * S.windingNumber y) atTop
      (𝓝 (∫ y, ψ y * S.windingNumber y)) := by
    simp_rw [hrw _ (hsupp _), hrw _ hψ0]
    refine tendsto_integral_of_dominated_convergence (fun y => Mψ * ‖β y * S.windingNumber y‖)
      (fun n => ?_) (hint₀.norm.const_mul _) (fun n => ae_of_all _ fun y => ?_)
      (ae_of_all _ fun y => ?_)
    · exact (continuous_div3 ((hFn2 n).of_le one_le_two)).aestronglyMeasurable.mul
        hint₀.aestronglyMeasurable
    · rw [norm_mul]
      gcongr
      rw [hdivn]
      exact norm_mollify_le _ hMψ y
    · refine Tendsto.mul_const _ ?_
      simp_rw [hdivn]
      exact ContDiffBump.convolution_tendsto_right_of_continuous tendsto_mollifier_rOut hψc y
  exact tendsto_nhds_unique hL (by simpa only [heq] using hR2)

end ClosedSurface

/-! ### Gauss's theorem and Green's theorem for volume, general regions -/

/-- A function of class `Cⁿ` on an open `U ⊇ K` (`K` compact) agrees on a neighbourhood of `K`
with a compactly supported `Cⁿ` function (multiply by a smooth cutoff). -/
theorem exists_contDiff_eqOn_nhds_fin3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {F : (Fin 3 → ℝ) → E} {U K : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hF : ContDiffOn ℝ n F U) :
    ∃ F' : (Fin 3 → ℝ) → E, ContDiff ℝ n F' ∧ HasCompactSupport F' ∧
      ∃ V : Set (Fin 3 → ℝ), IsOpen V ∧ K ⊆ V ∧ EqOn F' F V := by
  obtain ⟨V₂, hV₂o, hKV₂, hV₂U, hV₂c⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₁, hV₁o, hKV₁, hV₁V₂, -⟩ := exists_open_between_and_isCompact_closure hK hV₂o hKV₂
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := n) hV₂o isClosed_closure hV₁V₂
  have hχt : tsupport χ = closure V₂ := by rw [tsupport, hχs]
  refine ⟨fun x => χ x • F x, ?_, ?_, V₁, hV₁o, hKV₁, fun q hq => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ U
    · exact hχ.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hq))
    · have hqs : q ∉ tsupport χ := by
        rw [hχt]
        exact fun h => hq (hV₂U h)
      have h0 : χ =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.mp hqs
      refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with r hr
      simp [hr]
  · refine HasCompactSupport.smul_right ?_
    rw [HasCompactSupport, hχt]
    exact hV₂c
  · have : χ q = 1 := (hχ1 q).mp (subset_closure hq)
    simp [this]

namespace ClosedSurface

variable (S : ClosedSurface)

/-- The image `S = ⋃ⱼ Φⱼ(D̄ⱼ)` of the surface. -/
def image : Set (Fin 3 → ℝ) := ⋃ j, (S.piece j).Φ '' closure (S.piece j).D

theorem isCompact_image : IsCompact S.image :=
  isCompact_iUnion fun j => (S.piece j).isCompact_closure_D.image_of_continuousOn
    ((S.piece j).hΦ.continuousOn.mono (S.piece j).closure_D_subset_U)

/-- The flux only depends on the field on the surface. -/
theorem flux_congr {F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (h : EqOn F G S.image) :
    S.flux F = S.flux G := by
  unfold flux
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold SurfacePiece.flux fluxIntegral
  refine setIntegral_congr_fun (S.piece j).measurableSet_D fun p hp => ?_
  rw [h (mem_iUnion.mpr ⟨j, p, subset_closure hp, rfl⟩)]

end ClosedSurface

theorem div3_congr {F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {y : Fin 3 → ℝ} (h : F =ᶠ[𝓝 y] G) :
    div3 F y = div3 G y := by
  unfold div3
  refine Finset.sum_congr rfl fun i _ => ?_
  show fderiv ℝ (fun q => F q i) y (unitE i) = fderiv ℝ (fun q => G q i) y (unitE i)
  have hk : (fun q => F q i) =ᶠ[𝓝 y] fun q => G q i := h.mono fun q hq => by simp only [hq]
  rw [hk.fderiv_eq]

/-- The solid-angle form of "`S` is the boundary of `V`, oriented by the outward normal":
the solid angle `W_S` subtended by `S` is `1` at almost every point of `V` and `0` at almost
every point outside `V`. -/
def ClosedSurface.BoundsOutward (S : ClosedSurface) (V : Set (Fin 3 → ℝ)) : Prop :=
  ∀ᵐ y, S.windingNumber y = V.indicator 1 y

/-- **DLMF 1.6.58** (Gauss's or the divergence theorem): for a closed piecewise smooth surface
`S` forming the boundary of a bounded measurable set `V`, oriented outwards
(`S.BoundsOutward V`), and `F` continuously differentiable on an open set `U` containing
`V̄ ∪ S`: `∭_V ∇ · F dV = ∬_S F · dS`. -/
theorem dlmf_1_6_58_general (S : ClosedSurface) {V : Set (Fin 3 → ℝ)}
    (hVb : Bornology.IsBounded V) (hVm : MeasurableSet V) (hW : S.BoundsOutward V)
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hKU : closure V ∪ S.image ⊆ U)
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiffOn ℝ 1 F U) :
    ∫ y in V, div3 F y = S.flux F := by
  have hK : IsCompact (closure V ∪ S.image) :=
    (hVb.isCompact_closure).union S.isCompact_image
  obtain ⟨F', hF', hF's, V', hV'o, hKV', hFF'⟩ :=
    exists_contDiff_eqOn_nhds_fin3 (n := 1) hU hK hKU hF
  have hflux : S.flux F = S.flux F' :=
    S.flux_congr fun x hx => (hFF' (hKV' (Or.inr hx))).symm
  have hdiv : ∀ y ∈ V, div3 F y = div3 F' y := fun y hy =>
    div3_congr (Filter.eventuallyEq_of_mem (hV'o.mem_nhds (hKV' (Or.inl (subset_closure hy))))
      fun q hq => (hFF' hq).symm)
  rw [hflux, S.flux_eq_integral hF' hF's, setIntegral_congr_fun hVm hdiv,
    ← integral_indicator hVm]
  refine integral_congr_ae (hW.mono fun y hy => ?_)
  show _ = div3 F' y * S.windingNumber y
  rw [hy]
  by_cases hyV : y ∈ V
  · simp [hyV]
  · simp [hyV]

/-- **DLMF 1.6.59** (Green's theorem for volume): for `f`, `g` twice continuously
differentiable near `V̄ ∪ S`, `∭_V (f ∇²g + ∇f · ∇g) dV = ∬_S f ∂g/∂n dA`, where
`∂g/∂n dA = ∇g · dS`. -/
theorem dlmf_1_6_59_general (S : ClosedSurface) {V : Set (Fin 3 → ℝ)}
    (hVb : Bornology.IsBounded V) (hVm : MeasurableSet V) (hW : S.BoundsOutward V)
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hKU : closure V ∪ S.image ⊆ U)
    {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) :
    ∫ y in V, (f y * lap3 g y + grad3 f y ⬝ᵥ grad3 g y) =
      S.flux fun x => f x • grad3 g x := by
  have hG : ContDiffOn ℝ 1 (grad3 g) U := by
    refine contDiffOn_pi.mpr fun i => ?_
    exact (hg.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hFU : ContDiffOn ℝ 1 (fun x => f x • grad3 g x) U :=
    (hf.of_le one_le_two).smul hG
  rw [← dlmf_1_6_58_general S hVb hVm hW hU hKU hFU]
  refine setIntegral_congr_fun hVm fun y hy => ?_
  have hyU : y ∈ U := hKU (Or.inl (subset_closure hy))
  have hfd : DifferentiableAt ℝ f y :=
    (hf.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
  have hGd : DifferentiableAt ℝ (grad3 g) y :=
    (hG.contDiffAt (hU.mem_nhds hyU)).differentiableAt one_ne_zero
  rw [dlmf_1_6_25 hfd hGd, dotProduct_comm]
  rfl

/-- **DLMF 1.6.60** (Green's theorem for volume):
`∭_V (f ∇²g − g ∇²f) dV = ∬_S (f ∂g/∂n − g ∂f/∂n) dA`. -/
theorem dlmf_1_6_60_general (S : ClosedSurface) {V : Set (Fin 3 → ℝ)}
    (hVb : Bornology.IsBounded V) (hVm : MeasurableSet V) (hW : S.BoundsOutward V)
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hKU : closure V ∪ S.image ⊆ U)
    {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) :
    ∫ y in V, (f y * lap3 g y - g y * lap3 f y) =
      S.flux fun x => f x • grad3 g x - g x • grad3 f x := by
  have hGg : ContDiffOn ℝ 1 (grad3 g) U :=
    contDiffOn_pi.mpr fun i => (hg.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hGf : ContDiffOn ℝ 1 (grad3 f) U :=
    contDiffOn_pi.mpr fun i => (hf.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hFU : ContDiffOn ℝ 1 (fun x => f x • grad3 g x - g x • grad3 f x) U :=
    ((hf.of_le one_le_two).smul hGg).sub ((hg.of_le one_le_two).smul hGf)
  rw [← dlmf_1_6_58_general S hVb hVm hW hU hKU hFU]
  refine setIntegral_congr_fun hVm fun y hy => ?_
  have hyU : y ∈ U := hKU (Or.inl (subset_closure hy))
  have hn := hU.mem_nhds hyU
  have hfd : DifferentiableAt ℝ f y := (hf.contDiffAt hn).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g y := (hg.contDiffAt hn).differentiableAt (by norm_num)
  have hGgd : DifferentiableAt ℝ (grad3 g) y := (hGg.contDiffAt hn).differentiableAt one_ne_zero
  have hGfd : DifferentiableAt ℝ (grad3 f) y := (hGf.contDiffAt hn).differentiableAt one_ne_zero
  rw [div3_sub (F := fun x => f x • grad3 g x) (G := fun x => g x • grad3 f x)
    (hfd.smul hGgd) (hgd.smul hGfd), dlmf_1_6_25 hfd hGgd, dlmf_1_6_25 hgd hGfd]
  simp only [lap3]
  rw [dotProduct_comm (grad3 g y) (grad3 f y)]
  ring

end Azurite.DLMF
