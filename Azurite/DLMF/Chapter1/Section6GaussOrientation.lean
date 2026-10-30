/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section6GaussExamples

/-!
# Orientation for Gauss's theorem

DLMF §1.6(v) states Gauss's theorem (1.6.58–1.6.60) for a volume `V` whose complete boundary is
the closed surface `S`, "oriented by its normal being outwards".
`Section6Gauss` proves it under the analytic hypothesis `ClosedSurface.BoundsOutward S V`:
the solid angle `W` of `S` equals `1_V` almost everywhere.
This file derives that hypothesis from the geometric reading of the DLMF sentence.

* **Coordinates.**  `e3 : ℝ³ ≃L ℝ × ℝ × ℝ` preserves Lebesgue measure and the sup norm
  (`measurePreserving_e3`, `norm_e3`).
  A linear map with columns `a`, `b`, `c` has determinant `a · (b × c)` (`det_eq_triple`).
* **The crossing map** `Ψ(τ, p) = Φ(p) − y₀ − τ v` has Jacobian `−v · (T_u × T_v)`
  (`det_crossDeriv`).
  The flux of the segment test field through a piece is an integral of `ρ ∘ Ψ` against
  `v · N` over `(0, 1] × D` (`SurfacePiece.flux_segField_eq`, Fubini).
* **The jump.**  Suppose the segment from `y₀` to `y₀ + v` meets the surface only at
  `Φ_j(p₀) = y₀ + τ₀ v`, with `p₀` inside the parameter region, `0 < τ₀ < 1` and `v · N < 0`.
  Near `(τ₀, p₀)` the crossing map is a diffeomorphism (inverse function theorem).
  Change of variables then gives flux `−1` for every small bump
  (`exists_flux_segField_eq_neg_one`).
  Hence `W(y₀ + v) = W(y₀) + 1` (`windingNumber_add_eq_add_one`).
* **The surface is null** (`volume_image`): each piece is a differentiable image of a planar set.
* **The orientation theorem** (`boundsOutward_of_crossing`).  Assume:
  - `V` is bounded and its frontier is the surface;
  - the interior and the exterior of `V` are connected;
  - one exterior-to-interior segment crosses the surface once, against the normal.

  Then `W` is `0` on the exterior, by constancy and decay, and `1` on the interior, by the jump.
  So `S.BoundsOutward V` holds.
* **DLMF-facing form.**  `ClosedSurface.OutwardBoundary S V` bundles these hypotheses.
  `dlmf_1_6_58_outward`, `dlmf_1_6_59_outward` and `dlmf_1_6_60_outward` state Gauss's theorem
  and Green's identities for it.

Connectedness of the interior and exterior is a hypothesis here.  `Section6GaussSeparation.lean`
derives it from the Jordan–Brouwer separation theorem when the surface is connected and locally a
graph (`ClosedSurface.outwardBoundary_of_isLocallyGraph`).
-/

namespace Azurite.DLMF

open Matrix MeasureTheory Set Metric Filter Topology
open scoped Real

/-- The coordinates `x ↦ (x₀, x₁, x₂)` of `ℝ³`. -/
noncomputable def e3 : (Fin 3 → ℝ) ≃L[ℝ] ℝ × ℝ × ℝ := finThreeEquivProd.toContinuousLinearEquiv

theorem e3_apply (x : Fin 3 → ℝ) : e3 x = (x 0, x 1, x 2) := rfl

theorem norm_e3 (x : Fin 3 → ℝ) : ‖e3 x‖ = ‖x‖ := by
  rw [e3_apply]
  refine le_antisymm ?_ ?_
  · simp only [Prod.norm_def]
    exact max_le (norm_le_pi_norm x 0) (max_le (norm_le_pi_norm x 1) (norm_le_pi_norm x 2))
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    simp only [Prod.norm_def]
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

theorem measurePreserving_e3 : MeasurePreserving e3 volume volume := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  have h := h2.comp h1
  have e : (e3 : (Fin 3 → ℝ) → ℝ × ℝ × ℝ) =
      Prod.map id MeasurableEquiv.finTwoArrow ∘ MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 :=
    funext fun x => rfl
  rw [e]
  exact h

/-- The determinant of a linear map of `ℝ³` with columns `e3 a`, `e3 b`, `e3 c` is the triple
product `a · (b × c)`. -/
theorem det_eq_triple (L : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ) {a b c : Fin 3 → ℝ}
    (ha : L (1, 0, 0) = e3 a) (hb : L (0, 1, 0) = e3 b) (hc : L (0, 0, 1) = e3 c) :
    L.det = a ⬝ᵥ (b ⨯₃ c) := by
  rw [ContinuousLinearMap.det_prod_three, ha, hb, hc, Matrix.det_fin_three]
  simp only [e3_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  simp only [dotProduct, Fin.sum_univ_three, cross_apply]
  simp
  ring

/-! ### The crossing map -/

/-- `Ψ(τ, p) = Φ(p) − y₀ − τ v`: from the point `y₀ + τ v` of the segment to the surface point
`Φ(p)`. -/
def crossMap (Φ : ℝ × ℝ → Fin 3 → ℝ) (y₀ v : Fin 3 → ℝ) (q : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  Φ q.2 - y₀ - q.1 • v

/-- The derivative of `e3 ∘ Ψ` at `q`. -/
noncomputable def crossDeriv (Φ : ℝ × ℝ → Fin 3 → ℝ) (v : Fin 3 → ℝ) (q : ℝ × ℝ × ℝ) :
    ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
  (e3 : (Fin 3 → ℝ) →L[ℝ] ℝ × ℝ × ℝ).comp
    ((fderiv ℝ Φ q.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight v)

theorem hasFDerivAt_crossMap {Φ : ℝ × ℝ → Fin 3 → ℝ} {y₀ v : Fin 3 → ℝ} {q : ℝ × ℝ × ℝ}
    (hΦ : DifferentiableAt ℝ Φ q.2) :
    HasFDerivAt (fun q => e3 (crossMap Φ y₀ v q)) (crossDeriv Φ v q) q := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => Φ q.2)
      ((fderiv ℝ Φ q.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) q :=
    hΦ.hasFDerivAt.comp q hasFDerivAt_snd
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).smul_const v
  exact e3.hasFDerivAt.comp q ((h1.sub_const y₀).sub h2)

/-- The Jacobian of the crossing map is `−v · (T_u × T_v)`. -/
theorem det_crossDeriv (Φ : ℝ × ℝ → Fin 3 → ℝ) (v : Fin 3 → ℝ) (q : ℝ × ℝ × ℝ) :
    (crossDeriv Φ v q).det = -(v ⬝ᵥ (tangentU Φ q.2 ⨯₃ tangentV Φ q.2)) := by
  rw [det_eq_triple _ (a := -v) (b := tangentU Φ q.2) (c := tangentV Φ q.2), neg_dotProduct]
  all_goals simp [crossDeriv, tangentU, tangentV, Prod.mk_zero_zero]

theorem continuous_crossMap_snd {Φ : ℝ × ℝ → Fin 3 → ℝ} {U : Set (ℝ × ℝ)}
    (hΦ : ContinuousOn Φ U) (y₀ v : Fin 3 → ℝ) :
    ContinuousOn (crossMap Φ y₀ v) {q | q.2 ∈ U} :=
  ((hΦ.comp continuous_snd.continuousOn fun _ hq => hq).sub continuousOn_const).sub
    (continuous_fst.smul continuous_const).continuousOn

/-- A continuous map without zeros on a compact set is bounded away from zero. -/
theorem exists_pos_le_norm_of_isCompact {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → Fin 3 → ℝ} (hf : ContinuousOn f K) (h0 : ∀ q ∈ K, f q ≠ 0) :
    ∃ δ > 0, ∀ q ∈ K, δ ≤ ‖f q‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨m, hm, hmin⟩ := hK.exists_isMinOn hne hf.norm
  exact ⟨‖f m‖, norm_pos_iff.mpr (h0 m hm), fun q hq => hmin hq⟩

/-- The flux of the segment test field through a piece, as an integral over
`(0, 1] × D` (Fubini). -/
theorem SurfacePiece.flux_segField_eq (P : SurfacePiece) {ρ : (Fin 3 → ℝ) → ℝ}
    (hρ : Continuous ρ) (y₀ v : Fin 3 → ℝ) :
    P.flux (segField ρ y₀ v) =
      ∫ q in Ioc (0 : ℝ) 1 ×ˢ P.D, ρ (crossMap P.Φ y₀ v q) * (v ⬝ᵥ P.normal q.2) := by
  set g : ℝ × ℝ × ℝ → ℝ := fun q => ρ (crossMap P.Φ y₀ v q) * (v ⬝ᵥ P.normal q.2)
  have hpt : ∀ p, segField ρ y₀ v (P.Φ p) ⬝ᵥ P.normal p = ∫ τ in Ioc (0 : ℝ) 1, g (τ, p) := by
    intro p
    simp only [segField, g, crossMap]
    rw [intervalIntegral.integral_smul_const, smul_dotProduct,
      intervalIntegral.integral_of_le zero_le_one, integral_mul_const, smul_eq_mul]
  have hcont : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => g (z.2, z.1)) (closure P.D ×ˢ Icc 0 1) := by
    have hmaps : MapsTo (fun z : (ℝ × ℝ) × ℝ => (z.2, z.1)) (closure P.D ×ˢ Icc 0 1)
        {q : ℝ × ℝ × ℝ | q.2 ∈ P.U} := fun z hz => P.closure_D_subset_U hz.1
    refine ContinuousOn.mul (hρ.comp_continuousOn
      ((continuous_crossMap_snd P.hΦ.continuousOn y₀ v).comp (by fun_prop) hmaps)) ?_
    exact continuousOn_dotProduct continuousOn_const
      (P.continuousOn_normal.comp continuous_fst.continuousOn fun z hz =>
        P.closure_D_subset_U hz.1)
  have hint : IntegrableOn (fun z : (ℝ × ℝ) × ℝ => g (z.2, z.1)) (P.D ×ˢ Ioc 0 1)
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    (hcont.integrableOn_compact (P.isCompact_closure_D.prod isCompact_Icc)).mono_set
      (prod_mono subset_closure Ioc_subset_Icc_self)
  show ∫ p in P.D, segField ρ y₀ v (P.Φ p) ⬝ᵥ P.normal p = _
  simp_rw [hpt]
  rw [← setIntegral_prod _ hint, Measure.volume_eq_prod,
    ← setIntegral_prod_swap P.D (Ioc (0 : ℝ) 1) fun z : (ℝ × ℝ) × ℝ => g (z.2, z.1)]
  rfl

/-! ### The jump of the solid angle across the surface -/

instance instIsAddHaarMeasureVolumeR3 : (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := by
  rw [← measurePreserving_e3.map_eq]
  exact e3.isAddHaarMeasure_map volume

namespace ClosedSurface

variable (S : ClosedSurface)

/-- **The crossing computation.**  If the segment from `y₀` to `y₀ + v` meets the surface exactly
once, at an interior parameter point and against the normal, then the segment test field of
every small enough bump has flux `−1`: near the crossing, `(τ, p) ↦ Φ(p) − y₀ − τ v` is a
diffeomorphism with Jacobian `−v · N > 0`, and the flux is minus the integral of the bump. -/
theorem exists_flux_segField_eq_neg_one {j : Fin S.m} {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ (S.piece j).D)
    {y₀ v : Fin 3 → ℝ} {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo (0 : ℝ) 1)
    (hx₀ : (S.piece j).Φ p₀ = y₀ + τ₀ • v)
    (hcross : ∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
      (S.piece k).Φ p = y₀ + τ • v → k = j ∧ p = p₀)
    (horient : v ⬝ᵥ (S.piece j).normal p₀ < 0) :
    ∃ δ > 0, ∀ φ : ContDiffBump (0 : Fin 3 → ℝ), φ.rOut ≤ δ →
      S.flux (segField (φ.normed volume) y₀ v) = -1 := by
  set P := S.piece j with hP
  have hv : v ≠ 0 := by rintro rfl; simp at horient
  have hp₀U : p₀ ∈ P.U := P.hSU (Or.inl hp₀)
  set q₀ : ℝ × ℝ × ℝ := (τ₀, p₀) with hq₀
  set Ψ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun q => e3 (crossMap P.Φ y₀ v q) with hΨ
  have hΦa : ContDiffAt ℝ 2 P.Φ p₀ := P.hΦ.contDiffAt (P.hU.mem_nhds hp₀U)
  have hΨc : ContDiffAt ℝ 2 Ψ q₀ :=
    e3.contDiff.contDiffAt.comp q₀ (((hΦa.comp q₀ contDiffAt_snd).sub contDiffAt_const).sub
      (contDiffAt_fst.smul contDiffAt_const))
  have hdet0 : (crossDeriv P.Φ v q₀).det ≠ 0 := by
    rw [det_crossDeriv]; exact (neg_pos.mpr horient).ne'
  have hL : HasFDerivAt Ψ ((crossDeriv P.Φ v q₀).toContinuousLinearEquivOfDetNeZero hdet0 :
      ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ) q₀ := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hasFDerivAt_crossMap (hΦa.differentiableAt (by norm_num))
  set H := hΨc.toOpenPartialHomeomorph Ψ hL (by norm_num) with hH
  -- a neighbourhood of the crossing on which `Ψ` is injective and `v · N < 0`
  set N : Set (ℝ × ℝ) := P.U ∩ (fun p => v ⬝ᵥ P.normal p) ⁻¹' Iio 0
  have hN : IsOpen N := (continuousOn_dotProduct continuousOn_const
    P.continuousOn_normal).isOpen_inter_preimage P.hU isOpen_Iio
  set U₀ := H.source ∩ Ioo (0 : ℝ) 1 ×ˢ (P.D ∩ N) with hU₀
  have hU₀o : IsOpen U₀ :=
    H.open_source.inter (isOpen_Ioo.prod ((isOpen_planeInterior P.P).inter hN))
  have hq₀U₀ : q₀ ∈ U₀ :=
    ⟨hΨc.mem_toOpenPartialHomeomorph_source hL _, hτ₀, hp₀, hp₀U, horient⟩
  have hU₀K : U₀ ⊆ Ioc (0 : ℝ) 1 ×ˢ P.D := fun q hq =>
    ⟨Ioo_subset_Ioc_self hq.2.1, hq.2.2.1⟩
  -- the image of `U₀` contains a ball around `0`
  have hΨq₀ : Ψ q₀ = 0 := by simp [hΨ, crossMap, hq₀, hx₀]
  have himg : IsOpen (Ψ '' U₀) :=
    (H.isOpen_image_iff_of_subset_source inter_subset_left).mpr hU₀o
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp himg 0 ⟨q₀, hq₀U₀, hΨq₀⟩
  -- away from the crossing, the segment is far from the surface
  set K : Fin S.m → Set (ℝ × ℝ × ℝ) := fun k =>
    (Icc (0 : ℝ) 1 ×ˢ closure (S.piece k).D) \ {q | k = j ∧ q ∈ U₀}
  have hK : ∀ k, ∃ δ > 0, ∀ q ∈ K k, δ ≤ ‖crossMap (S.piece k).Φ y₀ v q‖ := by
    intro k
    refine exists_pos_le_norm_of_isCompact ?_ ?_ ?_
    · refine (isCompact_Icc.prod (S.piece k).isCompact_closure_D).diff ?_
      by_cases hk : k = j
      · simpa [hk] using hU₀o
      · simp [hk]
    · exact (continuous_crossMap_snd (S.piece k).hΦ.continuousOn y₀ v).mono fun q hq =>
        (S.piece k).closure_D_subset_U hq.1.2
    · rintro q ⟨⟨hq1, hq2⟩, hqU⟩ h0
      have hq : (S.piece k).Φ q.2 = y₀ + q.1 • v := by
        rw [← sub_eq_zero, ← sub_sub]; exact h0
      obtain ⟨hk, hq2'⟩ := hcross k q.2 hq2 q.1 hq1 hq
      have e : P.Φ q.2 = y₀ + q.1 • v := by rw [hP, ← hk]; exact hq
      rw [hq2', hx₀] at e
      have hτ : τ₀ = q.1 := smul_left_injective ℝ hv (add_left_cancel e)
      have hqq : q = q₀ := Prod.ext hτ.symm hq2'
      exact hqU ⟨hk, hqq ▸ hq₀U₀⟩
  choose δk hδk hδkK using hK
  have : Nonempty (Fin S.m) := ⟨j⟩
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min δk
  refine ⟨min δ₁ (δk k₀), lt_min hδ₁ (hδk k₀), fun φ hφ => ?_⟩
  have hr₁ : φ.rOut ≤ δ₁ := hφ.trans (min_le_left _ _)
  have hr₂ : ∀ k, φ.rOut ≤ δk k := fun k => (hφ.trans (min_le_right _ _)).trans (hk₀ k)
  set ρ := φ.normed volume
  have hρ : Continuous ρ := φ.continuous_normed
  have hzero : ∀ k, ∀ q ∈ K k, ρ (crossMap (S.piece k).Φ y₀ v q) = 0 := fun k q hq =>
    normed_eq_zero φ ((hr₂ k).trans (hδkK k q hq))
  have hother : ∀ k ≠ j, (S.piece k).flux (segField ρ y₀ v) = 0 := by
    intro k hk
    rw [(S.piece k).flux_segField_eq hρ]
    refine setIntegral_eq_zero_of_forall_eq_zero fun q hq => ?_
    rw [hzero k q ⟨⟨Ioc_subset_Icc_self hq.1, subset_closure hq.2⟩, fun h => hk h.1⟩, zero_mul]
  have hmain : P.flux (segField ρ y₀ v) = -1 := by
    have hcongr : ∀ q ∈ U₀, ρ (crossMap P.Φ y₀ v q) * (v ⬝ᵥ P.normal q.2) =
        -(|(crossDeriv P.Φ v q).det| • ρ (e3.symm (Ψ q))) := by
      intro q hq
      have hneg : v ⬝ᵥ P.normal q.2 < 0 := hq.2.2.2.2
      rw [det_crossDeriv, abs_of_pos (neg_pos.mpr
        (show v ⬝ᵥ (tangentU P.Φ q.2 ⨯₃ tangentV P.Φ q.2) < 0 from hneg))]
      simp only [hΨ, ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, SurfacePiece.normal]
      ring
    have hderiv : ∀ q ∈ U₀, HasFDerivWithinAt Ψ (crossDeriv P.Φ v q) U₀ q := fun q hq =>
      (hasFDerivAt_crossMap ((P.hΦ.contDiffAt (P.hU.mem_nhds hq.2.2.2.1)).differentiableAt
        (by norm_num))).hasFDerivWithinAt
    have hinj : InjOn Ψ U₀ := H.injOn.mono inter_subset_left
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hU₀o.measurableSet
      hderiv hinj (fun w => ρ (e3.symm w))
    rw [P.flux_segField_eq hρ, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioc.prod P.measurableSet_D) hU₀K fun q hq => by
        rw [hzero j q ⟨⟨Ioc_subset_Icc_self hq.1.1, subset_closure hq.1.2⟩, fun h => hq.2 h.2⟩,
          zero_mul],
      setIntegral_congr_fun hU₀o.measurableSet hcongr, integral_neg,
      ← hcov,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_]
    · have h : ∫ w, ρ (e3.symm w) = ∫ x, ρ x := by
        rw [← measurePreserving_e3.integral_comp e3.toHomeomorph.measurableEmbedding]
        simp
      rw [h, φ.integral_normed]
    · show ρ (e3.symm w) = 0
      refine normed_eq_zero φ (hr₁.trans ?_)
      rw [← norm_e3, ContinuousLinearEquiv.apply_symm_apply]
      by_contra hlt
      exact hw (hball (mem_ball_zero_iff.mpr (not_le.mp hlt)))
  unfold ClosedSurface.flux
  rw [Finset.sum_eq_single j (fun k _ hk => hother k hk) (by simp)]
  exact hmain

/-- **The solid angle jumps by one across the surface**, against the normal. -/
theorem windingNumber_add_eq_add_one {j : Fin S.m} {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ (S.piece j).D)
    {y₀ v : Fin 3 → ℝ} {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo (0 : ℝ) 1)
    (hx₀ : (S.piece j).Φ p₀ = y₀ + τ₀ • v)
    (hcross : ∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
      (S.piece k).Φ p = y₀ + τ • v → k = j ∧ p = p₀)
    (horient : v ⬝ᵥ (S.piece j).normal p₀ < 0) :
    S.windingNumber (y₀ + v) = S.windingNumber y₀ + 1 := by
  obtain ⟨δ, hδ, hflux⟩ := S.exists_flux_segField_eq_neg_one hp₀ hτ₀ hx₀ hcross horient
  have hv : v ≠ 0 := by rintro rfl; simp at horient
  have hend : ∀ τ ∈ Icc (0 : ℝ) 1, τ ≠ τ₀ → y₀ + τ • v ∉ S.image := by
    intro τ hτ hne h
    obtain ⟨k, p, hp, hpe⟩ := mem_iUnion.mp h
    obtain ⟨hk, rfl⟩ := hcross k p hp τ hτ hpe
    have e : (S.piece j).Φ p = y₀ + τ • v := hk ▸ hpe
    rw [hx₀] at e
    exact hne (smul_left_injective ℝ hv (add_left_cancel e)).symm
  have hy₀ : y₀ ∉ S.image := by
    simpa using hend 0 ⟨le_rfl, zero_le_one⟩ hτ₀.1.ne
  have hy₁ : y₀ + v ∉ S.image := by
    simpa using hend 1 ⟨zero_le_one, le_rfl⟩ hτ₀.2.ne'
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨η₀, hη₀, h₀⟩ := Metric.continuousAt_iff.mp (S.continuousAt_windingNumber hy₀) (ε / 2)
    (half_pos hε)
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.continuousAt_iff.mp (S.continuousAt_windingNumber hy₁) (ε / 2)
    (half_pos hε)
  set r := min (min η₀ η₁) δ / 2 with hr
  have hr0 : 0 < r := by positivity
  let φ : ContDiffBump (0 : Fin 3 → ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hrη₀ : r < η₀ := by
    have := min_le_left (min η₀ η₁) δ; have := min_le_left η₀ η₁
    simp only [hr]; linarith
  have hrη₁ : r < η₁ := by
    have := min_le_left (min η₀ η₁) δ; have := min_le_right η₀ η₁
    simp only [hr]; linarith
  have hrδ : r ≤ δ := by
    have := min_le_right (min η₀ η₁) δ
    simp only [hr]; linarith
  have hf := S.flux_segField φ y₀ v
  rw [hflux φ hrδ] at hf
  have e₀ := S.abs_integral_bump_sub_le φ (half_pos hε).le fun x hx =>
    (h₀ (hx.trans hrη₀)).le
  have e₁ := S.abs_integral_bump_sub_le φ (half_pos hε).le fun x hx =>
    (h₁ (hx.trans hrη₁)).le
  rw [Real.dist_eq]
  rw [abs_le] at e₀ e₁ ⊢
  constructor <;> linarith [e₀.1, e₀.2, e₁.1, e₁.2]

/-- The surface is a Lebesgue null set: each piece is the image of a planar set under a
differentiable map. -/
theorem volume_image : volume S.image = 0 := by
  refine measure_iUnion_null fun k => ?_
  set P := S.piece k
  set T : Set (Fin 3 → ℝ) := {x | (x 0, x 1) ∈ closure P.D ∧ x 2 = 0}
  have hGT : (fun x : Fin 3 → ℝ => P.Φ (x 0, x 1)) '' T = P.Φ '' closure P.D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, hx.1, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨![p.1, p.2, 0], ⟨by simpa using hp, by simp⟩, by simp⟩
  rw [← hGT]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
  · have hlin : Differentiable ℝ fun x : Fin 3 → ℝ => (x 0, x 1) :=
      (differentiable_apply 0).prodMk (differentiable_apply 1)
    exact (P.hΦ.differentiableOn (by norm_num)).comp hlin.differentiableOn
      fun x hx => P.closure_D_subset_U hx.1
  · set W := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)
    have hW : W ≠ ⊤ := by
      intro h
      have : (Pi.single 2 1 : Fin 3 → ℝ) ∈ W := by rw [h]; exact Submodule.mem_top
      simp [W] at this
    exact measure_mono_null (fun x hx => by simpa [W] using hx.2)
      (Measure.addHaar_submodule volume W hW)

/-- **The orientation theorem.**  Let `V` be a bounded set whose frontier is the surface, with
connected interior and connected exterior.  If some segment from an exterior point to an
interior point crosses the surface exactly once, at an interior parameter point of a piece and
against that piece's normal, then the surface bounds `V` with the outward normal:
`W = 1_V` almost everywhere. -/
theorem boundsOutward_of_crossing {V : Set (Fin 3 → ℝ)} (hVb : Bornology.IsBounded V)
    (hfr : frontier V = S.image) (hint : IsPreconnected (interior V))
    (hext : IsPreconnected (closure V)ᶜ) {yo yi : Fin 3 → ℝ} (hout : yo ∉ closure V)
    (hin : yi ∈ interior V) {j : Fin S.m} {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ (S.piece j).D) {τ₀ : ℝ}
    (hτ₀ : τ₀ ∈ Icc (0 : ℝ) 1) (hx₀ : (S.piece j).Φ p₀ = yo + τ₀ • (yi - yo))
    (hcross : ∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
      (S.piece k).Φ p = yo + τ • (yi - yo) → k = j ∧ p = p₀)
    (horient : (yi - yo) ⬝ᵥ (S.piece j).normal p₀ < 0) :
    S.BoundsOutward V := by
  have hx₀S : (S.piece j).Φ p₀ ∈ S.image := mem_iUnion.mpr ⟨j, p₀, subset_closure hp₀, rfl⟩
  have hfr' : S.image ⊆ closure V := by rw [← hfr]; exact frontier_subset_closure
  have hfrint : ∀ w ∈ S.image, w ∉ interior V := fun w hw => by
    rw [← hfr] at hw; exact hw.2
  have hτ₀' : τ₀ ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hτ₀.1 ?_, lt_of_le_of_ne hτ₀.2 ?_⟩
    · rintro rfl
      rw [zero_smul, add_zero] at hx₀
      rw [hx₀] at hx₀S
      exact hout (hfr' hx₀S)
    · rintro rfl
      rw [one_smul, add_sub_cancel] at hx₀
      rw [hx₀] at hx₀S
      exact hfrint _ hx₀S hin
  have hstep := S.windingNumber_add_eq_add_one hp₀ hτ₀' hx₀ hcross horient
  rw [add_sub_cancel] at hstep
  -- `W` vanishes on the exterior: it is constant there and decays at infinity
  have hWext : ∀ y ∉ closure V, S.windingNumber y = 0 := by
    intro y hy
    obtain ⟨C, hC⟩ := S.exists_abs_windingNumber_le
    obtain ⟨M, hM⟩ := hVb.closure.subset_closedBall 0
    set M' := max M 0
    have hM' : 0 ≤ M' := le_max_right _ _
    have hxM : ∀ x ∈ closure V, ‖x‖ ≤ M' := fun x hx =>
      (mem_closedBall_zero_iff.mp (hM hx)).trans (le_max_left _ _)
    have hbound : ∀ R : ℝ, 0 < R → |S.windingNumber y| ≤ C * R ^ (-2 : ℝ) := by
      intro R hR
      set z : Fin 3 → ℝ := fun _ => M' + R
      have hz : ‖z‖ = M' + R := by
        rw [show ‖z‖ = ‖M' + R‖ from pi_norm_const (M' + R), Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      have hzV : z ∉ closure V := fun h => by have := hxM z h; linarith
      rw [S.windingNumber_eq_of_isPreconnected hext (fun w hw h => hw (hfr' h)) hy hzV]
      refine hC z R hR fun x hx => ?_
      have := hxM x (hfr' hx)
      rw [dist_eq_norm']
      linarith [norm_sub_norm_le z x]
    have hlim : Tendsto (fun R : ℝ => C * R ^ (-2 : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul C
    exact abs_nonpos_iff.mp (ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hbound))
  -- `W` is `1` on the interior: it is constant there and equals `W(yo) + 1`
  have hWint : ∀ y ∈ interior V, S.windingNumber y = 1 := by
    intro y hy
    rw [S.windingNumber_eq_of_isPreconnected hint (fun w hw h => hfrint w h hw) hy hin, hstep,
      hWext yo hout, zero_add]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp S.volume_image] with y hy
  by_cases h1 : y ∈ interior V
  · rw [hWint y h1, indicator_of_mem (interior_subset h1), Pi.one_apply]
  · have h2 : y ∉ closure V := fun h2 => hy (by rw [← hfr]; exact ⟨h2, h1⟩)
    rw [hWext y h2, indicator_of_notMem (fun h => h2 (subset_closure h))]

/-- **`S` is the outward boundary of `V`** (DLMF §1.6(v): "`S` forms the complete boundary of
`V`, oriented by its normal being outwards").  `V` is bounded, its frontier is the surface, its
interior and exterior are connected, and some segment from an exterior point to an interior
point crosses the surface exactly once, at an interior parameter point of a piece and against
that piece's normal. -/
structure OutwardBoundary (V : Set (Fin 3 → ℝ)) : Prop where
  isBounded : Bornology.IsBounded V
  frontier_eq : frontier V = S.image
  isPreconnected_interior : IsPreconnected (interior V)
  isPreconnected_exterior : IsPreconnected (closure V)ᶜ
  crossing : ∃ yo yi : Fin 3 → ℝ, ∃ j : Fin S.m, ∃ p₀ ∈ (S.piece j).D, ∃ τ₀ ∈ Icc (0 : ℝ) 1,
    yo ∉ closure V ∧ yi ∈ interior V ∧ (S.piece j).Φ p₀ = yo + τ₀ • (yi - yo) ∧
    (∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
      (S.piece k).Φ p = yo + τ • (yi - yo) → k = j ∧ p = p₀) ∧
    (yi - yo) ⬝ᵥ (S.piece j).normal p₀ < 0

theorem OutwardBoundary.boundsOutward {S : ClosedSurface} {V : Set (Fin 3 → ℝ)}
    (h : S.OutwardBoundary V) : S.BoundsOutward V := by
  obtain ⟨yo, yi, j, p₀, hp₀, τ₀, hτ₀, hout, hin, hx₀, hcross, horient⟩ := h.crossing
  exact S.boundsOutward_of_crossing h.isBounded h.frontier_eq h.isPreconnected_interior
    h.isPreconnected_exterior hout hin hp₀ hτ₀ hx₀ hcross horient

end ClosedSurface

/-! ### DLMF 1.6.58–1.6.60 for outward boundaries -/

/-- **DLMF 1.6.58** (Gauss's divergence theorem) for a region whose complete boundary is the
closed surface `S`, oriented by its normal being outwards. -/
theorem dlmf_1_6_58_outward (S : ClosedSurface) {V : Set (Fin 3 → ℝ)} (hS : S.OutwardBoundary V)
    (hVm : MeasurableSet V) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hKU : closure V ∪ S.image ⊆ U) {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiffOn ℝ 1 F U) :
    ∫ y in V, div3 F y = S.flux F :=
  dlmf_1_6_58_general S hS.isBounded hVm hS.boundsOutward hU hKU hF

/-- **DLMF 1.6.59** (Green's first identity) for an outward boundary. -/
theorem dlmf_1_6_59_outward (S : ClosedSurface) {V : Set (Fin 3 → ℝ)} (hS : S.OutwardBoundary V)
    (hVm : MeasurableSet V) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hKU : closure V ∪ S.image ⊆ U) {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) :
    ∫ y in V, (f y * lap3 g y + grad3 f y ⬝ᵥ grad3 g y) =
      S.flux (fun x => f x • grad3 g x) :=
  dlmf_1_6_59_general S hS.isBounded hVm hS.boundsOutward hU hKU hf hg

/-- **DLMF 1.6.60** (Green's second identity) for an outward boundary. -/
theorem dlmf_1_6_60_outward (S : ClosedSurface) {V : Set (Fin 3 → ℝ)} (hS : S.OutwardBoundary V)
    (hVm : MeasurableSet V) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hKU : closure V ∪ S.image ⊆ U) {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) :
    ∫ y in V, (f y * lap3 g y - g y * lap3 f y) =
      S.flux (fun x => f x • grad3 g x - g x • grad3 f x) :=
  dlmf_1_6_60_general S hS.isBounded hVm hS.boundsOutward hU hKU hf hg

end Azurite.DLMF
