/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section6Gauss

/-!
# Examples for Gauss's theorem: the box and the sphere

The general Gauss and Green theorems of `Section6Gauss.lean` (`dlmf_1_6_58_general`,
`dlmf_1_6_59_general`, `dlmf_1_6_60_general`) are exercised on a box and a sphere: both are built
as `ClosedSurface`s and shown to bound their solid regions with the outward orientation
(`BoundsOutward`), so the general theorems apply.

* **Rectangles as Green regions** (`Rect`): the anticlockwise boundary path `Rect.path` on
  `[0, 4]`, as a closed piecewise-`C¹` curve (`Rect.piecewise`); its image is the boundary of the
  rectangle (`Rect.image_path`), the region it bounds is the open rectangle
  (`Rect.planeInterior_eq`), and it is positively oriented (`Rect.isPositivelyOriented`, from the
  winding-number Green theorem and the area `∮ −½y dx + ½x dy = (u₁ − u₀)(v₁ − v₀)`).
  `SurfacePiece.ofRect`; boundary integrals split into the four edges
  (`SurfacePiece.boundaryIntegral_ofRect`), `segIntegral`, `segIntegral_add_swap`.
* **The box** (`Box3`): six affine faces with outward normals (`Box3.face`); the twelve edges
  cancel in pairs (`Box3.face_closed`), giving `Box3.surface`; its flux is Mathlib's box flux
  (`Box3.surface_flux`).  The solid angle is `1` inside and `0` outside
  (`Box3.windingNumber_of_mem_interior`, `Box3.windingNumber_of_notMem`): the flux of the field
  `(1 − φ) K(· − y)` of a point source cut off near `y` (`cutSource`, `div3_cutSource`,
  `integral_div3_cutSource`, using `div3_newtonKernel`) is computed by Mathlib's divergence
  theorem on the box.  Hence `Box3.boundsOutward` and `Box3.gauss`.
* **The solid angle off a surface** (`ClosedSurface`): continuous
  (`continuousAt_windingNumber`), equal at the ends of any segment staying away from the surface
  (`windingNumber_eq_of_segment`, via the test field `segField` whose divergence is a bump minus
  its translate, so that its flux is a difference of bump averages of `W`: `flux_segField`),
  hence locally constant (`eventually_windingNumber_eq`) and constant on connected
  sets (`windingNumber_eq_of_isPreconnected`); it decays like `R⁻²`
  (`exists_abs_windingNumber_le`).
* **The sphere** (`Sphere3`): one spherical-coordinate chart over `[0, π] × [0, 2π]`, whose
  boundary maps to the two poles and to one meridian traversed both ways
  (`Sphere3.boundaryIntegral_piece`), giving `Sphere3.surface`; `T_θ × T_φ = ρ sin θ · Φ`
  (`cross_tangent_sphereParam`); the solid angle is `1` at the centre
  (`Sphere3.windingNumber_center`), hence on the open ball (convex), and `0` outside (constant
  along outward rays, decaying).  The sphere is null (`Sphere3.volume_sphere`), so
  `Sphere3.boundsOutward` and `Sphere3.gauss`.
-/

namespace Azurite.DLMF

open Matrix MeasureTheory Set Metric Filter Topology
open scoped Real

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ### Rectangles as Green regions -/

/-- A nondegenerate rectangle `[u₀, u₁] × [v₀, v₁]` in the parameter plane. -/
structure Rect where
  u₀ : ℝ
  u₁ : ℝ
  v₀ : ℝ
  v₁ : ℝ
  hu : u₀ < u₁
  hv : v₀ < v₁

namespace Rect

variable (R : Rect)

/-- The corners, anticlockwise from `(u₀, v₀)`. -/
def corner : ℕ → ℝ × ℝ
  | 0 => (R.u₀, R.v₀)
  | 1 => (R.u₁, R.v₀)
  | 2 => (R.u₁, R.v₁)
  | 3 => (R.u₀, R.v₁)
  | _ => (R.u₀, R.v₀)

/-- The `k`-th side, an affine function of `t ∈ [k, k + 1]`. -/
def seg (k : ℕ) (t : ℝ) : ℝ × ℝ := R.corner k + (t - k) • (R.corner (k + 1) - R.corner k)

/-- The anticlockwise boundary path, on `[0, 4]`. -/
noncomputable def path (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then R.seg 0 t else if t ≤ 2 then R.seg 1 t else if t ≤ 3 then R.seg 2 t
    else R.seg 3 t

/-- The open rectangle. -/
def openSet : Set (ℝ × ℝ) := Ioo R.u₀ R.u₁ ×ˢ Ioo R.v₀ R.v₁

/-- The closed rectangle. -/
def closedSet : Set (ℝ × ℝ) := Icc R.u₀ R.u₁ ×ˢ Icc R.v₀ R.v₁

theorem seg_start (k : ℕ) : R.seg k k = R.corner k := by simp [seg]

theorem seg_end (k : ℕ) : R.seg k (k + 1) = R.corner (k + 1) := by
  simp only [seg, add_sub_cancel_left, one_smul, add_sub_cancel]

theorem path_eq_seg {k : ℕ} (hk : k < 4) {t : ℝ} (ht : t ∈ Icc (k : ℝ) (k + 1)) :
    R.path t = R.seg k t := by
  obtain ⟨h1, h2⟩ := ht
  unfold path
  interval_cases k
  · simp only [Nat.cast_zero, zero_add] at h1 h2
    simp [h2]
  · norm_num at h1 h2
    by_cases ht1 : t ≤ 1
    · have : t = 1 := le_antisymm ht1 h1
      subst this
      simp only [le_refl, ↓reduceIte]
      have e1 := R.seg_end 0
      have e2 := R.seg_start 1
      push_cast at e1 e2
      rw [zero_add] at e1
      rw [e1, e2]
    · simp [ht1, h2]
  · norm_num at h1 h2
    have ht1 : ¬ t ≤ 1 := by linarith
    by_cases ht2 : t ≤ 2
    · have : t = 2 := le_antisymm ht2 h1
      subst this
      simp only [ht1, le_refl, ↓reduceIte]
      have e1 := R.seg_end 1
      have e2 := R.seg_start 2
      push_cast at e1 e2
      norm_num at e1
      rw [e1, e2]
    · simp [ht1, ht2, h2]
  · norm_num at h1 h2
    have ht1 : ¬ t ≤ 1 := by linarith
    have ht2 : ¬ t ≤ 2 := by linarith
    by_cases ht3 : t ≤ 3
    · have : t = 3 := le_antisymm ht3 h1
      subst this
      simp only [ht1, ht2, le_refl, ↓reduceIte]
      have e1 := R.seg_end 2
      have e2 := R.seg_start 3
      push_cast at e1 e2
      norm_num at e1
      rw [e1, e2]
    · simp [ht1, ht2, ht3]

theorem path_zero : R.path 0 = R.corner 0 := by
  rw [R.path_eq_seg (k := 0) (by norm_num) ⟨by norm_num, by norm_num⟩]
  simpa using R.seg_start 0

theorem path_four : R.path 4 = R.corner 0 := by
  rw [R.path_eq_seg (k := 3) (by norm_num) ⟨by norm_num, by norm_num⟩]
  have := R.seg_end 3
  norm_num at this
  rw [this]
  rfl

theorem toComplexPath_eq (c : ℝ → ℝ × ℝ) (t : ℝ) :
    toComplexPath c t = Complex.equivRealProdCLM.symm (c t) := by
  apply Complex.ext <;> simp [toComplexPath]

theorem contDiff_seg (k : ℕ) : ContDiff ℝ 1 (R.seg k) := by
  unfold seg
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).smul contDiff_const)

/-- The boundary path as a closed piecewise-`C¹` curve. -/
noncomputable def piecewise : JordanCurve.ClosedPiecewiseC1 (toComplexPath R.path) 0 4 where
  n := 4
  t k := k
  g k s := Complex.equivRealProdCLM.symm (R.seg k s)
  lt k _ := by push_cast; linarith
  first := by simp
  last := by norm_num
  contDiff k _ := Complex.equivRealProdCLM.symm.contDiff.comp (R.contDiff_seg k)
  eqOn k hk s hs := by
    simp only [toComplexPath_eq]
    rw [R.path_eq_seg hk ⟨by exact_mod_cast hs.1, by have := hs.2; push_cast at this; exact this⟩]
  closed := by simp only [toComplexPath_eq, R.path_zero, R.path_four]

theorem seg0 (t : ℝ) : R.seg 0 t = (R.u₀ + t * (R.u₁ - R.u₀), R.v₀) := by
  ext <;> simp [seg, corner]
theorem seg1 (t : ℝ) : R.seg 1 t = (R.u₁, R.v₀ + (t - 1) * (R.v₁ - R.v₀)) := by
  ext <;> simp [seg, corner]
theorem seg2 (t : ℝ) : R.seg 2 t = (R.u₁ + (t - 2) * (R.u₀ - R.u₁), R.v₁) := by
  ext <;> simp [seg, corner]
theorem seg3 (t : ℝ) : R.seg 3 t = (R.u₀, R.v₁ + (t - 3) * (R.v₀ - R.v₁)) := by
  ext <;> simp [seg, corner]

theorem mem_closedSet_of_mem_image {q : ℝ × ℝ} (hq : q ∈ R.path '' Icc 0 4) :
    q ∈ R.closedSet ∧ q ∉ R.openSet := by
  obtain ⟨t, ht, rfl⟩ := hq
  have hu := R.hu
  have hv := R.hv
  obtain ⟨ht0, ht4⟩ := ht
  simp only [closedSet, openSet, mem_prod, mem_Icc, mem_Ioo]
  by_cases h1 : t ≤ 1
  · rw [R.path_eq_seg (k := 0) (by norm_num) ⟨by simpa using ht0, by simpa using h1⟩, seg0]
    refine ⟨⟨⟨by nlinarith, by nlinarith⟩, le_refl _, hv.le⟩, fun h => by linarith [h.2.1]⟩
  by_cases h2 : t ≤ 2
  · rw [R.path_eq_seg (k := 1) (by norm_num) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seg1]
    refine ⟨⟨⟨hu.le, le_refl _⟩, by nlinarith, by nlinarith⟩, fun h => by linarith [h.1.2]⟩
  by_cases h3 : t ≤ 3
  · rw [R.path_eq_seg (k := 2) (by norm_num) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seg2]
    refine ⟨⟨⟨by nlinarith, by nlinarith⟩, hv.le, le_refl _⟩, fun h => by linarith [h.2.2]⟩
  · rw [R.path_eq_seg (k := 3) (by norm_num) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seg3]
    refine ⟨⟨⟨le_refl _, hu.le⟩, by nlinarith, by nlinarith⟩, fun h => by linarith [h.1.1]⟩


theorem mem_image_of_mem_closedSet {q : ℝ × ℝ} (hc : q ∈ R.closedSet) (ho : q ∉ R.openSet) :
    q ∈ R.path '' Icc 0 4 := by
  have hu := R.hu
  have hv := R.hv
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc
  simp only [openSet, mem_prod, mem_Ioo, not_and_or, not_lt] at ho
  have hu' : R.u₁ - R.u₀ ≠ 0 := by linarith
  have hv' : R.v₁ - R.v₀ ≠ 0 := by linarith
  rcases ho with (ho | ho) | (ho | ho)
  · -- `q.1 = u₀`: the left side
    have he : q.1 = R.u₀ := le_antisymm ho h1
    set t := 3 + (R.v₁ - q.2) / (R.v₁ - R.v₀)
    have ht0 : 0 ≤ (R.v₁ - q.2) / (R.v₁ - R.v₀) := div_nonneg (by linarith) (by linarith)
    have ht1 : (R.v₁ - q.2) / (R.v₁ - R.v₀) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
    rw [R.path_eq_seg (k := 3) (by norm_num) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seg3]
    ext
    · exact he.symm
    · simp only [t]; field_simp; ring
  · -- `q.1 = u₁`: the right side
    have he : q.1 = R.u₁ := le_antisymm h2 ho
    set t := 1 + (q.2 - R.v₀) / (R.v₁ - R.v₀)
    have ht0 : 0 ≤ (q.2 - R.v₀) / (R.v₁ - R.v₀) := div_nonneg (by linarith) (by linarith)
    have ht1 : (q.2 - R.v₀) / (R.v₁ - R.v₀) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
    rw [R.path_eq_seg (k := 1) (by norm_num) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seg1]
    ext
    · exact he.symm
    · simp only [t]; field_simp; ring
  · -- `q.2 = v₀`: the bottom side
    have he : q.2 = R.v₀ := le_antisymm ho h3
    set t := (q.1 - R.u₀) / (R.u₁ - R.u₀)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    refine ⟨t, ⟨ht0, by linarith⟩, ?_⟩
    rw [R.path_eq_seg (k := 0) (by norm_num) ⟨by simpa using ht0, by simpa using ht1⟩, seg0]
    ext
    · simp only [t]; field_simp; ring
    · exact he.symm
  · -- `q.2 = v₁`: the top side
    have he : q.2 = R.v₁ := le_antisymm h4 ho
    set t := 2 + (R.u₁ - q.1) / (R.u₁ - R.u₀)
    have ht0 : 0 ≤ (R.u₁ - q.1) / (R.u₁ - R.u₀) := div_nonneg (by linarith) (by linarith)
    have ht1 : (R.u₁ - q.1) / (R.u₁ - R.u₀) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
    rw [R.path_eq_seg (k := 2) (by norm_num) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seg2]
    ext
    · simp only [t]; field_simp; ring
    · exact he.symm

theorem image_path : R.path '' Icc 0 4 = R.closedSet \ R.openSet :=
  Set.ext fun _ => ⟨fun h => R.mem_closedSet_of_mem_image h,
    fun h => R.mem_image_of_mem_closedSet h.1 h.2⟩

theorem not_isBounded_ray (q w : ℝ × ℝ) (hw : w ≠ 0) :
    ¬ Bornology.IsBounded ((fun s : ℝ => q + s • w) '' Ici 0) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall 0
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set s := (max M 0 + ‖q‖ + 1) / ‖w‖
  have hs : 0 ≤ s := by positivity
  have := hM ⟨s, hs, rfl⟩
  rw [mem_closedBall_zero_iff] at this
  have h1 : ‖s • w‖ ≤ ‖q + s • w‖ + ‖q‖ := by
    have := norm_sub_le (q + s • w) q
    rwa [add_sub_cancel_left] at this
  rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ _ hw'.ne'] at h1
  linarith [le_max_left M 0]

/-- The region bounded by the boundary path is the open rectangle. -/
theorem planeInterior_eq : planeInterior R.path 0 4 = R.openSet := by
  have hu := R.hu
  have hv := R.hv
  have hopen : IsOpen R.openSet := isOpen_Ioo.prod isOpen_Ioo
  have hclosed : IsClosed R.closedSet := isClosed_Icc.prod isClosed_Icc
  have hsub : R.openSet ⊆ R.closedSet := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hcompl : (R.path '' Icc 0 4)ᶜ = R.openSet ∪ R.closedSetᶜ := by
    rw [image_path]
    ext q
    simp only [mem_compl_iff, Set.mem_sdiff, not_and, not_not, mem_union]
    constructor
    · intro h
      by_cases hq : q ∈ R.closedSet
      · exact Or.inl (h hq)
      · exact Or.inr hq
    · rintro (h | h) h'
      · exact h
      · exact absurd h' h
  ext q
  constructor
  · rintro ⟨hq, hb⟩
    by_contra hqo
    have hqc : q ∉ R.closedSet := fun h => hq (by rw [image_path]; exact ⟨h, hqo⟩)
    -- a ray to infinity avoiding the closed rectangle
    obtain ⟨w, hw, hray⟩ : ∃ w : ℝ × ℝ, w ≠ 0 ∧ ∀ s : ℝ, 0 ≤ s → q + s • w ∉ R.closedSet := by
      simp only [closedSet, mem_prod, mem_Icc, not_and_or, not_le] at hqc
      rcases hqc with (h | h) | (h | h)
      · exact ⟨(-1, 0), by simp, fun s hs hm => by
          simp only [closedSet, mem_prod, mem_Icc] at hm; simp at hm; linarith [hm.1.1]⟩
      · exact ⟨(1, 0), by simp, fun s hs hm => by
          simp only [closedSet, mem_prod, mem_Icc] at hm; simp at hm; linarith [hm.1.2]⟩
      · exact ⟨(0, -1), by simp, fun s hs hm => by
          simp only [closedSet, mem_prod, mem_Icc] at hm; simp at hm; linarith [hm.2.1]⟩
      · exact ⟨(0, 1), by simp, fun s hs hm => by
          simp only [closedSet, mem_prod, mem_Icc] at hm; simp at hm; linarith [hm.2.2]⟩
    have hconn : IsPreconnected ((fun s : ℝ => q + s • w) '' Ici 0) :=
      (isPreconnected_Ici).image _ (by fun_prop : Continuous fun s : ℝ => q + s • w).continuousOn
    have hsub' : (fun s : ℝ => q + s • w) '' Ici 0 ⊆ (R.path '' Icc 0 4)ᶜ := by
      rintro _ ⟨s, hs, rfl⟩
      rw [hcompl]
      exact Or.inr (hray s hs)
    have hq0 : q ∈ (fun s : ℝ => q + s • w) '' Ici 0 := ⟨0, self_mem_Ici, by simp⟩
    exact not_isBounded_ray q w hw
      (hb.subset (hconn.subset_connectedComponentIn hq0 hsub'))
  · intro hq
    have hq' : q ∉ R.path '' Icc 0 4 := by rw [image_path]; exact fun h => h.2 hq
    refine ⟨hq', ?_⟩
    have hcomp : connectedComponentIn (R.path '' Icc 0 4)ᶜ q ⊆ R.openSet := by
      have hc := (isPreconnected_connectedComponentIn (F := (R.path '' Icc 0 4)ᶜ) (x := q))
      refine hc.subset_left_of_subset_union hopen hclosed.isOpen_compl
        (disjoint_compl_right.mono_left hsub) ?_ ⟨q, mem_connectedComponentIn hq', hq⟩
      rw [← hcompl]
      exact connectedComponentIn_subset _ _
    exact (Metric.isBounded_Icc (R.u₀, R.v₀) (R.u₁, R.v₁)).subset (fun p hp => by
      have := hcomp hp
      exact ⟨⟨this.1.1.le, this.2.1.le⟩, ⟨this.1.2.le, this.2.2.le⟩⟩)


/-- Splitting `∫₀⁴` into the four unit pieces. -/
theorem integral_split_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (h : ℕ → ℝ → E) (hc : ∀ k : ℕ, k < 4 → Continuous (h k))
    (hf : ∀ k : ℕ, k < 4 → ∀ s ∈ Ioo (0 : ℝ) 1, f (k + s) = h k s) :
    ∫ t in (0 : ℝ)..4, f t = ∑ k ∈ Finset.range 4, ∫ s in (0 : ℝ)..1, h k s := by
  have hae : ∀ k : ℕ, k < 4 → (fun s => f (k + s)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] h k := by
    intro k hk
    have : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) 1)), s ∈ Ioo (0 : ℝ) 1 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with s hs hs'
      exact ⟨hs'.1, lt_of_le_of_ne hs'.2 hs⟩
    filter_upwards [this] with s hs using hf k hk s hs
  have hint : ∀ k : ℕ, k < 4 → IntervalIntegrable (fun s => f (k + s)) volume 0 1 := by
    intro k hk
    refine ((hc k hk).intervalIntegrable 0 1).congr_ae ?_
    rw [uIoc_of_le zero_le_one]
    exact (hae k hk).symm
  have hint' : ∀ k : ℕ, k < 4 → IntervalIntegrable f volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    have := (hint k hk).comp_add_left (-(k : ℝ))
    simp only [add_neg_cancel_left, sub_neg_eq_add, zero_add] at this
    push_cast
    rwa [add_comm 1] at this
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
    (n := 4) hint'
  simp only [Nat.cast_zero, Nat.cast_ofNat] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have := intervalIntegral.integral_comp_add_left f (k : ℝ) (a := 0) (b := 1)
  simp only [add_zero] at this
  push_cast
  rw [add_comm (k : ℝ) 1, ← add_comm, ← this, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  exact integral_congr_ae (hae k hk')

theorem hasDerivAt_seg (k : ℕ) (t : ℝ) :
    HasDerivAt (R.seg k) (R.corner (k + 1) - R.corner k) t := by
  have := (((hasDerivAt_id t).sub_const (k : ℝ)).smul_const
    (R.corner (k + 1) - R.corner k)).const_add (R.corner k)
  simp only [one_smul] at this
  exact this

theorem path_eventuallyEq {k : ℕ} (hk : k < 4) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    R.path =ᶠ[𝓝 ((k : ℝ) + s)] R.seg k :=
  eventuallyEq_of_mem (Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2]))
    fun _ hx => R.path_eq_seg hk hx

/-- The planar line integral along the boundary path, side by side. -/
theorem lineIntegral2_path {F₁ F₂ : ℝ → ℝ → ℝ} (hF₁ : Continuous (Function.uncurry F₁))
    (hF₂ : Continuous (Function.uncurry F₂)) :
    lineIntegral2 F₁ F₂ R.path 0 4 = ∑ k ∈ Finset.range 4, ∫ s in (0 : ℝ)..1,
      (F₁ (R.seg k (k + s)).1 (R.seg k (k + s)).2 * (R.corner (k + 1) - R.corner k).1 +
        F₂ (R.seg k (k + s)).1 (R.seg k (k + s)).2 * (R.corner (k + 1) - R.corner k).2) := by
  unfold lineIntegral2
  refine integral_split_four _ (fun k _ => ?_) fun k hk s hs => ?_
  · have hs : Continuous fun s : ℝ => R.seg k (k + s) :=
      (R.contDiff_seg k).continuous.comp (continuous_const.add continuous_id)
    exact ((hF₁.comp ((continuous_fst.comp hs).prodMk (continuous_snd.comp hs))).mul
      continuous_const).add
      ((hF₂.comp ((continuous_fst.comp hs).prodMk (continuous_snd.comp hs))).mul continuous_const)
  · have hev := R.path_eventuallyEq hk hs
    have hd := R.hasDerivAt_seg k ((k : ℝ) + s)
    have hev1 : (fun r => (R.path r).1) =ᶠ[𝓝 ((k : ℝ) + s)] fun r => (R.seg k r).1 :=
      hev.mono fun x hx => by simp only [hx]
    have hev2 : (fun r => (R.path r).2) =ᶠ[𝓝 ((k : ℝ) + s)] fun r => (R.seg k r).2 :=
      hev.mono fun x hx => by simp only [hx]
    have h1 : deriv (fun r => (R.path r).1) ((k : ℝ) + s) = (R.corner (k + 1) - R.corner k).1 := by
      rw [hev1.deriv_eq]
      exact ((hasFDerivAt_fst (𝕜 := ℝ) (p := R.seg k ((k : ℝ) + s))).comp_hasDerivAt _ hd).deriv
    have h2 : deriv (fun r => (R.path r).2) ((k : ℝ) + s) = (R.corner (k + 1) - R.corner k).2 := by
      rw [hev2.deriv_eq]
      exact ((hasFDerivAt_snd (𝕜 := ℝ) (p := R.seg k ((k : ℝ) + s))).comp_hasDerivAt _ hd).deriv
    rw [h1, h2, hev.eq_of_nhds]

/-- The area form `−½ y dx + ½ x dy` integrates to the area along the boundary path. -/
theorem lineIntegral2_area :
    lineIntegral2 (fun _ y => -y / 2) (fun x _ => x / 2) R.path 0 4 =
      (R.u₁ - R.u₀) * (R.v₁ - R.v₀) := by
  rw [R.lineIntegral2_path (by fun_prop) (by fun_prop)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat]
  have e0 : ∀ s : ℝ, R.seg 0 s = _ := R.seg0
  simp only [R.seg0, R.seg1, R.seg2, R.seg3, corner, Prod.fst_sub, Prod.snd_sub, sub_self,
    mul_zero, add_zero, zero_add, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
  ring

/-- The boundary path is positively oriented. -/
theorem isPositivelyOriented : R.piecewise.IsPositivelyOriented := by
  have hu := R.hu
  have hv := R.hv
  set J := JordanCurve.jordanInterior (toComplexPath R.path) 0 4 with hJdef
  have hJ : J = Complex.measurableEquivRealProd ⁻¹' R.openSet := by
    rw [hJdef, ← preimage_planeInterior, planeInterior_eq]
  have hconv : Convex ℝ J := by
    rw [hJ]
    exact ((convex_Ioo _ _).prod (convex_Ioo _ _)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  set z₀ : ℂ := ⟨(R.u₀ + R.u₁) / 2, (R.v₀ + R.v₁) / 2⟩
  have hz₀ : z₀ ∈ J := by
    rw [hJ]
    simp only [mem_preimage, Complex.measurableEquivRealProd_apply, openSet, mem_prod, mem_Ioo, z₀]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  set w := R.piecewise.windingNumber z₀
  have hw : ∀ p ∈ J, R.piecewise.windingNumber p = w := fun p hp =>
    R.piecewise.windingNumber_eq_of_isPreconnected hconv.isPreconnected
      JordanCurve.jordanInterior_subset hp hz₀
  have h := lineIntegral2_eq_mul_setIntegral R.piecewise hw
    (F₁ := fun _ y => -y / 2) (F₂ := fun x _ => x / 2) (by fun_prop) (by fun_prop)
  have hpd : ∀ q : ℝ × ℝ, partialX (fun x (_ : ℝ) => x / 2) q.1 q.2 -
      partialY (fun (_ : ℝ) y => -y / 2) q.1 q.2 = 1 := by
    intro q
    simp [partialX, partialY]
    norm_num
  simp only [hpd, planeInterior_eq, setIntegral_const, smul_eq_mul, mul_one] at h
  rw [lineIntegral2_area, measureReal_def, openSet, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, Real.volume_Ioo, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)] at h
  have harea : 0 < (R.u₁ - R.u₀) * (R.v₁ - R.v₀) := mul_pos (by linarith) (by linarith)
  have hw1 : (w : ℝ) = 1 := by
    have := mul_right_cancel₀ harea.ne' (h.symm.trans (one_mul _).symm)
    exact this
  have hw1' : w = 1 := by exact_mod_cast hw1
  intro p hp
  rw [hw p hp, hw1']


/-- The image of side `k` under `Φ`, on `[0, 1]`. -/
def edge (Φ : ℝ × ℝ → Fin 3 → ℝ) (k : ℕ) (s : ℝ) : Fin 3 → ℝ :=
  Φ (R.corner k + s • (R.corner (k + 1) - R.corner k))

theorem seg_add (k : ℕ) (s : ℝ) :
    R.seg k (k + s) = R.corner k + s • (R.corner (k + 1) - R.corner k) := by
  simp [seg]

end Rect

/-- The line integral of `A` along the segment from `P` to `Q`. -/
noncomputable def segIntegral (A : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (P Q : Fin 3 → ℝ) : ℝ :=
  lineIntegral A (fun s => P + s • (Q - P)) 0 1

/-- `d/dx c(d − x) = −c'(d − x)`, with no differentiability hypothesis. -/
theorem deriv_comp_const_sub_vec (c : ℝ → Fin 3 → ℝ) (d x : ℝ) :
    deriv (fun s => c (d - s)) x = -deriv c (d - x) := by
  have h : (fun s => c (d - s)) = fun s => (fun y => c (d + y)) (-s) := by
    funext s
    rw [sub_eq_add_neg]
  rw [h, deriv_comp_neg (fun y => c (d + y)), deriv_comp_const_add, ← sub_eq_add_neg]

theorem lineIntegral_reverse01 (A : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (c : ℝ → Fin 3 → ℝ) :
    lineIntegral A (fun s => c (1 - s)) 0 1 = -lineIntegral A c 0 1 := by
  unfold lineIntegral
  simp only [deriv_comp_const_sub_vec, dotProduct_neg, intervalIntegral.integral_neg]
  have hsub := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun t => A (c t) ⬝ᵥ deriv c t) 1
  rw [hsub, sub_zero, sub_self]

theorem segIntegral_add_swap (A : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (P Q : Fin 3 → ℝ) :
    segIntegral A P Q + segIntegral A Q P = 0 := by
  have h : (fun s : ℝ => Q + s • (P - Q)) = fun s => (fun r => P + r • (Q - P)) (1 - s) := by
    funext s
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold segIntegral
  rw [h, lineIntegral_reverse01 A (fun r => P + r • (Q - P))]
  ring

/-- A surface piece parametrized over a rectangle by a globally `C²` map. -/
noncomputable def SurfacePiece.ofRect (R : Rect) (Φ : ℝ × ℝ → Fin 3 → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) : SurfacePiece where
  γ := R.path
  a := 0
  b := 4
  P := R.piecewise
  hpos := R.isPositivelyOriented
  Φ := Φ
  U := univ
  hU := isOpen_univ
  hSU := subset_univ _
  hΦ := hΦ.contDiffOn

theorem SurfacePiece.ofRect_D (R : Rect) (Φ : ℝ × ℝ → Fin 3 → ℝ) (hΦ : ContDiff ℝ 2 Φ) :
    (SurfacePiece.ofRect R Φ hΦ).D = R.openSet :=
  R.planeInterior_eq

/-- The boundary integral of a piece over a rectangle is the sum over its four edges. -/
theorem SurfacePiece.boundaryIntegral_ofRect (R : Rect) (Φ : ℝ × ℝ → Fin 3 → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) {A : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hA : Continuous A) :
    (SurfacePiece.ofRect R Φ hΦ).boundaryIntegral A =
      ∑ k ∈ Finset.range 4, lineIntegral A (R.edge Φ k) 0 1 := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΦc : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by norm_num)
  have hedge : ∀ k (s : ℝ), HasDerivAt (R.edge Φ k)
      (fderiv ℝ Φ (R.corner k + s • (R.corner (k + 1) - R.corner k))
        (R.corner (k + 1) - R.corner k)) s := by
    intro k s
    have hl : HasDerivAt (fun r : ℝ => R.corner k + r • (R.corner (k + 1) - R.corner k))
        (R.corner (k + 1) - R.corner k) s := by
      simpa using ((hasDerivAt_id s).smul_const (R.corner (k + 1) - R.corner k)).const_add
        (R.corner k)
    exact (hΦd _).hasFDerivAt.comp_hasDerivAt s hl
  unfold SurfacePiece.boundaryIntegral lineIntegral
  simp only [SurfacePiece.ofRect]
  refine (Rect.integral_split_four (fun k s => A (R.edge Φ k s) ⬝ᵥ
    fderiv ℝ Φ (R.corner k + s • (R.corner (k + 1) - R.corner k))
      (R.corner (k + 1) - R.corner k)) (fun k _ => ?_) fun k hk s hs => ?_).trans ?_
  · have hl : Continuous fun r : ℝ => R.corner k + r • (R.corner (k + 1) - R.corner k) := by
      fun_prop
    exact (hA.comp (hΦd.continuous.comp hl)).dotProduct
      ((hΦc.comp hl).clm_apply continuous_const)
  · have hev := R.path_eventuallyEq hk hs
    have hd : HasDerivAt (fun t => Φ (R.path t))
        (fderiv ℝ Φ (R.corner k + s • (R.corner (k + 1) - R.corner k))
          (R.corner (k + 1) - R.corner k)) ((k : ℝ) + s) := by
      have h1 := (hΦd (R.seg k ((k : ℝ) + s))).hasFDerivAt.comp_hasDerivAt _
        (R.hasDerivAt_seg k ((k : ℝ) + s))
      rw [R.seg_add] at h1
      exact h1.congr_of_eventuallyEq (hev.mono fun x hx => by simp only [Function.comp_apply, hx])
    rw [hd.deriv, hev.eq_of_nhds, R.seg_add]
    rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [(hedge k s).deriv]

/-! ### The box -/

/-- The affine map `(u, w) ↦ c + u e + w f`. -/
def affineFace (c e f : Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := c + p.1 • e + p.2 • f

theorem contDiff_affineFace (c e f : Fin 3 → ℝ) : ContDiff ℝ 2 (affineFace c e f) := by
  unfold affineFace
  fun_prop

theorem affineFace_apply (c e f : Fin 3 → ℝ) (p : ℝ × ℝ) :
    affineFace c e f p = ![c 0 + p.1 * e 0 + p.2 * f 0, c 1 + p.1 * e 1 + p.2 * f 1,
      c 2 + p.1 * e 2 + p.2 * f 2] := by
  ext i
  fin_cases i <;> simp [affineFace]

theorem Rect.edge_affineFace (R : Rect) (c e f : Fin 3 → ℝ) (k : ℕ) :
    R.edge (affineFace c e f) k = fun s => affineFace c e f (R.corner k) +
      s • (affineFace c e f (R.corner (k + 1)) - affineFace c e f (R.corner k)) := by
  funext s
  ext i
  simp only [Rect.edge, affineFace, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- A box `[a, b] ⊂ ℝ³` with `aᵢ < bᵢ`. -/
structure Box3 where
  a : Fin 3 → ℝ
  b : Fin 3 → ℝ
  hab : ∀ i, a i < b i

namespace Box3

variable (B : Box3)

/-- The standard basis vector `eᵢ`. -/
def e (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The parameter rectangle `[aᵢ, bᵢ] × [aⱼ, bⱼ]`. -/
def rect (i j : Fin 3) : Rect := ⟨B.a i, B.b i, B.a j, B.b j, B.hab i, B.hab j⟩

/-- The six faces, each parametrized so that `T_u × T_v` is the outward normal. -/
noncomputable def face : Fin 6 → SurfacePiece
  | 0 => .ofRect (B.rect 1 2) (affineFace (B.b 0 • e 0) (e 1) (e 2)) (contDiff_affineFace _ _ _)
  | 1 => .ofRect (B.rect 2 1) (affineFace (B.a 0 • e 0) (e 2) (e 1)) (contDiff_affineFace _ _ _)
  | 2 => .ofRect (B.rect 2 0) (affineFace (B.b 1 • e 1) (e 2) (e 0)) (contDiff_affineFace _ _ _)
  | 3 => .ofRect (B.rect 0 2) (affineFace (B.a 1 • e 1) (e 0) (e 2)) (contDiff_affineFace _ _ _)
  | 4 => .ofRect (B.rect 0 1) (affineFace (B.b 2 • e 2) (e 0) (e 1)) (contDiff_affineFace _ _ _)
  | 5 => .ofRect (B.rect 1 0) (affineFace (B.a 2 • e 2) (e 1) (e 0)) (contDiff_affineFace _ _ _)

theorem boundaryIntegral_face_affine (R : Rect) (c f g : Fin 3 → ℝ)
    {A : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hA : Continuous A) :
    (SurfacePiece.ofRect R (affineFace c f g) (contDiff_affineFace _ _ _)).boundaryIntegral A =
      segIntegral A (affineFace c f g (R.corner 0)) (affineFace c f g (R.corner 1)) +
      segIntegral A (affineFace c f g (R.corner 1)) (affineFace c f g (R.corner 2)) +
      segIntegral A (affineFace c f g (R.corner 2)) (affineFace c f g (R.corner 3)) +
      segIntegral A (affineFace c f g (R.corner 3)) (affineFace c f g (R.corner 0)) := by
  rw [SurfacePiece.boundaryIntegral_ofRect _ _ _ hA]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, R.edge_affineFace]
  rfl

/-- The boundary curves of the six faces cancel: each of the twelve edges is traversed once in
each direction. -/
theorem face_closed (A : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hA : ContDiff ℝ 1 A) :
    ∑ j, (B.face j).boundaryIntegral A = 0 := by
  simp only [Fin.sum_univ_six, face, boundaryIntegral_face_affine _ _ _ _ hA.continuous]
  simp only [Rect.corner, rect, affineFace_apply, e, Pi.smul_apply, smul_eq_mul]
  simp
  linear_combination
    segIntegral_add_swap A ![B.b 0, B.a 1, B.a 2] ![B.b 0, B.b 1, B.a 2] +
    segIntegral_add_swap A ![B.b 0, B.b 1, B.a 2] ![B.b 0, B.b 1, B.b 2] +
    segIntegral_add_swap A ![B.b 0, B.b 1, B.b 2] ![B.b 0, B.a 1, B.b 2] +
    segIntegral_add_swap A ![B.b 0, B.a 1, B.b 2] ![B.b 0, B.a 1, B.a 2] +
    segIntegral_add_swap A ![B.a 0, B.a 1, B.a 2] ![B.a 0, B.a 1, B.b 2] +
    segIntegral_add_swap A ![B.a 0, B.a 1, B.b 2] ![B.a 0, B.b 1, B.b 2] +
    segIntegral_add_swap A ![B.a 0, B.b 1, B.b 2] ![B.a 0, B.b 1, B.a 2] +
    segIntegral_add_swap A ![B.a 0, B.b 1, B.a 2] ![B.a 0, B.a 1, B.a 2] +
    segIntegral_add_swap A ![B.a 0, B.b 1, B.b 2] ![B.b 0, B.b 1, B.b 2] +
    segIntegral_add_swap A ![B.b 0, B.b 1, B.a 2] ![B.a 0, B.b 1, B.a 2] +
    segIntegral_add_swap A ![B.a 0, B.a 1, B.a 2] ![B.b 0, B.a 1, B.a 2] +
    segIntegral_add_swap A ![B.b 0, B.a 1, B.b 2] ![B.a 0, B.a 1, B.b 2]

/-- The boundary of the box as a closed piecewise smooth surface. -/
noncomputable def surface : ClosedSurface where
  m := 6
  piece := B.face
  closed := B.face_closed

end Box3

/-! ### The box: fluxes -/

theorem hasFDerivAt_affineFace (c e f : Fin 3 → ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (affineFace c e f) ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight e +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight f) p := by
  have h := ((hasFDerivAt_const c p).add ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).smul_const e)).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).smul_const f)
  simp only [zero_add] at h
  exact h

theorem tangentU_affineFace (c e f : Fin 3 → ℝ) (p : ℝ × ℝ) :
    tangentU (affineFace c e f) p = e := by
  simp [tangentU, (hasFDerivAt_affineFace c e f p).fderiv]

theorem tangentV_affineFace (c e f : Fin 3 → ℝ) (p : ℝ × ℝ) :
    tangentV (affineFace c e f) p = f := by
  simp [tangentV, (hasFDerivAt_affineFace c e f p).fderiv]

theorem flux_ofRect_affine (R : Rect) (c e f : Fin 3 → ℝ) (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    (SurfacePiece.ofRect R (affineFace c e f) (contDiff_affineFace _ _ _)).flux F =
      ∫ p in R.openSet, F (affineFace c e f p) ⬝ᵥ (e ⨯₃ f) := by
  unfold SurfacePiece.flux fluxIntegral
  rw [SurfacePiece.ofRect_D]
  simp only [SurfacePiece.ofRect, tangentU_affineFace, tangentV_affineFace]

/-- A set integral over a box in `Fin 2 → ℝ` as an integral over an open rectangle. -/
theorem integral_fin2_Icc (α β : Fin 2 → ℝ) (G : ℝ × ℝ → ℝ) :
    ∫ y in Icc α β, G (y 0, y 1) = ∫ p in Ioo (α 0) (β 0) ×ˢ Ioo (α 1) (β 1), G p := by
  have h := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow).measurableEmbedding G (Icc (α 0) (β 0) ×ˢ Icc (α 1) (β 1))
  have hpre : (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
      (Icc (α 0) (β 0) ×ˢ Icc (α 1) (β 1)) = Icc α β := by
    ext y
    simp only [mem_preimage, MeasurableEquiv.finTwoArrow_apply, mem_prod, mem_Icc,
      Pi.le_def, Fin.forall_fin_two]
    tauto
  rw [hpre] at h
  simp only [MeasurableEquiv.finTwoArrow_apply] at h
  rw [h, Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
    Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := α 0) (b := β 0)),
    Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := α 1) (b := β 1))]

theorem integral_Ioo_prod_swap (α₀ β₀ α₁ β₁ : ℝ) (G : ℝ × ℝ → ℝ) :
    ∫ p in Ioo α₁ β₁ ×ˢ Ioo α₀ β₀, G (p.2, p.1) = ∫ p in Ioo α₀ β₀ ×ˢ Ioo α₁ β₁, G p := by
  rw [Measure.volume_eq_prod]
  exact setIntegral_prod_swap (Ioo α₀ β₀) (Ioo α₁ β₁) G

namespace Box3

variable (B : Box3)

theorem e_cross : e 1 ⨯₃ e 2 = e 0 ∧ e 2 ⨯₃ e 1 = -e 0 ∧ e 2 ⨯₃ e 0 = e 1 ∧
    e 0 ⨯₃ e 2 = -e 1 ∧ e 0 ⨯₃ e 1 = e 2 ∧ e 1 ⨯₃ e 0 = -e 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [e, cross_apply]

/-- The flux through the boundary of the box is Mathlib's box flux (`boxFlux`). -/
theorem surface_flux (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : B.surface.flux F = boxFlux F B.a B.b := by
  obtain ⟨h12, h21, h20, h02, h01, h10⟩ := e_cross
  have hface : ∀ (i j : Fin 3) (c f g : Fin 3 → ℝ),
      (SurfacePiece.ofRect (B.rect i j) (affineFace c f g) (contDiff_affineFace _ _ _)).flux F =
        ∫ p in Ioo (B.a i) (B.b i) ×ˢ Ioo (B.a j) (B.b j),
          F (affineFace c f g p) ⬝ᵥ (f ⨯₃ g) := fun i j c f g =>
    flux_ofRect_affine _ _ _ _ F
  show ∑ j : Fin 6, (B.face j).flux F = _
  rw [Fin.sum_univ_six]
  simp only [face, hface, h12, h21, h20, h02, h01, h10, boxFlux, Fin.sum_univ_three]
  have hb0 : ∀ y : Fin 2 → ℝ, boxFace 0 (B.b 0) y = ![B.b 0, y 0, y 1] := fun y => by
    ext j; fin_cases j <;> rfl
  have ha0 : ∀ y : Fin 2 → ℝ, boxFace 0 (B.a 0) y = ![B.a 0, y 0, y 1] := fun y => by
    ext j; fin_cases j <;> rfl
  have hb1 : ∀ y : Fin 2 → ℝ, boxFace 1 (B.b 1) y = ![y 0, B.b 1, y 1] := fun y => by
    ext j; fin_cases j <;> rfl
  have ha1 : ∀ y : Fin 2 → ℝ, boxFace 1 (B.a 1) y = ![y 0, B.a 1, y 1] := fun y => by
    ext j; fin_cases j <;> rfl
  have hb2 : ∀ y : Fin 2 → ℝ, boxFace 2 (B.b 2) y = ![y 0, y 1, B.b 2] := fun y => by
    ext j; fin_cases j <;> rfl
  have ha2 : ∀ y : Fin 2 → ℝ, boxFace 2 (B.a 2) y = ![y 0, y 1, B.a 2] := fun y => by
    ext j; fin_cases j <;> rfl
  simp only [hb0, ha0, hb1, ha1, hb2, ha2]
  rw [integral_fin2_Icc _ _ fun q => F ![B.b 0, q.1, q.2] 0,
    integral_fin2_Icc _ _ fun q => F ![B.a 0, q.1, q.2] 0,
    integral_fin2_Icc _ _ fun q => F ![q.1, B.b 1, q.2] 1,
    integral_fin2_Icc _ _ fun q => F ![q.1, B.a 1, q.2] 1,
    integral_fin2_Icc _ _ fun q => F ![q.1, q.2, B.b 2] 2,
    integral_fin2_Icc _ _ fun q => F ![q.1, q.2, B.a 2] 2]
  have s00 : Fin.succAbove (0 : Fin 3) 0 = 1 := rfl
  have s01 : Fin.succAbove (0 : Fin 3) 1 = 2 := rfl
  have s10 : Fin.succAbove (1 : Fin 3) 0 = 0 := rfl
  have s11 : Fin.succAbove (1 : Fin 3) 1 = 2 := rfl
  have s20 : Fin.succAbove (2 : Fin 3) 0 = 0 := rfl
  have s21 : Fin.succAbove (2 : Fin 3) 1 = 1 := rfl
  simp only [Function.comp_apply, s00, s01, s10, s11, s20, s21]
  rw [← integral_Ioo_prod_swap (B.a 1) (B.b 1) (B.a 2) (B.b 2) fun q => F ![B.a 0, q.1, q.2] 0,
    ← integral_Ioo_prod_swap (B.a 0) (B.b 0) (B.a 2) (B.b 2) fun q => F ![q.1, B.b 1, q.2] 1,
    ← integral_Ioo_prod_swap (B.a 0) (B.b 0) (B.a 1) (B.b 1) fun q => F ![q.1, q.2, B.a 2] 2]
  simp only [affineFace_apply, e, Pi.smul_apply, smul_eq_mul, dotProduct_neg,
    integral_neg]
  simp [dotProduct, Fin.sum_univ_three]
  ring

end Box3

/-! ### Point sources -/

theorem vnorm_neg (z : Fin 3 → ℝ) : vnorm (-z) = vnorm z := by
  simp [vnorm]

theorem newtonKernel_neg (z : Fin 3 → ℝ) : newtonKernel (-z) = -newtonKernel z := by
  simp [newtonKernel, vnorm_neg]

theorem vnorm_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < vnorm z :=
  (norm_pos_iff.mpr hz).trans_le (norm_le_vnorm z)

theorem dotProduct_self_ne_zero {z : Fin 3 → ℝ} (hz : z ≠ 0) : z ⬝ᵥ z ≠ 0 := by
  intro h
  have := vnorm_pos hz
  rw [vnorm, h, Real.sqrt_zero] at this
  exact lt_irrefl _ this

theorem contDiff_dotProduct_self : ContDiff ℝ 2 fun x : Fin 3 → ℝ => x ⬝ᵥ x := by
  simp only [dotProduct, Fin.sum_univ_three]
  fun_prop

theorem contDiffAt_newtonKernel {z : Fin 3 → ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 2 newtonKernel z := by
  have hq := contDiff_dotProduct_self.contDiffAt (x := z)
  have hs : ContDiffAt ℝ 2 vnorm z := hq.sqrt (dotProduct_self_ne_zero hz)
  have hd : ContDiffAt ℝ 2 (fun x => 4 * π * vnorm x ^ 3) z := contDiffAt_const.mul (hs.pow 3)
  have hne : 4 * π * vnorm z ^ 3 ≠ 0 :=
    mul_ne_zero (by positivity) (pow_ne_zero 3 (vnorm_pos hz).ne')
  exact (hd.inv hne).smul contDiffAt_id

theorem vnorm_sq (z : Fin 3 → ℝ) : vnorm z ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  rw [vnorm, Real.sq_sqrt (by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)])]
  simp [dotProduct, Fin.sum_univ_three, sq]

/-- `∂ᵢ Kᵢ(z) = 1/(4π|z|³) − 3 zᵢ²/(4π|z|⁵)`. -/
theorem pd_newtonKernel {z : Fin 3 → ℝ} (hz : z ≠ 0) (i : Fin 3) :
    pd i (fun x => newtonKernel x i) z =
      1 / (4 * π * vnorm z ^ 3) - 3 * z i ^ 2 / (4 * π * vnorm z ^ 5) := by
  have hd : DifferentiableAt ℝ (fun x => newtonKernel x i) z :=
    differentiableAt_pi.mp ((contDiffAt_newtonKernel hz).differentiableAt (by norm_num)) i
  have h1 := hasDerivAt_pd hd i
  set w : ℝ → Fin 3 → ℝ := fun t => z + t • unitE i with hw
  have hwd : HasDerivAt w (unitE i) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (unitE i)).const_add z
    simp only [one_smul] at this
    exact this
  have hw0 : w 0 = z := by simp [hw]
  have hq := hasDerivAt_dotProduct hwd hwd
  rw [hw0] at hq
  have hz2 := dotProduct_self_ne_zero hz
  have hs := hq.sqrt (by rw [hw0]; exact hz2)
  have hv : 0 < vnorm z := vnorm_pos hz
  have hp := (hs.pow 3).const_mul (4 * π)
  have hne : 4 * π * √(w 0 ⬝ᵥ w 0) ^ 3 ≠ 0 := by
    rw [hw0]
    exact mul_ne_zero (by positivity) (pow_ne_zero 3 (hv.ne' : √(z ⬝ᵥ z) ≠ 0))
  have hinv := hp.inv hne
  have hc : HasDerivAt (fun t => w t i) 1 0 := by
    have := (hasDerivAt_pi.mp hwd) i
    simpa [unitE] using this
  have h2 := (hinv.mul hc).congr_of_eventuallyEq
    (f₁ := fun t => newtonKernel (z + t • unitE i) i)
    (Eventually.of_forall fun t => rfl)
  rw [h1.unique h2]
  simp only [Pi.inv_apply, Pi.pow_apply, hw0]
  have hzi : unitE i ⬝ᵥ z = z i := by simp [unitE, dotProduct, Pi.single_apply]
  have hiz : z ⬝ᵥ unitE i = z i := by simp [unitE, dotProduct, Pi.single_apply]
  rw [hzi, hiz]
  change _ = 1 / (4 * π * √(z ⬝ᵥ z) ^ 3) - 3 * z i ^ 2 / (4 * π * √(z ⬝ᵥ z) ^ 5)
  have hv' : 0 < √(z ⬝ᵥ z) := hv
  field_simp
  ring

/-- The Newton kernel is divergence-free away from the origin. -/
theorem div3_newtonKernel {z : Fin 3 → ℝ} (hz : z ≠ 0) : div3 newtonKernel z = 0 := by
  rw [dlmf_1_6_21, pd_newtonKernel hz, pd_newtonKernel hz, pd_newtonKernel hz]
  have hv := vnorm_pos hz
  have h2 := vnorm_sq z
  field_simp
  linear_combination 3 * h2

/-- The field of a point source at `y`, cut off near `y` by a bump `φ` (equal to `1` near `y`):
`F = (1 − φ) K(· − y)`. -/
noncomputable def cutSource (y : Fin 3 → ℝ) (φ : ContDiffBump y) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 - φ x) • newtonKernel (x - y)

theorem cutSource_eventually_zero {y : Fin 3 → ℝ} (φ : ContDiffBump y) :
    cutSource y φ =ᶠ[𝓝 y] 0 := by
  filter_upwards [φ.eventuallyEq_one] with x hx
  simp [cutSource, hx]

theorem contDiff_cutSource {y : Fin 3 → ℝ} (φ : ContDiffBump y) :
    ContDiff ℝ 1 (cutSource y φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = y
  · subst hx
    exact (contDiffAt_const (c := (0 : Fin 3 → ℝ))).congr_of_eventuallyEq
      (cutSource_eventually_zero φ)
  · have hK : ContDiffAt ℝ 1 (fun q => newtonKernel (q - y)) x :=
      ((contDiffAt_newtonKernel (sub_ne_zero.mpr hx)).comp x
        (contDiffAt_id.sub contDiffAt_const)).of_le (by norm_num)
    exact (contDiffAt_const.sub φ.contDiff.contDiffAt).smul hK

theorem div3_cutSource {y : Fin 3 → ℝ} (φ : ContDiffBump y) (x : Fin 3 → ℝ) :
    div3 (cutSource y φ) x = -fderiv ℝ φ x (newtonKernel (x - y)) := by
  by_cases hx : x = y
  · subst hx
    rw [div3_congr (cutSource_eventually_zero φ)]
    have h1 : (φ : (Fin 3 → ℝ) → ℝ) =ᶠ[𝓝 x] fun _ => 1 := φ.eventuallyEq_one
    rw [h1.fderiv_eq]
    simp [div3, pd]
  · have hφd : DifferentiableAt ℝ (fun q => 1 - φ q) x :=
      (differentiableAt_const _).sub (φ.contDiff (n := 1).differentiable one_ne_zero x)
    have hKd : DifferentiableAt ℝ (fun q => newtonKernel (q - y)) x :=
      ((contDiffAt_newtonKernel (sub_ne_zero.mpr hx)).comp x
        (contDiffAt_id.sub contDiffAt_const)).differentiableAt (by norm_num)
    have h := dlmf_1_6_25 hφd hKd
    have hdivK : div3 (fun q => newtonKernel (q - y)) x = 0 := by
      have : div3 (fun q => newtonKernel (q - y)) x = div3 newtonKernel (x - y) := by
        unfold div3 pd
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fderiv_comp_sub (f := fun q => newtonKernel q i)]
      rw [this, div3_newtonKernel (sub_ne_zero.mpr hx)]
    have hgrad : grad3 (fun q => 1 - φ q) x = -grad3 φ x := by
      ext i
      simp only [grad3, Pi.neg_apply]
      rw [pd_sub (differentiableAt_const _) (φ.contDiff (n := 1).differentiable one_ne_zero x)]
      simp [pd]
    unfold cutSource
    rw [h, hdivK, hgrad, mul_zero, zero_add, dotProduct_neg, dotProduct_comm,
      ← fderiv_apply_eq_grad]

/-- `∫ −∇φ · K(· − y) = φ(y) = 1`: the source strength. -/
theorem integral_div3_cutSource {y : Fin 3 → ℝ} (φ : ContDiffBump y) :
    ∫ x, div3 (cutSource y φ) x = 1 := by
  have hN := integral_newton (ψ := φ) (φ.contDiff (n := 1)) φ.hasCompactSupport y
  rw [φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)] at hN
  simp_rw [div3_cutSource]
  rw [← hN, ← integral_sub_left_eq_self _ volume y]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [sub_sub_cancel_left, newtonKernel_neg, map_neg, neg_neg]

theorem Rect.closure_openSet (R : Rect) : closure R.openSet = R.closedSet := by
  rw [Rect.openSet, closure_prod_eq, closure_Ioo R.hu.ne, closure_Ioo R.hv.ne]
  rfl

theorem fderiv_bump_eq_zero {y : Fin 3 → ℝ} (φ : ContDiffBump y) {x : Fin 3 → ℝ}
    (hx : φ.rOut < dist x y) : fderiv ℝ φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by
    have := tsupport_fderiv_subset ℝ h
    rw [φ.tsupport_eq, mem_closedBall] at this
    linarith

theorem le_dist_of_coord {x y : Fin 3 → ℝ} (i : Fin 3) : |x i - y i| ≤ dist x y := by
  rw [dist_eq_norm, ← Real.norm_eq_abs, ← Pi.sub_apply]
  exact norm_le_pi_norm (x - y) i

namespace Box3

variable (B : Box3)

theorem face_mem (j : Fin 6) {p : ℝ × ℝ} (hp : p ∈ closure (B.face j).D) :
    (B.face j).Φ p ∈ Icc B.a B.b ∧
      ∃ i, (B.face j).Φ p i = B.a i ∨ (B.face j).Φ p i = B.b i := by
  have h0 := B.hab 0
  have h1 := B.hab 1
  have h2 := B.hab 2
  fin_cases j <;>
  · simp only [face, SurfacePiece.ofRect_D, Rect.closure_openSet, Rect.closedSet, rect, mem_prod,
      mem_Icc] at hp
    simp only [face, SurfacePiece.ofRect, affineFace_apply, e, Pi.smul_apply, smul_eq_mul]
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith
    · fin_cases i <;> simp <;> linarith
    · simp [Fin.exists_fin_succ]

theorem image_subset {x : Fin 3 → ℝ} (hx : x ∈ B.surface.image) :
    x ∈ Icc B.a B.b ∧ ∃ i, x i = B.a i ∨ x i = B.b i := by
  simp only [ClosedSurface.image, mem_iUnion] at hx
  obtain ⟨j, p, hp, rfl⟩ := hx
  exact B.face_mem j hp

end Box3

namespace Box3

variable (B : Box3)

theorem a_le_b : B.a ≤ B.b := fun i => (B.hab i).le

/-- The solid angle of the box seen from an interior point is `1`. -/
theorem windingNumber_of_mem_interior {y : Fin 3 → ℝ} (hy : ∀ i, B.a i < y i ∧ y i < B.b i) :
    B.surface.windingNumber y = 1 := by
  set r := min (min (y 0 - B.a 0) (B.b 0 - y 0))
    (min (min (y 1 - B.a 1) (B.b 1 - y 1)) (min (y 2 - B.a 2) (B.b 2 - y 2))) with hr
  have hr0 : 0 < r := by
    have := hy 0; have := hy 1; have := hy 2
    simp only [hr, lt_min_iff, sub_pos]
    tauto
  have hri : ∀ i, r ≤ y i - B.a i ∧ r ≤ B.b i - y i := by
    intro i
    fin_cases i <;> simp only [hr] <;> constructor <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, min_le_iff, le_refl, true_or, or_true]
  let φ : ContDiffBump y := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hfar : ∀ x, (∃ i, B.a i ≥ x i ∨ x i ≥ B.b i) → φ.rOut < dist x y := by
    rintro x ⟨i, hi⟩
    have h1 := le_dist_of_coord (x := x) (y := y) i
    have h2 := hri i
    show r / 2 < _
    rcases hi with hi | hi
    · rw [abs_sub_comm, abs_of_pos (by linarith)] at h1; linarith
    · rw [abs_of_pos (by linarith)] at h1; linarith
  have hS : EqOn (cutSource y φ) (fun x => newtonKernel (x - y)) B.surface.image := by
    intro x hx
    obtain ⟨-, i, hi⟩ := B.image_subset hx
    have := hfar x ⟨i, by rcases hi with hi | hi <;> [exact Or.inl hi.le; exact Or.inr hi.ge]⟩
    simp [cutSource, φ.zero_of_le_dist this.le]
  rw [ClosedSurface.windingNumber, ← B.surface.flux_congr hS, surface_flux,
    ← dlmf_1_6_58 (contDiff_cutSource φ) B.a_le_b,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_, integral_div3_cutSource]
  rw [div3_cutSource, fderiv_bump_eq_zero φ (hfar x ?_), _root_.zero_apply, neg_zero]
  simp only [mem_Icc, Pi.le_def, not_and_or, not_forall, not_le] at hx
  rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact ⟨i, Or.inl hi.le⟩
  · exact ⟨i, Or.inr hi.le⟩

/-- The solid angle of the box seen from an exterior point is `0`. -/
theorem windingNumber_of_notMem {y : Fin 3 → ℝ} (hy : y ∉ Icc B.a B.b) :
    B.surface.windingNumber y = 0 := by
  simp only [mem_Icc, Pi.le_def, not_and_or, not_forall, not_le] at hy
  obtain ⟨d, hd0, i, hdi⟩ : ∃ d > 0, ∃ i, ∀ x ∈ Icc B.a B.b, d ≤ |x i - y i| := by
    rcases hy with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine ⟨B.a i - y i, by linarith, i, fun x hx => ?_⟩
      rw [abs_of_pos (by linarith [hx.1 i])]
      linarith [hx.1 i]
    · refine ⟨y i - B.b i, by linarith, i, fun x hx => ?_⟩
      rw [abs_sub_comm, abs_of_pos (by linarith [hx.2 i])]
      linarith [hx.2 i]
  let φ : ContDiffBump y := ⟨d / 4, d / 2, by positivity, by linarith⟩
  have hfar : ∀ x ∈ Icc B.a B.b, φ.rOut < dist x y := fun x hx => by
    show d / 2 < _
    linarith [hdi x hx, le_dist_of_coord (x := x) (y := y) i]
  have hS : EqOn (cutSource y φ) (fun x => newtonKernel (x - y)) B.surface.image := by
    intro x hx
    simp [cutSource, φ.zero_of_le_dist (hfar x (B.image_subset hx).1).le]
  rw [ClosedSurface.windingNumber, ← B.surface.flux_congr hS, surface_flux,
    ← dlmf_1_6_58 (contDiff_cutSource φ) B.a_le_b]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
  rw [div3_cutSource, fderiv_bump_eq_zero φ (hfar x hx), _root_.zero_apply, neg_zero]

/-- **The boundary of the box bounds it with the outward orientation.** -/
theorem boundsOutward : B.surface.BoundsOutward (Icc B.a B.b) := by
  have hae : (Set.pi univ fun i => Ioo (B.a i) (B.b i)) =ᵐ[volume] Icc B.a B.b := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioo_ae_eq_Icc
  filter_upwards [hae] with y hy
  by_cases hyI : y ∈ Icc B.a B.b
  · have hyo : y ∈ Set.pi univ fun i => Ioo (B.a i) (B.b i) := by
      have : (y ∈ Set.pi univ fun i => Ioo (B.a i) (B.b i)) = (y ∈ Icc B.a B.b) := hy
      rw [this]
      exact hyI
    rw [indicator_of_mem hyI, Pi.one_apply]
    exact B.windingNumber_of_mem_interior fun i => hyo i (mem_univ i)
  · rw [indicator_of_notMem hyI]
    exact B.windingNumber_of_notMem hyI

/-- **Gauss's theorem for the box from the general theorem** `dlmf_1_6_58_general`: for `F`
continuously differentiable on an open set containing the closed box,
`∭_{[a, b]} ∇ · F dV = ∬_{∂[a, b]} F · dS`. -/
theorem gauss {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hBU : Icc B.a B.b ⊆ U)
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiffOn ℝ 1 F U) :
    ∫ x in Icc B.a B.b, div3 F x = B.surface.flux F :=
  dlmf_1_6_58_general B.surface (Metric.isBounded_Icc B.a B.b) measurableSet_Icc B.boundsOutward hU
    (union_subset (by rw [closure_Icc]; exact hBU) fun x hx => hBU (B.image_subset hx).1) hF

end Box3

/-! ### The solid angle is locally constant off the surface -/

namespace ClosedSurface

variable (S : ClosedSurface)

theorem exists_ball_disjoint {y₀ : Fin 3 → ℝ} (hy₀ : y₀ ∉ S.image) :
    ∃ r > 0, ∀ x ∈ S.image, 2 * r ≤ dist x y₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S.isCompact_image.isClosed.isOpen_compl y₀ hy₀
  refine ⟨ε / 2, half_pos hε, fun x hx => ?_⟩
  by_contra h
  exact hball (by rw [mem_ball]; linarith) hx

/-- The solid angle is continuous off the surface (dominated convergence). -/
theorem continuousAt_windingNumber {y₀ : Fin 3 → ℝ} (hy₀ : y₀ ∉ S.image) :
    ContinuousAt S.windingNumber y₀ := by
  obtain ⟨r, hr, hfar⟩ := S.exists_ball_disjoint hy₀
  unfold windingNumber flux
  refine tendsto_finsetSum _ fun j _ => ?_
  set P := S.piece j
  have hmem : ∀ p ∈ P.D, P.Φ p ∈ S.image := fun p hp =>
    mem_iUnion.mpr ⟨j, p, subset_closure hp, rfl⟩
  obtain ⟨L, hL⟩ := P.isCompact_closure_D.exists_bound_of_continuousOn
    (P.continuousOn_normal.mono P.closure_D_subset_U)
  have : IsFiniteMeasure (volume.restrict P.D) := ⟨by
    rw [Measure.restrict_apply_univ]; exact P.volume_D_lt_top⟩
  have hΦm : AEMeasurable P.Φ (volume.restrict P.D) :=
    (P.hΦ.continuousOn.mono (subset_closure.trans P.closure_D_subset_U)).aemeasurable
      P.measurableSet_D
  have hNm : AEMeasurable P.normal (volume.restrict P.D) :=
    (P.continuousOn_normal.mono (subset_closure.trans P.closure_D_subset_U)).aemeasurable
      P.measurableSet_D
  have hdot : Measurable fun w : (Fin 3 → ℝ) × (Fin 3 → ℝ) => w.1 ⬝ᵥ w.2 :=
    (continuous_fst.dotProduct continuous_snd).measurable
  unfold SurfacePiece.flux fluxIntegral
  refine continuousAt_of_dominated (bound := fun _ => 3 * ((4 * π)⁻¹ * r ^ (-2 : ℝ) * max L 0))
    (Eventually.of_forall fun y => ?_) ?_ (integrable_const _) ?_
  · exact (hdot.comp_aemeasurable ((measurable_newtonKernel.comp_aemeasurable
      (hΦm.sub aemeasurable_const)).prodMk hNm)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds y₀ hr] with y hy
    filter_upwards [ae_restrict_mem P.measurableSet_D] with p hp
    have hd : r ≤ ‖P.Φ p - y‖ := by
      have := hfar _ (hmem p hp)
      rw [mem_ball] at hy
      rw [← dist_eq_norm]
      linarith [dist_triangle (P.Φ p) y y₀]
    have hK : ‖newtonKernel (P.Φ p - y)‖ ≤ (4 * π)⁻¹ * r ^ (-2 : ℝ) := by
      refine (norm_newtonKernel_le _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.rpow_le_rpow_of_nonpos hr hd (by norm_num)
    have hN : ‖P.normal p‖ ≤ max L 0 := (hL p (subset_closure hp)).trans (le_max_left _ _)
    rw [Real.norm_eq_abs]
    refine (abs_dotProduct_le _ _).trans ?_
    gcongr
    exact hN
  · filter_upwards [ae_restrict_mem P.measurableSet_D] with p hp
    have hne : P.Φ p - y₀ ≠ 0 := fun h => by
      have := hfar _ (hmem p hp)
      rw [sub_eq_zero.mp h, dist_self] at this
      linarith
    exact ((continuous_id.dotProduct continuous_const).continuousAt).comp
      (((contDiffAt_newtonKernel hne).continuousAt).comp
        (continuous_const.sub continuous_id).continuousAt)

end ClosedSurface

/-- The test field along the segment from `y₀` to `y₀ + v`:
`x ↦ ∫₀¹ ρ(x − y₀ − τ v) dτ · v`.  Its divergence is `ρ(x − y₀) − ρ(x − y₀ − v)`. -/
noncomputable def segField (ρ : (Fin 3 → ℝ) → ℝ) (y₀ v : Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  ∫ τ in (0 : ℝ)..1, ρ (x - y₀ - τ • v) • v

theorem contDiff_segIntegrand {ρ : (Fin 3 → ℝ) → ℝ} (hρ : ContDiff ℝ 1 ρ) (y₀ v : Fin 3 → ℝ) :
    ContDiff ℝ 1 fun p : (Fin 3 → ℝ) × ℝ => ρ (p.1 - y₀ - p.2 • v) • v :=
  (hρ.comp ((contDiff_fst.sub contDiff_const).sub (contDiff_snd.smul contDiff_const))).smul
    contDiff_const

theorem contDiff_segField {ρ : (Fin 3 → ℝ) → ℝ} (hρ : ContDiff ℝ 1 ρ) (y₀ v : Fin 3 → ℝ) :
    ContDiff ℝ 1 (segField ρ y₀ v) :=
  contDiff_intervalIntegral_param (contDiff_segIntegrand hρ y₀ v)

theorem div3_segField {ρ : (Fin 3 → ℝ) → ℝ} (hρ : ContDiff ℝ 1 ρ) (y₀ v x : Fin 3 → ℝ) :
    div3 (segField ρ y₀ v) x = ρ (x - y₀) - ρ (x - y₀ - v) := by
  have hφ := contDiff_segIntegrand hρ y₀ v
  have hρd := hρ.differentiable one_ne_zero
  have hD : HasFDerivAt (segField ρ y₀ v)
      (∫ τ in (0 : ℝ)..1, fderiv ℝ (fun y => ρ (y - y₀ - τ • v) • v) x) x :=
    hasFDerivAt_intervalIntegral_param hφ x
  have hslice : ∀ τ : ℝ, ∀ w, fderiv ℝ (fun y => ρ (y - y₀ - τ • v) • v) x w =
      fderiv ℝ ρ (x - y₀ - τ • v) w • v := by
    intro τ w
    have h1 : HasFDerivAt (fun y => ρ (y - y₀ - τ • v))
        ((fderiv ℝ ρ (x - y₀ - τ • v)).comp (ContinuousLinearMap.id ℝ _)) x :=
      (hρd _).hasFDerivAt.comp x (((hasFDerivAt_id x).sub_const y₀).sub_const (τ • v))
    rw [(h1.smul_const v).fderiv]
    simp
  have hc : Continuous fun τ : ℝ => fderiv ℝ (fun y => ρ (y - y₀ - τ • v) • v) x := by
    have e : (fun τ : ℝ => fderiv ℝ (fun y => ρ (y - y₀ - τ • v) • v) x) =
        fun τ => (fderiv ℝ (fun p : (Fin 3 → ℝ) × ℝ => ρ (p.1 - y₀ - p.2 • v) • v) (x, τ)).comp
          ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod 0) :=
      funext fun τ => fderiv_slice_eq hφ x τ
    rw [e]
    exact ((hφ.continuous_fderiv one_ne_zero).clm_comp continuous_const).comp
      (continuous_const.prodMk continuous_id)
  have hint := hc.intervalIntegrable (μ := volume) 0 1
  have hρc : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv one_ne_zero
  have hcomp : ∀ i : Fin 3, pd i (fun q => segField ρ y₀ v q i) x =
      ∫ τ in (0 : ℝ)..1, fderiv ℝ ρ (x - y₀ - τ • v) (unitE i) * v i := by
    intro i
    rw [pd_apply_component hD.differentiableAt, hD.fderiv,
      ContinuousLinearMap.intervalIntegral_apply hint]
    have hint2 : IntervalIntegrable
        (fun τ => fderiv ℝ (fun y => ρ (y - y₀ - τ • v) • v) x (unitE i)) volume 0 1 :=
      (hc.clm_apply continuous_const).intervalIntegrable _ _
    have h2 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).intervalIntegral_comp_comm
        hint2
    simp only [ContinuousLinearMap.proj_apply] at h2
    rw [← h2]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [hslice, Pi.smul_apply, smul_eq_mul]
  have hcont : ∀ i : Fin 3, Continuous fun τ : ℝ => fderiv ℝ ρ (x - y₀ - τ • v) (unitE i) * v i :=
    fun i => ((hρc.comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
      continuous_const).mul continuous_const
  rw [div3]
  simp_rw [hcomp]
  rw [← intervalIntegral.integral_finsetSum fun i _ => (hcont i).intervalIntegrable 0 1]
  have hG : ∀ τ, HasDerivAt (fun τ : ℝ => -ρ (x - y₀ - τ • v))
      (∑ i, fderiv ℝ ρ (x - y₀ - τ • v) (unitE i) * v i) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => x - y₀ - τ • v) (-v) τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_sub (x - y₀)
    have h2 := ((hρd _).hasFDerivAt.comp_hasDerivAt τ h1).neg
    convert h2 using 1
    · rfl
    rw [map_neg, neg_neg]
    generalize x - y₀ - τ • v = p
    conv_rhs => rw [← dlmf_1_6_13 v]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hG τ)
    ((continuous_finsetSum _ fun i _ => hcont i).intervalIntegrable 0 1)]
  simp
  ring

namespace ClosedSurface

variable (S : ClosedSurface)

theorem normed_eq_zero (φ : ContDiffBump (0 : Fin 3 → ℝ)) {z : Fin 3 → ℝ} (hz : φ.rOut ≤ ‖z‖) :
    φ.normed volume z = 0 := by
  rw [← Function.notMem_support, φ.support_normed_eq, mem_ball, dist_zero_right, not_lt]
  exact hz

theorem flux_zero : S.flux (fun _ => 0) = 0 := by
  simp [flux, SurfacePiece.flux, fluxIntegral]

theorem segField_eq_zero (φ : ContDiffBump (0 : Fin 3 → ℝ)) {y₀ v x : Fin 3 → ℝ}
    (hx : ∀ τ ∈ Icc (0 : ℝ) 1, φ.rOut ≤ ‖x - y₀ - τ • v‖) :
    segField (φ.normed volume) y₀ v x = 0 := by
  simp only [segField]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : Fin 3 → ℝ)) fun τ hτ => by
    rw [uIcc_of_le zero_le_one] at hτ
    show φ.normed volume (x - y₀ - τ • v) • v = 0
    rw [normed_eq_zero φ (hx τ hτ), zero_smul]]
  simp

theorem hasCompactSupport_segField (φ : ContDiffBump (0 : Fin 3 → ℝ)) (y₀ v : Fin 3 → ℝ) :
    HasCompactSupport (segField (φ.normed volume) y₀ v) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ)
    (‖y₀‖ + ‖v‖ + φ.rOut)) fun x hx => segField_eq_zero φ fun τ hτ => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  have h1 : ‖τ • v‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hτ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
  have h2 := norm_sub_norm_le x (y₀ + τ • v)
  have h3 := norm_add_le y₀ (τ • v)
  rw [show x - (y₀ + τ • v) = x - y₀ - τ • v by abel] at h2
  linarith

/-- The flux of the segment test field is the difference of the bump averages of `W` at the
two ends of the segment. -/
theorem flux_segField (φ : ContDiffBump (0 : Fin 3 → ℝ)) (y₀ v : Fin 3 → ℝ) :
    S.flux (segField (φ.normed volume) y₀ v) =
      (∫ x, φ.normed volume (x - y₀) * S.windingNumber x) -
        ∫ x, φ.normed volume (x - (y₀ + v)) * S.windingNumber x := by
  set ρ := φ.normed volume
  have hρ : ContDiff ℝ 1 ρ := φ.contDiff_normed
  have h := S.flux_eq_integral (contDiff_segField hρ y₀ v) (hasCompactSupport_segField φ y₀ v)
  simp_rw [div3_segField hρ, sub_mul] at h
  have hi₀ := S.integrable_mul_windingNumber (ψ := fun x => ρ (x - y₀))
    (hρ.continuous.comp (continuous_id.sub continuous_const))
    (φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subRight y₀))
  have hi₁ := S.integrable_mul_windingNumber (ψ := fun x => ρ (x - (y₀ + v)))
    (hρ.continuous.comp (continuous_id.sub continuous_const))
    (φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subRight (y₀ + v)))
  have e : ∀ x, x - y₀ - v = x - (y₀ + v) := fun x => by abel
  simp_rw [e] at h
  rw [integral_sub hi₀ hi₁] at h
  exact h

/-- Averages of `W` around the ends of a segment that stays away from the surface agree. -/
theorem integral_bump_shift (φ : ContDiffBump (0 : Fin 3 → ℝ)) {y₀ v : Fin 3 → ℝ}
    (hfar : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x ∈ S.image, φ.rOut < dist x (y₀ + τ • v)) :
    ∫ x, φ.normed volume (x - y₀) * S.windingNumber x =
      ∫ x, φ.normed volume (x - (y₀ + v)) * S.windingNumber x := by
  have hFS : EqOn (segField (φ.normed volume) y₀ v) (fun _ => 0) S.image := fun x hx =>
    segField_eq_zero φ fun τ hτ => by
      have := hfar τ hτ x hx
      rw [dist_eq_norm, show x - (y₀ + τ • v) = x - y₀ - τ • v by abel] at this
      exact this.le
  have h := S.flux_segField φ y₀ v
  rw [S.flux_congr hFS, flux_zero] at h
  linarith

/-- A bump average of `W` is close to `W y` when `W` is close to `W y` on the bump's support. -/
theorem abs_integral_bump_sub_le (φ : ContDiffBump (0 : Fin 3 → ℝ)) {y : Fin 3 → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hW : ∀ x, dist x y < φ.rOut → |S.windingNumber x - S.windingNumber y| ≤ ε) :
    |(∫ x, φ.normed volume (x - y) * S.windingNumber x) - S.windingNumber y| ≤ ε := by
  set ρ := φ.normed volume
  have hρc : Continuous fun x => ρ (x - y) :=
    φ.continuous_normed.comp (continuous_id.sub continuous_const)
  have hρs : HasCompactSupport fun x => ρ (x - y) :=
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subRight y)
  have hi := S.integrable_mul_windingNumber hρc hρs
  have hρi : Integrable fun x => ρ (x - y) := hρc.integrable_of_hasCompactSupport hρs
  have h1 : ∫ x, ρ (x - y) = 1 := by
    rw [integral_sub_right_eq_self (fun x => ρ x) y]
    exact φ.integral_normed
  have e : (∫ x, ρ (x - y) * S.windingNumber x) - S.windingNumber y =
      ∫ x, ρ (x - y) * (S.windingNumber x - S.windingNumber y) := by
    simp_rw [mul_sub]
    rw [integral_sub hi (hρi.mul_const _), integral_mul_const, h1, one_mul]
  rw [e]
  calc |∫ x, ρ (x - y) * (S.windingNumber x - S.windingNumber y)|
      ≤ ∫ x, |ρ (x - y) * (S.windingNumber x - S.windingNumber y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, ρ (x - y) * ε := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (hρi.mul_const ε) (ae_of_all _ fun x => ?_)
        show |ρ (x - y) * _| ≤ ρ (x - y) * ε
        rw [abs_mul, abs_of_nonneg (φ.nonneg_normed _)]
        by_cases hx : dist x y < φ.rOut
        · exact mul_le_mul_of_nonneg_left (hW x hx) (φ.nonneg_normed _)
        · rw [normed_eq_zero φ (by rw [← dist_eq_norm]; exact not_lt.mp hx), zero_mul]
          exact mul_nonneg (φ.nonneg_normed _) hε
    _ = ε := by rw [integral_mul_const, h1, one_mul]

/-- `W` takes the same value at the ends of a segment that stays at distance `δ > 0` from the
surface. -/
theorem windingNumber_eq_of_segment {y₀ v : Fin 3 → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfar : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x ∈ S.image, δ ≤ dist x (y₀ + τ • v)) :
    S.windingNumber y₀ = S.windingNumber (y₀ + v) := by
  have hy₀ : y₀ ∉ S.image := fun h => by
    have := hfar 0 ⟨le_refl _, zero_le_one⟩ y₀ h
    simp at this
    linarith
  have hy₁ : y₀ + v ∉ S.image := fun h => by
    have := hfar 1 ⟨zero_le_one, le_refl _⟩ (y₀ + v) h
    simp at this
    linarith
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
  have hrδ : r < δ := by
    have := min_le_right (min η₀ η₁) δ
    simp only [hr]; linarith
  have hshift := S.integral_bump_shift φ fun τ hτ x hx => hrδ.trans_le (hfar τ hτ x hx)
  have e₀ := S.abs_integral_bump_sub_le φ (half_pos hε).le fun x hx =>
    (h₀ (hx.trans hrη₀)).le
  have e₁ := S.abs_integral_bump_sub_le φ (half_pos hε).le fun x hx =>
    (h₁ (hx.trans hrη₁)).le
  rw [hshift] at e₀
  rw [Real.dist_eq]
  have := abs_sub_le (S.windingNumber y₀)
    (∫ x, φ.normed volume (x - (y₀ + v)) * S.windingNumber x) (S.windingNumber (y₀ + v))
  rw [abs_sub_comm] at e₀
  linarith

/-- **The solid angle is locally constant off the surface.** -/
theorem eventually_windingNumber_eq {y₀ : Fin 3 → ℝ} (hy₀ : y₀ ∉ S.image) :
    ∀ᶠ y in 𝓝 y₀, S.windingNumber y = S.windingNumber y₀ := by
  obtain ⟨r, hr, hfar⟩ := S.exists_ball_disjoint hy₀
  filter_upwards [ball_mem_nhds y₀ hr] with y hy
  rw [mem_ball] at hy
  have := S.windingNumber_eq_of_segment (v := y - y₀) hr fun τ hτ x hx => by
    have h1 := hfar x hx
    have h2 : dist (y₀ + τ • (y - y₀)) y₀ ≤ dist y y₀ := by
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
    linarith [dist_triangle x (y₀ + τ • (y - y₀)) y₀]
  rw [add_sub_cancel] at this
  exact this.symm

/-- **The solid angle is constant on every connected set off the surface.** -/
theorem windingNumber_eq_of_isPreconnected {s : Set (Fin 3 → ℝ)} (hs : IsPreconnected s)
    (hsub : s ⊆ S.imageᶜ) {x y : Fin 3 → ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    S.windingNumber x = S.windingNumber y := by
  set A := {z | z ∉ S.image ∧ S.windingNumber z = S.windingNumber x}
  set B := {z | z ∉ S.image ∧ S.windingNumber z ≠ S.windingNumber x}
  have hopen : ∀ (P : ℝ → Prop), IsOpen {z | z ∉ S.image ∧ P (S.windingNumber z)} := by
    intro P
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hz, hPz⟩
    filter_upwards [S.isCompact_image.isClosed.isOpen_compl.mem_nhds hz,
      S.eventually_windingNumber_eq hz] with w hw hwz
    exact ⟨hw, by rw [hwz]; exact hPz⟩
  have hsAB : s ⊆ A ∪ B := fun z hz => by
    by_cases h : S.windingNumber z = S.windingNumber x
    · exact Or.inl ⟨hsub hz, h⟩
    · exact Or.inr ⟨hsub hz, h⟩
  have := hs.subset_left_of_subset_union (hopen fun t => t = S.windingNumber x)
    (hopen fun t => t ≠ S.windingNumber x) (Set.disjoint_left.mpr fun z hA hB => hB.2 hA.2)
    hsAB ⟨x, hx, hsub hx, rfl⟩ hy
  exact this.2.symm

end ClosedSurface

/-! ### The sphere -/

theorem sphereParam_apply (ρ θ φ : ℝ) :
    sphereParam ρ (θ, φ) = ![ρ * Real.sin θ * Real.cos φ, ρ * Real.sin θ * Real.sin φ,
      ρ * Real.cos θ] := rfl

theorem contDiff_sphereParam (ρ : ℝ) : ContDiff ℝ 2 (sphereParam ρ) := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp only [sphereParam, surfaceParam] <;> simp <;> fun_prop

theorem sphereParam_dot_self (ρ : ℝ) (p : ℝ × ℝ) :
    sphereParam ρ p ⬝ᵥ sphereParam ρ p = ρ ^ 2 := by
  obtain ⟨θ, φ⟩ := p
  simp only [sphereParam_apply, dotProduct, Fin.sum_univ_three]
  simp
  linear_combination (ρ ^ 2 * Real.sin θ ^ 2) * Real.sin_sq_add_cos_sq φ +
    ρ ^ 2 * Real.sin_sq_add_cos_sq θ

theorem vnorm_sphereParam {ρ : ℝ} (hρ : 0 < ρ) (p : ℝ × ℝ) : vnorm (sphereParam ρ p) = ρ := by
  rw [vnorm, sphereParam_dot_self, Real.sqrt_sq hρ.le]

/-- `T_θ × T_φ = ρ sin θ · Φ(θ, φ)` for the sphere `Φ = sphereParam ρ`. -/
theorem cross_tangent_sphereParam (ρ θ φ : ℝ) :
    tangentU (sphereParam ρ) (θ, φ) ⨯₃ tangentV (sphereParam ρ) (θ, φ) =
      (ρ * Real.sin θ) • sphereParam ρ (θ, φ) := by
  have hx : DifferentiableAt ℝ
      (Function.uncurry fun θ φ => ρ * Real.sin θ * Real.cos φ) (θ, φ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => ρ * Real.sin p.1 * Real.cos p.2) (θ, φ)
    fun_prop
  have hy : DifferentiableAt ℝ
      (Function.uncurry fun θ φ => ρ * Real.sin θ * Real.sin φ) (θ, φ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => ρ * Real.sin p.1 * Real.sin p.2) (θ, φ)
    fun_prop
  have hz : DifferentiableAt ℝ (Function.uncurry fun θ (_ : ℝ) => ρ * Real.cos θ) (θ, φ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => ρ * Real.cos p.1) (θ, φ)
    fun_prop
  rw [sphereParam, tangentU_surfaceParam hx hy hz, tangentV_surfaceParam hx hy hz]
  have a1 : partialX (fun θ φ => ρ * Real.sin θ * Real.cos φ) θ φ =
      ρ * Real.cos θ * Real.cos φ :=
    (((Real.hasDerivAt_sin θ).const_mul ρ).mul_const (Real.cos φ)).deriv
  have a2 : partialY (fun θ φ => ρ * Real.sin θ * Real.cos φ) θ φ =
      ρ * Real.sin θ * -Real.sin φ :=
    ((Real.hasDerivAt_cos φ).const_mul (ρ * Real.sin θ)).deriv
  have b1 : partialX (fun θ φ => ρ * Real.sin θ * Real.sin φ) θ φ =
      ρ * Real.cos θ * Real.sin φ :=
    (((Real.hasDerivAt_sin θ).const_mul ρ).mul_const (Real.sin φ)).deriv
  have b2 : partialY (fun θ φ => ρ * Real.sin θ * Real.sin φ) θ φ =
      ρ * Real.sin θ * Real.cos φ :=
    ((Real.hasDerivAt_sin φ).const_mul (ρ * Real.sin θ)).deriv
  have c1 : partialX (fun θ (_ : ℝ) => ρ * Real.cos θ) θ φ = ρ * -Real.sin θ :=
    ((Real.hasDerivAt_cos θ).const_mul ρ).deriv
  have c2 : partialY (fun θ (_ : ℝ) => ρ * Real.cos θ) θ φ = 0 :=
    deriv_const φ (ρ * Real.cos θ)
  rw [a1, a2, b1, b2, c1, c2]
  ext i
  fin_cases i
  · simp [cross_apply, surfaceParam]
  · simp [cross_apply, surfaceParam]
  · simp [cross_apply, surfaceParam]
    linear_combination (ρ ^ 2 * Real.sin θ * Real.cos θ) * Real.sin_sq_add_cos_sq φ

/-- A sphere of radius `ρ > 0` centred at `c`. -/
structure Sphere3 where
  c : Fin 3 → ℝ
  ρ : ℝ
  hρ : 0 < ρ

namespace Sphere3

variable (Sp : Sphere3)

/-- The parameter rectangle `[0, π] × [0, 2π]`. -/
noncomputable def rect : Rect := ⟨0, π, 0, 2 * π, Real.pi_pos, by positivity⟩

/-- The spherical-coordinate parametrization `c + ρ (sin θ cos φ, sin θ sin φ, cos θ)`. -/
noncomputable def param (p : ℝ × ℝ) : Fin 3 → ℝ := Sp.c + sphereParam Sp.ρ p

theorem contDiff_param : ContDiff ℝ 2 Sp.param :=
  contDiff_const.add (contDiff_sphereParam Sp.ρ)

/-- The sphere as a single surface piece. -/
noncomputable def piece : SurfacePiece := .ofRect Sphere3.rect Sp.param Sp.contDiff_param

theorem lineIntegral_const_path (A : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (P : Fin 3 → ℝ) :
    lineIntegral A (fun _ => P) 0 1 = 0 := by
  simp [lineIntegral]

/-- The boundary of the parameter rectangle maps to the two poles (traversed with zero speed) and
to the meridian `φ = 0`, traversed once in each direction. -/
theorem boundaryIntegral_piece {A : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hA : Continuous A) :
    Sp.piece.boundaryIntegral A = 0 := by
  rw [piece, SurfacePiece.boundaryIntegral_ofRect _ _ _ hA]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  set M : ℝ → Fin 3 → ℝ := fun s => Sp.param (s * π, 0) with hM
  have e0 : Sphere3.rect.edge Sp.param 0 = M := by
    funext s
    simp [Rect.edge, Rect.corner, rect, hM]
  have e1 : Sphere3.rect.edge Sp.param 1 = fun _ => Sp.param (π, 0) := by
    funext s
    simp only [Rect.edge, Rect.corner, rect, param]
    congr 1
    ext i
    fin_cases i <;> simp [sphereParam_apply]
  have e2 : Sphere3.rect.edge Sp.param 2 = fun s => M (1 - s) := by
    funext s
    simp only [Rect.edge, Rect.corner, rect, hM, param]
    congr 1
    have h1 : π + s * (0 - π) = (1 - s) * π := by ring
    have h2 : 2 * π + s * (2 * π - 2 * π) = 2 * π := by ring
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul, h1, h2, sphereParam_apply,
      Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  have e3 : Sphere3.rect.edge Sp.param 3 = fun _ => Sp.param (0, 0) := by
    funext s
    simp only [Rect.edge, Rect.corner, rect, param]
    congr 1
    ext i
    fin_cases i <;> simp [sphereParam_apply]
  rw [e0, e1, e2, e3, lineIntegral_const_path, lineIntegral_const_path,
    lineIntegral_reverse01 A M]
  ring

/-- The sphere as a closed surface. -/
noncomputable def surface : ClosedSurface where
  m := 1
  piece := fun _ => Sp.piece
  closed A hA := by
    rw [Fin.sum_univ_one]
    exact Sp.boundaryIntegral_piece hA.continuous

theorem image_subset {x : Fin 3 → ℝ} (hx : x ∈ Sp.surface.image) : vnorm (x - Sp.c) = Sp.ρ := by
  simp only [ClosedSurface.image, mem_iUnion] at hx
  obtain ⟨_, p, -, rfl⟩ := hx
  show vnorm (Sp.c + sphereParam Sp.ρ p - Sp.c) = Sp.ρ
  rw [add_sub_cancel_left, vnorm_sphereParam Sp.hρ]

/-- The solid angle of the sphere seen from its centre is `1`. -/
theorem windingNumber_center : Sp.surface.windingNumber Sp.c = 1 := by
  have hρ := Sp.hρ
  rw [ClosedSurface.windingNumber, ClosedSurface.flux]
  show ∑ _j : Fin 1, Sp.piece.flux (fun x => newtonKernel (x - Sp.c)) = 1
  rw [Fin.sum_univ_one]
  unfold piece SurfacePiece.flux fluxIntegral
  rw [SurfacePiece.ofRect_D]
  have htan : ∀ p : ℝ × ℝ, tangentU Sp.param p = tangentU (sphereParam Sp.ρ) p ∧
      tangentV Sp.param p = tangentV (sphereParam Sp.ρ) p := fun p => by
    simp only [tangentU, tangentV]
    rw [show Sp.param = fun p => Sp.c + sphereParam Sp.ρ p from rfl, fderiv_const_add]
    exact ⟨rfl, rfl⟩
  have hint : ∀ p : ℝ × ℝ, newtonKernel ((SurfacePiece.ofRect Sphere3.rect Sp.param
      Sp.contDiff_param).Φ p - Sp.c) ⬝ᵥ (tangentU (SurfacePiece.ofRect Sphere3.rect Sp.param
      Sp.contDiff_param).Φ p ⨯₃ tangentV (SurfacePiece.ofRect Sphere3.rect Sp.param
      Sp.contDiff_param).Φ p) = Real.sin p.1 / (4 * π) := by
    intro p
    obtain ⟨θ, φ⟩ := p
    simp only [SurfacePiece.ofRect]
    rw [(htan _).1, (htan _).2, cross_tangent_sphereParam]
    simp only [param, add_sub_cancel_left, newtonKernel, vnorm_sphereParam hρ, smul_dotProduct,
      dotProduct_smul, sphereParam_dot_self, smul_eq_mul]
    field_simp
  simp_rw [hint]
  show ∫ p in Ioo 0 π ×ˢ Ioo 0 (2 * π), Real.sin p.1 / (4 * π) = 1
  rw [setIntegral_Ioo_prod_angle (fun x => Real.sin x / (4 * π)) Real.pi_pos.le,
    intervalIntegral.integral_div, integral_sin, Real.cos_zero, Real.cos_pi]
  field_simp
  ring

end Sphere3

/-! ### Decay of the solid angle, and the ball -/

theorem vnorm_add_le (a b : Fin 3 → ℝ) : vnorm (a + b) ≤ vnorm a + vnorm b := by
  rw [dlmf_1_6_3, dlmf_1_6_3, dlmf_1_6_3, WithLp.toLp_add]
  exact norm_add_le _ _

theorem vnorm_le_sqrt_three_mul_norm (v : Fin 3 → ℝ) : vnorm v ≤ √3 * ‖v‖ := by
  have h : ∀ i, v i ^ 2 ≤ ‖v‖ ^ 2 := fun i => by
    have h0 := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h0
    have h1 := pow_le_pow_left₀ (abs_nonneg (v i)) h0 2
    rwa [sq_abs] at h1
  rw [vnorm, ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [h 0, h 1, h 2]

namespace ClosedSurface

variable (S : ClosedSurface)

/-- **Decay of the solid angle**: `|W(y)| ≤ C R⁻²` when `y` is at distance `≥ R` from the
surface. -/
theorem exists_abs_windingNumber_le :
    ∃ C : ℝ, ∀ y : Fin 3 → ℝ, ∀ R : ℝ, 0 < R → (∀ x ∈ S.image, R ≤ dist x y) →
      |S.windingNumber y| ≤ C * R ^ (-2 : ℝ) := by
  have hL : ∀ j, ∃ L : ℝ, ∀ x ∈ closure (S.piece j).D, ‖(S.piece j).normal x‖ ≤ L := fun j =>
    (S.piece j).isCompact_closure_D.exists_bound_of_continuousOn
      ((S.piece j).continuousOn_normal.mono (S.piece j).closure_D_subset_U)
  choose L hL using hL
  refine ⟨∑ j, 3 * ((4 * π)⁻¹ * max (L j) 0) * volume.real (S.piece j).D,
    fun y R hR hfar => ?_⟩
  unfold windingNumber flux
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  set P := S.piece j
  have hb : ∀ p ∈ P.D, ‖newtonKernel (P.Φ p - y) ⬝ᵥ (tangentU P.Φ p ⨯₃ tangentV P.Φ p)‖ ≤
      3 * ((4 * π)⁻¹ * R ^ (-2 : ℝ) * max (L j) 0) := by
    intro p hp
    have hd : R ≤ ‖P.Φ p - y‖ := by
      rw [← dist_eq_norm]; exact hfar _ (mem_iUnion.mpr ⟨j, p, subset_closure hp, rfl⟩)
    have hK : ‖newtonKernel (P.Φ p - y)‖ ≤ (4 * π)⁻¹ * R ^ (-2 : ℝ) :=
      (norm_newtonKernel_le _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hR hd (by norm_num)) (by positivity))
    have hN : ‖tangentU P.Φ p ⨯₃ tangentV P.Φ p‖ ≤ max (L j) 0 :=
      (hL j p (subset_closure hp)).trans (le_max_left _ _)
    rw [Real.norm_eq_abs]
    refine (abs_dotProduct_le _ _).trans ?_
    gcongr
  have := norm_setIntegral_le_of_norm_le_const P.volume_D_lt_top hb
  unfold SurfacePiece.flux fluxIntegral
  rw [← Real.norm_eq_abs]
  refine this.trans (le_of_eq ?_)
  ring

end ClosedSurface

namespace Sphere3

variable (Sp : Sphere3)

/-- The closed ball `{x : |x − c| ≤ ρ}` (Euclidean norm). -/
def ball : Set (Fin 3 → ℝ) := {x | vnorm (x - Sp.c) ≤ Sp.ρ}

theorem windingNumber_of_lt {y : Fin 3 → ℝ} (hy : vnorm (y - Sp.c) < Sp.ρ) :
    Sp.surface.windingNumber y = 1 := by
  set B := {z : Fin 3 → ℝ | vnorm (z - Sp.c) < Sp.ρ}
  have hconv : Convex ℝ B := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    show vnorm (a • z₁ + b • z₂ - Sp.c) < Sp.ρ
    have e : a • z₁ + b • z₂ - Sp.c = a • (z₁ - Sp.c) + b • (z₂ - Sp.c) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    rw [e]
    refine (vnorm_add_le _ _).trans_lt ?_
    rw [vnorm_smul, vnorm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_add] at hab
      subst hab
      have h2 : vnorm (z₂ - Sp.c) < Sp.ρ := hz₂
      simpa using h2
    · calc a * vnorm (z₁ - Sp.c) + b * vnorm (z₂ - Sp.c) < a * Sp.ρ + b * Sp.ρ := by
            have : b * vnorm (z₂ - Sp.c) ≤ b * Sp.ρ := mul_le_mul_of_nonneg_left hz₂.le hb
            nlinarith [mul_lt_mul_of_pos_left (show vnorm (z₁ - Sp.c) < Sp.ρ from hz₁) ha']
        _ = Sp.ρ := by rw [← add_mul, hab, one_mul]
  have hsub : B ⊆ Sp.surface.imageᶜ := fun z hz hzi => by
    have := Sp.image_subset hzi
    exact (ne_of_lt hz) this
  have hc : Sp.c ∈ B := by
    show vnorm (Sp.c - Sp.c) < Sp.ρ
    rw [sub_self]
    simpa [vnorm] using Sp.hρ
  rw [Sp.surface.windingNumber_eq_of_isPreconnected hconv.isPreconnected hsub hy hc,
    windingNumber_center]

theorem windingNumber_of_gt {y : Fin 3 → ℝ} (hy : Sp.ρ < vnorm (y - Sp.c)) :
    Sp.surface.windingNumber y = 0 := by
  set d := vnorm (y - Sp.c)
  set z : ℝ → Fin 3 → ℝ := fun t => y + t • (y - Sp.c)
  have hz : ∀ t, z t - Sp.c = (1 + t) • (y - Sp.c) := fun t => by
    simp only [z, add_smul, one_smul]; abel
  have hzv : ∀ t, 0 ≤ t → vnorm (z t - Sp.c) = (1 + t) * d := fun t ht => by
    rw [hz, vnorm_smul, abs_of_nonneg (by linarith)]
  have hray : (z '' Ici 0) ⊆ Sp.surface.imageᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hi
    have h1 := Sp.image_subset hi
    rw [hzv t ht] at h1
    have ht0 : (0 : ℝ) ≤ t := ht
    nlinarith [mul_nonneg ht0 (lt_trans Sp.hρ hy).le]
  have hconn : IsPreconnected (z '' Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous z).continuousOn
  have hW : ∀ t, 0 ≤ t → Sp.surface.windingNumber y = Sp.surface.windingNumber (z t) :=
    fun t ht => Sp.surface.windingNumber_eq_of_isPreconnected hconn hray
      ⟨0, self_mem_Ici, by simp [z]⟩ ⟨t, ht, rfl⟩
  obtain ⟨C, hC⟩ := Sp.surface.exists_abs_windingNumber_le
  set R : ℝ → ℝ := fun t => ((1 + t) * d - Sp.ρ) / √3
  have hR0 : ∀ t, 0 ≤ t → 0 < R t := fun t ht => by
    have : Sp.ρ < (1 + t) * d := by nlinarith [mul_nonneg ht (lt_trans Sp.hρ hy).le]
    exact div_pos (by linarith) (by positivity)
  have hfar : ∀ t, 0 ≤ t → ∀ x ∈ Sp.surface.image, R t ≤ dist x (z t) := by
    intro t ht x hx
    have h1 := Sp.image_subset hx
    have h2 : vnorm (z t - Sp.c) ≤ vnorm (z t - x) + vnorm (x - Sp.c) := by
      have := vnorm_add_le (z t - x) (x - Sp.c)
      rwa [sub_add_sub_cancel] at this
    have h3 := vnorm_le_sqrt_three_mul_norm (z t - x)
    rw [hzv t ht, h1] at h2
    rw [dist_comm, dist_eq_norm]
    show ((1 + t) * d - Sp.ρ) / √3 ≤ _
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hbound : ∀ t, 0 ≤ t → |Sp.surface.windingNumber y| ≤ C * R t ^ (-2 : ℝ) := fun t ht => by
    rw [hW t ht]
    exact hC _ _ (hR0 t ht) (hfar t ht)
  have hRt : Tendsto R atTop atTop := by
    have : Tendsto (fun t : ℝ => (1 + t) * d) atTop atTop :=
      (tendsto_atTop_add_const_left _ 1 tendsto_id).atTop_mul_const (lt_trans Sp.hρ hy)
    exact (tendsto_atTop_add_const_right _ (-Sp.ρ) this |>.congr fun t => by ring).atTop_div_const
      (by positivity)
  have hlim : Tendsto (fun t => C * R t ^ (-2 : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp hRt
    simpa using this.const_mul C
  have h0 : |Sp.surface.windingNumber y| ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun t ht => hbound t ht⟩)
  exact abs_nonpos_iff.mp h0

theorem volume_sphere : volume {x : Fin 3 → ℝ | vnorm (x - Sp.c) = Sp.ρ} = 0 := by
  have hpre : {x : Fin 3 → ℝ | vnorm (x - Sp.c) = Sp.ρ} =
      (WithLp.toLp 2) ⁻¹' Metric.sphere (WithLp.toLp 2 Sp.c : 𝔼) Sp.ρ := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_preimage, mem_sphere_iff_norm]
    rw [dlmf_1_6_3, WithLp.toLp_sub]
  rw [hpre, (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
  exact Measure.addHaar_sphere volume _ _

/-- **The sphere bounds the ball with the outward orientation.** -/
theorem boundsOutward : Sp.surface.BoundsOutward Sp.ball := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp Sp.volume_sphere] with y hy
  have hy : vnorm (y - Sp.c) ≠ Sp.ρ := hy
  rcases lt_or_gt_of_ne hy with h | h
  · rw [indicator_of_mem (show y ∈ Sp.ball from h.le), Pi.one_apply]
    exact Sp.windingNumber_of_lt h
  · rw [indicator_of_notMem (show y ∉ Sp.ball from not_le.mpr h)]
    exact Sp.windingNumber_of_gt h

/-- **Gauss's theorem for the ball from the general theorem** `dlmf_1_6_58_general`: for `F`
continuously differentiable on an open set containing the closed ball,
`∭_{ball} ∇ · F dV = ∬_{sphere} F · dS`. -/
theorem gauss {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hBU : Sp.ball ⊆ U)
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiffOn ℝ 1 F U) :
    ∫ x in Sp.ball, div3 F x = Sp.surface.flux F := by
  have hclosed : IsClosed Sp.ball :=
    isClosed_le (continuous_vnorm.comp (continuous_id.sub continuous_const)) continuous_const
  have hbdd : Bornology.IsBounded Sp.ball :=
    (Metric.isBounded_closedBall (x := Sp.c) (r := Sp.ρ)).subset fun x hx => by
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_le_vnorm _).trans hx
  refine dlmf_1_6_58_general Sp.surface hbdd hclosed.measurableSet Sp.boundsOutward hU
    (union_subset (by rw [hclosed.closure_eq]; exact hBU) fun x hx => hBU ?_) hF
  show vnorm (x - Sp.c) ≤ Sp.ρ
  rw [Sp.image_subset hx]

end Sphere3

end Azurite.DLMF
