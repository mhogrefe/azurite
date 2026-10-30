/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section6GaussOrientation
import Azurite.DLMF.Chapter1.Section6JordanBrouwer

/-!
# The Jordan–Brouwer separation theorem for closed surfaces

Completes the Jordan–Brouwer separation theorem for the closed surfaces of DLMF §1.6(v)
(`ClosedSurface`), and removes the connectedness hypotheses from the outward-orientation form of
Gauss's theorem (`Section6GaussOrientation.lean`).

* `windingNumber_eq_zero_of_not_isBounded`: the solid angle vanishes on unbounded connected sets
  off the surface.
* `HasCrossing yo yi`: the segment from `yo` to `yi` crosses the surface exactly once,
  transversally, against the normal; then `W(yi) = W(yo) + 1` (`HasCrossing.windingNumber`).
* **`ClosedSurface.jordanBrouwer`**: a connected closed surface that is locally a graph and has
  one transversal crossing separates `ℝ³` into exactly two connected open sets, a bounded interior
  (`W = ±1`) and an unbounded exterior (`W = 0`), each with frontier the surface.  "At most two"
  is `jordanBrouwer_le_two` (`Section6JordanBrouwer.lean`), "at least two" is the jump of `W`.
* `ClosedSurface.outwardBoundary_of_isLocallyGraph`: `OutwardBoundary` without the connectedness
  hypotheses; `dlmf_1_6_58_jordanBrouwer` (Gauss's theorem in that form).
* Example, the sphere: `Sphere3.mem_image_iff` (the image is the Euclidean sphere; spherical
  coordinates are onto, `exists_sphereParam`), `Sphere3.isPreconnected_image`,
  `Sphere3.isLocallyGraph` (a regular level set of `levelFn`), `Sphere3.hasCrossing`,
  `Sphere3.jordanBrouwer`.
-/

open Set Filter Topology MeasureTheory Matrix
open scoped Real

namespace Azurite.DLMF

namespace ClosedSurface

variable (S : ClosedSurface)

theorem one_lt_rank_fin3 : 1 < Module.rank ℝ (Fin 3 → ℝ) := by
  rw [rank_fin_fun]; norm_num

/-- The solid angle vanishes on every unbounded connected set off the surface. -/
theorem windingNumber_eq_zero_of_not_isBounded {O : Set (Fin 3 → ℝ)} (hO : IsPreconnected O)
    (hOK : O ⊆ S.imageᶜ) (hunb : ¬ Bornology.IsBounded O) {y : Fin 3 → ℝ} (hy : y ∈ O) :
    S.windingNumber y = 0 := by
  obtain ⟨C, hC⟩ := S.exists_abs_windingNumber_le
  obtain ⟨M, hM⟩ := S.isCompact_image.isBounded.subset_closedBall 0
  have hbound : ∀ R : ℝ, 0 < R → |S.windingNumber y| ≤ C * R ^ (-2 : ℝ) := by
    intro R hR
    obtain ⟨z, hzO, hz⟩ : ∃ z ∈ O, M + R < ‖z‖ := by
      by_contra h
      push Not at h
      exact hunb ((Metric.isBounded_closedBall (x := (0 : Fin 3 → ℝ)) (r := M + R)).subset
        fun z hz => mem_closedBall_zero_iff.mpr (h z hz))
    rw [S.windingNumber_eq_of_isPreconnected hO hOK hy hzO]
    refine hC z R hR fun x hx => ?_
    have := mem_closedBall_zero_iff.mp (hM hx)
    rw [dist_eq_norm']
    linarith [norm_sub_norm_le z x]
  have hlim : Tendsto (fun R : ℝ => C * R ^ (-2 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul C
  exact abs_nonpos_iff.mp (ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hbound))

/-- A transversal crossing: the segment from `yo` to `yi` meets the surface exactly once, at
`Φⱼ(p₀) = yo + τ₀ (yi − yo)` with `p₀` inside the parameter region and `0 < τ₀ < 1`, against
the normal. -/
def HasCrossing (yo yi : Fin 3 → ℝ) : Prop :=
  ∃ j : Fin S.m, ∃ p₀ ∈ (S.piece j).D, ∃ τ₀ ∈ Ioo (0 : ℝ) 1,
    (S.piece j).Φ p₀ = yo + τ₀ • (yi - yo) ∧
    (∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
      (S.piece k).Φ p = yo + τ • (yi - yo) → k = j ∧ p = p₀) ∧
    (yi - yo) ⬝ᵥ (S.piece j).normal p₀ < 0

theorem HasCrossing.windingNumber {S : ClosedSurface} {yo yi : Fin 3 → ℝ}
    (h : S.HasCrossing yo yi) : S.windingNumber yi = S.windingNumber yo + 1 := by
  obtain ⟨j, p₀, hp₀, τ₀, hτ₀, hx₀, hcross, horient⟩ := h
  have := S.windingNumber_add_eq_add_one hp₀ hτ₀ hx₀ hcross horient
  rwa [add_sub_cancel] at this

theorem HasCrossing.not_mem {S : ClosedSurface} {yo yi : Fin 3 → ℝ}
    (h : S.HasCrossing yo yi) : yo ∉ S.image ∧ yi ∉ S.image := by
  obtain ⟨j, p₀, hp₀, τ₀, hτ₀, hx₀, hcross, horient⟩ := h
  have hne : yi - yo ≠ 0 := fun h0 => by
    rw [h0, zero_dotProduct] at horient; exact lt_irrefl _ horient
  constructor
  · rintro hyo
    obtain ⟨k, p, hp, hpe⟩ := mem_iUnion.mp hyo
    obtain ⟨rfl, rfl⟩ := hcross k p hp 0 ⟨le_rfl, zero_le_one⟩ (by rw [zero_smul, add_zero, hpe])
    rw [hpe] at hx₀
    have : τ₀ • (yi - yo) = 0 := by
      have := congrArg (· - yo) hx₀; simpa using this.symm
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hτ₀.1.ne' h0
    · exact hne h0
  · rintro hyi
    obtain ⟨k, p, hp, hpe⟩ := mem_iUnion.mp hyi
    obtain ⟨rfl, rfl⟩ := hcross k p hp 1 ⟨zero_le_one, le_rfl⟩
      (by rw [one_smul, add_sub_cancel, hpe])
    rw [hpe] at hx₀
    have : (1 - τ₀) • (yi - yo) = 0 := by
      rw [sub_smul, one_smul]
      have := congrArg (· - yo) hx₀
      simp only [add_sub_cancel_left] at this
      rw [← this]; abel
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hτ₀.2.ne (by linarith)
    · exact hne h0

theorem HasCrossing.image_nonempty {S : ClosedSurface} {yo yi : Fin 3 → ℝ}
    (h : S.HasCrossing yo yi) : S.image.Nonempty := by
  obtain ⟨j, p₀, hp₀, -⟩ := h
  exact ⟨_, mem_iUnion.mpr ⟨j, p₀, subset_closure hp₀, rfl⟩⟩

/-- **The Jordan–Brouwer separation theorem for closed surfaces.**  Let the closed surface `S` be
connected and locally (at each of its points) a graph in some chart, and let some segment cross
it transversally exactly once.  Then the complement of `S` consists of exactly two connected open
sets: a bounded one `I` (the interior), on which the solid angle `W` is `1` or `−1`, and an
unbounded one `O` (the exterior), on which `W = 0`; `S` is the frontier of each. -/
theorem jordanBrouwer (hconn : IsPreconnected S.image) (hloc : IsLocallyGraph S.image)
    {yo yi : Fin 3 → ℝ}
    (hcr : S.HasCrossing yo yi) :
    ∃ I O : Set (Fin 3 → ℝ), IsOpen I ∧ IsOpen O ∧ IsConnected I ∧ IsConnected O ∧
      Disjoint I O ∧ S.imageᶜ = I ∪ O ∧ Bornology.IsBounded I ∧ ¬ Bornology.IsBounded O ∧
      frontier I = S.image ∧ frontier O = S.image ∧ (∀ y ∈ O, S.windingNumber y = 0) ∧
      ((∀ y ∈ I, S.windingNumber y = 1) ∨ ∀ y ∈ I, S.windingNumber y = -1) := by
  set K := S.image with hKdef
  obtain ⟨hyo, hyi⟩ := hcr.not_mem
  have hW := hcr.windingNumber
  obtain ⟨xInf, hxK, hunb, hbdd, htwo, hfr⟩ :=
    jordanBrouwer_le_two one_lt_rank_fin3 S.isCompact_image hconn hcr.image_nonempty hloc
  have hWc : ∀ x, x ∉ K → ∀ y ∈ connectedComponentIn Kᶜ x,
      S.windingNumber y = S.windingNumber x := fun x hx y hy =>
    S.windingNumber_eq_of_isPreconnected isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hy (mem_connectedComponentIn hx)
  have hdiff : connectedComponentIn Kᶜ yo ≠ connectedComponentIn Kᶜ yi := by
    intro h
    have := hWc yo hyo yi (h ▸ mem_connectedComponentIn hyi)
    linarith
  have key : ∀ a b, a ∉ K → b ∉ K → connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ xInf →
      connectedComponentIn Kᶜ b ≠ connectedComponentIn Kᶜ a →
      ∃ I O : Set (Fin 3 → ℝ), IsOpen I ∧ IsOpen O ∧ IsConnected I ∧ IsConnected O ∧
        Disjoint I O ∧ K ᶜ = I ∪ O ∧ Bornology.IsBounded I ∧ ¬ Bornology.IsBounded O ∧
        frontier I = K ∧ frontier O = K ∧ (∀ y ∈ O, S.windingNumber y = 0) ∧
        ∀ y ∈ I, S.windingNumber y = S.windingNumber b := by
    intro a b ha hb hax hba
    have hKcl : IsClosed K := S.isCompact_image.isClosed
    refine ⟨connectedComponentIn Kᶜ b, connectedComponentIn Kᶜ a,
      hKcl.isOpen_compl.connectedComponentIn, hKcl.isOpen_compl.connectedComponentIn,
      ⟨⟨b, mem_connectedComponentIn hb⟩, isPreconnected_connectedComponentIn⟩,
      ⟨⟨a, mem_connectedComponentIn ha⟩, isPreconnected_connectedComponentIn⟩, ?_, ?_,
      hbdd b hb (hax ▸ hba), hax ▸ hunb, hfr b hb, hfr a ha, fun y hy =>
        S.windingNumber_eq_zero_of_not_isBounded isPreconnected_connectedComponentIn
          (connectedComponentIn_subset _ _) (hax ▸ hunb) hy, hWc b hb⟩
    · refine Set.disjoint_left.mpr fun y hyb hya => hba ?_
      rw [connectedComponentIn_eq hyb, connectedComponentIn_eq hya]
    · ext y
      simp only [mem_compl_iff, mem_union]
      constructor
      · intro hy
        rcases htwo y hy b hb with h | h | h
        · have := mem_connectedComponentIn (F := Kᶜ) hy
          rw [h, ← hax] at this
          exact Or.inr this
        · exact absurd (h.trans hax.symm) hba
        · exact Or.inl (h ▸ mem_connectedComponentIn hy)
      · rintro (h | h) <;> exact connectedComponentIn_subset _ _ h
  by_cases hA : connectedComponentIn Kᶜ yo = connectedComponentIn Kᶜ xInf
  · obtain ⟨I, O, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      key yo yi hyo hyi hA (Ne.symm hdiff)
    have h0 : S.windingNumber yo = 0 :=
      S.windingNumber_eq_zero_of_not_isBounded isPreconnected_connectedComponentIn
        (connectedComponentIn_subset _ _) (hA ▸ hunb) (mem_connectedComponentIn hyo)
    refine ⟨I, O, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, Or.inl fun y hy => ?_⟩
    rw [h12 y hy, hW, h0, zero_add]
  · have hB : connectedComponentIn Kᶜ yi = connectedComponentIn Kᶜ xInf := by
      rcases htwo yo hyo yi hyi with h | h | h
      · exact absurd h hA
      · exact h
      · exact absurd h hdiff
    obtain ⟨I, O, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      key yi yo hyi hyo hB hdiff
    have h0 : S.windingNumber yi = 0 :=
      S.windingNumber_eq_zero_of_not_isBounded isPreconnected_connectedComponentIn
        (connectedComponentIn_subset _ _) (hB ▸ hunb) (mem_connectedComponentIn hyi)
    refine ⟨I, O, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, Or.inr fun y hy => ?_⟩
    rw [h12 y hy]
    linarith

/-- **Jordan–Brouwer for `OutwardBoundary`**: the connectedness of the interior and the exterior
of `V` follows when the surface is connected and locally a graph. -/
theorem outwardBoundary_of_isLocallyGraph {V : Set (Fin 3 → ℝ)} (hVb : Bornology.IsBounded V)
    (hfr : frontier V = S.image)
    (hconn : IsPreconnected S.image) (hloc : IsLocallyGraph S.image)
    (hcross : ∃ yo yi : Fin 3 → ℝ, ∃ j : Fin S.m, ∃ p₀ ∈ (S.piece j).D,
      ∃ τ₀ ∈ Icc (0 : ℝ) 1, yo ∉ closure V ∧ yi ∈ interior V ∧
      (S.piece j).Φ p₀ = yo + τ₀ • (yi - yo) ∧
      (∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
        (S.piece k).Φ p = yo + τ • (yi - yo) → k = j ∧ p = p₀) ∧
      (yi - yo) ⬝ᵥ (S.piece j).normal p₀ < 0) :
    S.OutwardBoundary V := by
  obtain ⟨yo, yi, j, p₀, hp₀, τ₀, hτ₀, hout, hin, hx₀, hcr, horient⟩ := hcross
  have hloc' : ∀ p ∈ S.image, LocallyTwoSided S.image p := hloc.locallyTwoSided
  have hKcl : IsClosed S.image := hfr ▸ isClosed_frontier
  have hKne : S.image.Nonempty := ⟨_, mem_iUnion.mpr ⟨j, p₀, subset_closure hp₀, rfl⟩⟩
  have hcompl : S.imageᶜ = interior V ∪ (closure V)ᶜ := by
    ext y
    rw [← hfr, frontier, mem_compl_iff, Set.mem_sdiff, mem_union, mem_compl_iff]
    constructor
    · intro h
      by_cases hc : y ∈ closure V
      · exact Or.inl (by by_contra hi; exact h ⟨hc, hi⟩)
      · exact Or.inr hc
    · rintro (h | h) ⟨hc, hi⟩
      · exact hi h
      · exact h hc
  have hdisj : Disjoint (interior V) (closure V)ᶜ :=
    Set.disjoint_left.mpr fun y hi hc => hc (interior_subset_closure hi)
  refine ⟨hVb, hfr, ?_, ?_, ⟨yo, yi, j, p₀, hp₀, τ₀, hτ₀, hout, hin, hx₀, hcr, horient⟩⟩
  · exact isPreconnected_of_compl_eq_union hKcl hconn hKne hloc' isOpen_interior
      isClosed_closure.isOpen_compl hdisj hcompl ⟨yi, hin⟩ ⟨yo, hout⟩
  · rw [union_comm] at hcompl
    exact isPreconnected_of_compl_eq_union hKcl hconn hKne hloc' isClosed_closure.isOpen_compl
      isOpen_interior hdisj.symm hcompl ⟨yo, hout⟩ ⟨yi, hin⟩

end ClosedSurface

/-- **DLMF 1.6.58** (Gauss's theorem) for a region `V` bounded by a connected closed surface that
is locally a graph, oriented outwards (Jordan–Brouwer supplies the connectedness of the interior
and the exterior). -/
theorem dlmf_1_6_58_jordanBrouwer (S : ClosedSurface) {V : Set (Fin 3 → ℝ)}
    (hVb : Bornology.IsBounded V) (hfr : frontier V = S.image)
    (hconn : IsPreconnected S.image) (hloc : IsLocallyGraph S.image)
    (hcross : ∃ yo yi : Fin 3 → ℝ, ∃ j : Fin S.m, ∃ p₀ ∈ (S.piece j).D,
      ∃ τ₀ ∈ Icc (0 : ℝ) 1, yo ∉ closure V ∧ yi ∈ interior V ∧
      (S.piece j).Φ p₀ = yo + τ₀ • (yi - yo) ∧
      (∀ k, ∀ p ∈ closure (S.piece k).D, ∀ τ ∈ Icc (0 : ℝ) 1,
        (S.piece k).Φ p = yo + τ • (yi - yo) → k = j ∧ p = p₀) ∧
      (yi - yo) ⬝ᵥ (S.piece j).normal p₀ < 0)
    (hVm : MeasurableSet V) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hKU : closure V ∪ S.image ⊆ U) {G : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hG : ContDiffOn ℝ 1 G U) :
    ∫ y in V, div3 G y = S.flux G :=
  dlmf_1_6_58_outward S (S.outwardBoundary_of_isLocallyGraph hVb hfr hconn hloc hcross) hVm hU
    hKU hG

/-! ### Example: the sphere -/

namespace Sphere3

variable (Sp : Sphere3)

theorem closure_rect_openSet :
    closure Sphere3.rect.openSet = Icc 0 π ×ˢ Icc 0 (2 * π) := by
  simp only [Rect.openSet, Sphere3.rect, closure_prod_eq]
  rw [closure_Ioo Real.pi_pos.ne, closure_Ioo (by positivity : (0 : ℝ) ≠ 2 * π)]

theorem image_eq : Sp.surface.image = Sp.param '' (Icc 0 π ×ˢ Icc 0 (2 * π)) := by
  simp only [ClosedSurface.image, surface, piece, SurfacePiece.ofRect_D, closure_rect_openSet]
  ext x
  simp only [mem_iUnion, exists_const]
  rfl

theorem isPreconnected_image : IsPreconnected Sp.surface.image := by
  rw [image_eq]
  exact ((convex_Icc 0 π).prod (convex_Icc 0 (2 * π))).isPreconnected.image _
    Sp.contDiff_param.continuous.continuousOn

theorem dot_self_eq (u : Fin 3 → ℝ) : u ⬝ᵥ u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  simp only [dotProduct, Fin.sum_univ_three]; ring

/-- Spherical coordinates are onto the sphere. -/
theorem exists_sphereParam {ρ : ℝ} (hρ : 0 < ρ) {u : Fin 3 → ℝ}
    (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = ρ ^ 2) :
    ∃ p ∈ Icc 0 π ×ˢ Icc 0 (2 * π), sphereParam ρ p = u := by
  have h2 : |u 2 / ρ| ≤ 1 := by
    have hsq : u 2 ^ 2 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have habs : |u 2| ≤ ρ := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hρ.le]; exact Real.sqrt_le_sqrt hsq
    rw [abs_div, abs_of_pos hρ, div_le_one hρ]; exact habs
  set θ := Real.arccos (u 2 / ρ)
  have hcos : Real.cos θ = u 2 / ρ := Real.cos_arccos (abs_le.mp h2).1 (abs_le.mp h2).2
  set r := √(u 0 ^ 2 + u 1 ^ 2)
  have hsin : ρ * Real.sin θ = r := by
    have e : ρ * Real.sin θ = √(ρ ^ 2 * (1 - (u 2 / ρ) ^ 2)) := by
      rw [Real.sin_arccos, Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ.le]
    rw [e]
    congr 1
    field_simp
    linarith
  have hθ : θ ∈ Icc 0 π := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hu2 : ρ * Real.cos θ = u 2 := by rw [hcos]; field_simp
  by_cases hz : u 0 = 0 ∧ u 1 = 0
  · refine ⟨(θ, 0), ⟨hθ, ⟨le_rfl, by positivity⟩⟩, ?_⟩
    have hr : r = 0 := by simp [r, hz.1, hz.2]
    ext i; fin_cases i
    · simp [sphereParam_apply, hsin, hr, hz.1]
    · simp [sphereParam_apply, hz.2]
    · simp [sphereParam_apply, hu2]
  · set z : ℂ := ⟨u 0, u 1⟩
    have hz0 : z ≠ 0 := fun h => hz ⟨congrArg Complex.re h, congrArg Complex.im h⟩
    have hnz : ‖z‖ = r := by
      simp only [r, Complex.norm_def, Complex.normSq_apply, z]; congr 1; ring
    have hcarg : r * Real.cos (Complex.arg z) = u 0 := by
      rw [Complex.cos_arg hz0, hnz]; field_simp [(norm_pos_iff.mpr hz0).ne', ← hnz]; rfl
    have hsarg : r * Real.sin (Complex.arg z) = u 1 := by
      rw [Complex.sin_arg, hnz]; field_simp [(norm_pos_iff.mpr hz0).ne', ← hnz]; rfl
    set φ := if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z
    have hφ : φ ∈ Icc 0 (2 * π) := by
      have := Complex.neg_pi_lt_arg z
      have := Complex.arg_le_pi z
      simp only [φ]
      split_ifs with h
      · constructor <;> linarith
      · constructor <;> linarith [Real.pi_pos]
    have hcφ : Real.cos φ = Real.cos (Complex.arg z) := by
      simp only [φ]; split_ifs <;> simp [Real.cos_add_two_pi]
    have hsφ : Real.sin φ = Real.sin (Complex.arg z) := by
      simp only [φ]; split_ifs <;> simp [Real.sin_add_two_pi]
    refine ⟨(θ, φ), ⟨hθ, hφ⟩, ?_⟩
    ext i; fin_cases i
    · simp only [sphereParam_apply]; simp
      rw [hcφ, ← hcarg, ← hsin]
    · simp only [sphereParam_apply]; simp
      rw [hsφ, ← hsarg, ← hsin]
    · simp only [sphereParam_apply]; simp [hu2]

/-- The image of the sphere surface is the Euclidean sphere `|x − c| = ρ`. -/
theorem mem_image_iff (x : Fin 3 → ℝ) :
    x ∈ Sp.surface.image ↔ (x 0 - Sp.c 0) ^ 2 + (x 1 - Sp.c 1) ^ 2 + (x 2 - Sp.c 2) ^ 2 =
      Sp.ρ ^ 2 := by
  constructor
  · intro hx
    have h := Sp.image_subset hx
    rw [vnorm] at h
    have := Real.sq_sqrt (by rw [dot_self_eq]; positivity : (0 : ℝ) ≤ (x - Sp.c) ⬝ᵥ (x - Sp.c))
    rw [h, dot_self_eq] at this
    simpa using this.symm
  · intro hx
    obtain ⟨p, hp, hpe⟩ := exists_sphereParam Sp.hρ (u := x - Sp.c) (by simpa using hx)
    rw [image_eq]
    exact ⟨p, hp, by rw [param, hpe, add_sub_cancel]⟩

/-- The defining function `|x − c|² − ρ²` of the sphere. -/
noncomputable def levelFn (x : Fin 3 → ℝ) : ℝ :=
  (x 0 - Sp.c 0) ^ 2 + (x 1 - Sp.c 1) ^ 2 + (x 2 - Sp.c 2) ^ 2 - Sp.ρ ^ 2

theorem contDiff_levelFn : ContDiff ℝ 1 Sp.levelFn := by
  unfold levelFn; fun_prop

/-- The sphere is locally a graph (a regular level set). -/
theorem isLocallyGraph : IsLocallyGraph Sp.surface.image := by
  refine isLocallyGraph_of_regular fun p hp => ⟨Sp.levelFn, fderiv ℝ Sp.levelFn p,
    (Sp.contDiff_levelFn.contDiffAt).hasStrictFDerivAt one_ne_zero, ?_, univ, univ_mem,
    (fun y _ => by rw [mem_image_iff, levelFn, sub_eq_zero])⟩
  intro h0
  have hpK := (Sp.mem_image_iff p).mp hp
  set v := p - Sp.c
  have hline : ∀ t : ℝ, Sp.levelFn (p + t • v) = (1 + t) ^ 2 * Sp.ρ ^ 2 - Sp.ρ ^ 2 := by
    intro t
    simp only [levelFn, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hpK]; ring
  have hd1 : HasDerivAt (fun t : ℝ => Sp.levelFn (p + t • v)) (fderiv ℝ Sp.levelFn p v) 0 := by
    have hf := (Sp.contDiff_levelFn.differentiable one_ne_zero p).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    exact hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hd2 : HasDerivAt (fun t : ℝ => Sp.levelFn (p + t • v)) (2 * Sp.ρ ^ 2) 0 := by
    have h : HasDerivAt (fun t : ℝ => (1 + t) ^ 2 * Sp.ρ ^ 2 - Sp.ρ ^ 2) (2 * Sp.ρ ^ 2) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const (Sp.ρ ^ 2)).sub_const
        (Sp.ρ ^ 2)
      convert this using 1
      · funext t; simp
      · norm_num
    exact h.congr_of_eventuallyEq (Eventually.of_forall hline)
  have := hd1.unique hd2
  rw [h0] at this
  have h2 : (2 : ℝ) * Sp.ρ ^ 2 = 0 := by rw [← this]; rfl
  have := Sp.hρ
  nlinarith

theorem normal_piece (p : ℝ × ℝ) :
    Sp.piece.normal p = (Sp.ρ * Real.sin p.1) • sphereParam Sp.ρ p := by
  obtain ⟨θ, φ⟩ := p
  have htan : ∀ p : ℝ × ℝ, tangentU Sp.param p = tangentU (sphereParam Sp.ρ) p ∧
      tangentV Sp.param p = tangentV (sphereParam Sp.ρ) p := fun p => by
    simp only [tangentU, tangentV]
    rw [show Sp.param = fun p => Sp.c + sphereParam Sp.ρ p from rfl, fderiv_const_add]
    exact ⟨rfl, rfl⟩
  show tangentU Sp.param (θ, φ) ⨯₃ tangentV Sp.param (θ, φ) = _
  rw [(htan _).1, (htan _).2, cross_tangent_sphereParam]

/-- The segment from `c − 2ρ e₀` to `c` crosses the sphere once, at `(θ, φ) = (π/2, π)`, against
the outward normal. -/
theorem hasCrossing :
    Sp.surface.HasCrossing (Sp.c + ![-2 * Sp.ρ, 0, 0]) Sp.c := by
  have hρ := Sp.hρ
  have hseg : ∀ τ : ℝ, Sp.c + ![-2 * Sp.ρ, 0, 0] + τ • (Sp.c - (Sp.c + ![-2 * Sp.ρ, 0, 0])) =
      Sp.c + ![(2 * τ - 2) * Sp.ρ, 0, 0] := by
    intro τ; ext i; fin_cases i <;> simp [vecHead, vecTail]; ring
  have hp₀ : sphereParam Sp.ρ (π / 2, π) = ![-Sp.ρ, 0, 0] := by
    ext i; fin_cases i <;> simp [sphereParam_apply]
  refine ⟨⟨0, by show 0 < 1; norm_num⟩, (π / 2, π), ?_, 1 / 2, ⟨by norm_num, by norm_num⟩, ?_,
    ?_, ?_⟩
  · show (π / 2, π) ∈ (SurfacePiece.ofRect Sphere3.rect Sp.param Sp.contDiff_param).D
    rw [SurfacePiece.ofRect_D]
    simp only [Rect.openSet, Sphere3.rect, mem_prod, mem_Ioo]
    exact ⟨⟨by positivity, by linarith [Real.pi_pos]⟩, ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩⟩
  · show Sp.param (π / 2, π) = _
    rw [hseg, param, hp₀]; congr 1; ext i; fin_cases i <;> simp; ring
  · intro k p hp τ hτ he
    refine ⟨Fin.ext (by have := k.2; change k.1 < 1 at this; show k.1 = 0; omega), ?_⟩
    have hp' : p ∈ Icc 0 π ×ˢ Icc 0 (2 * π) := by
      have : closure (Sp.surface.piece k).D = Icc 0 π ×ˢ Icc 0 (2 * π) := by
        show closure (SurfacePiece.ofRect Sphere3.rect Sp.param Sp.contDiff_param).D = _
        rw [SurfacePiece.ofRect_D, closure_rect_openSet]
      rwa [this] at hp
    have he' : sphereParam Sp.ρ p = ![(2 * τ - 2) * Sp.ρ, 0, 0] := by
      have : Sp.param p = Sp.c + ![(2 * τ - 2) * Sp.ρ, 0, 0] := by rw [← hseg]; exact he
      rw [param] at this
      exact add_left_cancel this
    obtain ⟨θ, φ⟩ := p
    have e0 := congrFun he' 0
    have e1 := congrFun he' 1
    have e2 := congrFun he' 2
    simp [sphereParam_apply] at e0 e1 e2
    have hcθ : Real.cos θ = 0 := by
      rcases e2 with h | h
      · exact absurd h hρ.ne'
      · exact h
    have hθ : θ = π / 2 := Real.injOn_cos hp'.1 ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by rw [hcθ, Real.cos_pi_div_two])
    have hdot := sphereParam_dot_self Sp.ρ (θ, φ)
    rw [he'] at hdot
    simp only [dotProduct, Fin.sum_univ_three] at hdot
    simp at hdot
    have hτ' : 2 * τ - 2 = -1 := by
      have h1 : (2 * τ - 2) ^ 2 = 1 := by
        have : Sp.ρ ^ 2 * ((2 * τ - 2) ^ 2 - 1) = 0 := by linear_combination hdot
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hρ.ne'
        · linarith
      have : 2 * τ - 2 ≤ 0 := by linarith [hτ.2]
      nlinarith
    rw [hθ, Real.sin_pi_div_two, hτ'] at e0
    have hcφ : Real.cos φ = -1 := by
      have : Sp.ρ * (Real.cos φ + 1) = 0 := by linear_combination e0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hρ.ne'
      · linarith
    have hφ : φ = π := by
      rcases le_total φ π with h | h
      · exact Real.injOn_cos ⟨hp'.2.1, h⟩ ⟨Real.pi_pos.le, le_rfl⟩ (by rw [hcφ, Real.cos_pi])
      · have hc : Real.cos (2 * π - φ) = Real.cos π := by
          rw [Real.cos_pi, show 2 * π - φ = -(φ - 2 * π) by ring, Real.cos_neg,
            Real.cos_sub_two_pi, hcφ]
        have := Real.injOn_cos (show 2 * π - φ ∈ Icc 0 π from
          ⟨by linarith [hp'.2.2], by linarith⟩) (show π ∈ Icc 0 π from
          ⟨Real.pi_pos.le, le_rfl⟩) hc
        linarith
    rw [hθ, hφ]
  · show (Sp.c - (Sp.c + ![-2 * Sp.ρ, 0, 0])) ⬝ᵥ Sp.piece.normal (π / 2, π) < 0
    rw [normal_piece, hp₀]
    simp [dotProduct, Fin.sum_univ_three, vecHead, vecTail]
    nlinarith [mul_pos hρ (mul_pos hρ hρ)]

/-- **Jordan–Brouwer for the sphere**: the hypotheses of `ClosedSurface.jordanBrouwer` hold, so
the complement of the sphere is a bounded interior (solid angle `±1`) and an unbounded exterior
(solid angle `0`), each connected, each with frontier the sphere. -/
theorem jordanBrouwer :
    ∃ I O : Set (Fin 3 → ℝ), IsOpen I ∧ IsOpen O ∧ IsConnected I ∧ IsConnected O ∧
      Disjoint I O ∧ Sp.surface.imageᶜ = I ∪ O ∧ Bornology.IsBounded I ∧
      ¬ Bornology.IsBounded O ∧ frontier I = Sp.surface.image ∧
      frontier O = Sp.surface.image ∧ (∀ y ∈ O, Sp.surface.windingNumber y = 0) ∧
      ((∀ y ∈ I, Sp.surface.windingNumber y = 1) ∨
        ∀ y ∈ I, Sp.surface.windingNumber y = -1) :=
  Sp.surface.jordanBrouwer Sp.isPreconnected_image Sp.isLocallyGraph Sp.hasCrossing

end Sphere3

end Azurite.DLMF
