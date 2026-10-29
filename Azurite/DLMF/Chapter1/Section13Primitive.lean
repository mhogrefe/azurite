/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9
import Azurite.DLMF.Chapter1.Section9Integration
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.ODE.Gronwall

/-!
# DLMF §1.13(i): simply-connected domains and primitives

Groundwork for <https://dlmf.nist.gov/1.13#i>. DLMF calls a domain *simply-connected* if its
complement in the extended plane `ℂ ∪ {∞}` is connected (`IsSimplyConnectedDLMF`, with
`OnePoint ℂ` as the extended plane). Mathlib has primitives of holomorphic functions only on
disks; this file proves that they exist on every simply-connected domain.

**Results.**
* Closed curves in a simply-connected `D` do not wind around points outside `D`
  (`ClosedPiecewiseC1.windingNumber_eq_zero_of_simplyConnected`), so the homology form of
  Cauchy's theorem from §1.9(iii) gives Cauchy's theorem on `D`
  (`ClosedPiecewiseC1.contourIntegral_eq_zero_of_simplyConnected`).
* Polygonal chains: `segInt` (the integral along a segment), `chainInt`, `IsChain`, and the closed
  polygon as a closed piecewise-`C¹` curve (`polygon`, `contourIntegral_polygon`). A closed chain
  in `D` integrates to zero (`chainInt_eq_zero_of_closed`).
* Chain algebra (`chainAppend`, `chainRev`, `chainSeg`), chains from polygonal joins
  (`exists_chain_of_polygonallyJoined`), and path independence (`chainInt_add_segInt`).
* `exists_primitive_of_simplyConnected`: an analytic function on a simply-connected domain has a
  primitive vanishing at any chosen point.
* `norm_le_along_chain`: a comparison estimate along chains, used for the Picard iteration and
  the uniqueness proof of `Section13.lean`; `norm_le_along_chain_gronwall`: Gronwall's inequality
  along chains, used in `Section13Parameter.lean`.
-/

open Filter Topology Set Metric Complex OnePoint

namespace Azurite.DLMF

/-- **DLMF §1.13(i)**: a domain `D` is *simply-connected* if its complement in the extended plane
`ℂ ∪ {∞}` is connected. -/
def IsSimplyConnectedDLMF (D : Set ℂ) : Prop :=
  IsConnected (((↑) : ℂ → OnePoint ℂ) '' D)ᶜ

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

open Azurite.DLMF

/-- A closed curve in a simply-connected domain does not wind around points outside it. -/
theorem windingNumber_eq_zero_of_simplyConnected {D : Set ℂ} (hD : IsSimplyConnectedDLMF D)
    (hP : P.curve ⊆ D) {p : ℂ} (hp : p ∉ D) : P.windingNumber p = 0 := by
  set T : Set (OnePoint ℂ) := (((↑) : ℂ → OnePoint ℂ) '' D)ᶜ with hT
  set F : OnePoint ℂ → ℤ := fun x => x.elim 0 fun q => P.windingNumber q with hF
  have hFc : ∀ q : ℂ, F q = P.windingNumber q := fun q => rfl
  have hFi : F ∞ = 0 := rfl
  have hinf : (∞ : OnePoint ℂ) ∈ T := by simp [hT]
  have hpT : (p : OnePoint ℂ) ∈ T := by
    simp only [hT, mem_compl_iff, mem_image, coe_eq_coe, not_exists, not_and]
    exact fun q hq h => hp (h ▸ hq)
  have hcont : ContinuousOn F T := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    induction x using OnePoint.rec with
    | infty =>
      obtain ⟨R, hR⟩ := P.exists_forall_windingNumber_eq_zero
      have hnhd : (((↑) : ℂ → OnePoint ℂ) '' closedBall 0 R)ᶜ ∈ 𝓝 (∞ : OnePoint ℂ) :=
        (isOpen_compl_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall 0 R⟩).mem_nhds
          (by simp)
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hnhd] with y hy
      induction y using OnePoint.rec with
      | infty => rfl
      | coe q =>
        have hq : q ∉ closedBall (0 : ℂ) R := fun h => hy ⟨q, h, rfl⟩
        rw [mem_closedBall, dist_zero_right, not_le] at hq
        rw [hFc, hFi, hR q hq]
    | coe q =>
      have hq : q ∉ P.curve := fun h => hx ⟨q, hP h, rfl⟩
      refine tendsto_nhds_of_eventually_eq ?_
      rw [nhds_coe_eq, eventually_map]
      filter_upwards [P.eventually_windingNumber_eq hq] with q' hq'
      rw [hFc, hFc, hq']
  have := hD.isPreconnected.constant hcont hpT hinf
  rwa [hFc, hFi] at this

/-- **Cauchy's theorem** on a simply-connected domain: the integral of a function analytic in `D`
around any closed curve in `D` vanishes. -/
theorem contourIntegral_eq_zero_of_simplyConnected {D : Set ℂ} (hDo : IsOpen D)
    (hD : IsSimplyConnectedDLMF D) (hP : P.curve ⊆ D) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) :
    P.contourIntegral f = 0 := by
  refine P.contourIntegral_eq_zero hDo hf ?_
  rintro z (hz | ⟨hz, hW⟩)
  · exact hP hz
  · by_contra hzD
    exact hW (P.windingNumber_eq_zero_of_simplyConnected hD hP hzD)

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

/-! ### Polygonal chains -/

/-- `∫_{[p,q]} h(z) dz = ∫₀¹ h(p + t(q − p))(q − p) dt`. -/
noncomputable def segInt (h : ℂ → ℂ) (p q : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, h (p + t * (q - p)) * (q - p)

/-- The integral along the polygonal chain `v₀ → v₁ → ⋯ → v_m`. -/
noncomputable def chainInt (h : ℂ → ℂ) (v : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ i ∈ Finset.range m, segInt h (v i) (v (i + 1))

/-- The chain `v₀ → ⋯ → v_m` lies in `D`. -/
def IsChain (D : Set ℂ) (v : ℕ → ℂ) (m : ℕ) : Prop :=
  ∀ i < m, segment ℝ (v i) (v (i + 1)) ⊆ D

theorem mem_segment_param (p q : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p + (t : ℂ) * (q - p) ∈ segment ℝ p q := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

/-- Fundamental theorem of calculus along a segment. -/
theorem segInt_eq_sub {h G : ℂ → ℂ} {U : Set ℂ} {p q : ℂ} (hseg : segment ℝ p q ⊆ U)
    (hG : ∀ w ∈ U, HasDerivAt G (h w) w) (hc : ContinuousOn h U) :
    segInt h p q = G q - G p := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => G (p + t * (q - p)))
      (h (p + t * (q - p)) * (q - p)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => p + (t : ℂ) * (q - p)) (q - p) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (q - p)).const_add p
    exact (hG _ (hseg (mem_segment_param p q ht))).comp t h1
  have hcont : ContinuousOn (fun t : ℝ => h (p + t * (q - p)) * (q - p)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine (hc.comp (Continuous.continuousOn (by fun_prop)) fun t ht =>
      hseg (mem_segment_param p q ht)).mul continuousOn_const
  rw [segInt, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  simp

theorem segInt_swap (h : ℂ → ℂ) (p q : ℂ) : segInt h q p = -segInt h p q := by
  set F : ℝ → ℂ := fun t => h (p + (t : ℂ) * (q - p)) * (q - p) with hF
  calc segInt h q p = ∫ t in (0 : ℝ)..1, -F (1 - t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [hF]
        rw [show q + (t : ℂ) * (p - q) = p + ((1 - t : ℝ) : ℂ) * (q - p) by push_cast; ring]
        ring
    _ = -segInt h p q := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left]
        norm_num [segInt, hF]

/-- The `i`-th side of the chain, parametrized over `[i, i + 1]`. -/
noncomputable def polySeg (v : ℕ → ℂ) (i : ℕ) (s : ℝ) : ℂ :=
  v i + ((s - i : ℝ) : ℂ) * (v (i + 1) - v i)

/-- The polygonal path through `v₀, v₁, …`, the `i`-th side traversed over `[i, i + 1]`. -/
noncomputable def polyPath (v : ℕ → ℂ) (s : ℝ) : ℂ := polySeg v ⌊s⌋₊ s

theorem polySeg_mem {D : Set ℂ} {v : ℕ → ℂ} {m : ℕ} (hv : IsChain D v m) {i : ℕ} (hi : i < m)
    {s : ℝ} (hs : s ∈ Icc (i : ℝ) (i + 1)) : polySeg v i s ∈ D :=
  hv i hi (mem_segment_param _ _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)

theorem polySeg_hasDerivAt (v : ℕ → ℂ) (i : ℕ) (s : ℝ) :
    HasDerivAt (polySeg v i) (v (i + 1) - v i) s := by
  show HasDerivAt (fun s : ℝ => v i + ((s - i : ℝ) : ℂ) * (v (i + 1) - v i)) _ s
  exact ((((hasDerivAt_id s).sub_const (i : ℝ)).ofReal_comp.mul_const
    (v (i + 1) - v i)).const_add (v i)).congr_deriv (by simp)

theorem polySeg_left (v : ℕ → ℂ) (i : ℕ) : polySeg v i i = v i := by simp [polySeg]

theorem polySeg_right (v : ℕ → ℂ) (i : ℕ) : polySeg v i (i + 1) = v (i + 1) := by
  simp [polySeg]

theorem polyPath_eq {v : ℕ → ℂ} {i : ℕ} {s : ℝ} (hs : s ∈ Icc (i : ℝ) (i + 1)) :
    polyPath v s = polySeg v i s := by
  rcases hs.2.lt_or_eq with hlt | rfl
  · have : ⌊s⌋₊ = i :=
      (Nat.floor_eq_iff (by linarith [hs.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)])).mpr ⟨hs.1, hlt⟩
    rw [polyPath, this]
  · have : ⌊(i : ℝ) + 1⌋₊ = i + 1 := by exact_mod_cast Nat.floor_natCast (R := ℝ) (i + 1)
    rw [polyPath, this, polySeg_right]
    exact_mod_cast polySeg_left v (i + 1)

/-- The closed polygon `v₀ → v₁ → ⋯ → v_m = v₀` as a closed piecewise-`C¹` curve on `[0, m]`. -/
noncomputable def polygon (v : ℕ → ℂ) (m : ℕ) (hv : v m = v 0) :
    JordanCurve.ClosedPiecewiseC1 (polyPath v) 0 m where
  n := m
  t i := i
  g := polySeg v
  lt i _ := by push_cast; linarith
  first := by simp
  last := rfl
  contDiff i _ := contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).mul contDiff_const)
  eqOn i _ _ hs := polyPath_eq (by exact_mod_cast hs)
  closed := by
    rw [polyPath_eq (i := 0) (by simp), polyPath_eq (i := m) (by simp), polySeg_left]
    simpa using polySeg_left v 0 |>.trans hv.symm

theorem contourIntegral_polygon (h : ℂ → ℂ) (v : ℕ → ℂ) (m : ℕ) (hv : v m = v 0) :
    (polygon v m hv).contourIntegral h = chainInt h v m := by
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∫ s in (i : ℝ)..((i + 1 : ℕ) : ℝ), h (polySeg v i s) * deriv (polySeg v i) s = _
  simp_rw [fun s => (polySeg_hasDerivAt v i s).deriv]
  have := intervalIntegral.integral_comp_sub_right
    (fun t : ℝ => h (v i + (t : ℂ) * (v (i + 1) - v i)) * (v (i + 1) - v i)) (i : ℝ)
    (a := i) (b := i + 1)
  simp only [sub_self, add_sub_cancel_left] at this
  push_cast
  exact this

theorem polygon_curve_subset {D : Set ℂ} {v : ℕ → ℂ} {m : ℕ} (hch : IsChain D v m) (hm : 0 < m)
    (hv : v m = v 0) : (polygon v m hv).curve ⊆ D := by
  rintro _ ⟨s, hs, rfl⟩
  by_cases hf : ⌊s⌋₊ < m
  · have hs' : s ∈ Icc (⌊s⌋₊ : ℝ) (⌊s⌋₊ + 1) := ⟨Nat.floor_le hs.1, (Nat.lt_floor_add_one s).le⟩
    rw [polyPath_eq hs']
    exact polySeg_mem hch hf hs'
  · have h1 : (m : ℝ) ≤ s :=
      (Nat.cast_le.mpr (not_lt.mp hf)).trans (Nat.floor_le hs.1)
    have hs' : s ∈ Icc ((m - 1 : ℕ) : ℝ) ((m - 1 : ℕ) + 1) := by
      rw [Nat.cast_sub hm]; push_cast; constructor <;> linarith [hs.2]
    rw [polyPath_eq hs']
    exact polySeg_mem hch (by omega) hs'

/-- **Cauchy's theorem for closed polygons** in a simply-connected domain. -/
theorem chainInt_eq_zero_of_closed {D : Set ℂ} (hDo : IsOpen D) (hD : IsSimplyConnectedDLMF D)
    {h : ℂ → ℂ} (hf : DifferentiableOn ℂ h D) {v : ℕ → ℂ} {m : ℕ} (hch : IsChain D v m)
    (hv : v m = v 0) : chainInt h v m = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [chainInt]
  rw [← contourIntegral_polygon h v m hv]
  exact (polygon v m hv).contourIntegral_eq_zero_of_simplyConnected hDo hD
    (polygon_curve_subset hch hm hv) hf

/-! ### Chain algebra -/

/-- The chain `v₀ → ⋯ → v_m` followed by `u₀ → u₁ → ⋯` (where `v_m = u₀`). -/
def chainAppend (v : ℕ → ℂ) (m : ℕ) (u : ℕ → ℂ) : ℕ → ℂ :=
  fun i => if i ≤ m then v i else u (i - m)

/-- The chain `v_m → ⋯ → v₀`. -/
def chainRev (v : ℕ → ℂ) (m : ℕ) : ℕ → ℂ := fun i => v (m - i)

/-- The one-sided chain `p → q`. -/
def chainSeg (p q : ℂ) : ℕ → ℂ := fun i => if i = 0 then p else q

theorem chainAppend_zero (v : ℕ → ℂ) (m : ℕ) (u : ℕ → ℂ) : chainAppend v m u 0 = v 0 := by
  simp [chainAppend]

theorem chainAppend_add {v u : ℕ → ℂ} {m : ℕ} (hvu : v m = u 0) (j : ℕ) :
    chainAppend v m u (m + j) = u j := by
  rcases j with _ | j
  · simp [chainAppend, hvu]
  · simp [chainAppend]

theorem chainInt_append (h : ℂ → ℂ) {v u : ℕ → ℂ} {m : ℕ} (hvu : v m = u 0) (k : ℕ) :
    chainInt h (chainAppend v m u) (m + k) = chainInt h v m + chainInt h u k := by
  rw [chainInt, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    simp [chainAppend, hi.le, Nat.succ_le_of_lt hi]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [chainAppend_add hvu, add_assoc, chainAppend_add hvu]

theorem isChain_append {D : Set ℂ} {v u : ℕ → ℂ} {m k : ℕ} (hvu : v m = u 0)
    (hv : IsChain D v m) (hu : IsChain D u k) : IsChain D (chainAppend v m u) (m + k) := by
  intro i hi
  by_cases him : i < m
  · simpa [chainAppend, him.le, Nat.succ_le_of_lt him] using hv i him
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp him)
    rw [chainAppend_add hvu, add_assoc, chainAppend_add hvu]
    exact hu j (by omega)

theorem chainInt_rev (h : ℂ → ℂ) (v : ℕ → ℂ) (m : ℕ) :
    chainInt h (chainRev v m) m = -chainInt h v m := by
  rw [chainInt, chainInt, ← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  simp only [chainRev]
  rw [show m - (m - 1 - j) = j + 1 by omega, show m - (m - 1 - j + 1) = j by omega, segInt_swap]

theorem isChain_rev {D : Set ℂ} {v : ℕ → ℂ} {m : ℕ} (hv : IsChain D v m) :
    IsChain D (chainRev v m) m := by
  intro j hj
  simp only [chainRev]
  rw [show m - j = m - 1 - j + 1 by omega, show m - (j + 1) = m - 1 - j by omega, segment_symm]
  exact hv _ (by omega)

theorem chainInt_seg (h : ℂ → ℂ) (p q : ℂ) : chainInt h (chainSeg p q) 1 = segInt h p q := by
  simp [chainInt, chainSeg]

theorem isChain_seg {D : Set ℂ} {p q : ℂ} (h : segment ℝ p q ⊆ D) : IsChain D (chainSeg p q) 1 := by
  intro i hi
  obtain rfl : i = 0 := by omega
  simpa [chainSeg] using h

theorem exists_chain_of_polygonallyJoined {D : Set ℂ} {a b : ℂ} (h : PolygonallyJoined D a b) :
    ∃ v : ℕ → ℂ, ∃ m : ℕ, v 0 = a ∧ v m = b ∧ IsChain D v m := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail c d _ hseg ih =>
    obtain ⟨v, m, h0, hm, hc⟩ := ih
    have hvu : v m = chainSeg c d 0 := by simp [chainSeg, hm]
    refine ⟨chainAppend v m (chainSeg c d), m + 1, by rw [chainAppend_zero, h0], ?_,
      isChain_append hvu hc (isChain_seg hseg)⟩
    rw [chainAppend_add hvu]
    simp [chainSeg]

/-- **Path independence**: integrating along a chain to `v_m` and then along `[v_m, u_k]` gives
the integral along any other chain from the same start to `u_k`. -/
theorem chainInt_add_segInt {D : Set ℂ} (hDo : IsOpen D) (hD : IsSimplyConnectedDLMF D)
    {h : ℂ → ℂ} (hf : DifferentiableOn ℂ h D) {v u : ℕ → ℂ} {m k : ℕ} (hv : IsChain D v m)
    (hu : IsChain D u k) (h0 : v 0 = u 0) (hseg : segment ℝ (v m) (u k) ⊆ D) :
    chainInt h v m + segInt h (v m) (u k) = chainInt h u k := by
  have h1 : v m = chainSeg (v m) (u k) 0 := by simp [chainSeg]
  set w₁ := chainAppend v m (chainSeg (v m) (u k)) with hw₁
  have h2 : w₁ (m + 1) = chainRev u k 0 := by
    rw [hw₁, chainAppend_add h1]; simp [chainSeg, chainRev]
  have hc := isChain_append h2 (isChain_append h1 hv (isChain_seg hseg)) (isChain_rev hu)
  have hclosed : chainAppend w₁ (m + 1) (chainRev u k) (m + 1 + k) =
      chainAppend w₁ (m + 1) (chainRev u k) 0 := by
    rw [chainAppend_add h2, chainAppend_zero, hw₁, chainAppend_zero, h0]
    simp [chainRev]
  have := chainInt_eq_zero_of_closed hDo hD hf hc hclosed
  rw [chainInt_append h h2, chainInt_append h h1, chainInt_seg, chainInt_rev] at this
  linear_combination this

/-- **DLMF §1.13(i)** (primitives): an analytic function on a simply-connected domain has a
primitive, which may be normalized to vanish at any `z₀ ∈ D`. -/
theorem exists_primitive_of_simplyConnected {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (hD : IsSimplyConnectedDLMF D) {h : ℂ → ℂ} (hf : DifferentiableOn ℂ h D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) : ∃ H : ℂ → ℂ, H z₀ = 0 ∧ ∀ z ∈ D, HasDerivAt H (h z) z := by
  have hj := ((dlmf_1_9_ii_domain hDo).mp hDc).2 z₀ hz₀
  have : ∀ z, ∃ vm : (ℕ → ℂ) × ℕ, z ∈ D → vm.1 0 = z₀ ∧ vm.1 vm.2 = z ∧ IsChain D vm.1 vm.2 := by
    intro z
    by_cases hz : z ∈ D
    · obtain ⟨v, m, h0, hm, hc⟩ := exists_chain_of_polygonallyJoined (hj z hz)
      exact ⟨(v, m), fun _ => ⟨h0, hm, hc⟩⟩
    · exact ⟨(fun _ => 0, 0), fun h => absurd h hz⟩
  choose C hC using this
  refine ⟨fun z => chainInt h (C z).1 (C z).2, ?_, fun z hz => ?_⟩
  · obtain ⟨h0, hm, hc⟩ := hC z₀ hz₀
    exact chainInt_eq_zero_of_closed hDo hD hf hc (hm.trans h0.symm)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hDo z hz
  obtain ⟨G, hG⟩ := (hf.mono hball).isExactOn_ball
  have hGz : HasDerivAt (fun w => chainInt h (C z).1 (C z).2 + (G w - G z)) (h z) z := by
    simpa using ((hG z (mem_ball_self hr)).sub_const (G z)).const_add
      (chainInt h (C z).1 (C z).2)
  refine hGz.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hr] with w hw
  obtain ⟨hz0, hzm, hzc⟩ := hC z hz
  obtain ⟨hw0, hwm, hwc⟩ := hC w (hball hw)
  have hseg : segment ℝ z w ⊆ ball z r := (convex_ball z r).segment_subset (mem_ball_self hr) hw
  have := chainInt_add_segInt hDo hD hf hzc hwc (hz0.trans hw0.symm)
    (by rw [hzm, hwm]; exact hseg.trans hball)
  rw [hzm, hwm, segInt_eq_sub hseg hG ((hf.mono hball).continuousOn)] at this
  exact this.symm

/-! ### Estimates along a chain -/

/-- **Comparison along a chain.** If `F` vanishes at `v₀` and its derivative is controlled along
the chain, `ℓ ‖F′‖ ≤ B′` (where `ℓ` bounds the side lengths), then `‖F‖ ≤ B` along the chain. -/
theorem norm_le_along_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set ℂ}
    {v : ℕ → ℂ} {m : ℕ} (hch : IsChain D v m) {ℓ : ℝ} (hℓ : ∀ i < m, ‖v (i + 1) - v i‖ ≤ ℓ)
    {F φ : ℂ → E} (hF : ∀ z ∈ D, HasDerivAt F (φ z) z) (hF0 : F (v 0) = 0)
    {B B' : ℝ → ℝ} (hB : ∀ t, HasDerivAt B (B' t) t) (hB0 : 0 ≤ B 0)
    (hφ : ∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1), ℓ * ‖φ (polySeg v i t)‖ ≤ B' t) :
    ∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1), ‖F (polySeg v i t)‖ ≤ B t := by
  have step : ∀ i < m, ‖F (v i)‖ ≤ B i → ∀ t ∈ Icc (i : ℝ) (i + 1),
      ‖F (polySeg v i t)‖ ≤ B t := by
    intro i hi hstart
    have hd : ∀ t ∈ Icc (i : ℝ) (i + 1), HasDerivAt (fun t => F (polySeg v i t))
        ((v (i + 1) - v i) • φ (polySeg v i t)) t := fun t ht =>
      (hF _ (polySeg_mem hch hi ht)).scomp t (polySeg_hasDerivAt v i t)
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by rwa [polySeg_left]) hB fun t ht => ?_
    have ht := Ico_subset_Icc_self ht
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hℓ i hi) (norm_nonneg _)).trans (hφ i hi t ht)
  have hstart : ∀ i < m, ‖F (v i)‖ ≤ B i := by
    intro i
    induction i with
    | zero => intro _; simpa [hF0] using hB0
    | succ i ih =>
      intro hi
      have := step i (by omega) (ih (by omega)) (i + 1) ⟨by linarith, le_rfl⟩
      rw [polySeg_right] at this
      exact_mod_cast this
  exact fun i hi => step i hi (hstart i hi)

theorem gronwallBound_le_exp {β K ε x : ℝ} (hβ : 0 ≤ β) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hx : x ∈ Icc (0 : ℝ) 1) : gronwallBound β K ε x ≤ Real.exp K * (β + ε) := by
  have hKx : K * x ≤ K := by nlinarith [hx.2]
  have hKx0 : 0 ≤ K * x := mul_nonneg hK hx.1
  have he : Real.exp (K * x) ≤ Real.exp K := Real.exp_le_exp.mpr hKx
  rcases hK.eq_or_lt with rfl | hKp
  · rw [gronwallBound_K0, Real.exp_zero]
    nlinarith [hx.2]
  rw [gronwallBound_of_K_ne_0 hKp.ne']
  have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
    have := Real.add_one_le_exp (-(K * x))
    have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (K * x)]
  have h3 : ε / K * (Real.exp (K * x) - 1) ≤ ε * Real.exp K := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hKp]
    calc ε * (Real.exp (K * x) - 1) ≤ ε * (K * x * Real.exp (K * x)) :=
          mul_le_mul_of_nonneg_left h1 hε
      _ = ε * K * (x * Real.exp (K * x)) := by ring
      _ ≤ ε * K * Real.exp K := mul_le_mul_of_nonneg_left
          (by nlinarith [hx.2, hx.1, Real.exp_pos (K * x)]) (mul_nonneg hε hKp.le)
      _ = ε * Real.exp K * K := by ring
  nlinarith [Real.exp_pos (K * x)]

/-- **Gronwall along a chain.** If `‖Z′‖ ≤ (K ‖Z‖ + ε)/ℓ` along the chain, where `ℓ` bounds the
side lengths, then `‖Z‖ ≤ e^{Km} (‖Z(v₀)‖ + m ε)` along the chain and at its end. -/
theorem norm_le_along_chain_gronwall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} {v : ℕ → ℂ} {m : ℕ} (hch : IsChain D v m) {ℓ : ℝ}
    (hℓ : ∀ i < m, ‖v (i + 1) - v i‖ ≤ ℓ) {Z φ : ℂ → E} (hZ : ∀ z ∈ D, HasDerivAt Z (φ z) z)
    {K ε δ : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (h0 : ‖Z (v 0)‖ ≤ δ)
    (hb : ∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1),
      ℓ * ‖φ (polySeg v i t)‖ ≤ K * ‖Z (polySeg v i t)‖ + ε) :
    (∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1),
      ‖Z (polySeg v i t)‖ ≤ Real.exp (K * m) * (δ + m * ε)) ∧
      ‖Z (v m)‖ ≤ Real.exp (K * m) * (δ + m * ε) := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  set β : ℕ → ℝ := fun i => Real.exp (K * i) * (δ + i * ε) with hβ
  have hβ0 : ∀ i, 0 ≤ β i := fun i => mul_nonneg (Real.exp_pos _).le (by positivity)
  have hβmono : ∀ {i j : ℕ}, i ≤ j → β i ≤ β j := fun {i j} hij => by
    have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) (by nlinarith) (by positivity)
      (Real.exp_pos _).le
  have hstep : ∀ i : ℕ, Real.exp K * (β i + ε) ≤ β (i + 1) := fun i => by
    simp only [hβ]
    push_cast
    have h1 : 1 ≤ Real.exp (K * i) := Real.one_le_exp (by positivity)
    rw [show K * ((i : ℝ) + 1) = K * i + K by ring, Real.exp_add]
    nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos K).le hε) (sub_nonneg.mpr h1)]
  have side : ∀ i < m, ‖Z (v i)‖ ≤ β i → ∀ t ∈ Icc (i : ℝ) (i + 1),
      ‖Z (polySeg v i t)‖ ≤ β (i + 1) := by
    intro i hi hstart t ht
    have hd : ∀ t ∈ Icc (i : ℝ) (i + 1), HasDerivAt (fun t => Z (polySeg v i t))
        ((v (i + 1) - v i) • φ (polySeg v i t)) t := fun t ht =>
      (hZ _ (polySeg_mem hch hi ht)).scomp t (polySeg_hasDerivAt v i t)
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := ε) (δ := β i)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by rw [polySeg_left]; exact hstart) (fun t ht => by
        have ht := Ico_subset_Icc_self ht
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_right (hℓ i hi) (norm_nonneg _)).trans (hb i hi t ht)) t ht
    refine hg.trans ((gronwallBound_le_exp (hβ0 i) hK hε ⟨by linarith [ht.1], by
      linarith [ht.2]⟩).trans (hstep i))
  have hstart : ∀ i ≤ m, ‖Z (v i)‖ ≤ β i := by
    intro i
    induction i with
    | zero => intro _; simpa [hβ] using h0
    | succ i ih =>
      intro hi
      have := side i (by omega) (ih (by omega)) (i + 1) ⟨by linarith, le_rfl⟩
      rw [polySeg_right] at this
      exact_mod_cast this
  exact ⟨fun i hi t ht => (side i hi (hstart i hi.le) t ht).trans (hβmono (by omega)),
    hstart m le_rfl⟩

end Azurite.DLMF
