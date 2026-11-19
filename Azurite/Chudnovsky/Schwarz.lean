/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.Hermite

/-!
# Schwarz's lemma with zeros on a bounded open set

`norm_le_of_zeros_on`: for `F` holomorphic on an open `V ⊇ closure U`, `U` bounded, with zeros
at the points of a multiset `s ⊆ V`, `|F| ≤ M` on the frontier of `U` and all zeros at distance
`≥ d` from the frontier: `|F(z)| d^|s| ≤ ∏_{b ∈ s} |z − b| · M` on `closure U`.
`norm_le_of_zeros_finset` is the version with zeros of order `N` at the points of a finset.

Also removable singularities with explicit local representatives (`exists_extension`).
-/

namespace Azurite.Chudnovsky

open Complex Metric Set Filter Topology Azurite.Feldman

/-- A function holomorphic on an open set `V` with zeros at the points of `s ⊆ V`, counted
with multiplicity, is the product of the factors `z − b` and a function holomorphic on `V`. -/
theorem exists_eq_prod_mul_on {V : Set ℂ} (hV : IsOpen V) : ∀ (s : Multiset ℂ) {F : ℂ → ℂ},
    DifferentiableOn ℂ F V → (∀ b ∈ s, b ∈ V) →
    (∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt F c) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G V ∧ ∀ z, F z = (s.map fun b => z - b).prod * G z := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro F hF _ _
    exact ⟨F, hF, fun z => by simp⟩
  | cons b s ih =>
    intro F hF hsV h
    have hbV : b ∈ V := hsV b (Multiset.mem_cons_self b s)
    have hFb : F b = 0 := by
      apply apply_eq_zero_of_analyticOrderAt_ne_zero
      intro h0
      have := h b
      rw [h0, Multiset.count_cons_self] at this
      simp at this
    have hG₁ : DifferentiableOn ℂ (dslope F b) V :=
      (differentiableOn_dslope (hV.mem_nhds hbV)).mpr hF
    have heq : ∀ z, F z = (z - b) * dslope F b z := fun z => by
      have := sub_smul_dslope F b z
      rw [hFb, sub_zero, smul_eq_mul] at this
      exact this.symm
    have hfun : F = (· - b) * dslope F b := funext heq
    have hord : ∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt (dslope F b) c := by
      intro c
      by_cases hcV : c ∈ V
      · have hmul : analyticOrderAt F c
            = analyticOrderAt (· - b) c + analyticOrderAt (dslope F b) c := by
          conv_lhs => rw [hfun]
          exact analyticOrderAt_mul (by fun_prop) (hG₁.analyticAt (hV.mem_nhds hcV))
        have hc := h c
        rw [hmul] at hc
        by_cases hcb : c = b
        · subst hcb
          rw [Multiset.count_cons_self, analyticOrderAt_id_sub_const_self] at hc
          push_cast at hc
          rw [add_comm] at hc
          exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp hc
        · rw [Multiset.count_cons_of_ne hcb, analyticOrderAt_id_sub_const_of_ne hcb, zero_add]
            at hc
          exact hc
      · have : c ∉ s := fun hc => hcV (hsV c (Multiset.mem_cons_of_mem hc))
        rw [Multiset.count_eq_zero_of_notMem this]
        simp
    obtain ⟨G, hG, hGeq⟩ := ih hG₁ (fun c hc => hsV c (Multiset.mem_cons_of_mem hc)) hord
    refine ⟨G, hG, fun z => ?_⟩
    rw [heq z, hGeq z, Multiset.map_cons, Multiset.prod_cons]
    ring

/-- **Schwarz's lemma with zeros** on a bounded open set. -/
theorem norm_le_of_zeros_on {U V : Set ℂ} (hU : Bornology.IsBounded U) (hV : IsOpen V)
    (hUV : closure U ⊆ V) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F V) (s : Multiset ℂ)
    (hsV : ∀ b ∈ s, b ∈ V) (hs : ∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt F c) {M d : ℝ}
    (hd : 0 < d) (hM : ∀ w ∈ frontier U, ‖F w‖ ≤ M)
    (hdist : ∀ w ∈ frontier U, ∀ b ∈ s, d ≤ ‖w - b‖) {z : ℂ} (hz : z ∈ closure U) :
    ‖F z‖ * d ^ Multiset.card s ≤ (s.map fun b => ‖z - b‖).prod * M := by
  obtain ⟨G, hG, hGeq⟩ := exists_eq_prod_mul_on hV s hF hsV hs
  have hnp : ∀ w : ℂ, ‖(s.map fun b => w - b).prod‖ = (s.map fun b => ‖w - b‖).prod :=
    norm_prod_sub s
  have hGs : ∀ w ∈ frontier U, ‖G w‖ ≤ M / d ^ Multiset.card s := by
    intro w hw
    have hprod : d ^ Multiset.card s ≤ (s.map fun b => ‖w - b‖).prod :=
      pow_card_le_prod_norm_sub s w hd (hdist w hw)
    have h1 := hM w hw
    rw [hGeq w, norm_mul, hnp] at h1
    rw [le_div_iff₀ (by positivity)]
    calc ‖G w‖ * d ^ Multiset.card s ≤ ‖G w‖ * (s.map fun b => ‖w - b‖).prod :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = (s.map fun b => ‖w - b‖).prod * ‖G w‖ := mul_comm _ _
      _ ≤ M := h1
  have hdc : DiffContOnCl ℂ G U :=
    ⟨hG.mono (subset_closure.trans hUV), hG.continuousOn.mono hUV⟩
  have hGz : ‖G z‖ ≤ M / d ^ Multiset.card s :=
    norm_le_of_forall_mem_frontier_norm_le hU hdc hGs hz
  rw [hGeq z, norm_mul, hnp]
  have hpz : 0 ≤ (s.map fun b => ‖z - b‖).prod :=
    Multiset.prod_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp hx
      exact norm_nonneg _
  calc (s.map fun b => ‖z - b‖).prod * ‖G z‖ * d ^ Multiset.card s
      = (s.map fun b => ‖z - b‖).prod * (‖G z‖ * d ^ Multiset.card s) := by ring
    _ ≤ (s.map fun b => ‖z - b‖).prod * M := by
        refine mul_le_mul_of_nonneg_left ?_ hpz
        rw [← le_div_iff₀ (by positivity)]
        exact hGz

/-- Schwarz's lemma with zeros of order `N` at the points of a finset. -/
theorem norm_le_of_zeros_finset {U V : Set ℂ} (hU : Bornology.IsBounded U) (hV : IsOpen V)
    (hUV : closure U ⊆ V) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F V) (Z : Finset ℂ) (N : ℕ)
    (hZV : ∀ b ∈ Z, b ∈ V) (hZ : ∀ b ∈ Z, (N : ℕ∞) ≤ analyticOrderAt F b) {M d : ℝ}
    (hd : 0 < d) (hM : ∀ w ∈ frontier U, ‖F w‖ ≤ M)
    (hdist : ∀ w ∈ frontier U, ∀ b ∈ Z, d ≤ ‖w - b‖) {z : ℂ} (hz : z ∈ closure U) :
    ‖F z‖ * d ^ (N * Z.card) ≤ (∏ b ∈ Z, ‖z - b‖) ^ N * M := by
  classical
  have h := norm_le_of_zeros_on hU hV hUV hF (N • Z.val)
    (fun b hb => hZV b (Finset.mem_val.mp (Multiset.mem_of_mem_nsmul hb)))
    (fun c => by
      rw [Multiset.count_nsmul]
      by_cases hc : c ∈ Z
      · rw [Multiset.count_eq_one_of_mem Z.nodup (Finset.mem_val.mpr hc), mul_one]
        exact hZ c hc
      · rw [Multiset.count_eq_zero_of_notMem (fun h => hc (Finset.mem_val.mp h))]
        simp)
    hd hM (fun w hw b hb => hdist w hw b (Finset.mem_val.mp (Multiset.mem_of_mem_nsmul hb))) hz
  rw [Multiset.card_nsmul, Multiset.map_nsmul, Multiset.prod_nsmul] at h
  exact h

/-! ### Removable singularities with local representatives -/

/-- If `f` is differentiable at the points of an open set `V` outside a finite set `S`, and
near every `s ∈ S` agrees off `s` with a function differentiable at `s`, then `f` agrees
outside `S` with a function differentiable on `V`. -/
theorem exists_extension {f : ℂ → ℂ} {V : Set ℂ} (S : Finset ℂ)
    (hf : ∀ z ∈ V, z ∉ S → DifferentiableAt ℂ f z)
    (hS : ∀ s ∈ S, ∃ g : ℂ → ℂ, DifferentiableAt ℂ g s ∧ ∀ᶠ z in 𝓝[≠] s, f z = g z) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F V ∧ ∀ z, z ∉ S → F z = f z := by
  classical
  choose! g hg hfg using hS
  refine ⟨fun z => if z ∈ S then g z z else f z, fun z hz => ?_, fun z hz => by simp [hz]⟩
  have hSc : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
  by_cases hzS : z ∈ S
  · -- near `z ∈ S` the function is `g z`
    have hev : (fun w => if w ∈ S then g w w else f w) =ᶠ[𝓝 z] g z := by
      have h1 : ∀ᶠ w in 𝓝[≠] z, w ∉ S := by
        have hcl : IsClosed ((S.erase z : Finset ℂ) : Set ℂ) := (S.erase z).finite_toSet.isClosed
        have hz' : z ∈ (((S.erase z : Finset ℂ) : Set ℂ))ᶜ := by simp
        have h2 : ∀ᶠ w in 𝓝 z, w ∈ (((S.erase z : Finset ℂ) : Set ℂ))ᶜ :=
          hcl.isOpen_compl.mem_nhds hz'
        filter_upwards [h2.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwz
        intro hwS
        exact hw (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, hwS⟩))
      have h3 : ∀ᶠ w in 𝓝[≠] z, (if w ∈ S then g w w else f w) = g z w := by
        filter_upwards [h1, hfg z hzS] with w hw hfw
        simp only [hw, ↓reduceIte, hfw]
      rw [eventually_nhdsWithin_iff] at h3
      filter_upwards [h3] with w hw
      by_cases hwz : w = z
      · subst hwz
        simp [hzS]
      · exact hw hwz
    exact ((hev.differentiableAt_iff).mpr (hg z hzS)).differentiableWithinAt
  · have hev : (fun w => if w ∈ S then g w w else f w) =ᶠ[𝓝 z] f := by
      filter_upwards [hSc.isOpen_compl.mem_nhds (by simpa using hzS)] with w hw
      have hw' : w ∉ S := by simpa using hw
      simp only [hw', ↓reduceIte]
    exact ((hev.differentiableAt_iff).mpr (hf z hz hzS)).differentiableWithinAt

end Azurite.Chudnovsky
