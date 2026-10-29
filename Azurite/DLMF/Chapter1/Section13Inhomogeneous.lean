/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13

/-!
# DLMF §1.13(iii): Inhomogeneous Equations

Formalizations of <https://dlmf.nist.gov/1.13#iii> for `w″ + f(z) w′ + g(z) w = r(z)` (1.13.8).

**Results.**
* 1.13.8: `IsInhomSolution`; solutions are analytic (`IsInhomSolution.analyticOnNhd`); the
  difference of two solutions solves (1.13.1) (`IsInhomSolution.sub`), and adding a solution of
  (1.13.1) gives a solution of (1.13.8) (`IsInhomSolution.add_hom`).
* 1.13.9: every solution is `w₀ + A w₁ + B w₂` for a fundamental pair `w₁, w₂` (`dlmf_1_13_9`),
  and conversely (`dlmf_1_13_9_converse`).
* 1.13.10: variation of parameters, `w₀ = w₂ ∫ w₁ r/𝒲 − w₁ ∫ w₂ r/𝒲` for any primitives of the
  two integrands (`dlmf_1_13_10`).
* On a simply-connected domain, with `f`, `g`, `r` analytic: a particular solution exists by
  (1.13.10) and the primitives of `Section13Primitive.lean` (`dlmf_1_13_iii_exists_particular`),
  every initial value problem is solvable (`dlmf_1_13_iii_exists`), and there are infinitely
  many solutions (`dlmf_1_13_iii_infinite`).
-/

open Filter Topology Set Complex

namespace Azurite.DLMF

variable {D : Set ℂ} {f g r : ℂ → ℂ}

/-- **DLMF (1.13.8)**: `w` solves `w″ + f(z) w′ + g(z) w = r(z)` in `D`. -/
def IsInhomSolution (D : Set ℂ) (f g r w : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ w D ∧ ∀ z ∈ D, deriv (deriv w) z + f z * deriv w z + g z * w z = r z

theorem IsInhomSolution.hasDerivAt (hDo : IsOpen D) {w : ℂ → ℂ}
    (hw : IsInhomSolution D f g r w) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt w (deriv w z) z ∧
      HasDerivAt (deriv w) (r z - (f z * deriv w z + g z * w z)) z := by
  refine ⟨(hw.1.differentiableAt (hDo.mem_nhds hz)).hasDerivAt, ?_⟩
  have := ((hw.1.deriv hDo).differentiableAt (hDo.mem_nhds hz)).hasDerivAt
  convert this using 1
  linear_combination -(hw.2 z hz)

theorem isInhomSolution_of_hasDerivAt (hDo : IsOpen D) {w w' : ℂ → ℂ}
    (h : ∀ z ∈ D, HasDerivAt w (w' z) z ∧ HasDerivAt w' (r z - (f z * w' z + g z * w z)) z) :
    IsInhomSolution D f g r w := by
  refine ⟨fun z hz => (h z hz).1.differentiableAt.differentiableWithinAt, fun z hz => ?_⟩
  have heq : deriv w =ᶠ[𝓝 z] w' := by
    filter_upwards [hDo.mem_nhds hz] with y hy using (h y hy).1.deriv
  rw [heq.deriv_eq, (h z hz).2.deriv, (h z hz).1.deriv]
  ring

/-- The difference of two solutions of (1.13.8) solves the homogeneous equation (1.13.1). -/
theorem IsInhomSolution.sub (hDo : IsOpen D) {w w₀ : ℂ → ℂ} (hw : IsInhomSolution D f g r w)
    (hw₀ : IsInhomSolution D f g r w₀) : IsODESolution D f g (fun z => w z - w₀ z) := by
  refine isODESolution_of_hasDerivAt hDo (w' := fun z => deriv w z - deriv w₀ z)
    fun z hz => ?_
  obtain ⟨a1, a2⟩ := hw.hasDerivAt hDo hz
  obtain ⟨b1, b2⟩ := hw₀.hasDerivAt hDo hz
  exact ⟨a1.sub b1, (a2.sub b2).congr_deriv (by ring)⟩

/-- A solution of (1.13.8) plus a solution of (1.13.1) solves (1.13.8). -/
theorem IsInhomSolution.add_hom (hDo : IsOpen D) {w₀ h : ℂ → ℂ}
    (hw₀ : IsInhomSolution D f g r w₀) (hh : IsODESolution D f g h) :
    IsInhomSolution D f g r (fun z => w₀ z + h z) := by
  refine isInhomSolution_of_hasDerivAt hDo (w' := fun z => deriv w₀ z + deriv h z)
    fun z hz => ?_
  obtain ⟨a1, a2⟩ := hw₀.hasDerivAt hDo hz
  obtain ⟨b1, b2⟩ := hh.hasDerivAt hDo hz
  exact ⟨a1.add b1, (a2.add b2).congr_deriv (by ring)⟩

/-- **DLMF (1.13.9)**: every solution of (1.13.8) is `w₀ + A w₁ + B w₂`. -/
theorem dlmf_1_13_9 (hDo : IsOpen D) {w₀ w₁ w₂ : ℂ → ℂ} (hfp : IsFundamentalPair D f g w₁ w₂)
    (hw₀ : IsInhomSolution D f g r w₀) {w : ℂ → ℂ} (hw : IsInhomSolution D f g r w) :
    ∃ A B : ℂ, ∀ z ∈ D, w z = w₀ z + A * w₁ z + B * w₂ z := by
  obtain ⟨A, B, hAB⟩ := hfp.2.2 _ (hw.sub hDo hw₀)
  exact ⟨A, B, fun z hz => by linear_combination hAB z hz⟩

/-- **DLMF (1.13.9)**, converse: every `w₀ + A w₁ + B w₂` solves (1.13.8). -/
theorem dlmf_1_13_9_converse (hDo : IsOpen D) {w₀ w₁ w₂ : ℂ → ℂ}
    (h₁ : IsODESolution D f g w₁) (h₂ : IsODESolution D f g w₂)
    (hw₀ : IsInhomSolution D f g r w₀) (A B : ℂ) :
    IsInhomSolution D f g r (fun z => w₀ z + A * w₁ z + B * w₂ z) := by
  have := hw₀.add_hom hDo (h₁.linearCombo hDo h₂ A B)
  simpa only [add_assoc] using this

/-- **DLMF (1.13.10)** (variation of parameters): if `w₁, w₂` solve (1.13.1) with nonvanishing
Wronskian `𝒲` and `F₁′ = w₁ r/𝒲`, `F₂′ = w₂ r/𝒲`, then `w₀ = w₂ F₁ − w₁ F₂` solves (1.13.8). -/
theorem dlmf_1_13_10 (hDo : IsOpen D) {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) (hW : ∀ z ∈ D, wronskian w₁ w₂ z ≠ 0) {F₁ F₂ : ℂ → ℂ}
    (hF₁ : ∀ z ∈ D, HasDerivAt F₁ (w₁ z * r z / wronskian w₁ w₂ z) z)
    (hF₂ : ∀ z ∈ D, HasDerivAt F₂ (w₂ z * r z / wronskian w₁ w₂ z) z) :
    IsInhomSolution D f g r (fun z => w₂ z * F₁ z - w₁ z * F₂ z) := by
  refine isInhomSolution_of_hasDerivAt hDo
    (w' := fun z => deriv w₂ z * F₁ z - deriv w₁ z * F₂ z) fun z hz => ?_
  obtain ⟨a1, a2⟩ := h₁.hasDerivAt hDo hz
  obtain ⟨b1, b2⟩ := h₂.hasDerivAt hDo hz
  have hWz := hW z hz
  refine ⟨((b1.mul (hF₁ z hz)).sub (a1.mul (hF₂ z hz))).congr_deriv (by ring),
    ((b2.mul (hF₁ z hz)).sub (a2.mul (hF₂ z hz))).congr_deriv ?_⟩
  unfold wronskian at hWz ⊢
  linear_combination r z * mul_inv_cancel₀ hWz

section Existence

variable (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
  (hr : DifferentiableOn ℂ r D)
include hD hf hg hr

/-- **DLMF §1.13(iii)**: (1.13.8) has an analytic solution in `D`, by (1.13.10). -/
theorem dlmf_1_13_iii_exists_particular : ∃ w, IsInhomSolution D f g r w := by
  obtain ⟨z₀, hz₀⟩ := hD.isConnected.nonempty
  obtain ⟨w₁, w₂, hfp, -⟩ := dlmf_1_13_3 hD hf hg hz₀
  have hW : ∀ z ∈ D, wronskian w₁ w₂ z ≠ 0 :=
    ((dlmf_1_13_6 hD hf hg hfp.1 hfp.2.1).out 1 2).mp hfp
  have hWd : DifferentiableOn ℂ (wronskian w₁ w₂) D := fun z hz =>
    (wronskian_hasDerivAt hD.isOpen hfp.1 hfp.2.1 hz).differentiableAt.differentiableWithinAt
  obtain ⟨F₁, -, hF₁⟩ := exists_primitive_of_simplyConnected hD.isOpen hD.isConnected
    hD.simplyConnected ((hfp.1.1.mul hr).div hWd hW) hz₀
  obtain ⟨F₂, -, hF₂⟩ := exists_primitive_of_simplyConnected hD.isOpen hD.isConnected
    hD.simplyConnected ((hfp.2.1.1.mul hr).div hWd hW) hz₀
  exact ⟨_, dlmf_1_13_10 hD.isOpen hfp.1 hfp.2.1 hW hF₁ hF₂⟩

/-- **DLMF §1.13(iii)**: (1.13.8) has a solution with any prescribed `w(z₀)` and `w′(z₀)`. -/
theorem dlmf_1_13_iii_exists {z₀ : ℂ} (hz₀ : z₀ ∈ D) (a b : ℂ) :
    ∃ w, IsInhomSolution D f g r w ∧ w z₀ = a ∧ deriv w z₀ = b := by
  obtain ⟨w₀, hw₀⟩ := dlmf_1_13_iii_exists_particular hD hf hg hr
  obtain ⟨w₁, w₂, hfp, a0, a1, b0, b1⟩ := dlmf_1_13_3 hD hf hg hz₀
  set A := a - w₀ z₀
  set B := b - deriv w₀ z₀
  have hc := hfp.1.linearCombo hD.isOpen hfp.2.1 A B
  refine ⟨_, hw₀.add_hom hD.isOpen hc, by simp [a0, b0, A], ?_⟩
  have hd : HasDerivAt (fun z => w₀ z + (A * w₁ z + B * w₂ z))
      (deriv w₀ z₀ + (A * deriv w₁ z₀ + B * deriv w₂ z₀)) z₀ :=
    (hw₀.hasDerivAt hD.isOpen hz₀).1.add
      (hfp.1.hasDerivAt_linearCombo hD.isOpen hfp.2.1 A B hz₀)
  rw [hd.deriv, a1, b1]
  simp [B]

/-- **DLMF §1.13(iii)**: (1.13.8) has infinitely many analytic solutions in `D`. -/
theorem dlmf_1_13_iii_infinite :
    Set.Infinite ((fun w (z : D) => w z) '' {w | IsInhomSolution D f g r w}) := by
  obtain ⟨z₀, hz₀⟩ := hD.isConnected.nonempty
  choose W hW using fun a : ℂ => dlmf_1_13_iii_exists hD hf hg hr hz₀ a 0
  refine Set.infinite_of_injective_forall_mem (f := fun a (z : D) => W a z) ?_
    fun a => ⟨W a, (hW a).1, rfl⟩
  intro a b hab
  have := congrFun hab ⟨z₀, hz₀⟩
  simp only at this
  rwa [(hW a).2.1, (hW b).2.1] at this

end Existence

/-- Solutions of (1.13.8) are analytic in `D`. -/
theorem IsInhomSolution.analyticOnNhd (hDo : IsOpen D) {w : ℂ → ℂ}
    (hw : IsInhomSolution D f g r w) : AnalyticOnNhd ℂ w D :=
  hw.1.analyticOnNhd hDo

end Azurite.DLMF
