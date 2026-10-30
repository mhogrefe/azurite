/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section10Laurent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# DLMF §1.10(iii): Landau's lemma and Bloch's theorem (towards Picard's theorem)

First step of the proof of Picard's theorem (`Section10Picard.lean`), following the classical
Bloch–Schottky route (no normal families).

* `exists_log_ball`: a nonvanishing holomorphic function on a disk has a holomorphic logarithm.
* `norm_sub_id_le`: if `f(0) = 0`, `f′(0) = 1` and `|f| ≤ M` on the unit disk, then
  `|f(z) − z| ≤ (M + 3)|z|²` (Schwarz's lemma applied to `dslope`).
* `ball_subset_image_of_bounded` (Landau): such an `f` covers the disk of radius `1/(8(M + 3))`.
* `bloch` (Bloch's theorem, Landau's form): a holomorphic `f` on `D(c, s)` covers some disk of
  radius `s |f′(c)|/160`.
-/

open Filter Topology Set Metric Complex
open scoped Real

namespace Azurite.DLMF

/-- A nonvanishing holomorphic function on a disk has a holomorphic logarithm, normalized at the
center by the principal logarithm. -/
theorem exists_log_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball c r))
    (hg0 : ∀ z ∈ ball c r, g z ≠ 0) (hc : c ∈ ball c r) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c r) ∧ (∀ z ∈ ball c r, cexp (L z) = g z) ∧
      L c = Complex.log (g c) := by
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c r) :=
    (hg.deriv isOpen_ball).div hg hg0
  obtain ⟨P, hP⟩ := hd.isExactOn_ball
  set L : ℂ → ℂ := fun z => P z - P c + Complex.log (g c) with hL
  have hLd : ∀ z ∈ ball c r, HasDerivAt L (deriv g z / g z) z := fun z hz =>
    ((hP z hz).sub_const _).add_const _
  refine ⟨L, fun z hz => (hLd z hz).differentiableAt.differentiableWithinAt, ?_, by simp [hL]⟩
  set φ : ℂ → ℂ := fun z => g z * cexp (-L z) with hφ
  have hφd : ∀ z ∈ ball c r, HasDerivAt φ 0 z := fun z hz => by
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have := hgz.mul ((hLd z hz).neg.cexp)
    refine this.congr_deriv ?_
    have := hg0 z hz
    field_simp
    ring
  have hconst : ∀ z ∈ ball c r, φ z = φ c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      (fun w hw => (hφd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hφd w hw).deriv) hz hc
  have hφc : φ c = 1 := by
    simp only [hφ, hL, sub_self, zero_add]
    rw [Complex.exp_neg, Complex.exp_log (hg0 c hc), mul_inv_cancel₀ (hg0 c hc)]
  intro z hz
  have h1 := hconst z hz
  rw [hφc] at h1
  simp only [hφ, Complex.exp_neg] at h1
  have hne : cexp (L z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at h1
  exact h1.symm

/-- Second-order estimate: if `f(0) = 0`, `f′(0) = 1` and `|f| ≤ M` on the unit disk, then
`|f(z) − z| ≤ (M + 3)|z|²` there (Schwarz's lemma twice). -/
theorem norm_sub_id_le {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 1)) (h0 : f 0 = 0)
    (h1 : deriv f 0 = 1) (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖f z - z‖ ≤ (M + 3) * ‖z‖ ^ 2 := by
  have hb : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  have hmaps : MapsTo f (ball 0 1) (closedBall (f 0) M) := fun w hw => by
    rw [mem_closedBall, h0, dist_zero_right]; exact hM w hw
  have hds : ∀ w ∈ ball (0 : ℂ) 1, ‖dslope f 0 w‖ ≤ M := fun w hw => by
    simpa using norm_dslope_le_div_of_mapsTo_ball hf hmaps hw
  set h : ℂ → ℂ := fun w => dslope f 0 w - 1 with hh
  have hhd : DifferentiableOn ℂ h (ball 0 1) := ((differentiableOn_dslope hb).mpr hf).sub_const _
  have hh0 : h 0 = 0 := by simp [hh, dslope_same, h1]
  have hmaps2 : MapsTo h (ball 0 1) (closedBall (h 0) (M + 3)) := fun w hw => by
    rw [mem_closedBall, hh0, dist_zero_right]
    calc ‖h w‖ ≤ ‖dslope f 0 w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ M + 1 := by rw [norm_one]; linarith [hds w hw]
      _ ≤ M + 3 := by linarith
  have hdh := norm_dslope_le_div_of_mapsTo_ball hhd hmaps2 hz
  rw [div_one] at hdh
  have e1 : h z = z * dslope h 0 z := by
    have := sub_smul_dslope h 0 z; rw [hh0, sub_zero, sub_zero, smul_eq_mul] at this
    exact this.symm
  have e2 : f z - z = z * h z := by
    have := sub_smul_dslope f 0 z; rw [h0, sub_zero, sub_zero, smul_eq_mul] at this
    simp only [hh]; rw [mul_sub, this, mul_one]
  rw [e2, e1, norm_mul, norm_mul, ← mul_assoc, sq]
  have := norm_nonneg z
  nlinarith

/-- **Landau's lemma**: if `f(0) = 0`, `f′(0) = 1` and `|f| ≤ M` on the unit disk, then the image
of the unit disk contains the disk of radius `1/(8(M + 3))` about `0`. -/
theorem ball_subset_image_of_bounded {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ball 0 (1 / (8 * (M + 3))) ⊆ f '' ball 0 1 := by
  have hM0 : 0 ≤ M := by simpa [h0] using hM 0 (mem_ball_self one_pos)
  set K := M + 3 with hK
  have hK0 : 3 ≤ K := by linarith
  set r := 1 / (2 * K) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  intro w hw
  rw [mem_ball, dist_zero_right] at hw
  by_contra hcon
  have hne : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ w := fun z hz hfz =>
    hcon ⟨z, hsub hz, hfz⟩
  have hw0 : w ≠ 0 := fun h => hne 0 (mem_closedBall_self hr0.le) (by rw [h0, h])
  set k : ℂ → ℂ := fun z => (f z - w)⁻¹ with hk
  have hkd : DiffContOnCl ℂ k (ball 0 r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 hr0.ne']
    exact ((hf.mono hsub).sub_const w).inv fun z hz => sub_ne_zero.mpr (hne z hz)
  have hfront : ∀ z ∈ frontier (ball (0 : ℂ) r), ‖k z‖ ≤ 4 / r := fun z hz => by
    rw [frontier_ball 0 hr0.ne', mem_sphere, dist_zero_right] at hz
    have hzb : z ∈ ball (0 : ℂ) 1 := hsub (by rw [mem_closedBall, dist_zero_right, hz])
    have h2 := norm_sub_id_le hf h0 h1 hM hzb
    have hfz : r / 2 ≤ ‖f z‖ := by
      have := norm_sub_norm_le z (z - f z)
      rw [sub_sub_cancel, norm_sub_rev] at this
      have hKr : K * r = 1 / 2 := by rw [hr]; field_simp
      rw [hz] at h2 this
      nlinarith
    have hlow : r / 4 ≤ ‖f z - w‖ := by
      have := norm_sub_norm_le (f z) w
      have hw' : ‖w‖ < r / 4 := by
        rw [hr]; rw [hK] at hw ⊢; field_simp at hw ⊢; linarith
      linarith
    rw [hk, norm_inv, inv_le_comm₀ (by linarith) (by positivity), inv_div]
    linarith
  have hk0 := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hkd hfront
    (subset_closure (mem_ball_self hr0))
  simp only [hk] at hk0
  rw [h0, zero_sub, norm_inv, norm_neg, inv_le_comm₀ (norm_pos_iff.mpr hw0) (by positivity),
    inv_div] at hk0
  have : r / 4 = 1 / (8 * K) := by rw [hr]; field_simp; ring
  linarith

/-- **Bloch's theorem** (Landau's form): if `f` is holomorphic on the disk `D(c, s)`, then
`f(D(c, s))` contains a disk of radius `s |f′(c)|/160`. -/
theorem bloch {f : ℂ → ℂ} {c : ℂ} {s : ℝ} (hs : 0 < s) (hf : DifferentiableOn ℂ f (ball c s)) :
    ∃ w, ball w (s * ‖deriv f c‖ / 160) ⊆ f '' ball c s := by
  rcases eq_or_ne (deriv f c) 0 with hd0 | hd0
  · exact ⟨0, by rw [hd0, norm_zero, mul_zero, zero_div, ball_zero]; exact empty_subset _⟩
  set ρ := s / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hcl : closedBall c ρ ⊆ ball c s := closedBall_subset_ball (by linarith)
  have hfd : ∀ z ∈ ball c s, DifferentiableAt ℂ f z := fun z hz =>
    hf.differentiableAt (isOpen_ball.mem_nhds hz)
  have hdc : ContinuousOn (deriv f) (closedBall c ρ) :=
    ((hf.deriv isOpen_ball).continuousOn).mono hcl
  set φ : ℂ → ℝ := fun z => (ρ - ‖z - c‖) * ‖deriv f z‖ with hφ
  have hφc : ContinuousOn φ (closedBall c ρ) :=
    ((continuous_const.sub (continuous_id.sub continuous_const).norm).continuousOn).mul hdc.norm
  obtain ⟨a, ha, hamax⟩ := (isCompact_closedBall c ρ).exists_isMaxOn
    (nonempty_closedBall.mpr hρ0.le) hφc
  have hφa : ρ * ‖deriv f c‖ ≤ φ a := by
    have := hamax (mem_closedBall_self hρ0.le)
    simpa [hφ] using this
  set t := ρ - ‖a - c‖ with ht
  have hφa' : φ a = t * ‖deriv f a‖ := rfl
  have hpos : 0 < φ a := lt_of_lt_of_le (by have := norm_pos_iff.mpr hd0; positivity) hφa
  have ht0 : 0 < t := by
    by_contra h; push Not at h
    have : φ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _)
    linarith
  have hfa0 : 0 < ‖deriv f a‖ := by
    by_contra h; push Not at h
    have : φ a ≤ 0 := by rw [hφa']; exact mul_nonpos_of_nonneg_of_nonpos ht0.le h
    linarith
  have hfa : deriv f a ≠ 0 := norm_pos_iff.mp hfa0
  -- the derivative is at most `2|f′(a)|` on `D(a, t/2)`
  have hsmall : ball a (t / 2) ⊆ closedBall c ρ := fun z hz => by
    rw [mem_ball] at hz; rw [mem_closedBall]
    have := dist_triangle z a c
    rw [dist_eq_norm a c] at this
    linarith
  have hball : ball a (t / 2) ⊆ ball c s := hsmall.trans hcl
  have hder : ∀ z ∈ ball a (t / 2), ‖deriv f z‖ ≤ 2 * ‖deriv f a‖ := fun z hz => by
    have h1 := hamax (hsmall hz)
    simp only [hφ, Set.mem_ofPred_eq] at h1
    have h2 : t / 2 ≤ ρ - ‖z - c‖ := by
      rw [mem_ball] at hz
      have := dist_triangle z a c
      rw [dist_eq_norm z c, dist_eq_norm a c] at this
      linarith
    have h3 : t / 2 * ‖deriv f z‖ ≤ t * ‖deriv f a‖ :=
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    nlinarith
  -- rescale to the unit disk
  set κ : ℂ := deriv f a * (t / 2 : ℝ) with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero hfa (by exact_mod_cast (by positivity : t / 2 ≠ 0))
  set g : ℂ → ℂ := fun u => (f (a + (t / 2 : ℝ) * u) - f a) / κ with hg
  have hmap : ∀ u ∈ ball (0 : ℂ) 1, a + (t / 2 : ℝ) * u ∈ ball a (t / 2) := fun u hu => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    rw [mem_ball, dist_zero_right] at hu
    nlinarith
  have hgd : DifferentiableOn ℂ g (ball 0 1) := fun u hu => by
    have h1 : DifferentiableAt ℂ (fun u : ℂ => a + (t / 2 : ℝ) * u) u := by fun_prop
    exact ((((hfd _ (hball (hmap u hu))).comp u h1).sub_const _).div_const _).differentiableWithinAt
  have hg0 : g 0 = 0 := by simp [hg]
  have hg1 : deriv g 0 = 1 := by
    have h1 : HasDerivAt (fun u : ℂ => a + (t / 2 : ℝ) * u) ((t / 2 : ℝ) : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul ((t / 2 : ℝ) : ℂ)).const_add a
    have h2 := (((hfd a (hball (mem_ball_self (by positivity)))).hasDerivAt.comp_of_eq
      (0 : ℂ) h1 (by simp)).sub_const (f a)).div_const κ
    have h3 : HasDerivAt g (deriv f a * ((t / 2 : ℝ) : ℂ) / κ) 0 := h2
    rw [h3.deriv, hκ, div_self hκ0]
  have hgb : ∀ u ∈ ball (0 : ℂ) 1, ‖g u‖ ≤ 2 := fun u hu => by
    have hmv := (convex_ball a (t / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => hfd z (hball hz)) hder (mem_ball_self (by positivity)) (hmap u hu)
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      at hmv
    rw [mem_ball, dist_zero_right] at hu
    rw [hg, norm_div, hκ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg u, mul_pos hfa0 ht0]
  have hland := ball_subset_image_of_bounded hgd hg0 hg1 hgb
  refine ⟨f a, fun v hv => ?_⟩
  rw [mem_ball] at hv
  have hv' : (v - f a) / κ ∈ ball (0 : ℂ) (1 / (8 * (2 + 3))) := by
    rw [mem_ball, dist_zero_right, norm_div, hκ, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), div_lt_iff₀ (by positivity), ← dist_eq_norm]
    have : s * ‖deriv f c‖ / 160 ≤ t * ‖deriv f a‖ / 80 := by
      have := hφa; rw [hφa'] at this; rw [hρ] at this; linarith
    nlinarith
  obtain ⟨u, hu, hgu⟩ := hland hv'
  refine ⟨a + (t / 2 : ℝ) * u, hball (hmap u hu), ?_⟩
  simp only [hg] at hgu
  field_simp at hgu
  linear_combination hgu

end Azurite.DLMF
