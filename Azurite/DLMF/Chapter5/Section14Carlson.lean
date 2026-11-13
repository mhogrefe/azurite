/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Carlson's theorem

If `f` is holomorphic on a neighbourhood `ℜz > −δ` of the closed right half-plane, of exponential
type there, of type `< π` on the imaginary axis, and vanishes at `0, 1, 2, …`, then `f = 0` on
`ℜz ≥ 0` (Carlson 1914; used for DLMF 5.14.7).

Proof: `φ = f/sin(πz)` is holomorphic (removable singularities at the integers) and of exponential
type (`|sin(πu)| ≥ 2|u|` for `|ℜu| ≤ ½`, and the maximum principle on small discs about the
integers); on the imaginary axis it decays like `e^{−a|y|}`, `a = π − c > 0`. Then
`G(z) = φ(z) e^{−κ(z+1) log(z+1)}`, `κ = 2a/π`, is bounded on the imaginary axis, of order `< 2`,
and decays superexponentially along the positive reals, so `G = 0` by the Phragmén–Lindelöf
principle (`PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`).
-/

open Complex Filter Topology Set Metric

namespace Azurite.DLMF

/-! ### A lower bound for `sin(πu)` -/

theorem sq_norm_sin (w : ℂ) :
    ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have e : Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ) +
      ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * I := by
    rw [Complex.sin_eq]; push_cast; ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have := Real.cosh_sq w.im
  have := Real.sin_sq_add_cos_sq w.re
  linear_combination (Real.sin w.re ^ 2) * (by assumption : Real.cosh w.im ^ 2 =
    Real.sinh w.im ^ 2 + 1) + Real.sinh w.im ^ 2 * this

/-- `|sin(πu)| ≥ 2|u|` for `|ℜu| ≤ ½`. -/
theorem two_mul_norm_le_norm_sin_pi {u : ℂ} (hu : |u.re| ≤ 1 / 2) :
    2 * ‖u‖ ≤ ‖Complex.sin (Real.pi * u)‖ := by
  have hπ := Real.pi_pos
  have hre : (Real.pi * u : ℂ).re = Real.pi * u.re := by simp
  have him : (Real.pi * u : ℂ).im = Real.pi * u.im := by simp
  have h1 : (2 * |u.re|) ^ 2 ≤ Real.sin (Real.pi * u.re) ^ 2 := by
    have hj := Real.mul_le_sin (x := Real.pi * |u.re|) (by positivity) (by nlinarith)
    have hj' : 2 * |u.re| ≤ |Real.sin (Real.pi * u.re)| := by
      rw [show Real.sin (Real.pi * u.re) = Real.sin (Real.pi * u.re) from rfl]
      rcases le_total 0 u.re with h | h
      · rw [abs_of_nonneg h] at hj ⊢
        have : 2 / Real.pi * (Real.pi * u.re) = 2 * u.re := by field_simp
        rw [this] at hj
        exact hj.trans (le_abs_self _)
      · rw [abs_of_nonpos h] at hj ⊢
        have : 2 / Real.pi * (Real.pi * -u.re) = 2 * -u.re := by field_simp
        rw [this, show Real.pi * -u.re = -(Real.pi * u.re) by ring, Real.sin_neg] at hj
        exact hj.trans (neg_le_abs _)
    rw [← sq_abs (Real.sin _)]
    exact pow_le_pow_left₀ (by positivity) hj' 2
  have h2 : (2 * |u.im|) ^ 2 ≤ Real.sinh (Real.pi * u.im) ^ 2 := by
    have hs : Real.pi * |u.im| ≤ |Real.sinh (Real.pi * u.im)| := by
      rw [Real.abs_sinh, abs_mul, abs_of_pos hπ]
      exact Real.self_le_sinh_iff.mpr (by positivity)
    rw [← sq_abs (Real.sinh _)]
    exact pow_le_pow_left₀ (by positivity) ((mul_le_mul_of_nonneg_right
      (by linarith [Real.two_le_pi]) (abs_nonneg _)).trans hs) 2
  have h3 : (2 * ‖u‖) ^ 2 ≤ ‖Complex.sin (Real.pi * u)‖ ^ 2 := by
    rw [sq_norm_sin, hre, him, mul_pow, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_abs u.re, sq_abs u.im]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3

theorem sin_pi_add_int (u : ℂ) (k : ℤ) :
    ‖Complex.sin (Real.pi * (u + k))‖ = ‖Complex.sin (Real.pi * u)‖ := by
  rw [mul_add, Complex.sin_add, show (Real.pi : ℂ) * k = (k : ℂ) * Real.pi by ring,
    Complex.sin_int_mul_pi, mul_zero, add_zero, norm_mul,
    show ((k : ℂ) * Real.pi) = ((k * Real.pi : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    Complex.norm_real, Real.norm_eq_abs, Real.abs_cos_int_mul_pi, mul_one]

theorem sin_pi_eq_zero_iff (z : ℂ) : Complex.sin (Real.pi * z) = 0 ↔ ∃ k : ℤ, z = k := by
  rw [Complex.sin_eq_zero_iff]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ hπ (by rw [hk]; ring)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/-! ### The quotient `f(z)/sin(πz)` -/

/-- `f(z)/sin(πz)`, with the removable singularities at the integers filled in. -/
noncomputable def carlsonQ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if Complex.sin (Real.pi * z) = 0 then deriv f z / (Real.pi * Complex.cos (Real.pi * z))
  else f z / Complex.sin (Real.pi * z)

theorem hasDerivAt_sin_pi (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.sin (Real.pi * w))
      (Complex.cos (Real.pi * z) * Real.pi) z := by
  simpa using ((hasDerivAt_id z).const_mul (Real.pi : ℂ)).csin

theorem cos_pi_int_ne_zero (k : ℤ) : Complex.cos (Real.pi * k) ≠ 0 := by
  rw [show (Real.pi : ℂ) * k = ((k * Real.pi : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos]
  intro h
  have := Real.abs_cos_int_mul_pi k
  rw [Complex.ofReal_eq_zero.mp h, abs_zero] at this
  exact zero_ne_one this

section Quotient

variable {f : ℂ → ℂ} {δ : ℝ}

theorem differentiableAt_carlsonQ_of_ne {z : ℂ} (hfz : DifferentiableAt ℂ f z)
    (hz : Complex.sin (Real.pi * z) ≠ 0) : DifferentiableAt ℂ (carlsonQ f) z := by
  have hev : carlsonQ f =ᶠ[𝓝 z] fun w => f w / Complex.sin (Real.pi * w) := by
    have hc : ContinuousAt (fun w : ℂ => Complex.sin (Real.pi * w)) z := by fun_prop
    filter_upwards [hc.eventually_ne hz] with w hw
    simp only [carlsonQ, hw, ↓reduceIte]
  exact (hfz.div (hasDerivAt_sin_pi z).differentiableAt hz).congr_of_eventuallyEq hev

theorem tendsto_carlsonQ_int {k : ℤ} (hfk : DifferentiableAt ℂ f k) (hk : f k = 0) :
    Tendsto (carlsonQ f) (𝓝[≠] (k : ℂ)) (𝓝 (carlsonQ f k)) := by
  have hsin : Complex.sin (Real.pi * (k : ℂ)) = 0 := (sin_pi_eq_zero_iff _).mpr ⟨k, rfl⟩
  simp only [carlsonQ, hsin, ↓reduceIte]
  have h1 := hasDerivAt_iff_tendsto_slope.mp hfk.hasDerivAt
  have h2 := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_sin_pi (k : ℂ))
  have hne : Complex.cos (Real.pi * k) * Real.pi ≠ 0 :=
    mul_ne_zero (cos_pi_int_ne_zero k) (by exact_mod_cast Real.pi_ne_zero)
  have h3 := h1.div h2 hne
  rw [show deriv f k / (Real.pi * Complex.cos (Real.pi * k)) =
    deriv f k / (Complex.cos (Real.pi * k) * Real.pi) by ring]
  refine h3.congr' ?_
  have hball : ∀ᶠ w in 𝓝[≠] (k : ℂ), w ∈ ball (k : ℂ) (1 / 2) ∧ w ≠ k :=
    Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by norm_num)))
      self_mem_nhdsWithin
  filter_upwards [hball] with w ⟨hw, hwk⟩
  have hsw : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h0
    obtain ⟨j, rfl⟩ := (sin_pi_eq_zero_iff w).mp h0
    have hjk : j ≠ k := fun h => hwk (by rw [h])
    rw [mem_ball, dist_eq_norm, ← Int.cast_sub, Complex.norm_intCast] at hw
    have : (1 : ℝ) ≤ |((j - k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjk)
    linarith
  simp only [carlsonQ, hsw, ↓reduceIte]
  rw [Pi.div_apply, slope_def_field, slope_def_field, hk, hsin, sub_zero, sub_zero]
  have hwk' : w - k ≠ 0 := sub_ne_zero.mpr hwk
  field_simp

/-- The radius `ρ = min(δ, ½)/2` of the discs about the integers. -/
noncomputable def carlsonRho (δ : ℝ) : ℝ := min δ (1 / 2) / 2

theorem carlsonRho_pos (hδ : 0 < δ) : 0 < carlsonRho δ := by
  unfold carlsonRho; positivity

theorem carlsonRho_le (δ : ℝ) : carlsonRho δ ≤ 1 / 4 := by
  unfold carlsonRho; linarith [min_le_right δ (1 / 2)]

theorem carlsonRho_lt (hδ : 0 < δ) : carlsonRho δ < δ := by
  unfold carlsonRho; linarith [min_le_left δ (1 / 2), lt_min hδ (by norm_num : (0 : ℝ) < 1 / 2)]

theorem int_nonneg_of_re {k : ℤ} (hk : -carlsonRho δ < ((k : ℂ)).re) : 0 ≤ k := by
  have := carlsonRho_le δ
  simp only [Complex.intCast_re] at hk
  by_contra h
  push Not at h
  have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
  linarith

variable (hδ : 0 < δ) (hf : DifferentiableOn ℂ f {z | -δ < z.re}) (hz : ∀ k : ℕ, f k = 0)
include hδ hf hz

/-- `f(z)/sin(πz)` is holomorphic on `ℜz > −ρ`. -/
theorem differentiableOn_carlsonQ :
    DifferentiableOn ℂ (carlsonQ f) {z | -carlsonRho δ < z.re} := by
  have hρ := carlsonRho_lt hδ
  have hopen : IsOpen {z : ℂ | -δ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfat : ∀ z : ℂ, -carlsonRho δ < z.re → DifferentiableAt ℂ f z := fun z hz' =>
    hf.differentiableAt (hopen.mem_nhds (show -δ < z.re by linarith))
  intro z hz'
  by_cases hs : Complex.sin (Real.pi * z) = 0
  · obtain ⟨k, rfl⟩ := (sin_pi_eq_zero_iff z).mp hs
    have hk0 := int_nonneg_of_re hz'
    have hfk : f k = 0 := by
      have := hz k.toNat
      rwa [show ((k.toNat : ℕ) : ℂ) = (k : ℂ) by exact_mod_cast Int.toNat_of_nonneg hk0] at this
    have hball : ball (k : ℂ) (1 / 2) ∩ {z | -carlsonRho δ < z.re} ∈ 𝓝 (k : ℂ) :=
      Filter.inter_mem (ball_mem_nhds _ (by norm_num))
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz')
    have hdo : DifferentiableOn ℂ (carlsonQ f)
        (ball (k : ℂ) (1 / 2) ∩ {z | -carlsonRho δ < z.re}) :=
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hball).mp
        ⟨fun w hw => ?_, ?_⟩
    · exact (hdo.differentiableAt hball).differentiableWithinAt
    · refine (differentiableAt_carlsonQ_of_ne (hfat w hw.1.2) ?_).differentiableWithinAt
      intro h0
      obtain ⟨j, rfl⟩ := (sin_pi_eq_zero_iff w).mp h0
      have hjk : j ≠ k := fun h => hw.2 (by rw [h]; rfl)
      have hw1 := hw.1.1
      rw [mem_ball, dist_eq_norm, ← Int.cast_sub, Complex.norm_intCast] at hw1
      have : (1 : ℝ) ≤ |((j - k : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjk)
      linarith
    · exact continuousWithinAt_compl_self.mp (tendsto_carlsonQ_int (hfat _ hz') hfk)
  · exact (differentiableAt_carlsonQ_of_ne (hfat z hz') hs).differentiableWithinAt

omit hδ hf in
/-- `f = sin(πz) · f(z)/sin(πz)` on `ℜz > −ρ`. -/
theorem carlsonQ_mul_sin {z : ℂ} (hz' : -carlsonRho δ < z.re) :
    f z = carlsonQ f z * Complex.sin (Real.pi * z) := by
  by_cases hs : Complex.sin (Real.pi * z) = 0
  · obtain ⟨k, rfl⟩ := (sin_pi_eq_zero_iff z).mp hs
    have hk0 := int_nonneg_of_re hz'
    rw [hs, mul_zero]
    have := hz k.toNat
    rwa [show ((k.toNat : ℕ) : ℂ) = (k : ℂ) by exact_mod_cast Int.toNat_of_nonneg hk0] at this
  · simp only [carlsonQ, hs, ↓reduceIte]
    rw [div_mul_cancel₀ _ hs]

/-- `f(z)/sin(πz)` is of exponential type on `ℜz ≥ 0` (maximum principle on discs about the
integers). -/
theorem carlsonQ_bound (hexp : ∃ A B : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) :
    ∃ A' B' : ℝ, 0 ≤ B' ∧ ∀ z : ℂ, 0 ≤ z.re → ‖carlsonQ f z‖ ≤ A' * Real.exp (B' * ‖z‖) := by
  obtain ⟨A, B, hAB⟩ := hexp
  set A₀ := max A 0
  set B₀ := max B 0
  have hA₀ : 0 ≤ A₀ := le_max_right _ _
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hf0 : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ A₀ * Real.exp (B₀ * ‖z‖) := fun z hz' =>
    (hAB z hz').trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (Real.exp_pos _).le hA₀)
  set r := carlsonRho δ / 2
  have hr : 0 < r := by have := carlsonRho_pos hδ; positivity
  have hr4 : r ≤ 1 / 8 := by have := carlsonRho_le δ; simp only [r]; linarith
  have hreg : ∀ w : ℂ, -r ≤ w.re → -carlsonRho δ < w.re := fun w hw => by
    have := carlsonRho_pos hδ; simp only [r] at hw; linarith
  have hdq := differentiableOn_carlsonQ hδ hf hz
  have hopen : IsOpen {z : ℂ | -δ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨M₀, hM₀⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
    (f := f) (hf.continuousOn.mono fun w hw => by
      have h1 := Complex.abs_re_le_norm w
      rw [mem_sphere_zero_iff_norm] at hw
      have := carlsonRho_lt hδ
      show -δ < w.re
      have := (abs_le.mp (h1.trans hw.le)).1
      simp only [r] at this; linarith)
  set M := max M₀ 0
  refine ⟨(A₀ * Real.exp (2 * B₀ * r) + M) / (2 * r), B₀, hB₀, fun z hz' => ?_⟩
  have hM : 0 ≤ M := le_max_right _ _
  have hE1 : 1 ≤ Real.exp (B₀ * ‖z‖) := Real.one_le_exp (by positivity)
  set k : ℤ := round z.re
  have hk0 : 0 ≤ k := by
    simp only [k, round_eq]; exact Int.floor_nonneg.mpr (by linarith)
  have hu : |(z - k).re| ≤ 1 / 2 := by
    simp only [Complex.sub_re, Complex.intCast_re, k]; exact abs_sub_round z.re
  have hsinz : ‖Complex.sin (Real.pi * z)‖ = ‖Complex.sin (Real.pi * (z - k))‖ := by
    rw [← sin_pi_add_int (z - k) k, sub_add_cancel]
  -- off the small discs
  have hoff : ∀ w : ℂ, 0 ≤ w.re → r ≤ ‖w - round w.re‖ →
      ‖carlsonQ f w‖ ≤ ‖f w‖ / (2 * r) := by
    intro w hw hwr
    have hw' : |(w - (round w.re : ℤ)).re| ≤ 1 / 2 := by
      simp only [Complex.sub_re, Complex.intCast_re]; exact abs_sub_round w.re
    have hs := two_mul_norm_le_norm_sin_pi hw'
    rw [← sin_pi_add_int (w - (round w.re : ℤ)) (round w.re), sub_add_cancel] at hs
    have hs0 : Complex.sin (Real.pi * w) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hs; linarith
    simp only [carlsonQ, hs0, ↓reduceIte]
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
  by_cases hzr : r ≤ ‖z - k‖
  · refine (hoff z hz' hzr).trans ?_
    rw [div_le_iff₀ (by positivity)]
    calc ‖f z‖ ≤ A₀ * Real.exp (B₀ * ‖z‖) := hf0 z hz'
      _ ≤ A₀ * Real.exp (2 * B₀ * r) * Real.exp (B₀ * ‖z‖) + M * Real.exp (B₀ * ‖z‖) := by
          have h1 : 1 ≤ Real.exp (2 * B₀ * r) := Real.one_le_exp (by positivity)
          have hx := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA₀ (Real.exp_pos (B₀ * ‖z‖)).le)
          have hy := mul_nonneg hM (Real.exp_pos (B₀ * ‖z‖)).le
          nlinarith
      _ = _ := by field_simp
  · push Not at hzr
    have hzb : z ∈ closure (ball (k : ℂ) r) := subset_closure (by
      rw [mem_ball, dist_eq_norm]; exact hzr)
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball ?_ ?_ hzb
    · refine DifferentiableOn.diffContOnCl (hdq.mono fun w hw => hreg w ?_)
      rw [closure_ball _ hr.ne', mem_closedBall, dist_eq_norm] at hw
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (w - k)).trans hw)).1
      simp only [Complex.sub_re, Complex.intCast_re] at h1
      have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    · intro w hw
      rw [frontier_ball _ hr.ne', mem_sphere, dist_eq_norm] at hw
      have hwre : |(w - k).re| ≤ r := (Complex.abs_re_le_norm _).trans hw.le
      simp only [Complex.sub_re, Complex.intCast_re] at hwre
      have hs := two_mul_norm_le_norm_sin_pi (u := w - k)
        (by simp only [Complex.sub_re, Complex.intCast_re]; linarith)
      rw [← sin_pi_add_int (w - k) k, sub_add_cancel, hw] at hs
      have hs0 : Complex.sin (Real.pi * w) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hs; linarith
      simp only [carlsonQ, hs0, ↓reduceIte]
      rw [norm_div, div_le_iff₀ (by linarith)]
      have hfw : ‖f w‖ ≤ A₀ * Real.exp (2 * B₀ * r) * Real.exp (B₀ * ‖z‖) + M := by
        rcases eq_or_lt_of_le hk0 with hk | hk
        · have hw0 : w ∈ sphere (0 : ℂ) r := by
            rw [mem_sphere, dist_eq_norm, sub_zero]
            rw [← hk, Int.cast_zero, sub_zero] at hw; exact hw
          have : ‖f w‖ ≤ M := (hM₀ w hw0).trans (le_max_left _ _)
          have : 0 ≤ A₀ * Real.exp (2 * B₀ * r) * Real.exp (B₀ * ‖z‖) := by positivity
          linarith
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          have hwr : 0 ≤ w.re := by linarith [(abs_le.mp hwre).1]
          have hwz : ‖w‖ ≤ ‖z‖ + 2 * r := by
            have : ‖w - z‖ ≤ 2 * r := by
              calc ‖w - z‖ = ‖(w - k) - (z - k)‖ := by ring_nf
                _ ≤ ‖w - k‖ + ‖z - k‖ := norm_sub_le _ _
                _ ≤ 2 * r := by rw [hw]; linarith
            calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
              _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
              _ ≤ _ := by linarith
          calc ‖f w‖ ≤ A₀ * Real.exp (B₀ * ‖w‖) := hf0 w hwr
            _ ≤ A₀ * Real.exp (B₀ * (‖z‖ + 2 * r)) := by
                gcongr
            _ = A₀ * Real.exp (2 * B₀ * r) * Real.exp (B₀ * ‖z‖) := by
                rw [mul_assoc, ← Real.exp_add]; ring_nf
            _ ≤ _ := by linarith
      calc ‖f w‖ ≤ A₀ * Real.exp (2 * B₀ * r) * Real.exp (B₀ * ‖z‖) + M := hfw
        _ ≤ (A₀ * Real.exp (2 * B₀ * r) + M) * Real.exp (B₀ * ‖z‖) := by nlinarith
        _ = (A₀ * Real.exp (2 * B₀ * r) + M) / (2 * r) * Real.exp (B₀ * ‖z‖) * (2 * r) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

end Quotient

/-! ### The auxiliary factor `e^{−κ(z+1) log(z+1)}` -/

/-- `e^{−κ(z+1) log(z+1)}`. -/
noncomputable def carlsonE (κ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(κ : ℂ) * ((z + 1) * Complex.log (z + 1)))

theorem differentiableAt_carlsonE (κ : ℝ) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (carlsonE κ) z := by
  have hs : z + 1 ∈ slitPlane := Or.inl (by simp; linarith)
  unfold carlsonE
  exact ((differentiableAt_const _).mul ((differentiableAt_id.add_const 1).mul
    ((differentiableAt_id.add_const 1).clog hs))).cexp

theorem norm_carlsonE_imag {κ : ℝ} (hκ : 0 ≤ κ) (y : ℝ) :
    ‖carlsonE κ (y * I)‖ ≤ Real.exp (κ * (Real.pi / 2) * |y|) := by
  rw [carlsonE, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  set w : ℂ := y * I + 1
  have hwre : w.re = 1 := by simp [w]
  have hwim : w.im = y := by simp [w]
  have hlog : 0 ≤ Real.log ‖w‖ := Real.log_nonneg (by
    have := Complex.re_le_norm w; rw [hwre] at this; exact this)
  have harg : |arg w| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by rw [hwre]; norm_num)
  have hre : (-(κ : ℂ) * (w * Complex.log w)).re = -κ * (Real.log ‖w‖ - y * arg w) := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.log_re, Complex.log_im, hwre, hwim]
    ring
  rw [hre]
  have : y * arg w ≤ |y| * (Real.pi / 2) := by
    calc y * arg w ≤ |y * arg w| := le_abs_self _
      _ = |y| * |arg w| := abs_mul _ _
      _ ≤ |y| * (Real.pi / 2) := mul_le_mul_of_nonneg_left harg (abs_nonneg _)
  nlinarith

theorem norm_carlsonE_real (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖carlsonE κ x‖ = Real.exp (-κ * ((x + 1) * Real.log (x + 1))) := by
  rw [carlsonE, Complex.norm_exp, show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by linarith)]
  congr 1
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re]

theorem norm_carlsonE_le {κ : ℝ} (hκ : 0 ≤ κ) {z : ℂ} (hz : 0 ≤ z.re) (h1 : 1 ≤ ‖z‖) :
    ‖carlsonE κ z‖ ≤ Real.exp (κ * (8 + 4 * Real.pi) * ‖z‖ ^ (3 / 2 : ℝ)) := by
  rw [carlsonE, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  set w : ℂ := z + 1
  have hw1 : 1 ≤ ‖w‖ := by
    have := Complex.re_le_norm w; simp only [w, Complex.add_re, Complex.one_re] at this; linarith
  have hw2 : ‖w‖ ≤ 2 * ‖z‖ := by
    calc ‖w‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖z‖ := by rw [norm_one]; linarith
  have hlog : ‖Complex.log w‖ ≤ 2 * ‖w‖ ^ (1 / 2 : ℝ) + Real.pi := by
    have e : Complex.log w = (Real.log ‖w‖ : ℂ) + (arg w : ℂ) * I := by
      apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hw1)]
      have := Real.log_le_rpow_div (norm_nonneg w) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact Complex.abs_arg_le_pi w
  have hre : (-(κ : ℂ) * (w * Complex.log w)).re ≤ κ * (‖w‖ * ‖Complex.log w‖) := by
    have h := Complex.re_le_norm (-(κ : ℂ) * (w * Complex.log w))
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ,
      norm_mul] at h
    exact h
  have h32 : ‖w‖ ^ (3 / 2 : ℝ) = ‖w‖ * ‖w‖ ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have hww : ‖w‖ ≤ ‖w‖ ^ (3 / 2 : ℝ) := by
    calc ‖w‖ = ‖w‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
  have hwz : ‖w‖ ^ (3 / 2 : ℝ) ≤ 4 * ‖z‖ ^ (3 / 2 : ℝ) := by
    calc ‖w‖ ^ (3 / 2 : ℝ) ≤ (2 * ‖z‖) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hw2 (by norm_num)
      _ = 2 ^ (3 / 2 : ℝ) * ‖z‖ ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _ ≤ 2 ^ (2 : ℝ) * ‖z‖ ^ (3 / 2 : ℝ) := by
          gcongr
          · norm_num
          · norm_num
      _ = 4 * ‖z‖ ^ (3 / 2 : ℝ) := by norm_num
  have hpos : 0 ≤ ‖w‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hπ := Real.pi_pos
  calc (-(κ : ℂ) * (w * Complex.log w)).re ≤ κ * (‖w‖ * ‖Complex.log w‖) := hre
    _ ≤ κ * (‖w‖ * (2 * ‖w‖ ^ (1 / 2 : ℝ) + Real.pi)) := by gcongr
    _ = κ * (2 * ‖w‖ ^ (3 / 2 : ℝ) + Real.pi * ‖w‖) := by rw [h32]; ring
    _ ≤ κ * ((2 + Real.pi) * ‖w‖ ^ (3 / 2 : ℝ)) := by gcongr; nlinarith
    _ ≤ κ * ((2 + Real.pi) * (4 * ‖z‖ ^ (3 / 2 : ℝ))) := by gcongr
    _ = κ * (8 + 4 * Real.pi) * ‖z‖ ^ (3 / 2 : ℝ) := by ring

/-! ### Carlson's theorem -/

theorem exp_div_four_le_sinh {t : ℝ} (ht : 1 ≤ t) : Real.exp t / 4 ≤ Real.sinh t := by
  rw [Real.sinh_eq]
  have h1 := Real.add_one_le_exp (2 * t)
  have h2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos t
  have h5 := Real.exp_pos (-t)
  nlinarith

theorem norm_sin_pi_mul_I (y : ℝ) :
    ‖Complex.sin (Real.pi * (y * I))‖ = Real.sinh (Real.pi * |y|) := by
  rw [show (Real.pi : ℂ) * (y * I) = ((Real.pi * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sinh,
    Complex.norm_real, Real.norm_eq_abs, Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]

/-- **Carlson's theorem.** If `f` is holomorphic on `ℜz > −δ`, of exponential type on `ℜz ≥ 0`,
of type `c < π` on the imaginary axis, and `f(k) = 0` for `k = 0, 1, 2, …`, then `f = 0` on
`ℜz ≥ 0`. -/
theorem carlson {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hf : DifferentiableOn ℂ f {z | -δ < z.re})
    (hz : ∀ k : ℕ, f k = 0)
    (hexp : ∃ A B : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ A * Real.exp (B * ‖z‖))
    (him : ∃ C c : ℝ, c < Real.pi ∧ ∀ y : ℝ, ‖f (y * I)‖ ≤ C * Real.exp (c * |y|)) :
    ∀ z : ℂ, 0 ≤ z.re → f z = 0 := by
  obtain ⟨A', B', hB', hQ⟩ := carlsonQ_bound hδ hf hz hexp
  obtain ⟨C, c, hcπ, hC⟩ := him
  set a := Real.pi - c with ha_def
  have ha : 0 < a := by linarith
  set κ := 2 * a / Real.pi with hκ_def
  have hπ := Real.pi_pos
  have hκ : 0 < κ := by positivity
  have hκa : κ * (Real.pi / 2) = a := by rw [hκ_def]; field_simp
  have hA' : 0 ≤ A' := by
    have := hQ 0 (by simp)
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set Q := carlsonQ f
  set K := 4 * C + A' * Real.exp B' * Real.exp a
  -- the quotient decays on the imaginary axis
  have hQim : ∀ y : ℝ, ‖Q (y * I)‖ ≤ K * Real.exp (-a * |y|) := by
    intro y
    have hE : Real.exp (-a * |y|) * Real.exp (a * |y|) = 1 := by
      rw [← Real.exp_add]; simp
    by_cases hy : 1 ≤ |y|
    · have hs := exp_div_four_le_sinh (t := Real.pi * |y|) (by nlinarith [Real.two_le_pi])
      rw [← norm_sin_pi_mul_I] at hs
      have hs0 : Complex.sin (Real.pi * (y * I)) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hs; linarith [Real.exp_pos (Real.pi * |y|)]
      have hQy : Q (y * I) = f (y * I) / Complex.sin (Real.pi * (y * I)) := by
        simp only [Q, carlsonQ, hs0, ↓reduceIte]
      rw [hQy, norm_div, div_le_iff₀ (norm_pos_iff.mpr hs0)]
      have hcy : Real.exp (c * |y|) = Real.exp (-a * |y|) * Real.exp (Real.pi * |y|) := by
        rw [← Real.exp_add]; congr 1; rw [ha_def]; ring
      calc ‖f (y * I)‖ ≤ C * Real.exp (c * |y|) := hC y
        _ = 4 * C * Real.exp (-a * |y|) * (Real.exp (Real.pi * |y|) / 4) := by rw [hcy]; ring
        _ ≤ K * Real.exp (-a * |y|) * ‖Complex.sin (Real.pi * (y * I))‖ := by
            gcongr
            simp only [K]
            have : 0 ≤ A' * Real.exp B' * Real.exp a := by positivity
            linarith
    · push Not at hy
      have h1 := hQ (y * I) (by simp)
      have hn : ‖(y : ℂ) * I‖ = |y| := by simp
      rw [hn] at h1
      calc ‖Q (y * I)‖ ≤ A' * Real.exp (B' * |y|) := h1
        _ ≤ A' * Real.exp B' := by gcongr; nlinarith [abs_nonneg y]
        _ ≤ A' * Real.exp B' * (Real.exp a * Real.exp (-a * |y|)) := by
            have : 1 ≤ Real.exp a * Real.exp (-a * |y|) := by
              rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [abs_nonneg y])
            have : 0 ≤ A' * Real.exp B' := by positivity
            nlinarith
        _ ≤ K * Real.exp (-a * |y|) := by
            simp only [K]
            have : 0 ≤ 4 * C * Real.exp (-a * |y|) := by positivity
            nlinarith
  set G : ℂ → ℂ := fun z => Q z * carlsonE κ z
  have hρ := carlsonRho_pos hδ
  have hρ4 := carlsonRho_le δ
  have hU : DifferentiableOn ℂ G {z | -carlsonRho δ < z.re} :=
    (differentiableOn_carlsonQ hδ hf hz).mul fun z hz' =>
      (differentiableAt_carlsonE κ (by
        have : -carlsonRho δ < z.re := hz'
        linarith)).differentiableWithinAt
  have hd : DiffContOnCl ℂ G {z | 0 < z.re} := by
    refine DifferentiableOn.diffContOnCl (hU.mono ?_)
    rw [closure_setOfPred_lt_re]
    intro z hz'
    show -carlsonRho δ < z.re
    have : 0 ≤ z.re := hz'
    linarith
  have hexpG : ∃ c' < (2 : ℝ), ∃ B,
      G =O[Bornology.cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}]
        fun z => Real.exp (B * ‖z‖ ^ c') := by
    refine ⟨3 / 2, by norm_num, B' + κ * (8 + 4 * Real.pi), Asymptotics.IsBigO.of_bound A' ?_⟩
    filter_upwards [(eventually_cobounded_le_norm 1).filter_mono inf_le_left,
      mem_inf_of_right (mem_principal_self {z : ℂ | 0 < z.re})] with z hz1 hzre
    have hzre' : 0 ≤ z.re := le_of_lt hzre
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hz32 : ‖z‖ ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
      calc ‖z‖ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
    calc ‖G z‖ = ‖Q z‖ * ‖carlsonE κ z‖ := norm_mul _ _
      _ ≤ A' * Real.exp (B' * ‖z‖) *
          Real.exp (κ * (8 + 4 * Real.pi) * ‖z‖ ^ (3 / 2 : ℝ)) :=
          mul_le_mul (hQ z hzre') (norm_carlsonE_le hκ.le hzre' hz1) (norm_nonneg _)
            (by positivity)
      _ ≤ A' * Real.exp (B' * ‖z‖ ^ (3 / 2 : ℝ)) *
          Real.exp (κ * (8 + 4 * Real.pi) * ‖z‖ ^ (3 / 2 : ℝ)) := by gcongr
      _ = A' * Real.exp ((B' + κ * (8 + 4 * Real.pi)) * ‖z‖ ^ (3 / 2 : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hreG : Asymptotics.SuperpolynomialDecay atTop Real.exp fun x : ℝ => ‖G x‖ := by
    intro N
    set T : ℝ → ℝ := fun x => (N + B') * x - κ * ((x + 1) * Real.log (x + 1))
    have hT : Tendsto T atTop atBot := by
      have h1 : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_id
      have h2 : Tendsto (fun x : ℝ => (N + B') + -(κ * Real.log (x + 1))) atTop atBot :=
        tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp
          ((Real.tendsto_log_atTop.comp h1).const_mul_atTop hκ))
      refine tendsto_atBot_mono' _ ?_ (h1.atTop_mul_atBot₀ h2)
      filter_upwards [eventually_ge_atTop 0] with x hx
      simp only [T]
      have : 0 ≤ (N : ℝ) + B' := by positivity
      nlinarith
    have hlim : Tendsto (fun x => A' * Real.exp (T x)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp hT).const_mul A'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun x => by positivity) ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have hQx := hQ x (by simpa using hx)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at hQx
    calc Real.exp x ^ N * ‖G x‖ = Real.exp x ^ N * (‖Q x‖ * ‖carlsonE κ x‖) := by
          rw [norm_mul]
      _ ≤ Real.exp x ^ N * (A' * Real.exp (B' * x) *
          Real.exp (-κ * ((x + 1) * Real.log (x + 1)))) := by
          rw [norm_carlsonE_real κ hx]; gcongr
      _ = A' * Real.exp (T x) := by
          rw [← Real.exp_nat_mul]
          simp only [T]
          rw [show A' * Real.exp ((N + B') * x - κ * ((x + 1) * Real.log (x + 1))) =
            A' * (Real.exp (N * x) * Real.exp (B' * x) *
              Real.exp (-κ * ((x + 1) * Real.log (x + 1)))) by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf]
          ring
  have himG : ∃ C, ∀ x : ℝ, ‖G (x * I)‖ ≤ C := by
    refine ⟨K, fun y => ?_⟩
    calc ‖G (y * I)‖ = ‖Q (y * I)‖ * ‖carlsonE κ (y * I)‖ := norm_mul _ _
      _ ≤ K * Real.exp (-a * |y|) * Real.exp (κ * (Real.pi / 2) * |y|) :=
          mul_le_mul (hQim y) (norm_carlsonE_imag hκ.le y) (norm_nonneg _)
            (by have : 0 ≤ K := by simp only [K]; positivity
                positivity)
      _ = K := by rw [hκa, mul_assoc, ← Real.exp_add]; simp
  have hG0 := PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay hd hexpG
    hreG himG
  intro z hz'
  have hGz : Q z * carlsonE κ z = 0 := hG0 hz'
  have hQz : Q z = 0 := by
    rcases mul_eq_zero.mp hGz with h | h
    · exact h
    · exact absurd h (Complex.exp_ne_zero _)
  rw [carlsonQ_mul_sin hz (by linarith : -carlsonRho δ < z.re), show carlsonQ f z = Q z from rfl,
    hQz, zero_mul]

end Azurite.DLMF
