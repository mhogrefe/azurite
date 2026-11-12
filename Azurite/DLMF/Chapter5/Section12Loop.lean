/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section12Trig
import Azurite.DLMF.Chapter5.Section9Hankel

/-!
# DLMF §5.12: circles around a branch point

The loop integrals 5.12.10–5.12.12 consist of segments on which the integrand is a constant phase
times Euler's integrand, and circles around the branch points `0` and `1`. For a circle of radius
`δ` around `0`, traversed once counterclockwise from `δ` with `t^{a−1}` continued from its principal
value (`arc0`),

  `∫ h(t) t^{a−1} dt = (e^{2πia} − 1) ∫₀^δ h(r) r^{a−1} dr`, `ℜa > 0`, `h` holomorphic near the
  closed disk (`arc0_eq`).

Proof: in the coordinate `t = e^w` the circle is the side `ℜw = ln δ` of the rectangle
`[−R, ln δ] × [0, 2π]`, the two horizontal sides are the segment `[e^{−R}, δ]` on two sheets
(phases `1` and `e^{2πia}`), and the left side is `O(e^{−Rℜa})`. Cauchy's theorem for the
rectangle (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) and `R → ∞` give the
identity.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- The circle `t = δe^{iθ}`, `0 ≤ θ ≤ 2π`, of `∫ h(t) t^{a−1} dt`, with
`t^{a−1} = δ^{a−1}e^{i(a−1)θ}` continued from the principal value at `t = δ`. -/
noncomputable def arc0 (h : ℂ → ℂ) (a : ℂ) (δ : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), h (δ * cexp (θ * I)) * ((δ : ℂ) ^ (a - 1) * cexp ((a - 1) * θ * I)) *
    (I * δ * cexp (θ * I))

theorem cexp_log_add_mul_I {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    cexp ((Real.log δ : ℂ) + y * I) = δ * cexp (y * I) := by
  rw [Complex.exp_add, ← ofReal_exp, Real.exp_log hδ]

/-- **Circle around a branch point** (see the module docstring). -/
theorem arc0_eq {h : ℂ → ℂ} {ρ δ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (hh : DifferentiableOn ℂ h (Metric.ball 0 ρ)) {a : ℂ} (ha : 0 < a.re) :
    arc0 h a δ = (cexp (2 * π * a * I) - 1) * ∫ r in (0 : ℝ)..δ, h r * (r : ℂ) ^ (a - 1) := by
  have hπ := Real.pi_pos
  set g : ℂ → ℂ := fun w => h (cexp w) * cexp (a * w)
  set L := Real.log δ
  set c := cexp (2 * π * a * I)
  set F : ℝ → ℂ := fun u => ∫ r in u..δ, h r * (r : ℂ) ^ (a - 1)
  set V : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..(2 * π), g (x + y * I)
  have hball : ∀ w : ℂ, w.re ≤ L → cexp w ∈ Metric.ball (0 : ℂ) ρ := fun w hw => by
    rw [mem_ball_zero_iff, Complex.norm_exp]
    calc Real.exp w.re ≤ Real.exp L := Real.exp_le_exp.mpr hw
      _ = δ := Real.exp_log hδ
      _ < ρ := hδρ
  have hcont : ContinuousOn h (Metric.closedBall 0 δ) :=
    hh.continuousOn.mono (Metric.closedBall_subset_ball hδρ)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) δ).exists_bound_of_continuousOn hcont
  -- (i) the circle is the right side of the rectangle
  have hright : I * ∫ y in (0 : ℝ)..(2 * π), g (L + y * I) = arc0 h a δ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [g, L]
    rw [cexp_log_add_mul_I hδ, cpow_pos_eq hδ, show (δ : ℂ) = cexp (Real.log δ) by
      rw [← ofReal_exp, Real.exp_log hδ]]
    rw [show cexp (a * ((Real.log δ : ℂ) + y * I)) = cexp ((a - 1) * Real.log δ) *
        cexp ((a - 1) * y * I) * (cexp (Real.log δ) * cexp (y * I)) by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring]
    ring
  -- (ii) the identity for each rectangle
  have hrect : ∀ x : ℝ, x < L → arc0 h a δ = (c - 1) * F (Real.exp x) + I * V x := by
    intro x hx
    have hd : DifferentiableOn ℂ g (uIcc ((x : ℂ)).re ((L : ℂ) + 2 * π * I).re ×ℂ
        uIcc ((x : ℂ)).im ((L : ℂ) + 2 * π * I).im) := by
      intro w hw
      have hwre : w.re ≤ L := by
        have : w.re ∈ uIcc x L := by simpa using (mem_reProdIm.mp hw).1
        rw [uIcc_of_le hx.le] at this
        exact this.2
      exact (((hh.differentiableAt (Metric.isOpen_ball.mem_nhds (hball w hwre))).comp w
        (differentiableAt_exp)).mul ((differentiableAt_id.const_mul a).cexp)).differentiableWithinAt
    have H := integral_boundary_rect_eq_zero_of_differentiableOn g (x : ℂ) ((L : ℂ) + 2 * π * I) hd
    simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re,
      re_ofNat, im_ofNat, mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add,
      smul_eq_mul] at H
    -- the top side is `c` times the bottom side
    have htop : ∫ t in x..L, g (t + ((2 * π : ℝ) : ℂ) * I) =
        c * ∫ t in x..L, g (t + ((0 : ℝ) : ℂ) * I) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [g, c, ofReal_zero, zero_mul, add_zero]
      push_cast
      rw [Complex.exp_add, exp_two_pi_mul_I, mul_one, mul_add, Complex.exp_add,
        show a * (2 * π * I) = 2 * π * a * I by ring]
      ring
    -- the bottom side is the segment `[e^x, δ]`
    have hbot : ∫ t in x..L, g (t + ((0 : ℝ) : ℂ) * I) = F (Real.exp x) := by
      simp only [ofReal_zero, zero_mul, add_zero]
      have hsub := intervalIntegral.integral_deriv_smul_comp' (a := x) (b := L)
        (f := Real.exp) (f' := Real.exp) (g := fun r : ℝ => h r * (r : ℂ) ^ (a - 1))
        (fun t _ => Real.hasDerivAt_exp t) Real.continuous_exp.continuousOn ?_
      · rw [Real.exp_log hδ] at hsub
        simp only [F]
        rw [← hsub]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [g, Function.comp, Complex.real_smul, ofReal_exp]
        rw [cexp_cpow_of_im (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos]),
          mul_left_comm, ← Complex.exp_add]
        congr 2
        ring
      · intro r hr
        obtain ⟨t, ht, rfl⟩ := hr
        have hr0 : 0 < Real.exp t := Real.exp_pos t
        have hrδ : Real.exp t ≤ δ := by
          rw [uIcc_of_le hx.le] at ht
          calc Real.exp t ≤ Real.exp L := Real.exp_le_exp.mpr ht.2
            _ = δ := Real.exp_log hδ
        have hb : ((Real.exp t : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
          rw [mem_ball_zero_iff, norm_real, Real.norm_of_nonneg hr0.le]; linarith
        refine ContinuousAt.continuousWithinAt ?_
        exact ((hh.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hb)).comp
          continuous_ofReal.continuousAt).mul
          (continuousAt_ofReal_cpow_const _ _ (Or.inr hr0.ne'))
    rw [← hright]
    simp only [V]
    rw [htop, hbot] at H
    linear_combination H
  -- (iii) the left side vanishes as `x → −∞`
  have hV : Tendsto V atBot (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => M * Real.exp (2 * π * |a.im|) * Real.exp (x * a.re) *
        |2 * π - 0|) atBot (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.atBot_mul_const ha))
      simpa using (this.const_mul (M * Real.exp (2 * π * |a.im|))).mul_const |2 * π - 0|
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_le_atBot L] with x hx
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [uIoc_of_le (by linarith)] at hy
    simp only [g, norm_mul]
    have h1 : ‖h (cexp (x + y * I))‖ ≤ M := hM _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
      simp
      calc Real.exp x ≤ Real.exp L := Real.exp_le_exp.mpr hx
        _ = δ := Real.exp_log hδ)
    have h2 : ‖cexp (a * (x + y * I))‖ ≤ Real.exp (2 * π * |a.im|) * Real.exp (x * a.re) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, mul_zero, sub_zero,
        add_zero, mul_one, zero_add, add_im]
      nlinarith [neg_abs_le a.im, abs_nonneg a.im, hy.1, hy.2]
    calc ‖h (cexp (x + y * I))‖ * ‖cexp (a * (x + y * I))‖
        ≤ M * (Real.exp (2 * π * |a.im|) * Real.exp (x * a.re)) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := by ring
  -- (iv) the segment tends to `[0, δ]`
  have hF : Tendsto (fun x => F (Real.exp x)) atBot (𝓝 (F 0)) := by
    have hint : IntegrableOn (fun r : ℝ => h r * (r : ℂ) ^ (a - 1)) (uIcc 0 δ) := by
      have h1 : IntervalIntegrable (fun r : ℝ => (r : ℂ) ^ (a - 1)) volume 0 δ :=
        intervalIntegral.intervalIntegrable_cpow' (by simp only [sub_re, one_re]; linarith)
      have h2 : ContinuousOn (fun r : ℝ => h r) (uIcc 0 δ) := by
        refine hcont.comp continuous_ofReal.continuousOn fun r hr => ?_
        rw [uIcc_of_le hδ.le] at hr
        rw [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_of_nonneg hr.1]
        exact hr.2
      rw [uIcc_of_le hδ.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hδ.le).mp (h1.continuousOn_mul h2)
    have hc := intervalIntegral.continuousOn_primitive_interval_left hint
    have h0 : (0 : ℝ) ∈ uIcc 0 δ := left_mem_uIcc
    have hexp : Tendsto Real.exp atBot (𝓝[uIcc 0 δ] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot, ?_⟩
      filter_upwards [eventually_le_atBot L] with x hx
      rw [uIcc_of_le hδ.le]
      exact ⟨(Real.exp_pos x).le, (Real.exp_le_exp.mpr hx).trans (Real.exp_log hδ).le⟩
    exact (hc 0 h0).tendsto.comp hexp
  -- conclusion
  have hlim : Tendsto (fun x => (c - 1) * F (Real.exp x) + I * V x) atBot
      (𝓝 ((c - 1) * F 0 + I * 0)) := (hF.const_mul _).add (hV.const_mul _)
  rw [mul_zero, add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_lt_atBot L] with x hx
  exact hrect x hx

/-! ### Helpers -/

/-- `sin(πb)Γ(b) = π/Γ(1 − b)` away from the poles `b = 0, −1, −2, …` (at a positive integer
both sides vanish). -/
theorem sin_mul_Gamma {b : ℂ} (hb : ∀ n : ℕ, b ≠ -n) :
    Complex.sin (π * b) * Gamma b = π * (Gamma (1 - b))⁻¹ := by
  by_cases hs : Complex.sin (π * b) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbk : b = k := by
      have := hk; rw [mul_comm] at this; exact mul_right_cancel₀ hπ this
    rcases le_or_gt k 0 with h | h
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -n := ⟨k.natAbs, by omega⟩
      exact absurd (by rw [hbk]; push_cast; ring) (hb n)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
      rw [hs, zero_mul, hbk, show (1 : ℂ) - ((n + 1 : ℤ) : ℂ) = -(n : ℂ) by push_cast; ring,
        Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  · have h := Complex.Gamma_mul_Gamma_one_sub b
    have h1 : Gamma (1 - b) ≠ 0 := fun h0 => by
      rw [h0, mul_zero, eq_comm, div_eq_zero_iff] at h
      rcases h with h | h
      · exact Real.pi_ne_zero (by exact_mod_cast h)
      · exact hs h
    field_simp
    rw [mul_assoc, h]
    field_simp

/-- `e^{−iπ(b−1)}(1 − e^{2πib}) = 2i sin(πb)`. -/
theorem exp_phase_mul (b : ℂ) :
    cexp (-(π * (b - 1) * I)) * (1 - cexp (2 * π * b * I)) = 2 * I * Complex.sin (π * b) := by
  rw [Complex.sin, show -(π * (b - 1) * I) = -(π * b * I) + π * I by ring, Complex.exp_add,
    exp_pi_mul_I, show 2 * π * b * I = π * b * I + π * b * I by ring, Complex.exp_add,
    show -(π * b) * I = -(π * b * I) by ring, Complex.exp_neg]
  have h0 := Complex.exp_ne_zero (π * b * I)
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem one_sub_mem_slitPlane_of_lt_one {u : ℂ} (hu : ‖u‖ < 1) : 1 - u ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have := re_le_norm u
  simp only [sub_re, one_re]
  linarith

theorem one_add_mem_slitPlane_of_lt_one {u : ℂ} (hu : ‖u‖ < 1) : 1 + u ∈ slitPlane := by
  have := one_sub_mem_slitPlane_of_lt_one (u := -u) (by rwa [norm_neg])
  rwa [sub_neg_eq_add] at this

theorem norm_ofReal_mul_cexp {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) : ‖(δ : ℂ) * cexp (θ * I)‖ = δ := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hδ]

/-- Euler's integral split at `x`. -/
theorem beta_split {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) +
      ∫ t in x..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) = dlmfBeta a b := by
  have hi := Complex.betaIntegral_convergent ha hb
  have hm : x ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one]; exact ⟨hx0, hx1⟩
  rw [intervalIntegral.integral_add_adjacent_intervals (hi.mono_set (uIcc_subset_uIcc_left hm))
    (hi.mono_set (uIcc_subset_uIcc_right hm)), (dlmf_5_12_1 ha hb).1]

/-- `∫₀^ε (1 − r)^{a−1} r^{b−1} dr = ∫_{1−ε}^1 t^{a−1}(1 − t)^{b−1} dt`. -/
theorem integral_reflect (a b : ℂ) (ε : ℝ) :
    ∫ r in (0 : ℝ)..ε, (1 - (r : ℂ)) ^ (a - 1) * (r : ℂ) ^ (b - 1) =
      ∫ t in (1 - ε)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) := by
  have := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) (a := 0) (b := ε) 1
  rw [sub_zero] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [ofReal_sub, ofReal_one, sub_sub_cancel]

/-- `b ↦ ∫ₓʸ t^{a−1}(1 − t)^{b−1} dt` is entire for `0 ≤ x`, `y < 1`, `ℜa > 0`. -/
theorem differentiable_beta_seg_b {a : ℂ} (ha : 0 < a.re) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y < 1) : Differentiable ℂ fun b : ℂ =>
      ∫ t in x..y, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) := by
  have hw : Integrable (fun t : ℝ => (t : ℂ) ^ (a - 1)) (volume.restrict (Ioc x y)) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := x) (b := y)
      (by simp only [sub_re, one_re]; linarith)).1
  have hd := differentiable_integral_mul_cexp_of_bounded (μ := volume.restrict (Ioc x y)) hw
    (ℓ := fun t : ℝ => ((Real.log (1 - t) : ℝ) : ℂ))
    (by fun_prop : Measurable fun t : ℝ => ((Real.log (1 - t) : ℝ) : ℂ)).aestronglyMeasurable
    (M := -Real.log (1 - y))
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      have h1 : 0 < 1 - t := by linarith [ht.2]
      rw [norm_real, Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos h1.le (by linarith [ht.1]))]
      exact neg_le_neg (Real.log_le_log (by linarith) (by linarith [ht.2])))
  have he : (fun b : ℂ => ∫ t in x..y, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) =
      fun b => ∫ t in Ioc x y, (t : ℂ) ^ (a - 1) * cexp ((b - 1) * (Real.log (1 - t) : ℂ)) := by
    funext b
    rw [intervalIntegral.integral_of_le hxy]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have h1 : 0 < 1 - t := by linarith [ht.2]
    rw [show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring, cpow_pos_eq h1]
  rw [he]
  exact hd.comp (differentiable_id.sub_const 1)

/-! ### 5.12.10 -/

/-- The loop of 5.12.10 (Figure 5.12.1): from `0` along `[0, 1 − δ]`, once counterclockwise
around `|t − 1| = δ` starting and ending at `1 − δ`, and back along `[0, 1 − δ]`. The power
`(t − 1)^{b−1}` is continuous on the loop: it is `(1 − t)^{b−1}e^{−iπ(b−1)}` on the way out
(`ph(t − 1) = −π`), `δ^{b−1}e^{i(b−1)θ}` at `t = 1 + δe^{iθ}`, `−π ≤ θ ≤ π` (the principal
value), and `(1 − t)^{b−1}e^{iπ(b−1)}` on the way back. -/
noncomputable def loop10 (a b : ℂ) (δ : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * ((1 - (t : ℂ)) ^ (b - 1) *
    cexp (-(π * (b - 1) * I)))) +
  (∫ θ in (-π)..π, (1 + δ * cexp (θ * I)) ^ (a - 1) *
    ((δ : ℂ) ^ (b - 1) * cexp ((b - 1) * θ * I)) * (I * δ * cexp (θ * I))) -
  ∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * ((1 - (t : ℂ)) ^ (b - 1) * cexp (π * (b - 1) * I))

/-- The circle of 5.12.10 is `−e^{−iπ(b−1)}` times a standard circle around `0`. -/
theorem loop10_arc_eq (a b : ℂ) (δ : ℝ) :
    (∫ θ in (-π)..π, (1 + δ * cexp (θ * I)) ^ (a - 1) *
      ((δ : ℂ) ^ (b - 1) * cexp ((b - 1) * θ * I)) * (I * δ * cexp (θ * I))) =
      -cexp (-(π * (b - 1) * I)) * arc0 (fun u => (1 - u) ^ (a - 1)) b δ := by
  have h := intervalIntegral.integral_comp_sub_right (fun θ : ℝ =>
    (1 + δ * cexp (θ * I)) ^ (a - 1) * ((δ : ℂ) ^ (b - 1) * cexp ((b - 1) * θ * I)) *
      (I * δ * cexp (θ * I))) π (a := 0) (b := 2 * π)
  rw [zero_sub, show 2 * π - π = π by ring] at h
  rw [← h, arc0, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  have e : cexp (((φ - π : ℝ) : ℂ) * I) = -cexp (φ * I) := by
    rw [ofReal_sub, sub_mul, Complex.exp_sub, exp_pi_mul_I, div_neg, div_one]
  rw [e, show (b - 1) * ((φ - π : ℝ) : ℂ) * I = (b - 1) * φ * I + -(π * (b - 1) * I) by
    push_cast; ring, Complex.exp_add]
  ring_nf

theorem loop10_eq_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    loop10 a b δ = 2 * I * Complex.sin (π * b) * dlmfBeta a b := by
  have harc := arc0_eq (h := fun u => (1 - u) ^ (a - 1)) hδ0 hδ1 (fun u hu =>
    (differentiableAt_id.const_sub 1 |>.cpow_const (one_sub_mem_slitPlane_of_lt_one
      (by simpa using hu))).differentiableWithinAt) hb
  rw [integral_reflect] at harc
  have hseg : ∀ c : ℂ, (∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * ((1 - (t : ℂ)) ^ (b - 1) *
      c)) = (∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) * c :=
    fun c => by
      rw [← intervalIntegral.integral_mul_const]
      exact intervalIntegral.integral_congr fun t _ => by ring
  rw [loop10, loop10_arc_eq, harc, hseg, hseg, ← exp_phase_mul,
    ← beta_split ha hb (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith)]
  rw [show cexp (π * (b - 1) * I) = cexp (-(π * (b - 1) * I)) * cexp (2 * π * b * I) by
    rw [← Complex.exp_add, show -(π * (b - 1) * I) + 2 * π * b * I = π * (b - 1) * I + 2 * π * I
      by ring, Complex.exp_add, exp_two_pi_mul_I, mul_one]]
  ring

theorem differentiable_loop10 {a : ℂ} (ha : 0 < a.re) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Differentiable ℂ fun b => loop10 a b δ := by
  have hseg := differentiable_beta_seg_b ha le_rfl (by linarith : (0 : ℝ) ≤ 1 - δ)
    (by linarith : 1 - δ < 1)
  have hseg' : ∀ c : ℂ → ℂ, Differentiable ℂ c → Differentiable ℂ fun b =>
      ∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * ((1 - (t : ℂ)) ^ (b - 1) * c b) := by
    intro c hc
    have : (fun b => ∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * ((1 - (t : ℂ)) ^ (b - 1) *
        c b)) = fun b => (∫ t in (0 : ℝ)..(1 - δ), (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) *
        c b := by
      funext b
      rw [← intervalIntegral.integral_mul_const]
      exact intervalIntegral.integral_congr fun t _ => by ring
    rw [this]
    exact hseg.mul hc
  have hA : Continuous fun θ : ℝ => (1 + δ * cexp (θ * I)) ^ (a - 1) *
      (I * δ * cexp (θ * I)) := by
    refine (Continuous.cpow (by fun_prop) continuous_const fun θ =>
      one_add_mem_slitPlane_of_lt_one ?_).mul (by fun_prop)
    rw [norm_ofReal_mul_cexp hδ0.le]; exact hδ1
  have harc := (differentiable_integral_mul_cexp hA (by fun_prop :
    Continuous fun θ : ℝ => -(((Real.log δ : ℝ) : ℂ) + θ * I)) (-π) π).comp
    (differentiable_id.sub_const (1 : ℂ))
  have he : (fun b : ℂ => ∫ θ in (-π)..π, (1 + δ * cexp (θ * I)) ^ (a - 1) *
      ((δ : ℂ) ^ (b - 1) * cexp ((b - 1) * θ * I)) * (I * δ * cexp (θ * I))) =
      (fun c : ℂ => ∫ θ in (-π)..π, (1 + δ * cexp (θ * I)) ^ (a - 1) * (I * δ * cexp (θ * I)) *
        cexp (-(c * -(((Real.log δ : ℝ) : ℂ) + θ * I)))) ∘ fun b => b - 1 := by
    funext b
    simp only [Function.comp]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [cpow_pos_eq hδ0, ← Complex.exp_add, show -((b - 1) * -(((Real.log δ : ℝ) : ℂ) + θ * I)) =
      (b - 1) * Real.log δ + (b - 1) * θ * I by ring]
    ring
  have harc' : Differentiable ℂ (fun b : ℂ => ∫ θ in (-π)..π, (1 + δ * cexp (θ * I)) ^ (a - 1) *
      ((δ : ℂ) ^ (b - 1) * cexp ((b - 1) * θ * I)) * (I * δ * cexp (θ * I))) := by
    rw [he]; exact harc
  have h1 := hseg' (fun b => cexp (-(π * (b - 1) * I))) (by fun_prop)
  have h3 := hseg' (fun b => cexp (π * (b - 1) * I)) (by fun_prop)
  exact (h1.add harc').sub h3

/-- **DLMF 5.12.10**, entire form: `(2πi)⁻¹ ∫₀^{(1+)} t^{a−1}(t − 1)^{b−1} dt =
Γ(a)/(Γ(1 − b)Γ(a + b))` for `ℜa > 0`, every `b`, and every loop radius `δ ∈ (0, 1)`. -/
theorem dlmf_5_12_10_gamma {a : ℂ} (ha : 0 < a.re) (b : ℂ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 / (2 * π * I) * loop10 a b δ = Gamma a * (Gamma (1 - b))⁻¹ * (Gamma (a + b))⁻¹ := by
  have hinv : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  have hf : Differentiable ℂ fun b => 1 / (2 * π * I) * loop10 a b δ :=
    (differentiable_loop10 ha hδ0 hδ1).const_mul _
  have hg : Differentiable ℂ fun b : ℂ => Gamma a * (Gamma (1 - b))⁻¹ * (Gamma (a + b))⁻¹ :=
    ((hinv.comp (differentiable_id.const_sub 1)).const_mul _).mul
      (hinv.comp (differentiable_id.const_add a))
  have heq := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ 1) (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℂ) ∈ {w : ℂ | 0 < w.re} by simp)] with w hw
      have hw' : ∀ n : ℕ, w ≠ -n := fun n h => by
        have := congrArg re h; simp at this; rw [this] at hw; simp at hw
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [loop10_eq_of_re_pos ha hw hδ0 hδ1, dlmfBeta]
      have hs := sin_mul_Gamma hw'
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have hI : (I : ℂ) ≠ 0 := I_ne_zero
      calc 1 / (2 * π * I) * (2 * I * Complex.sin (π * w) * (Gamma a * Gamma w / Gamma (a + w)))
          = Complex.sin (π * w) * Gamma w * Gamma a * (Gamma (a + w))⁻¹ / π := by
            field_simp
        _ = π * (Gamma (1 - w))⁻¹ * Gamma a * (Gamma (a + w))⁻¹ / π := by rw [hs]
        _ = _ := by field_simp)
  exact heq (mem_univ b)

/-- **DLMF 5.12.10**: `(2πi)⁻¹ ∫₀^{(1+)} t^{a−1}(t − 1)^{b−1} dt = (sin(πb)/π) B(a, b)`, `ℜa > 0`,
on the loop `loop10` of any radius `δ ∈ (0, 1)` (`b ≠ 0, −1, −2, …`, where `B(a, b)` has a pole;
`dlmf_5_12_10_gamma` covers every `b`). -/
theorem dlmf_5_12_10 {a b : ℂ} (ha : 0 < a.re) (hb : ∀ n : ℕ, b ≠ -n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 / (2 * π * I) * loop10 a b δ = Complex.sin (π * b) / π * dlmfBeta a b := by
  rw [dlmf_5_12_10_gamma ha b hδ0 hδ1, dlmfBeta]
  have hs := sin_mul_Gamma hb
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show Complex.sin (π * b) / π * (Gamma a * Gamma b / Gamma (a + b)) =
    Complex.sin (π * b) * Gamma b * Gamma a * (Gamma (a + b))⁻¹ / π by ring, hs]
  field_simp

/-! ### 5.12.11 -/

/-- The loop of 5.12.11 (Figure 5.12.2): in from `+∞` to `δ` along `ph t = 0`, once
counterclockwise around `|t| = δ` (crossing the real axis between `−1` and `0`, `δ < 1`), and out
to `+∞` along `ph t = 2π`. `t^{a−1}` is continuous on the loop and principal at the start:
`r^{a−1}` coming in, `δ^{a−1}e^{i(a−1)θ}` at `t = δe^{iθ}`, and `r^{a−1}e^{2πi(a−1)}` going out;
`(1 + t)^{−a−b}` is principal throughout. -/
noncomputable def loop11 (a b : ℂ) (δ : ℝ) : ℂ :=
  -(∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b)) +
  (∫ θ in (0 : ℝ)..(2 * π), (1 + δ * cexp (θ * I)) ^ (-a - b) *
    ((δ : ℂ) ^ (a - 1) * cexp ((a - 1) * θ * I)) * (I * δ * cexp (θ * I))) +
  ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * cexp (2 * π * (a - 1) * I) * (1 + (r : ℂ)) ^ (-a - b)

theorem exp_two_pi_mul_sub_one (a : ℂ) :
    cexp (2 * π * a * I) - 1 = 2 * I * cexp (π * a * I) * Complex.sin (π * a) := by
  rw [Complex.sin, show 2 * π * a * I = π * a * I + π * a * I by ring, Complex.exp_add,
    show -(π * a) * I = -(π * a * I) by ring, Complex.exp_neg]
  have h0 := Complex.exp_ne_zero (π * a * I)
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem integrableOn_beta_ray {b : ℂ} (hb : 0 < b.re) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun r : ℝ => cexp (-(Real.log r : ℂ) - b * (Real.log (1 + r) : ℂ))) (Ioi δ) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -1 - b.re) (by linarith) hδ).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun r : ℝ =>
      cexp (-(Real.log r : ℂ) - b * (Real.log (1 + r) : ℂ))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hδ.trans hr
    rw [Complex.norm_exp]
    simp only [sub_re, neg_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
    rw [Real.rpow_def_of_pos hr0]
    refine Real.exp_le_exp.mpr ?_
    have := Real.log_le_log hr0 (by linarith : r ≤ 1 + r)
    nlinarith

theorem beta_ray_eq {a b : ℂ} {r : ℝ} (hr : 0 < r) :
    (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b) =
      cexp (-(Real.log r : ℂ) - b * (Real.log (1 + r) : ℂ)) *
        cexp (a * ((Real.log r - Real.log (1 + r) : ℝ) : ℂ)) := by
  rw [cpow_pos_eq hr, show (1 : ℂ) + r = ((1 + r : ℝ) : ℂ) by push_cast; ring,
    cpow_pos_eq (by linarith), ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem differentiable_beta_ray {b : ℂ} (hb : 0 < b.re) {δ : ℝ} (hδ : 0 < δ) :
    Differentiable ℂ fun a : ℂ => ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b) := by
  have hd := differentiable_integral_mul_cexp_of_bounded (μ := volume.restrict (Ioi δ))
    (integrableOn_beta_ray hb hδ)
    (ℓ := fun r : ℝ => ((Real.log r - Real.log (1 + r) : ℝ) : ℂ))
    (by fun_prop : Measurable fun r : ℝ =>
      ((Real.log r - Real.log (1 + r) : ℝ) : ℂ)).aestronglyMeasurable
    (M := Real.log (1 + δ) - Real.log δ)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
      have hr0 : 0 < r := hδ.trans hr
      have h1 : Real.log r - Real.log (1 + r) ≤ 0 := by
        have := Real.log_le_log hr0 (by linarith : r ≤ 1 + r); linarith
      have h2 : Real.log δ - Real.log (1 + δ) ≤ Real.log r - Real.log (1 + r) := by
        rw [← Real.log_div hδ.ne' (by linarith), ← Real.log_div hr0.ne' (by linarith)]
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [show δ ≤ r from le_of_lt hr]
      rw [norm_real, Real.norm_eq_abs, abs_of_nonpos h1]
      linarith)
  convert hd using 2 with a
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr => beta_ray_eq (hδ.trans hr)

theorem loop11_eq_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) : loop11 a b δ = (cexp (2 * π * a * I) - 1) * dlmfBeta a b := by
  have harc := arc0_eq (h := fun u => (1 + u) ^ (-a - b)) hδ0 hδ1 (fun u hu =>
    ((differentiableAt_id.const_add 1).cpow_const (one_add_mem_slitPlane_of_lt_one
      (by simpa using hu))).differentiableWithinAt) ha
  have hB := dlmf_5_12_3 ha hb
  have hI := integrableOn_beta_Ioi ha hb
  have e : ∀ r : ℝ, (r : ℂ) ^ (a - 1) / (1 + (r : ℂ)) ^ (a + b) =
      (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b) := fun r => by
    rw [div_eq_mul_inv, ← cpow_neg, neg_add']
  simp_rw [e] at hB hI
  have hsplit := intervalIntegral.integral_interval_add_Ioi hI (hI.mono_set (Ioi_subset_Ioi hδ0.le))
  rw [hB] at hsplit
  have h0 : ∫ r in (0 : ℝ)..δ, (1 + (r : ℂ)) ^ (-a - b) * (r : ℂ) ^ (a - 1) =
      ∫ r in (0 : ℝ)..δ, (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b) :=
    intervalIntegral.integral_congr fun r _ => by ring
  have hout : ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * cexp (2 * π * (a - 1) * I) *
      (1 + (r : ℂ)) ^ (-a - b) = cexp (2 * π * a * I) *
        ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    rw [show 2 * π * (a - 1) * I = 2 * π * a * I + -(2 * π * I) by ring, Complex.exp_add,
      Complex.exp_neg, exp_two_pi_mul_I, inv_one, mul_one]
    ring
  have harc' : (∫ θ in (0 : ℝ)..(2 * π), (1 + δ * cexp (θ * I)) ^ (-a - b) *
      ((δ : ℂ) ^ (a - 1) * cexp ((a - 1) * θ * I)) * (I * δ * cexp (θ * I))) =
      arc0 (fun u => (1 + u) ^ (-a - b)) a δ := rfl
  rw [loop11, harc', harc, hout, h0, ← hsplit]
  ring

theorem differentiable_loop11 {b : ℂ} (hb : 0 < b.re) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Differentiable ℂ fun a => loop11 a b δ := by
  have hR := differentiable_beta_ray hb hδ0
  have hout : (fun a : ℂ => ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * cexp (2 * π * (a - 1) * I) *
      (1 + (r : ℂ)) ^ (-a - b)) = fun a => cexp (2 * π * (a - 1) * I) *
        ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) * (1 + (r : ℂ)) ^ (-a - b) := by
    funext a
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun r => by ring)
  have hmem : ∀ θ : ℝ, 1 + (δ : ℂ) * cexp (θ * I) ∈ slitPlane := fun θ =>
    one_add_mem_slitPlane_of_lt_one (by rw [norm_ofReal_mul_cexp hδ0.le]; exact hδ1)
  have hL : Continuous fun θ : ℝ => Complex.log (1 + δ * cexp (θ * I)) -
      (((Real.log δ : ℝ) : ℂ) + θ * I) := by
    refine Continuous.sub ?_ (by fun_prop)
    exact continuous_iff_continuousAt.mpr fun θ =>
      ContinuousAt.comp (f := fun θ : ℝ => 1 + (δ : ℂ) * cexp (θ * I)) (x := θ)
        (continuousAt_clog (hmem θ)) (by fun_prop)
  have hA : Continuous fun θ : ℝ => (1 + δ * cexp (θ * I)) ^ (-b) *
      cexp (-(((Real.log δ : ℝ) : ℂ) + θ * I)) * (I * δ * cexp (θ * I)) :=
    ((Continuous.cpow (by fun_prop) continuous_const hmem).mul (by fun_prop)).mul (by fun_prop)
  have harc := differentiable_integral_mul_cexp hA hL 0 (2 * π)
  have he : (fun a : ℂ => ∫ θ in (0 : ℝ)..(2 * π), (1 + δ * cexp (θ * I)) ^ (-a - b) *
      ((δ : ℂ) ^ (a - 1) * cexp ((a - 1) * θ * I)) * (I * δ * cexp (θ * I))) =
      fun a => ∫ θ in (0 : ℝ)..(2 * π), (1 + δ * cexp (θ * I)) ^ (-b) *
        cexp (-(((Real.log δ : ℝ) : ℂ) + θ * I)) * (I * δ * cexp (θ * I)) *
        cexp (-(a * (Complex.log (1 + δ * cexp (θ * I)) - (((Real.log δ : ℝ) : ℂ) + θ * I)))) := by
    funext a
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have h0 : (1 : ℂ) + δ * cexp (θ * I) ≠ 0 := slitPlane_ne_zero (hmem θ)
    rw [show -a - b = -a + -b by ring, cpow_add _ _ h0, cpow_def_of_ne_zero h0, cpow_pos_eq hδ0]
    have key : cexp (Complex.log (1 + δ * cexp (θ * I)) * -a) *
        (cexp ((a - 1) * ((Real.log δ : ℝ) : ℂ)) * cexp ((a - 1) * θ * I)) =
        cexp (-(((Real.log δ : ℝ) : ℂ) + θ * I)) * cexp (-(a * (Complex.log (1 + δ * cexp (θ * I)) -
          (((Real.log δ : ℝ) : ℂ) + θ * I)))) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    linear_combination ((1 + δ * cexp (θ * I)) ^ (-b) * (I * δ * cexp (θ * I))) * key
  rw [← he] at harc
  have hout' : Differentiable ℂ (fun a : ℂ => ∫ r in Ioi δ, (r : ℂ) ^ (a - 1) *
      cexp (2 * π * (a - 1) * I) * (1 + (r : ℂ)) ^ (-a - b)) := by
    rw [hout]
    exact (by fun_prop : Differentiable ℂ fun a : ℂ => cexp (2 * π * (a - 1) * I)).mul hR
  unfold loop11
  exact (hR.neg.add harc).add hout'

/-- **DLMF 5.12.11**, entire form: the loop integral `∫_∞^{(0+)} t^{a−1}(1 + t)^{−a−b} dt` equals
`2πi e^{iπa}Γ(b)/(Γ(1 − a)Γ(a + b))` for every `a` and `ℜb > 0`. -/
theorem dlmf_5_12_11_gamma (a : ℂ) {b : ℂ} (hb : 0 < b.re) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    loop11 a b δ = 2 * π * I * cexp (π * a * I) * Gamma b * (Gamma (1 - a))⁻¹ *
      (Gamma (a + b))⁻¹ := by
  have hinv : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  have hg : Differentiable ℂ fun a : ℂ => 2 * π * I * cexp (π * a * I) * Gamma b *
      (Gamma (1 - a))⁻¹ * (Gamma (a + b))⁻¹ :=
    ((((by fun_prop : Differentiable ℂ fun a : ℂ => 2 * π * I * cexp (π * a * I))).mul_const
      _).mul (hinv.comp (differentiable_id.const_sub 1))).mul
      (hinv.comp (differentiable_id.add_const b))
  have heq := ((differentiable_loop11 hb hδ0 hδ1).differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_of_preconnected_of_eventuallyEq (hg.differentiableOn.analyticOnNhd
    isOpen_univ) isPreconnected_univ (mem_univ 1) (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℂ) ∈ {w : ℂ | 0 < w.re} by simp)] with w hw
      have hw' : ∀ n : ℕ, w ≠ -n := fun n h => by
        have := congrArg re h; simp at this; rw [this] at hw; simp at hw
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [loop11_eq_of_re_pos hw hb hδ0 hδ1, dlmfBeta, exp_two_pi_mul_sub_one]
      have hs := sin_mul_Gamma hw'
      calc 2 * I * cexp (π * w * I) * Complex.sin (π * w) * (Gamma w * Gamma b / Gamma (w + b))
          = 2 * I * cexp (π * w * I) * (Complex.sin (π * w) * Gamma w) * Gamma b *
            (Gamma (w + b))⁻¹ := by ring
        _ = _ := by rw [hs]; ring)
  exact heq (mem_univ a)

/-- **DLMF 5.12.11**: `(e^{2πia} − 1)⁻¹ ∫_∞^{(0+)} t^{a−1}(1 + t)^{−a−b} dt = B(a, b)` for
`ℜb > 0`, `a ∉ ℤ`, on the loop `loop11` of any radius `δ ∈ (0, 1)`. -/
theorem dlmf_5_12_11 {a b : ℂ} (hb : 0 < b.re) (ha : ∀ n : ℤ, a ≠ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) : 1 / (cexp (2 * π * I * a) - 1) * loop11 a b δ = dlmfBeta a b := by
  have hs : Complex.sin (π * a) ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    exact ha k (by rw [mul_comm] at hk; exact mul_right_cancel₀ hπ hk)
  have hG1 : Gamma (1 - a) ≠ 0 := Complex.Gamma_ne_zero fun m h => ha (m + 1) (by
    push_cast; linear_combination -h)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub a
  have hE : cexp (π * a * I) ≠ 0 := Complex.exp_ne_zero _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [dlmf_5_12_11_gamma a hb hδ0 hδ1, show 2 * π * I * a = 2 * π * a * I by ring,
    exp_two_pi_mul_sub_one, dlmfBeta]
  have hGa : Gamma a = π / Complex.sin (π * a) / Gamma (1 - a) := by
    rw [← hrefl]; field_simp
  rw [hGa]
  field_simp

end Azurite.DLMF
