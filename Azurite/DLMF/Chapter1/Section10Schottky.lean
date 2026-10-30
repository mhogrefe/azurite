/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section10Bloch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §1.10(iii): Schottky's theorem (towards Picard's theorem)

Second step of the proof of Picard's theorem (`Section10Picard.lean`).

* The grid `CoshSqInt` of points `w` with `cosh² w ∈ ℤ` is invariant under `w ↦ w ± iπ/2` and
  `w ↦ w + n·iπ/2`, and every `w ∈ ℂ` lies within distance `2` of it (`exists_coshSqInt_near`).
* `schottky_core`: if `g` is holomorphic on the unit disk and omits `0` and `1`, then
  `H = log(√F − √(F − 1))` with `F = (log g)/(2πi)` satisfies `cosh² H = F` and so omits the grid;
  by Bloch's theorem `|H′|` is bounded, hence `|g(z)| ≤ schottkyS κ` for `|z| ≤ 1/2` whenever
  `|log |g(0)|| ≤ κ`.
* `schottky_unit`, `schottky` (**Schottky's theorem**): if `g` is holomorphic on `D(c, R)`, omits
  `0` and `1`, and `|g(c)| ≤ t`, then `|g| ≤ schottkyBound t` on `|z − c| ≤ R/2` (for small
  `|g(c)|` apply the core to `1 − g`).
-/

open Filter Topology Set Metric Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The grid `{w : cosh² w ∈ ℤ}` -/

/-- The grid of points where `cosh² w` is an integer. -/
def CoshSqInt (w : ℂ) : Prop := ∃ n : ℤ, Complex.cosh w ^ 2 = n

theorem cosh_sq_add_pi_div_two_I (z : ℂ) :
    Complex.cosh (z + (π / 2 : ℂ) * I) ^ 2 = 1 - Complex.cosh z ^ 2 := by
  have h1 : Complex.cosh ((π / 2 : ℂ) * I) = 0 := by
    rw [Complex.cosh_mul_I, ← ofReal_ofNat, ← ofReal_div, ← ofReal_cos, Real.cos_pi_div_two,
      ofReal_zero]
  have h2 : Complex.sinh ((π / 2 : ℂ) * I) = I := by
    rw [Complex.sinh_mul_I, ← ofReal_ofNat, ← ofReal_div, ← ofReal_sin, Real.sin_pi_div_two,
      ofReal_one, one_mul]
  rw [Complex.cosh_add, h1, h2, mul_zero, zero_add, mul_pow, I_sq]
  have := Complex.cosh_sq_sub_sinh_sq z
  linear_combination this

theorem CoshSqInt.add_pi_div_two_I {z : ℂ} (h : CoshSqInt z) : CoshSqInt (z + (π / 2 : ℂ) * I) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨1 - n, by rw [cosh_sq_add_pi_div_two_I, hn]; push_cast; ring⟩

theorem CoshSqInt.sub_pi_div_two_I {z : ℂ} (h : CoshSqInt z) : CoshSqInt (z - (π / 2 : ℂ) * I) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨1 - n, ?_⟩
  have := cosh_sq_add_pi_div_two_I (z - (π / 2 : ℂ) * I)
  rw [sub_add_cancel, hn] at this
  rw [show Complex.cosh (z - (π / 2 : ℂ) * I) ^ 2 = 1 - (n : ℂ) by linear_combination this]
  push_cast; ring

theorem CoshSqInt.add_int_mul {z : ℂ} (h : CoshSqInt z) (m : ℤ) :
    CoshSqInt (z + (m : ℂ) * ((π / 2 : ℂ) * I)) := by
  induction m using Int.induction_on with
  | zero => simpa using h
  | succ k ih =>
    have e : z + ((k + 1 : ℤ) : ℂ) * ((π / 2 : ℂ) * I) =
        z + ((k : ℤ) : ℂ) * ((π / 2 : ℂ) * I) + (π / 2 : ℂ) * I := by push_cast; ring
    rw [e]; exact ih.add_pi_div_two_I
  | pred k ih =>
    have e : z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * ((π / 2 : ℂ) * I) =
        z + ((-(k : ℤ) : ℤ) : ℂ) * ((π / 2 : ℂ) * I) - (π / 2 : ℂ) * I := by push_cast; ring
    rw [e]; exact ih.sub_pi_div_two_I

/-- Every point is within distance `2` of the grid. -/
theorem exists_coshSqInt_near (w : ℂ) : ∃ e, CoshSqInt e ∧ ‖w - e‖ < 2 := by
  set a := |w.re| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set N := ⌊Real.cosh a ^ 2⌋ with hN
  have hc0 : Continuous fun x : ℝ => Real.cosh x ^ 2 := by fun_prop
  have hN1 : (1 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ Real.cosh a ^ 2 := by
      nlinarith [Real.cosh_sq a, sq_nonneg (Real.sinh a)]
    rw [hN]; exact_mod_cast Int.le_floor.mpr (by exact_mod_cast this)
  have hNle : (N : ℝ) ≤ Real.cosh a ^ 2 := Int.floor_le _
  obtain ⟨τ, hτ, hτN⟩ := intermediate_value_Icc ha0 hc0.continuousOn
    ⟨by simp only [Real.cosh_zero, one_pow]; exact hN1, hNle⟩
  simp only at hτN
  have hlt : Real.cosh a ^ 2 - Real.cosh τ ^ 2 < 1 := by
    rw [hτN]; linarith [Int.lt_floor_add_one (Real.cosh a ^ 2)]
  have hid : Real.cosh a ^ 2 - Real.cosh τ ^ 2 = Real.sinh (a + τ) * Real.sinh (a - τ) := by
    rw [Real.sinh_add, Real.sinh_sub]
    have h1 := Real.cosh_sq a
    have h2 := Real.cosh_sq τ
    nlinarith [h1, h2]
  have hdist : a - τ < 1 := by
    have hs1 : 0 ≤ Real.sinh (a - τ) := Real.sinh_nonneg_iff.mpr (by linarith [hτ.2])
    have hs2 : Real.sinh (a - τ) ≤ Real.sinh (a + τ) := Real.sinh_le_sinh.mpr (by linarith [hτ.1])
    have : Real.sinh (a - τ) ^ 2 < 1 := by nlinarith
    have hx : a - τ ≤ Real.sinh (a - τ) := Real.self_le_sinh_iff.mpr (by linarith [hτ.2])
    nlinarith
  set t := if 0 ≤ w.re then τ else -τ with ht
  have htc : Real.cosh t ^ 2 = N := by
    rw [ht]; split_ifs <;> simp [Real.cosh_neg, hτN]
  have htu : |w.re - t| < 1 := by
    rw [ht]; split_ifs with h
    · rw [abs_of_nonneg h] at ha; rw [abs_lt]; constructor <;> linarith [hτ.2]
    · push Not at h; rw [abs_of_neg h] at ha; rw [abs_lt]; constructor <;> linarith [hτ.2]
  set m := round (w.im / (π / 2)) with hm
  have hπ := Real.pi_pos
  have hmv : |w.im - m * (π / 2)| ≤ π / 4 := by
    have h1 := abs_sub_round (w.im / (π / 2))
    rw [← hm] at h1
    have : w.im - m * (π / 2) = (π / 2) * (w.im / (π / 2) - m) := by field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  refine ⟨(t : ℂ) + (m : ℂ) * ((π / 2 : ℂ) * I), ?_, ?_⟩
  · refine CoshSqInt.add_int_mul ⟨N, ?_⟩ m
    rw [← ofReal_cosh, ← ofReal_pow, htc]; push_cast; rfl
  · have hre : (w - ((t : ℂ) + (m : ℂ) * ((π / 2 : ℂ) * I))).re = w.re - t := by simp
    have him : (w - ((t : ℂ) + (m : ℂ) * ((π / 2 : ℂ) * I))).im = w.im - m * (π / 2) := by
      simp
    calc ‖w - ((t : ℂ) + (m : ℂ) * ((π / 2 : ℂ) * I))‖
        ≤ |(w - ((t : ℂ) + (m : ℂ) * ((π / 2 : ℂ) * I))).re| +
          |(w - ((t : ℂ) + (m : ℂ) * ((π / 2 : ℂ) * I))).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < 2 := by rw [hre, him]; linarith [Real.pi_le_four]

/-! ### Schottky's theorem -/

theorem norm_log_le (w : ℂ) : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + π := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  linarith [abs_arg_le_pi w]

theorem norm_cosh_le (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.exp ‖w‖ := by
  have h := Complex.two_cosh w
  have h1 : ‖cexp w‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm w)
  have h2 : ‖cexp (-w)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((neg_re w ▸ le_abs.mpr (Or.inr le_rfl)).trans
      (Complex.abs_re_le_norm w))
  have : ‖(2 : ℂ) * Complex.cosh w‖ ≤ 2 * Real.exp ‖w‖ := by
    rw [h]; exact (norm_add_le _ _).trans (by linarith)
  rw [norm_mul, Complex.norm_two] at this
  linarith

/-- The bound in Schottky's theorem, in terms of a bound `κ` for `|log |g(0)||`. -/
noncomputable def schottkyS (κ : ℝ) : ℝ :=
  Real.exp (2 * π * Real.exp (2 * (Real.log (2 * √((κ + π) / (2 * π) + 1)) + π + 320)))

/-- **Schottky's theorem** (core form): if `g` is holomorphic on the unit disk and omits `0` and
`1`, and `|log |g(0)|| ≤ κ`, then `|g(z)| ≤ S(κ)` for `|z| ≤ 1/2`. With `F = (log g)/2πi` and
`H = log(√F − √(F − 1))`, `cosh² H = F` is never an integer, so `H` omits the grid
`{cosh² w ∈ ℤ}`; Bloch's theorem then bounds `H′`. -/
theorem schottky_core {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg0 : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) (hg1 : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 1) {κ : ℝ}
    (hκ : |Real.log ‖g 0‖| ≤ κ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖g z‖ ≤ schottkyS κ := by
  have hπ := Real.pi_pos
  have hB : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  obtain ⟨L, hLd, hLe, hL0⟩ := exists_log_ball hg hg0 hB
  set c : ℂ := 2 * π * I with hc
  have hc0 : c ≠ 0 := by simp [hc, Real.pi_ne_zero, I_ne_zero]
  set F : ℂ → ℂ := fun w => L w / c with hF
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hLd.div_const c
  have hLF : ∀ w, L w = c * F w := fun w => by simp only [hF]; field_simp
  have hFint : ∀ w ∈ ball (0 : ℂ) 1, ∀ n : ℤ, F w ≠ n := fun w hw n hn => by
    apply hg1 w hw
    rw [← hLe w hw, hLF, hn, hc, mul_comm, Complex.exp_int_mul_two_pi_mul_I]
  have hFne0 : ∀ w ∈ ball (0 : ℂ) 1, F w ≠ 0 := fun w hw => by
    simpa using hFint w hw 0
  have hFne1 : ∀ w ∈ ball (0 : ℂ) 1, F w - 1 ≠ 0 := fun w hw h => by
    exact hFint w hw 1 (by simpa [sub_eq_zero] using h)
  obtain ⟨A₁, hA₁d, hA₁e, -⟩ := exists_log_ball hFd hFne0 hB
  obtain ⟨A₂, hA₂d, hA₂e, -⟩ := exists_log_ball (hFd.sub_const 1) hFne1 hB
  set s₁ : ℂ → ℂ := fun w => cexp (A₁ w / 2) with hs₁
  set s₂ : ℂ → ℂ := fun w => cexp (A₂ w / 2) with hs₂
  have hsq : ∀ A : ℂ, cexp (A / 2) ^ 2 = cexp A := fun A => by
    rw [sq, ← Complex.exp_add, add_halves]
  have hs₁sq : ∀ w ∈ ball (0 : ℂ) 1, s₁ w ^ 2 = F w := fun w hw => by
    simp only [hs₁]; rw [hsq, hA₁e w hw]
  have hs₂sq : ∀ w ∈ ball (0 : ℂ) 1, s₂ w ^ 2 = F w - 1 := fun w hw => by
    simp only [hs₂]; rw [hsq, hA₂e w hw]
  set G : ℂ → ℂ := fun w => s₁ w - s₂ w with hG
  have hprod : ∀ w ∈ ball (0 : ℂ) 1, (s₁ w + s₂ w) * G w = 1 := fun w hw => by
    simp only [hG]
    have h1 := hs₁sq w hw
    have h2 := hs₂sq w hw
    linear_combination h1 - h2
  have hG0 : ∀ w ∈ ball (0 : ℂ) 1, G w ≠ 0 := fun w hw h => by
    have := hprod w hw; rw [h, mul_zero] at this; exact zero_ne_one this
  have hGd : DifferentiableOn ℂ G (ball 0 1) :=
    ((hA₁d.div_const 2).cexp).sub ((hA₂d.div_const 2).cexp)
  obtain ⟨H, hHd, hHe, hH0⟩ := exists_log_ball hGd hG0 hB
  have hcosh : ∀ w ∈ ball (0 : ℂ) 1, Complex.cosh (H w) ^ 2 = F w := fun w hw => by
    have hinv : (G w)⁻¹ = s₁ w + s₂ w := (eq_inv_of_mul_eq_one_left (hprod w hw)).symm
    have h2 : 2 * Complex.cosh (H w) = 2 * s₁ w := by
      rw [Complex.two_cosh, Complex.exp_neg, hHe w hw, hinv]
      simp only [hG]; ring
    have h3 : Complex.cosh (H w) = s₁ w := mul_left_cancel₀ two_ne_zero h2
    rw [h3, hs₁sq w hw]
  have hgrid : ∀ w ∈ ball (0 : ℂ) 1, ¬ CoshSqInt (H w) := fun w hw ⟨n, hn⟩ => by
    rw [hcosh w hw] at hn; exact hFint w hw n hn
  -- the derivative of `H` is bounded on `|y| ≤ 1/2`
  have hHder : ∀ y ∈ closedBall (0 : ℂ) (1 / 2), ‖deriv H y‖ ≤ 640 := fun y hy => by
    rw [mem_closedBall, dist_zero_right] at hy
    set r := 1 - ‖y‖ with hr
    have hr0 : 1 / 2 ≤ r := by linarith
    have hsub : ball y r ⊆ ball (0 : ℂ) 1 := fun x hx => by
      rw [mem_ball, dist_zero_right]; rw [mem_ball, dist_eq_norm] at hx
      have := norm_sub_norm_le x y
      linarith
    obtain ⟨w, hw⟩ := bloch (by linarith) (hHd.mono hsub)
    by_contra hcon; push Not at hcon
    obtain ⟨e, he, hwe⟩ := exists_coshSqInt_near w
    have hrad : 2 < r * ‖deriv H y‖ / 160 := by nlinarith
    have hemem : e ∈ ball w (r * ‖deriv H y‖ / 160) := by
      rw [mem_ball, dist_comm, dist_eq_norm]; linarith
    obtain ⟨x, hx, hxe⟩ := hw hemem
    exact hgrid x (hsub hx) (hxe ▸ he)
  have hHz : ‖H z - H 0‖ ≤ 320 := by
    have hcl : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    have := (convex_closedBall (0 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => hHd.differentiableAt (isOpen_ball.mem_nhds (hcl hx))) hHder
      (mem_closedBall_self (by norm_num)) (by rw [mem_closedBall, dist_zero_right]; exact hz)
    rw [sub_zero] at this
    linarith
  -- the value at `0`
  set Φ := (κ + π) / (2 * π) with hΦ
  have hF0 : ‖F 0‖ ≤ Φ := by
    have h1 : ‖L 0‖ ≤ κ + π := by rw [hL0]; linarith [norm_log_le (g 0)]
    rw [hF, norm_div, hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_two, Real.norm_of_nonneg hπ.le, div_le_div_iff_of_pos_right (by positivity)]
    exact h1
  have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans hF0
  set X := 2 * √(Φ + 1) with hX
  have hX1 : 1 ≤ X := by
    have : 1 ≤ √(Φ + 1) := Real.one_le_sqrt.mpr (by linarith)
    linarith
  have hsq_le : ∀ u : ℂ, ‖u‖ ^ 2 ≤ Φ + 1 → ‖u‖ ≤ √(Φ + 1) := fun u hu =>
    Real.le_sqrt_of_sq_le hu
  have hn1 : ‖s₁ 0‖ ≤ √(Φ + 1) := hsq_le _ (by rw [← norm_pow, hs₁sq 0 hB]; linarith)
  have hn2 : ‖s₂ 0‖ ≤ √(Φ + 1) := hsq_le _ (by
    rw [← norm_pow, hs₂sq 0 hB]; linarith [norm_sub_le (F 0) 1, norm_one (α := ℂ)])
  have hGup : ‖G 0‖ ≤ X := by
    simp only [hG, hX]; linarith [norm_sub_le (s₁ 0) (s₂ 0)]
  have hGlow : ‖G 0‖⁻¹ ≤ X := by
    rw [← norm_inv, (eq_inv_of_mul_eq_one_left (hprod 0 hB)).symm]
    simp only [hX]; linarith [norm_add_le (s₁ 0) (s₂ 0)]
  have hGpos : 0 < ‖G 0‖ := norm_pos_iff.mpr (hG0 0 hB)
  have hlogG : |Real.log ‖G 0‖| ≤ Real.log X := by
    rcases le_total 1 ‖G 0‖ with h | h
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      exact Real.log_le_log hGpos hGup
    · rw [abs_of_nonpos (Real.log_nonpos hGpos.le h), ← Real.log_inv]
      exact Real.log_le_log (by positivity) hGlow
  have hH0b : ‖H 0‖ ≤ Real.log X + π := by rw [hH0]; linarith [norm_log_le (G 0)]
  set K₁ := Real.log X + π + 320 with hK₁
  have hHzb : ‖H z‖ ≤ K₁ := by
    have := norm_sub_norm_le (H z) (H 0)
    linarith [norm_le_insert' (H z) (H 0)]
  have hzb : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; linarith
  have hFz : ‖F z‖ ≤ Real.exp (2 * K₁) := by
    rw [← hcosh z hzb, norm_pow]
    calc ‖Complex.cosh (H z)‖ ^ 2 ≤ Real.exp ‖H z‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_cosh_le _) 2
      _ = Real.exp (2 * ‖H z‖) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (2 * K₁) := Real.exp_le_exp.mpr (by linarith)
  rw [← hLe z hzb, Complex.norm_exp, schottkyS]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
  rw [hLF, norm_mul, hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_two, Real.norm_of_nonneg hπ.le]
  exact mul_le_mul_of_nonneg_left hFz (by positivity)

theorem schottkyS_pos (κ : ℝ) : 0 < schottkyS κ := Real.exp_pos _

/-- The bound in Schottky's theorem in terms of an upper bound `t` for `|g(0)|`. -/
noncomputable def schottkyBound (t : ℝ) : ℝ :=
  schottkyS (Real.log 2 + |Real.log t|) + 1 + schottkyS (Real.log 2)

theorem schottkyBound_pos (t : ℝ) : 0 < schottkyBound t := by
  have := schottkyS_pos (Real.log 2 + |Real.log t|)
  have := schottkyS_pos (Real.log 2)
  unfold schottkyBound; linarith

/-- **Schottky's theorem** on the unit disk: if `g` omits `0` and `1` and `|g(0)| ≤ t`, then
`|g(z)| ≤ B(t)` for `|z| ≤ 1/2`. (When `|g(0)| < 1/2`, apply the core to `1 − g`.) -/
theorem schottky_unit {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg0 : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) (hg1 : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 1) {t : ℝ}
    (ht : ‖g 0‖ ≤ t) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖g z‖ ≤ schottkyBound t := by
  have hB : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hS1 := schottkyS_pos (Real.log 2 + |Real.log t|)
  have hS2 := schottkyS_pos (Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg0n : 0 < ‖g 0‖ := norm_pos_iff.mpr (hg0 0 hB)
  rcases le_or_gt (1 / 2) ‖g 0‖ with h | h
  · have hκ : |Real.log ‖g 0‖| ≤ Real.log 2 + |Real.log t| := by
      rcases le_total 1 ‖g 0‖ with h1 | h1
      · rw [abs_of_nonneg (Real.log_nonneg h1)]
        have := Real.log_le_log hg0n ht
        linarith [le_abs_self (Real.log t)]
      · rw [abs_of_nonpos (Real.log_nonpos hg0n.le h1)]
        have : Real.log (1 / 2) ≤ Real.log ‖g 0‖ := Real.log_le_log (by norm_num) h
        rw [one_div, Real.log_inv] at this
        linarith [abs_nonneg (Real.log t)]
    have := schottky_core hg hg0 hg1 hκ hz
    unfold schottkyBound; linarith
  · have hg' : DifferentiableOn ℂ (fun w => 1 - g w) (ball 0 1) := hg.const_sub 1
    have h0' : ∀ w ∈ ball (0 : ℂ) 1, 1 - g w ≠ 0 := fun w hw h =>
      hg1 w hw (by linear_combination -h)
    have h1' : ∀ w ∈ ball (0 : ℂ) 1, 1 - g w ≠ 1 := fun w hw h =>
      hg0 w hw (by linear_combination -h)
    have hκ : |Real.log ‖1 - g 0‖| ≤ Real.log 2 := by
      have hlo : 1 / 2 < ‖1 - g 0‖ := by
        have := norm_sub_norm_le (1 : ℂ) (g 0); rw [norm_one] at this; linarith
      have hhi : ‖1 - g 0‖ < 2 := by
        have := norm_sub_le (1 : ℂ) (g 0); rw [norm_one] at this; linarith
      rw [abs_le]
      constructor
      · have : Real.log (1 / 2) ≤ Real.log ‖1 - g 0‖ := Real.log_le_log (by norm_num) hlo.le
        rw [one_div, Real.log_inv] at this; linarith
      · exact Real.log_le_log (by linarith) hhi.le
    have := schottky_core hg' h0' h1' hκ hz
    have h2 := norm_sub_le (1 : ℂ) (1 - g z)
    rw [sub_sub_cancel, norm_one] at h2
    unfold schottkyBound; linarith

/-- **Schottky's theorem** on a disk `D(c, R)`. -/
theorem schottky {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) (hg1 : ∀ z ∈ ball c R, g z ≠ 1) {t : ℝ} (ht : ‖g c‖ ≤ t)
    {z : ℂ} (hz : z ∈ closedBall c (R / 2)) : ‖g z‖ ≤ schottkyBound t := by
  set k : ℂ → ℂ := fun u => g (c + (R : ℂ) * u) with hk
  have hmap : ∀ u ∈ ball (0 : ℂ) 1, c + (R : ℂ) * u ∈ ball c R := fun u hu => by
    rw [mem_ball, dist_zero_right] at hu
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
    nlinarith
  have hkd : DifferentiableOn ℂ k (ball 0 1) := fun u hu =>
    ((hg.differentiableAt (isOpen_ball.mem_nhds (hmap u hu))).comp u
      (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => c + (R : ℂ) * u) u)).differentiableWithinAt
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have := schottky_unit hkd (fun u hu => hg0 _ (hmap u hu)) (fun u hu => hg1 _ (hmap u hu))
    (by simpa [hk] using ht) (z := (z - c) / R) (by
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_le_iff₀ hR]
      linarith)
  simpa [hk, mul_div_cancel₀ _ hRc] using this

end Azurite.DLMF
