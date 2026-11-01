/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4Coalescing
import Azurite.DLMF.Chapter2.Section4SaddleCoeff

/-!
# DLMF §2.4(v): existence of the cubic change of variable (Chester–Friedman–Ursell)

The local existence theorem behind 2.4.18, for one value of the parameter `α`:

* at the confluence (`p′(t̂) = p″(t̂) = 0 ≠ p‴(t̂)`, i.e. `p(t) = p(t̂) + (t − t̂)³P(t)` with
  `P(t̂) ≠ 0`), `w = (3P(t))^{1/3}(t − t̂)` is an analytic change of variable with
  `p = ⅓w³ + p(t̂)` (`a = b = 0`, `w₁ = w₂ = 0`): `exists_cfuTransform_confluence`;
* at a simple saddle point `t₀` (`p(t) = p(t₀) + (t − t₀)²P(t)`, `P(t₀) ≠ 0`) and for any
  prescribed `w₀ ≠ 0`, there is an analytic `W` near `t₀` with `W(t₀) = w₀`, `W′(t₀) ≠ 0` and
  `p = ⅓W³ − w₀²W + p(t₀) + ⅔w₀³`, a cubic with critical points `±w₀`
  (`exists_cfuTransform_saddle`): `W = Φ⁻¹ ∘ Ψ` with `Ψ(t) = (t − t₀)P(t)^{1/2}` and
  `Φ(w) = (w − w₀)((w + 2w₀)/3)^{1/2}`, since `Φ² = ⅓w³ − w₀²w + ⅔w₀³` and `Ψ² = p − p(t₀)`;
* two separated simple saddle points `t₁ ≠ t₂` with `p(t₁) ≠ p(t₂)`: one cubic
  `⅓w³ − ζw + A`, `ζ = w₁²`, `w₁³ = ¾(p(t₂) − p(t₁))`, `A = (p(t₁) + p(t₂))/2`, and analytic
  changes of variable near `t₁` and near `t₂` onto its critical points `w₁`, `−w₁`
  (`exists_cfuTransform_pair`).

The gluing of the two local transformations along the path and the analytic dependence on `α`
through the confluence (the uniformity of Chester, Friedman and Ursell (1957)) are not treated.
-/

open Set Filter Topology Complex

namespace Azurite.DLMF

/-! ### Helpers -/

theorem sqrtP_sq {φ₀ : ℝ} {P : ℂ → ℂ} {t : ℂ} (hP : P t ≠ 0) : sqrtP φ₀ P t ^ 2 = P t := by
  rw [sqrtP, ← Complex.exp_nat_mul, ← UnifSetup.exp_LogP hP]
  congr 1
  push_cast
  ring

theorem unif_two_sq (a : ℂ) (φ₀ : ℝ) {P : ℂ → ℂ} {t : ℂ} (hP : P t ≠ 0) :
    unif a φ₀ 2 P t ^ 2 = (t - a) ^ 2 * P t := by
  rw [unif_two_eq, mul_pow, sqrtP_sq hP]

theorem unif_three_cube (a : ℂ) (φ₀ : ℝ) {P : ℂ → ℂ} {t : ℂ} (hP : P t ≠ 0) :
    unif a φ₀ 3 P t ^ 3 = (t - a) ^ 3 * P t := by
  rw [unif, mul_pow, ← Complex.exp_nat_mul, ← UnifSetup.exp_LogP hP]
  congr 2
  push_cast
  ring

/-- An analytic function with nonzero derivative at `a` is one-to-one, with nonzero derivative,
on a ball around `a`. -/
theorem exists_ball_injOn_of_analyticAt {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hf' : deriv f a ≠ 0) :
    ∃ ε > 0, InjOn f (Metric.ball a ε) ∧
      ∀ t ∈ Metric.ball a ε, deriv f t ≠ 0 ∧ AnalyticAt ℂ f t := by
  have hsd := hf.hasStrictDerivAt
  have h1 := hsd.eventually_left_inverse hf'
  have h2 := hf.deriv.continuousAt.eventually_ne hf'
  have h3 := hf.eventually_analyticAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and (h2.and h3))
  refine ⟨ε, hε, fun s hs t ht hst => ?_, fun t ht => (hball (Metric.mem_ball.mp ht)).2⟩
  have hs' := (hball (Metric.mem_ball.mp hs)).1
  have ht' := (hball (Metric.mem_ball.mp ht)).1
  rw [← hs', ← ht', hst]

theorem UnifSetup.const_mul {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P) {k : ℝ}
    (hk : 0 < k) : UnifSetup a φ₀ μ ρ (fun t => (k : ℂ) * P t) where
  μ_pos := h.μ_pos
  ρ_pos := h.ρ_pos
  differentiableOn := h.differentiableOn.const_mul _
  P_a := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le]
    conv_lhs => rw [h.P_a]
    push_cast
    ring
  P_ne := mul_ne_zero (ofReal_ne_zero.mpr hk.ne') h.P_ne

/-! ### The confluence -/

/-- **Chester–Friedman–Ursell at the confluence**: if `p(t) = p(t̂) + (t − t̂)³P(t)` with `P`
analytic and `P(t̂) ≠ 0` (`p′(t̂) = p″(t̂) = 0 ≠ p‴(t̂)`), then `w = (3P(t))^{1/3}(t − t̂)` is a
change of variable 2.4.18 near `t̂` with `a = b = 0`, `c = p(t̂)`, `w(t̂) = 0`. -/
theorem exists_cfuTransform_confluence {p P : ℂ → ℂ} {t₀ : ℂ} {φ₀ ρ : ℝ}
    (h : UnifSetup t₀ φ₀ 3 ρ P) (hp : ∀ t ∈ Metric.ball t₀ ρ, p t = p t₀ + (t - t₀) ^ 3 * P t) :
    ∃ (U : Set ℂ) (w : ℂ → ℂ), t₀ ∈ U ∧ CFUTransform p U w 0 0 (p t₀) ∧ w t₀ = 0 := by
  have h3 := h.const_mul (k := 3) (by norm_num)
  set w := unif t₀ φ₀ 3 (fun t => ((3 : ℝ) : ℂ) * P t) with hw
  obtain ⟨ε, hε, hερ, hball⟩ := h3.exists_eps one_pos
  obtain ⟨ε', hε', hinj, hder⟩ :=
    exists_ball_injOn_of_analyticAt h3.analyticAt_unif_a h3.deriv_unif_a_ne
  refine ⟨Metric.ball t₀ (min ε ε'), w, Metric.mem_ball_self (lt_min hε hε'), ?_,
    UnifSetup.unif_a _ _ _ _⟩
  have hsub : Metric.ball t₀ (min ε ε') ⊆ Metric.ball t₀ ε :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsub' : Metric.ball t₀ (min ε ε') ⊆ Metric.ball t₀ ε' :=
    Metric.ball_subset_ball (min_le_right _ _)
  exact
    { U_open := Metric.isOpen_ball
      w_diff := fun t ht => (hder t (hsub' ht)).2.differentiableAt.differentiableWithinAt
      w_inj := hinj.mono hsub'
      deriv_ne := fun t ht => (hder t (hsub' ht)).1
      p_eq := fun t ht => by
        have hP : ((3 : ℝ) : ℂ) * P t ≠ 0 := (hball t (hsub ht)).2.2
        rw [hp t (Metric.ball_subset_ball hερ (hsub ht)), cfuCubic, hw,
          unif_three_cube (P := fun t => ((3 : ℝ) : ℂ) * P t) _ _ hP]
        push_cast
        ring }

/-! ### A simple saddle point -/

/-- **Chester–Friedman–Ursell at a simple saddle point**: if `p(t) = p(t₀) + (t − t₀)²P(t)` with
`P(t₀) ≠ 0`, then for every `w₀ ≠ 0` there is an analytic change of variable `W` near `t₀` with
`W(t₀) = w₀`, `W′ ≠ 0`, and `p = ⅓W³ − w₀²W + p(t₀) + ⅔w₀³` (the cubic with critical points
`±w₀` and critical value `p(t₀)` at `w₀`). -/
theorem exists_cfuTransform_saddle {p P : ℂ → ℂ} {t₀ : ℂ} {φ₀ ρ : ℝ} (h : UnifSetup t₀ φ₀ 2 ρ P)
    (hp : ∀ t ∈ Metric.ball t₀ ρ, p t = p t₀ + (t - t₀) ^ 2 * P t) {w₀ : ℂ} (hw₀ : w₀ ≠ 0) :
    ∃ (U : Set ℂ) (W : ℂ → ℂ), t₀ ∈ U ∧
      CFUTransform p U W 0 (-(w₀ ^ 2)) (p t₀ + 2 / 3 * w₀ ^ 3) ∧ W t₀ = w₀ := by
  set Q : ℂ → ℂ := fun w => (w + 2 * w₀) / 3 with hQ
  have hQw₀ : Q w₀ = w₀ := by
    simp only [hQ]
    ring
  have hΦ : UnifSetup w₀ (arg w₀) 2 1 Q :=
    { μ_pos := by norm_num
      ρ_pos := one_pos
      differentiableOn := by
        simp only [hQ]
        fun_prop
      P_a := by
        rw [hQw₀]
        exact (Complex.norm_mul_exp_arg_mul_I w₀).symm
      P_ne := by
        rw [hQw₀]
        exact hw₀ }
  set W : ℂ → ℂ := fun t => unifInv hΦ (unif t₀ φ₀ 2 P t) with hW
  have hΨ0 : unif t₀ φ₀ 2 P t₀ = 0 := UnifSetup.unif_a _ _ _ _
  have hΨan : AnalyticAt ℂ (unif t₀ φ₀ 2 P) t₀ := h.analyticAt_unif_a
  have hWt₀ : W t₀ = w₀ := by
    show unifInv hΦ (unif t₀ φ₀ 2 P t₀) = w₀
    rw [hΨ0, hΦ.unifInv_zero]
  have hinv : AnalyticAt ℂ (unifInv hΦ) (unif t₀ φ₀ 2 P t₀) := by
    rw [hΨ0]
    exact hΦ.analyticAt_unifInv
  have hWan : AnalyticAt ℂ W t₀ := hinv.comp hΨan
  have hWd : deriv W t₀ ≠ 0 := by
    have h1 : HasDerivAt W (deriv (unifInv hΦ) (unif t₀ φ₀ 2 P t₀) * deriv (unif t₀ φ₀ 2 P) t₀)
        t₀ :=
      hinv.differentiableAt.hasDerivAt.comp t₀ hΨan.differentiableAt.hasDerivAt
    rw [h1.deriv, hΨ0, hΦ.deriv_unifInv_zero]
    exact mul_ne_zero (inv_ne_zero (Complex.exp_ne_zero _)) h.deriv_unif_a_ne
  have hΨtend : Tendsto (unif t₀ φ₀ 2 P) (𝓝 t₀) (𝓝 0) := by
    rw [← hΨ0]
    exact hΨan.continuousAt
  have hev1 : ∀ᶠ t in 𝓝 t₀, unif w₀ (arg w₀) 2 Q (W t) = unif t₀ φ₀ 2 P t :=
    hΨtend.eventually hΦ.eventually_unif_unifInv
  have hWtend : Tendsto W (𝓝 t₀) (𝓝 w₀) := by
    rw [← hWt₀]
    exact hWan.continuousAt
  have hev2 : ∀ᶠ t in 𝓝 t₀, Q (W t) ≠ 0 := by
    have hQc : ContinuousAt Q w₀ := by
      simp only [hQ]
      fun_prop
    have hQ0 : Q w₀ ≠ 0 := by
      rw [hQw₀]
      exact hw₀
    exact hWtend.eventually (hQc.eventually_ne hQ0)
  obtain ⟨ε₁, hε₁, hερ, hball⟩ := h.exists_eps one_pos
  obtain ⟨ε₂, hε₂, hinj, hder⟩ := exists_ball_injOn_of_analyticAt hWan hWd
  obtain ⟨ε₃, hε₃, hev⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  have hε : 0 < min ε₁ (min ε₂ ε₃) := lt_min hε₁ (lt_min hε₂ hε₃)
  have hs1 : Metric.ball t₀ (min ε₁ (min ε₂ ε₃)) ⊆ Metric.ball t₀ ε₁ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hs2 : Metric.ball t₀ (min ε₁ (min ε₂ ε₃)) ⊆ Metric.ball t₀ ε₂ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : Metric.ball t₀ (min ε₁ (min ε₂ ε₃)) ⊆ Metric.ball t₀ ε₃ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨Metric.ball t₀ (min ε₁ (min ε₂ ε₃)), W, Metric.mem_ball_self hε, ?_, hWt₀⟩
  exact
    { U_open := Metric.isOpen_ball
      w_diff := fun t ht => (hder t (hs2 ht)).2.differentiableAt.differentiableWithinAt
      w_inj := hinj.mono hs2
      deriv_ne := fun t ht => (hder t (hs2 ht)).1
      p_eq := fun t ht => by
        obtain ⟨e1, e2⟩ := hev (Metric.mem_ball.mp (hs3 ht))
        have hP : P t ≠ 0 := (hball t (hs1 ht)).2.2
        have sq1 : (W t - w₀) ^ 2 * Q (W t) = (t - t₀) ^ 2 * P t := by
          rw [← unif_two_sq w₀ (arg w₀) e2, e1, unif_two_sq t₀ φ₀ hP]
        rw [hp t (Metric.ball_subset_ball hερ (hs1 ht)), cfuCubic]
        simp only [hQ] at sq1
        linear_combination -sq1 }

/-! ### Two separated saddle points -/

/-- **Chester–Friedman–Ursell for two separated simple saddle points** `t₁ ≠ t₂` with
`p(t₁) ≠ p(t₂)`: there is one cubic `⅓w³ − w₁²w + A`, `w₁³ = ¾(p(t₂) − p(t₁))`,
`A = (p(t₁) + p(t₂))/2`, whose critical points `w₁`, `−w₁` carry the critical values `p(t₁)`,
`p(t₂)`, and analytic changes of variable 2.4.18 near `t₁` and near `t₂` onto it. -/
theorem exists_cfuTransform_pair {p P₁ P₂ : ℂ → ℂ} {t₁ t₂ : ℂ} {φ₁ φ₂ ρ₁ ρ₂ : ℝ}
    (h₁ : UnifSetup t₁ φ₁ 2 ρ₁ P₁)
    (hp₁ : ∀ t ∈ Metric.ball t₁ ρ₁, p t = p t₁ + (t - t₁) ^ 2 * P₁ t)
    (h₂ : UnifSetup t₂ φ₂ 2 ρ₂ P₂)
    (hp₂ : ∀ t ∈ Metric.ball t₂ ρ₂, p t = p t₂ + (t - t₂) ^ 2 * P₂ t) (hne : p t₁ ≠ p t₂) :
    ∃ w₁ : ℂ, w₁ ≠ 0 ∧ w₁ ^ 3 = 3 / 4 * (p t₂ - p t₁) ∧
      ∃ (U₁ : Set ℂ) (W₁ : ℂ → ℂ) (U₂ : Set ℂ) (W₂ : ℂ → ℂ),
        t₁ ∈ U₁ ∧ CFUTransform p U₁ W₁ 0 (-(w₁ ^ 2)) ((p t₁ + p t₂) / 2) ∧ W₁ t₁ = w₁ ∧
        t₂ ∈ U₂ ∧ CFUTransform p U₂ W₂ 0 (-(w₁ ^ 2)) ((p t₁ + p t₂) / 2) ∧ W₂ t₂ = -w₁ := by
  set w₁ : ℂ := (3 / 4 * (p t₂ - p t₁)) ^ (((3 : ℕ) : ℂ)⁻¹) with hw₁def
  have hw₁ : w₁ ^ 3 = 3 / 4 * (p t₂ - p t₁) :=
    Complex.cpow_nat_inv_pow (3 / 4 * (p t₂ - p t₁)) (by norm_num : (3 : ℕ) ≠ 0)
  have hw₁0 : w₁ ≠ 0 := by
    intro h0
    rw [h0, zero_pow three_ne_zero] at hw₁
    exact hne (by linear_combination (4 / 3 : ℂ) * hw₁)
  obtain ⟨U₁, W₁, ht₁, hT₁, hW₁⟩ := exists_cfuTransform_saddle h₁ hp₁ hw₁0
  obtain ⟨U₂, W₂, ht₂, hT₂, hW₂⟩ := exists_cfuTransform_saddle h₂ hp₂ (neg_ne_zero.mpr hw₁0)
  have hA₁ : p t₁ + 2 / 3 * w₁ ^ 3 = (p t₁ + p t₂) / 2 := by linear_combination (2 / 3 : ℂ) * hw₁
  have hA₂ : p t₂ + 2 / 3 * (-w₁) ^ 3 = (p t₁ + p t₂) / 2 := by
    linear_combination (-2 / 3 : ℂ) * hw₁
  have hζ : -((-w₁) ^ 2) = -(w₁ ^ 2) := by ring
  rw [hA₁] at hT₁
  rw [hA₂, hζ] at hT₂
  exact ⟨w₁, hw₁0, hw₁, U₁, W₁, U₂, W₂, ht₁, hT₁, hW₁, ht₂, hT₂, hW₂⟩

end Azurite.DLMF
