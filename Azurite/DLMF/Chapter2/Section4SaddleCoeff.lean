/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4Saddle

/-!
# DLMF 2.4.16: the coefficient `b₂`

`b₂ = (2q″ − 2(p‴/p″)q′ + (5(p‴)²/(6(p″)²) − p⁗/(2p″)) q) / (2p″)^{3/2}` at the saddle point, with
the branch `(2p″)^{3/2} = (2|p″|)^{3/2} e^{3iω₀/2}`.

The coefficient is `b₂ = g₂/2` with `g₂ = G″(0)/2`, `G(w) = Q(t(w)) t′(w)` and `t = unifInv` the
inverse of `w = (t − a) E(t)`, `E = P^{1/2} = exp(½ LogP)`. We differentiate `t′(w) u′(t(w)) = 1`
twice to express `t′(0)`, `t″(0)`, `t‴(0)` through `u′(a) = E`, `u″(a) = 2E′`, `u‴(a) = 3E″`, and
`E′ = E P′/(2P)`, `E″ = (E′P′/P + E (P″P − P′²)/P²)/2`; the identity then follows from `E² = P`
(`laplaceCoeff_two`). For the saddle point, `p″ = 2P`, `p‴ = 6P′`, `p⁗ = 12P″`
(`dlmf_2_4_16_b2`).
-/

open Set Filter Topology Complex

namespace Azurite.DLMF

/-- `E(t) = P(t)^{1/2} = exp(½ LogP(t))`, so that `unif(t) = (t − a) E(t)` for `μ = 2`. -/
noncomputable def sqrtP (φ₀ : ℝ) (P : ℂ → ℂ) (t : ℂ) : ℂ :=
  cexp (((1 / (2 : ℝ) : ℝ) : ℂ) * LogP φ₀ P t)

theorem unif_two_eq (a : ℂ) (φ₀ : ℝ) (P : ℂ → ℂ) :
    unif a φ₀ 2 P = fun t => (t - a) * sqrtP φ₀ P t := rfl

namespace UnifSetup

variable {a : ℂ} {φ₀ ρ : ℝ} {P : ℂ → ℂ}

/-- The local facts near `a`. -/
theorem eventually_local (h : UnifSetup a φ₀ 2 ρ P) :
    ∀ᶠ t in 𝓝 a, P t ≠ 0 ∧ AnalyticAt ℂ P t ∧ AnalyticAt ℂ (LogP φ₀ P) t ∧
      HasDerivAt (LogP φ₀ P) (deriv P t / P t) t := by
  obtain ⟨ε, hε, hερ, hball⟩ := h.exists_eps one_pos
  filter_upwards [Metric.ball_mem_nhds a hε] with t ht
  exact ⟨(hball t ht).2.2, h.analyticAt_P (Metric.ball_subset_ball hερ ht),
    h.analyticAt_LogP hερ (fun s hs => (hball s hs).1) ht,
    h.hasDerivAt_LogP (Metric.ball_subset_ball hερ ht) (hball t ht).1⟩

theorem eventually_sqrtP (h : UnifSetup a φ₀ 2 ρ P) :
    ∀ᶠ t in 𝓝 a, AnalyticAt ℂ (sqrtP φ₀ P) t ∧ sqrtP φ₀ P t ^ 2 = P t ∧
      HasDerivAt (sqrtP φ₀ P) (sqrtP φ₀ P t * (deriv P t / P t) / 2) t := by
  filter_upwards [h.eventually_local] with t ht
  obtain ⟨hP0, -, hL, hLd⟩ := ht
  refine ⟨(analyticAt_const.mul hL).cexp', ?_, ?_⟩
  · rw [sqrtP, ← Complex.exp_nat_mul, ← exp_LogP hP0]
    congr 1
    push_cast
    ring
  · have := (hLd.const_mul (((1 / (2 : ℝ) : ℝ) : ℂ))).cexp
    refine this.congr_deriv ?_
    simp only [sqrtP]
    push_cast
    ring

theorem sqrtP_ne_zero (φ₀ : ℝ) (P : ℂ → ℂ) (t : ℂ) : sqrtP φ₀ P t ≠ 0 := Complex.exp_ne_zero _

theorem deriv_sqrtP (h : UnifSetup a φ₀ 2 ρ P) :
    ∀ᶠ t in 𝓝 a, deriv (sqrtP φ₀ P) t = sqrtP φ₀ P t * (deriv P t / P t) / 2 := by
  filter_upwards [h.eventually_sqrtP] with t ht
  exact ht.2.2.deriv

theorem deriv2_sqrtP_a (h : UnifSetup a φ₀ 2 ρ P) :
    deriv (deriv (sqrtP φ₀ P)) a = (deriv (sqrtP φ₀ P) a * (deriv P a / P a) +
      sqrtP φ₀ P a * ((deriv (deriv P) a * P a - deriv P a * deriv P a) / P a ^ 2)) / 2 := by
  rw [Filter.EventuallyEq.deriv_eq h.deriv_sqrtP]
  obtain ⟨hP0, hP, -, -⟩ := h.eventually_local.self_of_nhds
  have hE := h.eventually_sqrtP.self_of_nhds.1
  have h1 := hE.differentiableAt.hasDerivAt
  have hP1 := hP.differentiableAt.hasDerivAt
  have hP2 := hP.deriv.differentiableAt.hasDerivAt
  have this : HasDerivAt (fun x => sqrtP φ₀ P x * (deriv P x / P x) / 2)
      ((deriv (sqrtP φ₀ P) a * (deriv P a / P a) +
        sqrtP φ₀ P a * ((deriv (deriv P) a * P a - deriv P a * deriv P a) / P a ^ 2)) / 2) a :=
    (h1.mul (hP2.div hP1 hP0)).div_const 2
  rw [this.deriv]

/-! ### Derivatives of `u = unif` at `a` -/

theorem deriv_unif_two (h : UnifSetup a φ₀ 2 ρ P) :
    ∀ᶠ t in 𝓝 a, deriv (unif a φ₀ 2 P) t = sqrtP φ₀ P t + (t - a) * deriv (sqrtP φ₀ P) t := by
  filter_upwards [h.eventually_sqrtP] with t ht
  rw [unif_two_eq]
  have this : HasDerivAt (fun x => (x - a) * sqrtP φ₀ P x)
      (1 * sqrtP φ₀ P t + (t - a) * deriv (sqrtP φ₀ P) t) t :=
    ((hasDerivAt_id' t).sub_const a).mul ht.1.differentiableAt.hasDerivAt
  rw [this.deriv, one_mul]

theorem deriv2_unif_two (h : UnifSetup a φ₀ 2 ρ P) :
    ∀ᶠ t in 𝓝 a, deriv (deriv (unif a φ₀ 2 P)) t =
      2 * deriv (sqrtP φ₀ P) t + (t - a) * deriv (deriv (sqrtP φ₀ P)) t := by
  filter_upwards [h.eventually_sqrtP, eventually_eventually_nhds.mpr h.deriv_unif_two] with t
    ht hev
  rw [Filter.EventuallyEq.deriv_eq hev]
  have h1 := ht.1.differentiableAt.hasDerivAt
  have h2 := ht.1.deriv.differentiableAt.hasDerivAt
  have this : HasDerivAt (fun x => sqrtP φ₀ P x + (x - a) * deriv (sqrtP φ₀ P) x)
      (deriv (sqrtP φ₀ P) t + (1 * deriv (sqrtP φ₀ P) t + (t - a) * deriv (deriv (sqrtP φ₀ P)) t))
      t :=
    h1.add (((hasDerivAt_id' t).sub_const a).mul h2)
  rw [this.deriv, one_mul]
  ring

theorem deriv3_unif_two_a (h : UnifSetup a φ₀ 2 ρ P) :
    deriv (deriv (deriv (unif a φ₀ 2 P))) a = 3 * deriv (deriv (sqrtP φ₀ P)) a := by
  rw [Filter.EventuallyEq.deriv_eq h.deriv2_unif_two]
  have hE := h.eventually_sqrtP.self_of_nhds.1
  have h1 := hE.deriv.differentiableAt.hasDerivAt
  have h2 := hE.deriv.deriv.differentiableAt.hasDerivAt
  have this : HasDerivAt
      (fun x => 2 * deriv (sqrtP φ₀ P) x + (x - a) * deriv (deriv (sqrtP φ₀ P)) x)
      (2 * deriv (deriv (sqrtP φ₀ P)) a + (1 * deriv (deriv (sqrtP φ₀ P)) a +
        (a - a) * deriv (deriv (deriv (sqrtP φ₀ P))) a)) a :=
    (h1.const_mul (2 : ℂ)).add (((hasDerivAt_id' a).sub_const a).mul h2)
  rw [this.deriv, sub_self, zero_mul, add_zero, one_mul]
  ring

/-! ### Derivatives of the inverse `t = unifInv` at `0` -/

theorem eventually_deriv2_unifInv (h : UnifSetup a φ₀ 2 ρ P) :
    ∀ᶠ w in 𝓝 0, deriv (deriv (unifInv h)) w * deriv (unif a φ₀ 2 P) (unifInv h w) +
      deriv (unifInv h) w ^ 2 * deriv (deriv (unif a φ₀ 2 P)) (unifInv h w) = 0 := by
  have hτ := h.analyticAt_unifInv.eventually_analyticAt
  have hu := h.analyticAt_unif_a.eventually_analyticAt
  have hT1 := eventually_eventually_nhds.mpr h.eventually_deriv_unifInv
  filter_upwards [hτ, h.tendsto_unifInv.eventually hu, hT1] with w hw hu' hT
  have h1 : HasDerivAt (fun v => deriv (unifInv h) v * deriv (unif a φ₀ 2 P) (unifInv h v))
      (deriv (deriv (unifInv h)) w * deriv (unif a φ₀ 2 P) (unifInv h w) +
        deriv (unifInv h) w * (deriv (deriv (unif a φ₀ 2 P)) (unifInv h w) *
          deriv (unifInv h) w)) w :=
    hw.deriv.differentiableAt.hasDerivAt.mul
      (hu'.deriv.differentiableAt.hasDerivAt.comp w hw.differentiableAt.hasDerivAt)
  have h2 : HasDerivAt (fun v => deriv (unifInv h) v * deriv (unif a φ₀ 2 P) (unifInv h v)) 0 w :=
    (hasDerivAt_const w (1 : ℂ)).congr_of_eventuallyEq (hT.mono fun x hx => hx)
  have := h1.unique h2
  linear_combination this

theorem deriv3_unifInv_zero (h : UnifSetup a φ₀ 2 ρ P) :
    deriv (deriv (deriv (unifInv h))) 0 * deriv (unif a φ₀ 2 P) a +
      3 * deriv (unifInv h) 0 * deriv (deriv (unifInv h)) 0 * deriv (deriv (unif a φ₀ 2 P)) a +
      deriv (unifInv h) 0 ^ 3 * deriv (deriv (deriv (unif a φ₀ 2 P))) a = 0 := by
  have hτ := h.analyticAt_unifInv
  have hu := h.analyticAt_unif_a
  have hτ0 := h.unifInv_zero
  have hτ1 := hτ.differentiableAt.hasDerivAt
  have hτ2 := hτ.deriv.differentiableAt.hasDerivAt
  have hτ3 := hτ.deriv.deriv.differentiableAt.hasDerivAt
  have hu1 : HasDerivAt (deriv (unif a φ₀ 2 P)) (deriv (deriv (unif a φ₀ 2 P)) a)
      (unifInv h 0) := by
    rw [hτ0]
    exact hu.deriv.differentiableAt.hasDerivAt
  have hu2 : HasDerivAt (deriv (deriv (unif a φ₀ 2 P)))
      (deriv (deriv (deriv (unif a φ₀ 2 P))) a) (unifInv h 0) := by
    rw [hτ0]
    exact hu.deriv.deriv.differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun w => deriv (deriv (unifInv h)) w * deriv (unif a φ₀ 2 P) (unifInv h w)
      + deriv (unifInv h) w ^ 2 * deriv (deriv (unif a φ₀ 2 P)) (unifInv h w)) _ 0 :=
    (hτ3.mul (hu1.comp 0 hτ1)).add ((hτ2.pow 2).mul (hu2.comp 0 hτ1))
  have h2 : HasDerivAt (fun w => deriv (deriv (unifInv h)) w * deriv (unif a φ₀ 2 P) (unifInv h w)
      + deriv (unifInv h) w ^ 2 * deriv (deriv (unif a φ₀ 2 P)) (unifInv h w)) 0 0 :=
    (hasDerivAt_const 0 (0 : ℂ)).congr_of_eventuallyEq
      (h.eventually_deriv2_unifInv.mono fun x hx => hx)
  have := h1.unique h2
  simp only [Function.comp_apply, Pi.pow_apply, hτ0, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    at this
  linear_combination this

/-! ### `G″(0)` -/

theorem laplaceG_one (h : UnifSetup a φ₀ 2 ρ P) (Q : ℂ → ℂ) :
    laplaceG h 1 Q = fun w => Q (unifInv h w) * deriv (unifInv h) w := by
  funext w
  simp [laplaceG]

theorem iteratedDeriv_two_laplaceG (h : UnifSetup a φ₀ 2 ρ P) {Q : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q a) :
    iteratedDeriv 2 (laplaceG h 1 Q) 0 = deriv (deriv Q) a * deriv (unifInv h) 0 ^ 3 +
      3 * deriv Q a * deriv (unifInv h) 0 * deriv (deriv (unifInv h)) 0 +
      Q a * deriv (deriv (deriv (unifInv h))) 0 := by
  rw [h.laplaceG_one, iteratedDeriv_succ, iteratedDeriv_one]
  have hτ := h.analyticAt_unifInv
  have hev : deriv (fun w => Q (unifInv h w) * deriv (unifInv h) w) =ᶠ[𝓝 0]
      fun w => deriv Q (unifInv h w) * deriv (unifInv h) w ^ 2 +
        Q (unifInv h w) * deriv (deriv (unifInv h)) w := by
    have hQ' : ∀ᶠ w in 𝓝 0, AnalyticAt ℂ Q (unifInv h w) :=
      h.tendsto_unifInv.eventually hQ.eventually_analyticAt
    filter_upwards [hτ.eventually_analyticAt, hQ'] with w hw hQw
    have h1 : HasDerivAt (fun w => Q (unifInv h w) * deriv (unifInv h) w)
        (deriv Q (unifInv h w) * deriv (unifInv h) w * deriv (unifInv h) w +
          Q (unifInv h w) * deriv (deriv (unifInv h)) w) w :=
      (hQw.differentiableAt.hasDerivAt.comp w hw.differentiableAt.hasDerivAt).mul
        hw.deriv.differentiableAt.hasDerivAt
    rw [h1.deriv]
    ring
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hQa : HasDerivAt (deriv Q) (deriv (deriv Q) a) (unifInv h 0) := by
    rw [h.unifInv_zero]
    exact hQ.deriv.differentiableAt.hasDerivAt
  have hQa' : HasDerivAt Q (deriv Q a) (unifInv h 0) := by
    rw [h.unifInv_zero]
    exact hQ.differentiableAt.hasDerivAt
  have hτ1 := hτ.differentiableAt.hasDerivAt
  have hτ2 := hτ.deriv.differentiableAt.hasDerivAt
  have hτ3 := hτ.deriv.deriv.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun w => deriv Q (unifInv h w) * deriv (unifInv h) w ^ 2 +
      Q (unifInv h w) * deriv (deriv (unifInv h)) w) _ 0 :=
    ((hQa.comp 0 hτ1).mul (hτ2.pow 2)).add ((hQa'.comp 0 hτ1).mul hτ3)
  rw [h2.deriv]
  simp only [Function.comp_apply, Pi.pow_apply, h.unifInv_zero, Nat.reduceSub, pow_one,
    Nat.cast_ofNat]
  ring

/-- `b₂` in terms of `P`, `Q` and `E = P^{1/2}` at `a` (`μ = 2`, `λ = 1`). -/
theorem laplaceCoeff_two (h : UnifSetup a φ₀ 2 ρ P) {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q a) :
    laplaceCoeff h 1 Q 2 = (deriv (deriv Q) a - 3 * deriv Q a * deriv P a / P a +
      Q a * (15 * deriv P a ^ 2 / (4 * P a ^ 2) - 3 * deriv (deriv P) a / (2 * P a))) /
        (4 * sqrtP φ₀ P a ^ 3) := by
  have hE0 : sqrtP φ₀ P a ≠ 0 := sqrtP_ne_zero φ₀ P a
  have hE2 : sqrtP φ₀ P a ^ 2 = P a := h.eventually_sqrtP.self_of_nhds.2.1
  have hτ1 : deriv (unifInv h) 0 = (sqrtP φ₀ P a)⁻¹ := by
    rw [h.deriv_unifInv_zero]
    rfl
  have hu1 : deriv (unif a φ₀ 2 P) a = sqrtP φ₀ P a := by
    rw [h.deriv_unif_two.self_of_nhds, sub_self, zero_mul, add_zero]
  have hu2 : deriv (deriv (unif a φ₀ 2 P)) a = 2 * deriv (sqrtP φ₀ P) a := by
    rw [h.deriv2_unif_two.self_of_nhds, sub_self, zero_mul, add_zero]
  have hu3 := h.deriv3_unif_two_a
  have hE1 : deriv (sqrtP φ₀ P) a = sqrtP φ₀ P a * (deriv P a / P a) / 2 :=
    h.deriv_sqrtP.self_of_nhds
  have hE2' := h.deriv2_sqrtP_a
  have hT2 := h.eventually_deriv2_unifInv.self_of_nhds
  rw [h.unifInv_zero] at hT2
  have hT3 := h.deriv3_unifInv_zero
  have hu1' : deriv (unif a φ₀ 2 P) a ≠ 0 := by
    rw [hu1]
    exact hE0
  have hτ2 : deriv (deriv (unifInv h)) 0 =
      -(deriv (unifInv h) 0 ^ 2 * deriv (deriv (unif a φ₀ 2 P)) a) / deriv (unif a φ₀ 2 P) a := by
    rw [eq_div_iff hu1']
    linear_combination hT2
  have hτ3 : deriv (deriv (deriv (unifInv h))) 0 =
      -(3 * deriv (unifInv h) 0 * deriv (deriv (unifInv h)) 0 * deriv (deriv (unif a φ₀ 2 P)) a +
        deriv (unifInv h) 0 ^ 3 * deriv (deriv (deriv (unif a φ₀ 2 P))) a) /
          deriv (unif a φ₀ 2 P) a := by
    rw [eq_div_iff hu1']
    linear_combination hT3
  rw [laplaceCoeff, h.iteratedDeriv_two_laplaceG hQ, hτ3, hτ2, hτ1, hu1, hu2, hu3, hE2', hE1,
    ← hE2, Nat.factorial_two]
  push_cast
  field_simp
  ring

end UnifSetup

/-! ### The saddle point: `p‴ = 6P′`, `p⁗ = 12P″` and `b₂` -/

namespace SaddlePoint

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {A B : ℝ} {t₀ : ℂ} {ω : ℝ} {T : Set ℂ} {P : ℂ → ℂ}
  {ω₀ ρ : ℝ} {θ₁ θ₂ Z : ℝ}

theorem eventually_analyticAt_P (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ P t := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self h.uset.ρ_pos)] with t ht
  exact h.uset.analyticAt_P ht

theorem deriv_p (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    ∀ᶠ t in 𝓝 t₀, deriv p t = 2 * (t - t₀) * P t + (t - t₀) ^ 2 * deriv P t := by
  filter_upwards [h.eventually_analyticAt_P, eventually_eventually_nhds.mpr
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self h.uset.ρ_pos))] with t hP hball
  have hpe : p =ᶠ[𝓝 t] fun s => p t₀ + (s - t₀) ^ 2 * P s := hball.mono fun s hs => h.p_eq s hs
  rw [Filter.EventuallyEq.deriv_eq hpe]
  have this : HasDerivAt (fun s => p t₀ + (s - t₀) ^ 2 * P s)
      (0 + (((2 : ℕ) : ℂ) * (t - t₀) ^ (2 - 1) * 1 * P t + (t - t₀) ^ 2 * deriv P t)) t :=
    (hasDerivAt_const t (p t₀)).add
      ((((hasDerivAt_id' t).sub_const t₀).pow 2).mul hP.differentiableAt.hasDerivAt)
  rw [this.deriv]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one, zero_add]

theorem deriv2_p (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    ∀ᶠ t in 𝓝 t₀, deriv (deriv p) t =
      2 * P t + 4 * (t - t₀) * deriv P t + (t - t₀) ^ 2 * deriv (deriv P) t := by
  filter_upwards [h.eventually_analyticAt_P, eventually_eventually_nhds.mpr h.deriv_p] with t hP
    hev
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hP1 := hP.differentiableAt.hasDerivAt
  have hP2 := hP.deriv.differentiableAt.hasDerivAt
  have this : HasDerivAt (fun s => 2 * (s - t₀) * P s + (s - t₀) ^ 2 * deriv P s)
      ((2 * 1 * P t + 2 * (t - t₀) * deriv P t) +
        (((2 : ℕ) : ℂ) * (t - t₀) ^ (2 - 1) * 1 * deriv P t + (t - t₀) ^ 2 * deriv (deriv P) t))
      t :=
    ((((hasDerivAt_id' t).sub_const t₀).const_mul 2).mul hP1).add
      ((((hasDerivAt_id' t).sub_const t₀).pow 2).mul hP2)
  rw [this.deriv]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]
  ring

theorem deriv3_p (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    ∀ᶠ t in 𝓝 t₀, deriv (deriv (deriv p)) t =
      6 * deriv P t + 6 * (t - t₀) * deriv (deriv P) t +
        (t - t₀) ^ 2 * deriv (deriv (deriv P)) t := by
  filter_upwards [h.eventually_analyticAt_P, eventually_eventually_nhds.mpr h.deriv2_p] with t hP
    hev
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hP1 := hP.differentiableAt.hasDerivAt
  have hP2 := hP.deriv.differentiableAt.hasDerivAt
  have hP3 := hP.deriv.deriv.differentiableAt.hasDerivAt
  have this : HasDerivAt
      (fun s => 2 * P s + 4 * (s - t₀) * deriv P s + (s - t₀) ^ 2 * deriv (deriv P) s)
      (2 * deriv P t + (4 * 1 * deriv P t + 4 * (t - t₀) * deriv (deriv P) t) +
        (((2 : ℕ) : ℂ) * (t - t₀) ^ (2 - 1) * 1 * deriv (deriv P) t +
          (t - t₀) ^ 2 * deriv (deriv (deriv P)) t)) t :=
    ((hP1.const_mul 2).add ((((hasDerivAt_id' t).sub_const t₀).const_mul 4).mul hP2)).add
      ((((hasDerivAt_id' t).sub_const t₀).pow 2).mul hP3)
  rw [this.deriv]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]
  ring

theorem iteratedDeriv_three (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    iteratedDeriv 3 p t₀ = 6 * deriv P t₀ := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h.deriv3_p.self_of_nhds,
    sub_self]
  ring

theorem iteratedDeriv_four (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    iteratedDeriv 4 p t₀ = 12 * deriv (deriv P) t₀ := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    Filter.EventuallyEq.deriv_eq h.deriv3_p]
  have hP := h.uset.analyticAt_P (Metric.mem_ball_self h.uset.ρ_pos)
  have hP2 := hP.deriv.differentiableAt.hasDerivAt
  have hP3 := hP.deriv.deriv.differentiableAt.hasDerivAt
  have hP4 := hP.deriv.deriv.deriv.differentiableAt.hasDerivAt
  have this : HasDerivAt (fun s => 6 * deriv P s + 6 * (s - t₀) * deriv (deriv P) s +
      (s - t₀) ^ 2 * deriv (deriv (deriv P)) s)
      (6 * deriv (deriv P) t₀ + (6 * 1 * deriv (deriv P) t₀ +
        6 * (t₀ - t₀) * deriv (deriv (deriv P)) t₀) +
        (((2 : ℕ) : ℂ) * (t₀ - t₀) ^ (2 - 1) * 1 * deriv (deriv (deriv P)) t₀ +
          (t₀ - t₀) ^ 2 * deriv (deriv (deriv (deriv P))) t₀)) t₀ :=
    ((hP2.const_mul 6).add ((((hasDerivAt_id' t₀).sub_const t₀).const_mul 6).mul hP3)).add
      ((((hasDerivAt_id' t₀).sub_const t₀).pow 2).mul hP4)
  rw [this.deriv, sub_self]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one, mul_zero, zero_mul, add_zero,
    zero_pow two_ne_zero]
  ring

/-- `E(t₀) = |P(t₀)|^{1/2} e^{iω₀/2}`. -/
theorem sqrtP_eq (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    sqrtP ω₀ P t₀ = ((‖P t₀‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * cexp ((ω₀ / 2 : ℝ) * I) := by
  have hr := norm_pos_iff.mpr h.uset.P_ne
  have hL : LogP ω₀ P t₀ = Real.log ‖P t₀‖ + ω₀ * I := by
    rw [LogP]
    conv_lhs => rw [h.uset.P_a]
    exact logBr_polar hr (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [sqrtP, hL, mul_add, Complex.exp_add]
  congr 1
  · rw [Real.rpow_def_of_pos hr, ofReal_exp]
    push_cast
    ring_nf
  · push_cast
    ring_nf

theorem denom_eq (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    (((2 * ‖iteratedDeriv 2 p t₀‖) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * cexp ((3 * ω₀ / 2 : ℝ) * I) =
      8 * sqrtP ω₀ P t₀ ^ 3 := by
  rw [h.sqrtP_eq, h.norm_iteratedDeriv_two, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _),
    show (4 : ℝ) ^ (3 / 2 : ℝ) = 8 by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num,
    mul_pow, ← ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- **DLMF 2.4.16**: `b₂ = (2q″ − 2(p‴/p″)q′ + (5(p‴)²/(6(p″)²) − p⁗/(2p″)) q) / (2p″)^{3/2}` at the
saddle point, with `(2p″)^{3/2} = (2|p″|)^{3/2} e^{3iω₀/2}`. -/
theorem dlmf_2_4_16_b2 (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    saddleCoeff h 2 = (2 * iteratedDeriv 2 q t₀ -
      2 * (iteratedDeriv 3 p t₀ / iteratedDeriv 2 p t₀) * deriv q t₀ +
      (5 * iteratedDeriv 3 p t₀ ^ 2 / (6 * iteratedDeriv 2 p t₀ ^ 2) -
        iteratedDeriv 4 p t₀ / (2 * iteratedDeriv 2 p t₀)) * q t₀) /
      ((((2 * ‖iteratedDeriv 2 p t₀‖) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * cexp ((3 * ω₀ / 2 : ℝ) * I)) := by
  have hP0 := h.uset.P_ne
  have hE0 := UnifSetup.sqrtP_ne_zero ω₀ P t₀
  rw [h.denom_eq, saddleCoeff, h.uset.laplaceCoeff_two h.forward.analyticAt_Q, h.iteratedDeriv_two,
    h.iteratedDeriv_three, h.iteratedDeriv_four, iteratedDeriv_succ, iteratedDeriv_one]
  field_simp
  ring

end SaddlePoint

end Azurite.DLMF
