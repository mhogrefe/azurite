/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4LaplaceBranch
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# DLMF §2.4(iii): the uniformizing variable `w = (t − a) P(t)^{1/μ}`

DLMF 2.4.11 writes `p(t) − p(a) = (t − a)^μ P(t)` with `P(t) = ∑ pₛ (t − a)^s`, `p₀ = P(a) ≠ 0`,
and `q(t) = (t − a)^{λ−1} Q(t)`, the powers having `ph(t − a) → ω`. With `ph p₀ = φ₀` (2.4.13
fixes which branch) put

* `LogP t = logBr φ₀ (P t)`, the branch of `log P` with `Im LogP(a) = φ₀`;
* `unif t = (t − a) exp(LogP(t)/μ)`, so that `unif(t)^μ = p(t) − p(a)` with the branch
  `ph w → ω' = ω + φ₀/μ` (`brPow_unif`);
* `unifInv`, the analytic local inverse `t = t(w)` (Mathlib's `localInverse`);
* `laplaceG w = exp(−((λ−1)/μ) LogP(t(w))) Q(t(w)) t′(w)`, analytic at `0`, so that
  `q(t) dt = w^{λ−1} laplaceG(w) dw` (`brPow_unif_lam`).

`UnifSetup` collects the hypotheses, and `UnifSetup.exists_local` produces a radius `ε` on which
all branch identities hold for `t − a` in the sector `|ph(t − a) − ω| < α`.
-/

open Set Filter Topology Complex

namespace Azurite.DLMF

/-- The data of 2.4.11 near `a`: `P` analytic on `B(a, ρ)` with `P(a) = |p₀| e^{iφ₀} ≠ 0`. -/
structure UnifSetup (a : ℂ) (φ₀ μ ρ : ℝ) (P : ℂ → ℂ) : Prop where
  μ_pos : 0 < μ
  ρ_pos : 0 < ρ
  differentiableOn : DifferentiableOn ℂ P (Metric.ball a ρ)
  P_a : P a = (‖P a‖ : ℂ) * cexp (φ₀ * I)
  P_ne : P a ≠ 0

/-- The branch of `log P(t)` with `Im = φ₀` at `t = a`. -/
noncomputable def LogP (φ₀ : ℝ) (P : ℂ → ℂ) (t : ℂ) : ℂ := logBr φ₀ (P t)

/-- `w(t) = (t − a) P(t)^{1/μ}`. -/
noncomputable def unif (a : ℂ) (φ₀ μ : ℝ) (P : ℂ → ℂ) (t : ℂ) : ℂ :=
  (t - a) * cexp (((1 / μ : ℝ) : ℂ) * LogP φ₀ P t)

namespace UnifSetup

variable {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ}

theorem analyticAt_P (h : UnifSetup a φ₀ μ ρ P) {t : ℂ} (ht : t ∈ Metric.ball a ρ) :
    AnalyticAt ℂ P t :=
  h.differentiableOn.analyticAt (Metric.isOpen_ball.mem_nhds ht)

theorem slit_a (h : UnifSetup a φ₀ μ ρ P) : P a * cexp (-(φ₀ * I)) ∈ slitPlane := by
  rw [h.P_a, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  exact Or.inl (by simpa using norm_pos_iff.mpr h.P_ne)

/-- Near `a`, `P(t) e^{−iφ₀}` stays in the slit plane and `|arg| < β`. -/
theorem eventually_slit (h : UnifSetup a φ₀ μ ρ P) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ t in 𝓝 a, P t * cexp (-(φ₀ * I)) ∈ slitPlane ∧ |arg (P t * cexp (-(φ₀ * I)))| < β := by
  have hc : ContinuousAt (fun t => P t * cexp (-(φ₀ * I))) a :=
    ((h.analyticAt_P (Metric.mem_ball_self h.ρ_pos)).continuousAt).mul continuousAt_const
  have h1 : ∀ᶠ t in 𝓝 a, P t * cexp (-(φ₀ * I)) ∈ slitPlane :=
    hc.eventually (isOpen_slitPlane.mem_nhds h.slit_a)
  have harg : ContinuousAt (fun t => arg (P t * cexp (-(φ₀ * I)))) a :=
    ContinuousAt.comp (g := arg) (f := fun t => P t * cexp (-(φ₀ * I)))
      (continuousAt_arg h.slit_a) hc
  have h0 : arg (P a * cexp (-(φ₀ * I))) = 0 := by
    rw [h.P_a, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    exact arg_ofReal_of_nonneg (norm_nonneg _)
  have h2 : ∀ᶠ t in 𝓝 a, |arg (P t * cexp (-(φ₀ * I)))| < β := by
    have := harg.eventually (Metric.ball_mem_nhds _ hβ)
    simp only [h0] at this ⊢
    filter_upwards [this] with t ht
    simpa [Real.dist_eq] using ht
  exact h1.and h2

theorem exp_LogP {t : ℂ} (ht : P t ≠ 0) :
    cexp (LogP φ₀ P t) = P t := exp_logBr ht

theorem hasDerivAt_LogP (h : UnifSetup a φ₀ μ ρ P) {t : ℂ} (ht : t ∈ Metric.ball a ρ)
    (hs : P t * cexp (-(φ₀ * I)) ∈ slitPlane) :
    HasDerivAt (LogP φ₀ P) (deriv P t / P t) t := by
  have hP := (h.analyticAt_P ht).differentiableAt.hasDerivAt
  have := (hasDerivAt_logBr hs).comp t hP
  rw [div_eq_mul_inv, mul_comm]
  exact this

theorem LogP_im (t : ℂ) :
    (LogP φ₀ P t).im = arg (P t * cexp (-(φ₀ * I))) + φ₀ := by
  simp [LogP, logBr, log_im]

/-- The radius `ε` of the local analysis: on `B(a, ε)`, `LogP` is analytic, `|Im LogP − φ₀| < β`,
and `P ≠ 0`. -/
theorem exists_eps (h : UnifSetup a φ₀ μ ρ P) {β : ℝ} (hβ : 0 < β) :
    ∃ ε, 0 < ε ∧ ε ≤ ρ ∧ ∀ t ∈ Metric.ball a ε,
      P t * cexp (-(φ₀ * I)) ∈ slitPlane ∧ |(LogP φ₀ P t).im - φ₀| < β ∧ P t ≠ 0 := by
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp (h.eventually_slit hβ)
  refine ⟨min ε₁ ρ, lt_min hε₁ h.ρ_pos, min_le_right _ _, fun t ht => ?_⟩
  have ht₁ : t ∈ Metric.ball a ε₁ := Metric.ball_subset_ball (min_le_left _ _) ht
  obtain ⟨hs, harg⟩ := hball (Metric.mem_ball.mp ht₁)
  refine ⟨hs, ?_, ?_⟩
  · rw [LogP_im, add_sub_cancel_right]
    exact harg
  · intro h0
    rw [h0, zero_mul] at hs
    exact (mem_slitPlane_iff.mp hs).elim (lt_irrefl _) (fun h => h rfl)

theorem analyticAt_LogP (h : UnifSetup a φ₀ μ ρ P) {ε : ℝ} (hερ : ε ≤ ρ)
    (hball : ∀ t ∈ Metric.ball a ε, P t * cexp (-(φ₀ * I)) ∈ slitPlane) {t : ℂ}
    (ht : t ∈ Metric.ball a ε) : AnalyticAt ℂ (LogP φ₀ P) t := by
  refine DifferentiableOn.analyticAt (s := Metric.ball a ε) (fun s hs => ?_)
    (Metric.isOpen_ball.mem_nhds ht)
  exact (h.hasDerivAt_LogP (Metric.ball_subset_ball hερ hs) (hball s hs)).differentiableAt
    |>.differentiableWithinAt

theorem analyticAt_unif (h : UnifSetup a φ₀ μ ρ P) {ε : ℝ} (hερ : ε ≤ ρ)
    (hball : ∀ t ∈ Metric.ball a ε, P t * cexp (-(φ₀ * I)) ∈ slitPlane) {t : ℂ}
    (ht : t ∈ Metric.ball a ε) : AnalyticAt ℂ (unif a φ₀ μ P) t := by
  have h1 : AnalyticAt ℂ (fun t => (t - a)) t := analyticAt_id.sub analyticAt_const
  have h2 : AnalyticAt ℂ (fun t => cexp (((1 / μ : ℝ) : ℂ) * LogP φ₀ P t)) t :=
    (analyticAt_const.mul (h.analyticAt_LogP hερ hball ht)).cexp'
  exact h1.mul h2

theorem hasDerivAt_unif_a (h : UnifSetup a φ₀ μ ρ P) :
    HasDerivAt (unif a φ₀ μ P) (cexp (((1 / μ : ℝ) : ℂ) * LogP φ₀ P a)) a := by
  have hP := (h.hasDerivAt_LogP (Metric.mem_ball_self h.ρ_pos) h.slit_a).const_mul
    ((1 / μ : ℝ) : ℂ)
  have hE := hP.cexp
  have := ((hasDerivAt_id a).sub_const a).mul hE
  refine HasDerivAt.congr_deriv (this : HasDerivAt (unif a φ₀ μ P) _ a) ?_
  simp

theorem deriv_unif_a (h : UnifSetup a φ₀ μ ρ P) :
    deriv (unif a φ₀ μ P) a = cexp (((1 / μ : ℝ) : ℂ) * LogP φ₀ P a) :=
  h.hasDerivAt_unif_a.deriv

theorem deriv_unif_a_ne (h : UnifSetup a φ₀ μ ρ P) : deriv (unif a φ₀ μ P) a ≠ 0 := by
  rw [h.deriv_unif_a]
  exact Complex.exp_ne_zero _

theorem unif_a (a : ℂ) (φ₀ μ : ℝ) (P : ℂ → ℂ) : unif a φ₀ μ P a = 0 := by simp [unif]

theorem analyticAt_unif_a (h : UnifSetup a φ₀ μ ρ P) : AnalyticAt ℂ (unif a φ₀ μ P) a := by
  obtain ⟨ε, hε, hερ, hball⟩ := h.exists_eps one_pos
  exact h.analyticAt_unif hερ (fun t ht => (hball t ht).1) (Metric.mem_ball_self hε)

end UnifSetup

/-- The analytic local inverse `t = t(w)` of `w = unif(t)`. -/
noncomputable def unifInv {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P) : ℂ → ℂ :=
  h.analyticAt_unif_a.hasStrictDerivAt.localInverse _ _ _ h.deriv_unif_a_ne

/-- `laplaceG(w) = exp(−((λ−1)/μ) LogP(t(w))) Q(t(w)) t′(w)`: the analytic factor of
`q(t) dt/dw = w^{λ−1} laplaceG(w)`. -/
noncomputable def laplaceG {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P)
    (lam : ℂ) (Q : ℂ → ℂ) (w : ℂ) : ℂ :=
  cexp (-((lam - 1) / μ) * LogP φ₀ P (unifInv h w)) * Q (unifInv h w) * deriv (unifInv h) w

namespace UnifSetup

variable {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ}

theorem analyticAt_unifInv (h : UnifSetup a φ₀ μ ρ P) : AnalyticAt ℂ (unifInv h) 0 := by
  have := h.analyticAt_unif_a.analyticAt_localInverse h.deriv_unif_a_ne
  rwa [unif_a] at this

theorem eventually_unif_unifInv (h : UnifSetup a φ₀ μ ρ P) :
    ∀ᶠ w in 𝓝 0, unif a φ₀ μ P (unifInv h w) = w := by
  have := h.analyticAt_unif_a.hasStrictDerivAt.eventually_right_inverse h.deriv_unif_a_ne
  rwa [unif_a] at this

theorem eventually_unifInv_unif (h : UnifSetup a φ₀ μ ρ P) :
    ∀ᶠ t in 𝓝 a, unifInv h (unif a φ₀ μ P t) = t :=
  h.analyticAt_unif_a.hasStrictDerivAt.eventually_left_inverse h.deriv_unif_a_ne

theorem unifInv_zero (h : UnifSetup a φ₀ μ ρ P) : unifInv h 0 = a := by
  have := h.eventually_unifInv_unif.self_of_nhds
  rwa [unif_a] at this

theorem tendsto_unifInv (h : UnifSetup a φ₀ μ ρ P) : Tendsto (unifInv h) (𝓝 0) (𝓝 a) := by
  have := h.analyticAt_unifInv.continuousAt.tendsto
  rwa [h.unifInv_zero] at this

/-- The derivative of the inverse: `t′(w) · w′(t(w)) = 1` near `0`. -/
theorem eventually_deriv_unifInv (h : UnifSetup a φ₀ μ ρ P) :
    ∀ᶠ w in 𝓝 0, deriv (unifInv h) w * deriv (unif a φ₀ μ P) (unifInv h w) = 1 := by
  have hψ := h.analyticAt_unifInv.eventually_analyticAt
  have hu := h.analyticAt_unif_a.eventually_analyticAt
  have hr := h.eventually_unif_unifInv
  have hr' := eventually_eventually_nhds.mpr hr
  filter_upwards [hψ, h.tendsto_unifInv.eventually hu, hr'] with w hw hu' hr''
  have h1 : HasDerivAt (fun w => unif a φ₀ μ P (unifInv h w))
      (deriv (unif a φ₀ μ P) (unifInv h w) * deriv (unifInv h) w) w :=
    hu'.differentiableAt.hasDerivAt.comp w hw.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun w => unif a φ₀ μ P (unifInv h w)) 1 w :=
    (hasDerivAt_id w).congr_of_eventuallyEq (hr''.mono fun x hx => hx)
  rw [mul_comm]
  exact h1.unique h2

theorem analyticAt_laplaceG (h : UnifSetup a φ₀ μ ρ P) (lam : ℂ) {Q : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q a) : AnalyticAt ℂ (laplaceG h lam Q) 0 := by
  obtain ⟨ε, hε, hερ, hball⟩ := h.exists_eps one_pos
  have hψ := h.analyticAt_unifInv
  have hL : AnalyticAt ℂ (LogP φ₀ P) a :=
    h.analyticAt_LogP hερ (fun t ht => (hball t ht).1) (Metric.mem_ball_self hε)
  have hL' : AnalyticAt ℂ (LogP φ₀ P) (unifInv h 0) := by rwa [h.unifInv_zero]
  have hQ' : AnalyticAt ℂ Q (unifInv h 0) := by rwa [h.unifInv_zero]
  have h1 : AnalyticAt ℂ (fun w => LogP φ₀ P (unifInv h w)) 0 := hL'.comp hψ
  have h2 : AnalyticAt ℂ (fun w => Q (unifInv h w)) 0 := hQ'.comp hψ
  have h3 : AnalyticAt ℂ (deriv (unifInv h)) 0 := hψ.deriv
  exact ((analyticAt_const.mul h1).cexp'.mul h2).mul h3


/-! ### Branch identities on the sector `|ph(t − a) − ω| < α` -/

theorem unif_ne_zero {t : ℂ} (ht : t ≠ a) : unif a φ₀ μ P t ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr ht) (Complex.exp_ne_zero _)

/-- `logBr ω' (unif t) = logBr ω (t − a) + LogP(t)/μ`, `ω' = ω + φ₀/μ`, when `|ph(t − a) − ω| < α`,
`|Im LogP(t) − φ₀| < β` and `α + β/μ ≤ π`. -/
theorem logBr_unif (h : UnifSetup a φ₀ μ ρ P) {ω α β : ℝ} (hαβ : α + β / μ ≤ Real.pi) {t : ℂ}
    (hsec : t - a ∈ sectorBr ω α) (hβ : |(LogP φ₀ P t).im - φ₀| < β) :
    logBr (ω + φ₀ / μ) (unif a φ₀ μ P t) =
      logBr ω (t - a) + ((1 / μ : ℝ) : ℂ) * LogP φ₀ P t := by
  have hμ := h.μ_pos
  have hm : 0 < 1 / μ := one_div_pos.mpr hμ
  have hL := abs_lt.mp hsec.2
  have hB := abs_lt.mp hβ
  have him : (((1 / μ : ℝ) : ℂ) * LogP φ₀ P t).im = (1 / μ) * (LogP φ₀ P t).im := by
    simp [mul_im]
  have h1 : (1 / μ) * (LogP φ₀ P t).im < (1 / μ) * (φ₀ + β) :=
    mul_lt_mul_of_pos_left (by linarith) hm
  have h2 : (1 / μ) * (φ₀ - β) < (1 / μ) * (LogP φ₀ P t).im :=
    mul_lt_mul_of_pos_left (by linarith) hm
  have e1 : (1 / μ) * (φ₀ + β) = φ₀ / μ + β / μ := by ring
  have e2 : (1 / μ) * (φ₀ - β) = φ₀ / μ - β / μ := by ring
  refine logBr_eq_of_exp ?_ ?_ ?_
  · rw [Complex.exp_add, exp_logBr hsec.1]
    rfl
  · rw [add_im, him]
    linarith
  · rw [add_im, him]
    linarith

theorem brPow_unif_mu (h : UnifSetup a φ₀ μ ρ P) {ω α β : ℝ} (hαβ : α + β / μ ≤ Real.pi) {t : ℂ}
    (hsec : t - a ∈ sectorBr ω α) (hβ : |(LogP φ₀ P t).im - φ₀| < β) (hP : P t ≠ 0) :
    brPow (ω + φ₀ / μ) μ (unif a φ₀ μ P t) = brPow ω μ (t - a) * P t := by
  rw [brPow, h.logBr_unif hαβ hsec hβ, mul_add, Complex.exp_add, brPow]
  congr 1
  rw [← mul_assoc, show (μ : ℂ) * ((1 / μ : ℝ) : ℂ) = 1 by
    push_cast; rw [mul_one_div, div_self (ofReal_ne_zero.mpr h.μ_pos.ne')], one_mul,
    exp_LogP hP]

theorem brPow_unif (h : UnifSetup a φ₀ μ ρ P) {ω α β : ℝ} (hαβ : α + β / μ ≤ Real.pi) {t : ℂ}
    (hsec : t - a ∈ sectorBr ω α) (hβ : |(LogP φ₀ P t).im - φ₀| < β) (c : ℂ) :
    brPow ω c (t - a) =
      brPow (ω + φ₀ / μ) c (unif a φ₀ μ P t) * cexp (-(c * ((1 / μ : ℝ) : ℂ)) * LogP φ₀ P t) := by
  rw [brPow, brPow, h.logBr_unif hαβ hsec hβ, ← Complex.exp_add]
  congr 1
  ring

theorem unif_mem_sectorBr (h : UnifSetup a φ₀ μ ρ P) {ω α β : ℝ} (hαβ : α + β / μ ≤ Real.pi)
    {t : ℂ} (hsec : t - a ∈ sectorBr ω α) (hβ : |(LogP φ₀ P t).im - φ₀| < β) :
    unif a φ₀ μ P t ∈ sectorBr (ω + φ₀ / μ) (α + β / μ) := by
  have hμ := h.μ_pos
  have hm : 0 < 1 / μ := one_div_pos.mpr hμ
  refine ⟨unif_ne_zero (sub_ne_zero.mp hsec.1), ?_⟩
  rw [h.logBr_unif hαβ hsec hβ, add_im]
  have him : (((1 / μ : ℝ) : ℂ) * LogP φ₀ P t).im = (1 / μ) * (LogP φ₀ P t).im := by
    simp [mul_im]
  rw [him]
  have hL := abs_lt.mp hsec.2
  have hB := abs_lt.mp hβ
  have h1 : (1 / μ) * (LogP φ₀ P t).im < (1 / μ) * (φ₀ + β) :=
    mul_lt_mul_of_pos_left (by linarith) hm
  have h2 : (1 / μ) * (φ₀ - β) < (1 / μ) * (LogP φ₀ P t).im :=
    mul_lt_mul_of_pos_left (by linarith) hm
  have e1 : (1 / μ) * (φ₀ + β) = φ₀ / μ + β / μ := by ring
  have e2 : (1 / μ) * (φ₀ - β) = φ₀ / μ - β / μ := by ring
  rw [abs_lt]
  constructor <;> linarith

end UnifSetup

end Azurite.DLMF
