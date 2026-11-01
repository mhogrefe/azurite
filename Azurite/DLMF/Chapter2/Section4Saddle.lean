/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4LaplaceMethod

/-!
# DLMF §2.4(iv): Saddle points (2.4.14–2.4.16)

The minimum of `ℜ(zp(t))` on the path `𝒫` is attained at an interior point `t₀ = γ(0)`, which
is a simple saddle point: `p′(t₀) = 0`, `p″(t₀) ≠ 0`, i.e. `p(t) = p(t₀) + (t − t₀)² P(t)` with
`P` analytic and `P(t₀) = p″(t₀)/2 = |P(t₀)| e^{iω₀} ≠ 0`. The hypotheses are collected in
`SaddlePoint` (the path `γ` on `(−A, B)`, (b), (c) at both ends, and the strict form of the
branch condition `|θ + 2ω + ω₀| ≤ π/2` of 2.4.16, `ω` the direction of the path at `t₀` towards
`b`).

* 2.4.14 (`dlmf_2_4_14`): `I(z) = ∫_{t₀}^b − ∫_{t₀}^a`, the second integral being the one along
  the reversed path `u ↦ γ(−u)`; both are of the form 2.4.10 (`SaddlePoint.forward`,
  `SaddlePoint.backward`), with `μ = 2`, `λ = 1`, direction `ω` resp. `ω + π`, and the branch
  `ω₀ − 2π` of `ph p₀` for the reversed path ("different branches of some of the fractional
  powers of `p₀` are used").
* The two sets of coefficients are related by `b⁻ₛ = (−1)^{s+1} b⁺ₛ` (`laplaceCoeff_backward`):
  the substitution for the reversed path is `w ↦ −w`.
* 2.4.15 (`dlmf_2_4_15`): the odd terms cancel and the even ones double,
  `e^{zp(t₀)} I(z) ∼ 2 ∑ Γ(s + ½) b₂ₛ z^{−(s+½)}`; `dlmf_2_4_15'` is DLMF's form with the factor
  `e^{−zp(t₀)}` on the right.
* 2.4.16 (`dlmf_2_4_16_b0`): `b₀ = q(t₀)/(2p″(t₀))^{1/2}` with the branch `e^{iω₀/2}`; `b₂` is in
  `Section4SaddleCoeff`.
* The remark on `p′(t₀) ≠ 0`: at an interior minimum of `ℜ(zp(t))` the directional derivative
  vanishes (`re_deriv_eq_zero_of_isLocalMin`), so with `μ = 1` the branch condition 2.4.13 can
  only hold with equality and §2.4(iii) does not apply; formally the two sets of coefficients
  coincide (`laplaceCoeff_backward_one`) and the right-hand side of 2.4.14 "reduces to the error
  terms".
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-! ### Integer powers have no branch -/

theorem brPow_natCast {ω : ℝ} (n : ℕ) {z : ℂ} (hz : z ≠ 0) : brPow ω (n : ℂ) z = z ^ n := by
  rw [brPow, Complex.exp_nat_mul, exp_logBr hz]

theorem brPow_zero (ω : ℝ) (z : ℂ) : brPow ω 0 z = 1 := by simp [brPow]

/-! ### Changing the branch of `ph p₀` by `−2π` -/

theorem logBr_sub_two_pi (ω : ℝ) (z : ℂ) :
    logBr (ω - 2 * Real.pi) z = logBr ω z - 2 * Real.pi * I := by
  simp only [logBr]
  have : cexp (-(((ω - 2 * Real.pi : ℝ) : ℂ) * I)) = cexp (-(ω * I)) := by
    rw [show -(((ω - 2 * Real.pi : ℝ) : ℂ) * I) = -(ω * I) + 2 * Real.pi * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [this]
  push_cast
  ring

theorem LogP_sub_two_pi (φ₀ : ℝ) (P : ℂ → ℂ) (t : ℂ) :
    LogP (φ₀ - 2 * Real.pi) P t = LogP φ₀ P t - 2 * Real.pi * I :=
  logBr_sub_two_pi φ₀ (P t)

theorem unif_sub_two_pi (a : ℂ) (φ₀ μ : ℝ) (P : ℂ → ℂ) (t : ℂ) :
    unif a (φ₀ - 2 * Real.pi) μ P t =
      cexp (-(((1 / μ : ℝ) : ℂ) * (2 * Real.pi * I))) * unif a φ₀ μ P t := by
  simp only [unif, LogP_sub_two_pi]
  rw [show ((1 / μ : ℝ) : ℂ) * (LogP φ₀ P t - 2 * Real.pi * I) =
    ((1 / μ : ℝ) : ℂ) * LogP φ₀ P t + -(((1 / μ : ℝ) : ℂ) * (2 * Real.pi * I)) by ring,
    Complex.exp_add]
  ring

theorem unif_sub_two_pi_two (a : ℂ) (φ₀ : ℝ) (P : ℂ → ℂ) (t : ℂ) :
    unif a (φ₀ - 2 * Real.pi) 2 P t = -unif a φ₀ 2 P t := by
  rw [unif_sub_two_pi]
  have : cexp (-(((1 / (2 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * I))) = -1 := by
    rw [show -(((1 / (2 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * I)) = -(Real.pi * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg_one]
  rw [this, neg_one_mul]

/-- A `UnifSetup` with the branch `φ₀` of `ph p₀` is also one with the branch `φ₀ − 2π`. -/
theorem UnifSetup.sub_two_pi {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P) :
    UnifSetup a (φ₀ - 2 * Real.pi) μ ρ P where
  μ_pos := h.μ_pos
  ρ_pos := h.ρ_pos
  differentiableOn := h.differentiableOn
  P_a := by
    conv_lhs => rw [h.P_a]
    congr 1
    rw [show (((φ₀ - 2 * Real.pi : ℝ) : ℂ) * I) = φ₀ * I + -(2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
  P_ne := h.P_ne

/-! ### The hypotheses -/

/-- **DLMF §2.4(iv)**: the path `t = γ(u)`, `−A < u < B`, passes through the simple saddle point
`t₀ = γ(0)` of `p` with direction `ω` (towards `b`); `p(t) = p(t₀) + (t − t₀)² P(t)` near `t₀`
with `P(t₀) = |P(t₀)| e^{iω₀} ≠ 0`; (b) and (c) of §2.4(iii) hold at both ends; and the branch
condition of 2.4.16, `|θ + 2ω + ω₀| ≤ π/2`, holds strictly. -/
structure SaddlePoint (p q : ℂ → ℂ) (γ γ' : ℝ → ℂ) (A B : ℝ) (t₀ : ℂ) (ω : ℝ) (T : Set ℂ)
    (P : ℂ → ℂ) (ω₀ ρ : ℝ) (θ₁ θ₂ Z : ℝ) : Prop where
  A_pos : 0 < A
  B_pos : 0 < B
  γ_zero : γ 0 = t₀
  γ_deriv : ∀ u ∈ Ioo (-A) B, HasDerivAt γ (γ' u) u
  γ'_cont : ContinuousOn γ' (Ioo (-A) B)
  γ'_ne : γ' 0 ≠ 0
  γ'_dir : γ' 0 = (‖γ' 0‖ : ℂ) * cexp (ω * I)
  T_open : IsOpen T
  γ_mem : ∀ u ∈ Ioo (-A) B, γ u ∈ T
  p_diff : DifferentiableOn ℂ p T
  q_diff : DifferentiableOn ℂ q T
  -- the simple saddle point
  uset : UnifSetup t₀ ω₀ 2 ρ P
  p_eq : ∀ t ∈ Metric.ball t₀ ρ, p t = p t₀ + (t - t₀) ^ 2 * P t
  ball_sub : Metric.ball t₀ ρ ⊆ T
  -- (b)
  θ_lt : θ₂ - θ₁ < Real.pi
  θ₁_gt : -Real.pi < θ₁
  θ₂_le : θ₂ ≤ Real.pi
  θ_le : θ₁ ≤ θ₂
  Z_pos : 0 < Z
  integrable : ∀ z : ℂ, θ₁ ≤ arg z → arg z ≤ θ₂ → Z ≤ ‖z‖ →
    IntegrableOn (fun u => cexp (-(z * p (γ u))) * q (γ u) * γ' u) (Ioo (-A) B)
  unif_tail_b : ∀ ε > 0, ∃ U ∈ Ioo 0 B, ∀ z : ℂ, θ₁ ≤ arg z → arg z ≤ θ₂ → Z ≤ ‖z‖ →
    ∫ u in Ioo U B, ‖cexp (-(z * p (γ u))) * q (γ u) * γ' u‖ ≤ ε
  unif_tail_a : ∀ ε > 0, ∃ U ∈ Ioo 0 A, ∀ z : ℂ, θ₁ ≤ arg z → arg z ≤ θ₂ → Z ≤ ‖z‖ →
    ∫ u in Ioo (-A) (-U), ‖cexp (-(z * p (γ u))) * q (γ u) * γ' u‖ ≤ ε
  -- (c)
  re_pos : ∀ θ ∈ Icc θ₁ θ₂, ∀ u ∈ Ioo (-A) B, u ≠ 0 →
    0 < (cexp (θ * I) * (p (γ u) - p t₀)).re
  re_tail_b : ∃ c > 0, ∃ U ∈ Ioo 0 B, ∀ θ ∈ Icc θ₁ θ₂, ∀ u ∈ Ioo U B,
    c ≤ (cexp (θ * I) * (p (γ u) - p t₀)).re
  re_tail_a : ∃ c > 0, ∃ U ∈ Ioo 0 A, ∀ θ ∈ Icc θ₁ θ₂, ∀ u ∈ Ioo (-A) (-U),
    c ≤ (cexp (θ * I) * (p (γ u) - p t₀)).re
  -- the branch condition of 2.4.16 (strict)
  branch₁ : |θ₁ + 2 * ω + ω₀| < Real.pi / 2
  branch₂ : |θ₂ + 2 * ω + ω₀| < Real.pi / 2

namespace SaddlePoint

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {A B : ℝ} {t₀ : ℂ} {ω : ℝ} {T : Set ℂ} {P : ℂ → ℂ}
  {ω₀ ρ : ℝ} {θ₁ θ₂ Z : ℝ}

/-- The integral `∫_{t₀}^b` is of the form 2.4.10 with `μ = 2`, `λ = 1`, `Q = q`. -/
theorem forward (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    LaplaceContour p q γ γ' B t₀ ω T P q 1 2 ω₀ ρ (Real.pi / 2) θ₁ θ₂ Z where
  B_pos := h.B_pos
  γ_zero := h.γ_zero
  γ_deriv u hu := h.γ_deriv u ⟨by linarith [h.A_pos, hu.1], hu.2⟩
  γ'_cont := h.γ'_cont.mono fun u hu => ⟨by linarith [h.A_pos, hu.1], hu.2⟩
  γ'_ne := h.γ'_ne
  γ'_dir := h.γ'_dir
  T_open := h.T_open
  γ_mem u hu := h.γ_mem u ⟨by linarith [h.A_pos, hu.1], hu.2⟩
  p_diff := h.p_diff
  q_diff := h.q_diff
  uset := h.uset
  lam_re := by norm_num
  Q_diff := h.q_diff.mono h.ball_sub
  α_pos := by positivity
  α_le := le_rfl
  p_eq t ht hρ := by
    rw [h.p_eq t (by rwa [Metric.mem_ball, dist_eq_norm]),
      show ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) by norm_num, brPow_natCast 2 ht.1]
  q_eq t ht hρ := by rw [sub_self, brPow_zero, one_mul]
  θ_lt := h.θ_lt
  θ₁_gt := h.θ₁_gt
  θ₂_le := h.θ₂_le
  θ_le := h.θ_le
  Z_pos := h.Z_pos
  integrable z h1 h2 h3 :=
    (h.integrable z h1 h2 h3).mono_set fun u hu => ⟨by linarith [h.A_pos, hu.1], hu.2⟩
  unif_tail := h.unif_tail_b
  re_pos θ hθ u hu := h.re_pos θ hθ u ⟨by linarith [h.A_pos, hu.1], hu.2⟩ hu.1.ne'
  re_tail := h.re_tail_b
  branch₁ := h.branch₁
  branch₂ := h.branch₂

/-! ### Reversing the parameter -/

theorem setIntegral_Ioo_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    ∫ u in Ioo a b, g (-u) = ∫ u in Ioo (-b) (-a), g u := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_neg, intervalIntegral.integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo]

theorem integrableOn_Ioo_comp_neg {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hg : IntegrableOn g (Ioo (-b) (-a))) :
    IntegrableOn (fun u => g (-u)) (Ioo a b) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)] at hg
  simpa only [neg_neg] using ((IntervalIntegrable.iff_comp_neg (f := g)).mp hg).symm

/-- The integral `∫_{t₀}^a` (reversed path `u ↦ γ(−u)`) is of the form 2.4.10 with `μ = 2`,
`λ = 1`, direction `ω + π` and the branch `ω₀ − 2π` of `ph p₀`. -/
theorem backward (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    LaplaceContour p q (fun u => γ (-u)) (fun u => -γ' (-u)) A t₀ (ω + Real.pi) T P q 1 2
      (ω₀ - 2 * Real.pi) ρ (Real.pi / 2) θ₁ θ₂ Z where
  B_pos := h.A_pos
  γ_zero := by simpa using h.γ_zero
  γ_deriv u hu := by
    have := HasDerivAt.scomp u (h.γ_deriv (-u) ⟨by linarith [hu.2], by linarith [h.B_pos, hu.1]⟩)
      (hasDerivAt_neg u)
    simpa [Function.comp_def] using this
  γ'_cont := (h.γ'_cont.comp continuousOn_neg fun u hu =>
    ⟨by linarith [hu.2], by linarith [h.B_pos, hu.1]⟩).neg
  γ'_ne := by simpa using h.γ'_ne
  γ'_dir := by
    rw [neg_zero, norm_neg]
    conv_lhs => rw [h.γ'_dir]
    rw [show cexp (((ω + Real.pi : ℝ) : ℂ) * I) = -cexp (ω * I) by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring]
    ring
  T_open := h.T_open
  γ_mem u hu := h.γ_mem (-u) ⟨by linarith [hu.2], by linarith [h.B_pos, hu.1]⟩
  p_diff := h.p_diff
  q_diff := h.q_diff
  uset := h.uset.sub_two_pi
  lam_re := by norm_num
  Q_diff := h.q_diff.mono h.ball_sub
  α_pos := by positivity
  α_le := le_rfl
  p_eq t ht hρ := by
    rw [h.p_eq t (by rwa [Metric.mem_ball, dist_eq_norm]),
      show ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) by norm_num, brPow_natCast 2 ht.1]
  q_eq t ht hρ := by rw [sub_self, brPow_zero, one_mul]
  θ_lt := h.θ_lt
  θ₁_gt := h.θ₁_gt
  θ₂_le := h.θ₂_le
  θ_le := h.θ_le
  Z_pos := h.Z_pos
  integrable z h1 h2 h3 := by
    have hF := (h.integrable z h1 h2 h3).mono_set
      (fun u hu => ⟨hu.1, hu.2.trans h.B_pos⟩ : Ioo (-A) 0 ⊆ Ioo (-A) B)
    have := (integrableOn_Ioo_comp_neg h.A_pos.le (by simpa only [neg_zero] using hF)).neg
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioo
    simp only [Pi.neg_apply, mul_neg]
  unif_tail ε hε := by
    obtain ⟨U, hU, hbound⟩ := h.unif_tail_a ε hε
    refine ⟨U, hU, fun z h1 h2 h3 => ?_⟩
    have : (fun u => ‖cexp (-(z * p (γ (-u)))) * q (γ (-u)) * -γ' (-u)‖) =
        fun u => (fun v => ‖cexp (-(z * p (γ v))) * q (γ v) * γ' v‖) (-u) := by
      funext u
      simp only [mul_neg, norm_neg]
    rw [this]
    exact (setIntegral_Ioo_comp_neg (fun v => ‖cexp (-(z * p (γ v))) * q (γ v) * γ' v‖)
      hU.2.le).trans_le (hbound z h1 h2 h3)
  re_pos θ hθ u hu :=
    h.re_pos θ hθ (-u) ⟨by linarith [hu.2], by linarith [h.B_pos, hu.1]⟩ (neg_ne_zero.mpr hu.1.ne')
  re_tail := by
    obtain ⟨c, hc, U, hU, hb⟩ := h.re_tail_a
    exact ⟨c, hc, U, hU, fun θ hθ u hu => hb θ hθ (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩
  branch₁ := by
    have := h.branch₁
    rwa [show θ₁ + 2 * (ω + Real.pi) + (ω₀ - 2 * Real.pi) = θ₁ + 2 * ω + ω₀ by ring]
  branch₂ := by
    have := h.branch₂
    rwa [show θ₂ + 2 * (ω + Real.pi) + (ω₀ - 2 * Real.pi) = θ₂ + 2 * ω + ω₀ by ring]

/-- **DLMF 2.4.14**: `I(z) = ∫_{t₀}^b e^{−zp}q dt − ∫_{t₀}^a e^{−zp}q dt`, the second integral
along the reversed path. -/
theorem dlmf_2_4_14 (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) {z : ℂ}
    (h1 : θ₁ ≤ arg z) (h2 : arg z ≤ θ₂) (h3 : Z ≤ ‖z‖) :
    ∫ u in Ioo (-A) B, cexp (-(z * p (γ u))) * q (γ u) * γ' u =
      laplaceContour p q γ γ' B z -
        laplaceContour p q (fun u => γ (-u)) (fun u => -γ' (-u)) A z := by
  set F : ℝ → ℂ := fun u => cexp (-(z * p (γ u))) * q (γ u) * γ' u with hF
  have hFI := h.integrable z h1 h2 h3
  have hsplit : ∫ u in Ioo (-A) B, F u = (∫ u in Ioo (-A) 0, F u) + ∫ u in Ico 0 B, F u := by
    rw [← Ioo_union_Ico_eq_Ioo (neg_lt_zero.mpr h.A_pos) h.B_pos.le,
      setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => lt_irrefl _ (hx.2.trans_le hx'.1))
      measurableSet_Ico (hFI.mono_set fun u hu => ⟨hu.1, hu.2.trans h.B_pos⟩)
      (hFI.mono_set fun u hu => ⟨by linarith [h.A_pos, hu.1], hu.2⟩)]
  have hIco : ∫ u in Ico 0 B, F u = ∫ u in Ioo 0 B, F u := integral_Ico_eq_integral_Ioo
  have hneg : laplaceContour p q (fun u => γ (-u)) (fun u => -γ' (-u)) A z =
      -∫ u in Ioo (-A) 0, F u := by
    rw [laplaceContour]
    have : (fun u => cexp (-(z * p (γ (-u)))) * q (γ (-u)) * -γ' (-u)) = fun u => -F (-u) := by
      funext u
      simp only [hF, mul_neg]
    rw [this, integral_neg, setIntegral_Ioo_comp_neg F h.A_pos.le, neg_zero]
  rw [hsplit, hIco, hneg, laplaceContour]
  ring

end SaddlePoint

/-! ### The coefficients of the reversed path -/

section Coeff

variable {a : ℂ} {φ₀ ρ : ℝ} {P Q : ℂ → ℂ}

/-- With the branch `φ₀ − 2π` and `μ = 2` the substitution is `w ↦ −w`. -/
theorem unifInv_sub_two_pi_two (h : UnifSetup a φ₀ 2 ρ P)
    (h' : UnifSetup a (φ₀ - 2 * Real.pi) 2 ρ P) :
    unifInv h' =ᶠ[𝓝 0] fun w => unifInv h (-w) := by
  have hf := h'.analyticAt_unif_a.hasStrictDerivAt
  have hu := HasStrictFDerivAt.localInverse_unique (hf.hasStrictFDerivAt_equiv h'.deriv_unif_a_ne)
    (g := fun w => unifInv h (-w)) ?_
  · rw [UnifSetup.unif_a] at hu
    filter_upwards [hu] with w hw
    rw [unifInv]
    exact hw.symm
  · filter_upwards [h.eventually_unifInv_unif] with t ht
    simp only [unif_sub_two_pi_two, neg_neg, ht]

theorem laplaceG_sub_two_pi_two (h : UnifSetup a φ₀ 2 ρ P)
    (h' : UnifSetup a (φ₀ - 2 * Real.pi) 2 ρ P) (Q : ℂ → ℂ) :
    laplaceG h' 1 Q =ᶠ[𝓝 0] fun w => -laplaceG h 1 Q (-w) := by
  have h1 := unifInv_sub_two_pi_two h h'
  have h2 : deriv (unifInv h') =ᶠ[𝓝 0] fun w => -deriv (unifInv h) (-w) := by
    filter_upwards [h1.deriv] with w hw
    rw [hw, deriv_comp_neg]
  filter_upwards [h1, h2] with w hw1 hw2
  simp only [laplaceG, hw1, hw2, sub_self, zero_div, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  ring

/-- `b⁻ₛ = (−1)^{s+1} b⁺ₛ`: the coefficients of the reversed path. -/
theorem laplaceCoeff_sub_two_pi_two (h : UnifSetup a φ₀ 2 ρ P)
    (h' : UnifSetup a (φ₀ - 2 * Real.pi) 2 ρ P) (Q : ℂ → ℂ) (s : ℕ) :
    laplaceCoeff h' 1 Q s = (-1) ^ (s + 1) * laplaceCoeff h 1 Q s := by
  simp only [laplaceCoeff]
  rw [(laplaceG_sub_two_pi_two h h' Q).iteratedDeriv_eq s, iteratedDeriv_fun_neg,
    iteratedDeriv_comp_neg, neg_zero, smul_eq_mul, pow_succ]
  ring

/-- With `μ = 1` the branch `φ₀ − 2π` gives the same substitution. -/
theorem unif_sub_two_pi_one (a : ℂ) (φ₀ : ℝ) (P : ℂ → ℂ) (t : ℂ) :
    unif a (φ₀ - 2 * Real.pi) 1 P t = unif a φ₀ 1 P t := by
  rw [unif_sub_two_pi]
  have : cexp (-(((1 / (1 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * I))) = 1 := by
    rw [show -(((1 / (1 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * I)) = -(2 * Real.pi * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [this, one_mul]

/-- The remark of DLMF for `p′(t₀) ≠ 0` (`μ = 1`): the coefficients of the two integrals in 2.4.14
coincide, so formally the expansions cancel. -/
theorem laplaceCoeff_sub_two_pi_one (h : UnifSetup a φ₀ 1 ρ P)
    (h' : UnifSetup a (φ₀ - 2 * Real.pi) 1 ρ P) (Q : ℂ → ℂ) (s : ℕ) :
    laplaceCoeff h' 1 Q s = laplaceCoeff h 1 Q s := by
  have h1 : unifInv h' =ᶠ[𝓝 0] unifInv h := by
    have hf := h'.analyticAt_unif_a.hasStrictDerivAt
    have hu := HasStrictFDerivAt.localInverse_unique
      (hf.hasStrictFDerivAt_equiv h'.deriv_unif_a_ne) (g := unifInv h) ?_
    · rw [UnifSetup.unif_a] at hu
      filter_upwards [hu] with w hw
      rw [unifInv]
      exact hw.symm
    · filter_upwards [h.eventually_unifInv_unif] with t ht
      simp only [unif_sub_two_pi_one, ht]
  have h2 : laplaceG h' 1 Q =ᶠ[𝓝 0] laplaceG h 1 Q := by
    filter_upwards [h1, h1.deriv] with w hw1 hw2
    simp only [laplaceG, hw1, hw2, sub_self, zero_div, neg_zero, zero_mul, Complex.exp_zero]
  simp only [laplaceCoeff]
  rw [h2.iteratedDeriv_eq s]

end Coeff

/-! ### Two more facts on expansions -/

theorem IsGenAsympExpansionDLMF.sub {α : Type*} {l : Filter α} {φ : ℕ → α → ℂ} {f g : α → ℂ}
    {fs gs : ℕ → α → ℂ} (hf : IsGenAsympExpansionDLMF l φ f fs)
    (hg : IsGenAsympExpansionDLMF l φ g gs) :
    IsGenAsympExpansionDLMF l φ (fun x => f x - g x) (fun s x => fs s x - gs s x) := by
  refine ⟨hf.1, fun n => ?_⟩
  obtain ⟨K, hK⟩ := hf.2 n
  obtain ⟨K', hK'⟩ := hg.2 n
  refine ⟨K + K', ?_⟩
  rw [eventually_map] at hK hK' ⊢
  filter_upwards [hK, hK'] with x h1 h2
  calc ‖(f x - g x - ∑ s ∈ Finset.range n, (fs s x - gs s x)) / φ n x‖
      = ‖(f x - ∑ s ∈ Finset.range n, fs s x) / φ n x -
          (g x - ∑ s ∈ Finset.range n, gs s x) / φ n x‖ := by
        rw [Finset.sum_sub_distrib, ← sub_div]
        ring_nf
    _ ≤ ‖(f x - ∑ s ∈ Finset.range n, fs s x) / φ n x‖ +
          ‖(g x - ∑ s ∈ Finset.range n, gs s x) / φ n x‖ := norm_sub_le _ _
    _ ≤ K + K' := add_le_add h1 h2

theorem IsAsympScaleDLMF.congr {α : Type*} {l : Filter α} {φ φ' : ℕ → α → ℂ}
    (h : IsAsympScaleDLMF l φ) (hφ : ∀ s, φ s =ᶠ[l] φ' s) : IsAsympScaleDLMF l φ' := fun s =>
  (h s).congr' (by
    filter_upwards [hφ s, hφ (s + 1)] with x h1 h2
    rw [h1, h2])

/-- If the odd terms vanish, the even terms form an expansion with respect to the even scale. -/
theorem IsGenAsympExpansionDLMF.even {α : Type*} {l : Filter α} {φ : ℕ → α → ℂ} {f : α → ℂ}
    {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs) (hodd : ∀ k, fs (2 * k + 1) = 0)
    (hscale : IsAsympScaleDLMF l fun k => φ (2 * k)) :
    IsGenAsympExpansionDLMF l (fun k => φ (2 * k)) f (fun k => fs (2 * k)) := by
  refine ⟨hscale, fun m => ?_⟩
  have hsum : ∀ x, ∑ k ∈ Finset.range m, fs (2 * k) x = ∑ s ∈ Finset.range (2 * m), fs s x := by
    intro x
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, hodd m]
      simp
  simpa only [hsum] using h.2 (2 * m)

/-! ### The theorem -/

namespace SaddlePoint

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {A B : ℝ} {t₀ : ℂ} {ω : ℝ} {T : Set ℂ} {P : ℂ → ℂ}
  {ω₀ ρ : ℝ} {θ₁ θ₂ Z : ℝ}

/-- The coefficients `bₛ` of 2.4.15: those of §2.4(iii) for `∫_{t₀}^b` (`μ = 2`, `λ = 1`). -/
noncomputable def saddleCoeff (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) (s : ℕ) : ℂ :=
  laplaceCoeff h.uset 1 q s

theorem watsonExpC_two_mul (k : ℕ) : watsonExpC 1 2 (2 * k) = (k : ℂ) + 1 / 2 := by
  simp only [watsonExpC]
  push_cast
  ring

/-- **DLMF 2.4.15**: for a simple saddle point `t₀` interior to the path,
`e^{zp(t₀)} ∫_a^b e^{−zp(t)} q(t) dt ∼ 2 ∑ Γ(s + ½) b₂ₛ z^{−(s+½)}` as `z → ∞` in
`θ₁ ≤ ph z ≤ θ₂` (the odd terms of the two expansions in 2.4.14 cancel, the even ones double). -/
theorem dlmf_2_4_15 (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | θ₁ ≤ arg z ∧ arg z ≤ θ₂})
      (fun k z => z ^ (-((k : ℂ) + 1 / 2)))
      (fun z => cexp (z * p t₀) * ∫ u in Ioo (-A) B, cexp (-(z * p (γ u))) * q (γ u) * γ' u)
      (fun k z => 2 * Complex.Gamma ((k : ℂ) + 1 / 2) * saddleCoeff h (2 * k) *
        z ^ (-((k : ℂ) + 1 / 2))) := by
  set S := {z : ℂ | θ₁ ≤ arg z ∧ arg z ≤ θ₂} with hS
  set l := Bornology.cobounded ℂ ⊓ 𝓟 S with hl
  have hF := h.forward.dlmf_2_4_12
  have hB := h.backward.dlmf_2_4_12
  have hcoef : ∀ s, laplaceCoeff h.backward.uset 1 q s = (-1) ^ (s + 1) * saddleCoeff h s :=
    fun s => laplaceCoeff_sub_two_pi_two h.uset h.backward.uset q s
  have hfwd : ∀ s, laplaceCoeff h.forward.uset 1 q s = saddleCoeff h s := fun s => rfl
  have hsub := hF.sub hB
  have hZ : ∀ᶠ z in l, Z ≤ ‖z‖ :=
    mem_inf_of_left (Filter.hasBasis_cobounded_norm.mem_of_mem (i := Z) trivial)
  have hSz : ∀ᶠ z in l, z ∈ S := mem_inf_of_right (mem_principal_self S)
  have hscale : IsAsympScaleDLMF l fun k z => z ^ (-watsonExpC 1 2 (2 * k)) := by
    refine (WatsonSector.isAsympScale_cpow_neg (l := l) inf_le_left one_pos (1 / 2 : ℂ)).congr
      fun k => Eventually.of_forall fun z => ?_
    simp only [watsonExpC]
    congr 2
    push_cast
    ring
  have hodd : ∀ k, (fun z => Complex.Gamma (watsonExpC 1 2 (2 * k + 1)) *
      laplaceCoeff h.forward.uset 1 q (2 * k + 1) * z ^ (-watsonExpC 1 2 (2 * k + 1)) -
        Complex.Gamma (watsonExpC 1 2 (2 * k + 1)) * laplaceCoeff h.backward.uset 1 q (2 * k + 1) *
          z ^ (-watsonExpC 1 2 (2 * k + 1))) = 0 := by
    intro k
    funext z
    have : ((-1 : ℂ)) ^ (2 * k + 1 + 1) = 1 := by
      rw [pow_succ, pow_succ, pow_mul]
      norm_num
    rw [hcoef, this, one_mul]
    exact sub_self _
  have heven := hsub.even hodd hscale
  refine heven.congr' (fun k => Eventually.of_forall fun z => ?_) ?_
    (fun k => Eventually.of_forall fun z => ?_)
  · simp only [watsonExpC_two_mul]
  · filter_upwards [hSz, hZ] with z hz hzZ
    rw [h.dlmf_2_4_14 hz.1 hz.2 hzZ, mul_sub]
  · simp only [hcoef, hfwd, watsonExpC_two_mul]
    have : ((-1 : ℂ)) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [this]
    ring

/-- **DLMF 2.4.15** in DLMF's form, with the factor `e^{−zp(t₀)}` on the right. -/
theorem dlmf_2_4_15' (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | θ₁ ≤ arg z ∧ arg z ≤ θ₂})
      (fun k z => cexp (-(z * p t₀)) * z ^ (-((k : ℂ) + 1 / 2)))
      (fun z => ∫ u in Ioo (-A) B, cexp (-(z * p (γ u))) * q (γ u) * γ' u)
      (fun k z => 2 * cexp (-(z * p t₀)) * Complex.Gamma ((k : ℂ) + 1 / 2) *
        saddleCoeff h (2 * k) * z ^ (-((k : ℂ) + 1 / 2))) := by
  have := h.dlmf_2_4_15.mul_fun (g := fun z => cexp (-(z * p t₀)))
    (Eventually.of_forall fun z => Complex.exp_ne_zero _)
  refine this.congr' (fun k => EventuallyEq.refl _ _) (Eventually.of_forall fun z => ?_)
    (fun k => Eventually.of_forall fun z => ?_)
  · beta_reduce
    rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  · beta_reduce
    ring

end SaddlePoint

/-! ### 2.4.16: `b₀` -/

theorem UnifSetup.deriv_unifInv_zero {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P) :
    deriv (unifInv h) 0 = (cexp (((1 / μ : ℝ) : ℂ) * LogP φ₀ P a))⁻¹ := by
  have := h.eventually_deriv_unifInv.self_of_nhds
  rw [h.unifInv_zero, h.deriv_unif_a] at this
  exact eq_inv_of_mul_eq_one_left this

namespace SaddlePoint

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {A B : ℝ} {t₀ : ℂ} {ω : ℝ} {T : Set ℂ} {P : ℂ → ℂ}
  {ω₀ ρ : ℝ} {θ₁ θ₂ Z : ℝ}

/-- `p″(t₀) = 2P(t₀)`. -/
theorem iteratedDeriv_two (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    iteratedDeriv 2 p t₀ = 2 * P t₀ := by
  have hρ := h.uset.ρ_pos
  have hPan : ∀ t ∈ Metric.ball t₀ ρ, AnalyticAt ℂ P t := fun t ht => h.uset.analyticAt_P ht
  have hd1 : ∀ t ∈ Metric.ball t₀ ρ,
      HasDerivAt p (2 * (t - t₀) * P t + (t - t₀) ^ 2 * deriv P t) t := by
    intro t ht
    have hP := (hPan t ht).differentiableAt.hasDerivAt
    have h1 := (hasDerivAt_const t (p t₀)).add
      ((((hasDerivAt_id t).sub_const t₀).pow 2).mul hP)
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
      exact h.p_eq s hs
    · simp only [Pi.pow_apply, id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one,
        zero_add]
  have hd2 : HasDerivAt (fun t => 2 * (t - t₀) * P t + (t - t₀) ^ 2 * deriv P t) (2 * P t₀) t₀ := by
    have hP := (hPan t₀ (Metric.mem_ball_self hρ)).differentiableAt.hasDerivAt
    have hP' := (hPan t₀ (Metric.mem_ball_self hρ)).deriv.differentiableAt.hasDerivAt
    have h1 := (((hasDerivAt_id t₀).sub_const t₀).const_mul (2 : ℂ)).mul hP
    have h2 := (((hasDerivAt_id t₀).sub_const t₀).pow 2).mul hP'
    refine (h1.add h2).congr_deriv ?_
    simp only [Pi.pow_apply, id, sub_self, mul_zero, zero_mul, add_zero, mul_one, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, zero_pow two_ne_zero]
  have hev : deriv p =ᶠ[𝓝 t₀] fun t => 2 * (t - t₀) * P t + (t - t₀) ^ 2 * deriv P t := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)] with t ht
    exact (hd1 t ht).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, hd2.deriv]

theorem norm_iteratedDeriv_two (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    ‖iteratedDeriv 2 p t₀‖ = 2 * ‖P t₀‖ := by
  rw [h.iteratedDeriv_two, norm_mul]
  norm_num

/-- `ω₀` is a branch of `ph p″(t₀)`: `p″(t₀) = |p″(t₀)| e^{iω₀}`. -/
theorem dlmf_2_4_16_branch (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    iteratedDeriv 2 p t₀ = (‖iteratedDeriv 2 p t₀‖ : ℂ) * cexp (ω₀ * I) := by
  rw [h.norm_iteratedDeriv_two, h.iteratedDeriv_two]
  conv_lhs => rw [h.uset.P_a]
  push_cast
  ring

theorem saddleCoeff_zero (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    saddleCoeff h 0 =
      q t₀ / (2 * ((‖P t₀‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * cexp ((ω₀ / 2 : ℝ) * I)) := by
  have hr := norm_pos_iff.mpr h.uset.P_ne
  simp only [saddleCoeff, laplaceCoeff, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, laplaceG, sub_self, zero_div, neg_zero, zero_mul, Complex.exp_zero, one_mul,
    UnifSetup.unifInv_zero, UnifSetup.deriv_unifInv_zero]
  have hL : LogP ω₀ P t₀ = Real.log ‖P t₀‖ + ω₀ * I := by
    rw [LogP]
    conv_lhs => rw [h.uset.P_a]
    exact logBr_polar hr (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hE : cexp (((1 / (2 : ℝ) : ℝ) : ℂ) * LogP ω₀ P t₀) =
      ((‖P t₀‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * cexp ((ω₀ / 2 : ℝ) * I) := by
    rw [hL, mul_add, Complex.exp_add]
    congr 1
    · rw [Real.rpow_def_of_pos hr, ofReal_exp]
      push_cast
      ring_nf
    · push_cast
      ring_nf
  rw [hE]
  have h1 : ((‖P t₀‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hr _).ne'
  have h2 : cexp ((ω₀ / 2 : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
  push_cast
  field_simp

/-- **DLMF 2.4.16**: `b₀ = q(t₀)/(2p″(t₀))^{1/2}`, where `(2p″(t₀))^{1/2} = (2|p″(t₀)|)^{1/2}
e^{iω₀/2}` with the branch `ω₀` of `ph p″(t₀)` satisfying `|θ + 2ω + ω₀| < π/2`. -/
theorem dlmf_2_4_16_b0 (h : SaddlePoint p q γ γ' A B t₀ ω T P ω₀ ρ θ₁ θ₂ Z) :
    saddleCoeff h 0 = q t₀ /
      ((((2 * ‖iteratedDeriv 2 p t₀‖) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * cexp ((ω₀ / 2 : ℝ) * I)) := by
  rw [saddleCoeff_zero, h.norm_iteratedDeriv_two, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _),
    show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num]
  push_cast
  ring

end SaddlePoint

/-! ### The remark on `p′(t₀) ≠ 0` -/

/-- At an interior minimum of `ℜ(e^{iθ}p(t))` along the path the directional derivative vanishes:
`ℜ(e^{iθ} p′(t₀) γ′(0)) = 0`. -/
theorem re_deriv_eq_zero_of_isLocalMin {p : ℂ → ℂ} {γ : ℝ → ℂ} {p' γ'₀ : ℂ} {θ : ℝ}
    (hp : HasDerivAt p p' (γ 0)) (hγ : HasDerivAt γ γ'₀ 0)
    (hmin : ∀ᶠ u in 𝓝 0, 0 ≤ (cexp (θ * I) * (p (γ u) - p (γ 0))).re) :
    (cexp (θ * I) * (p' * γ'₀)).re = 0 := by
  have h1 : HasDerivAt (fun u : ℝ => p (γ u)) (p' * γ'₀) 0 := hp.comp 0 hγ
  have h2 : HasDerivAt (fun u : ℝ => (cexp (θ * I) * (p (γ u) - p (γ 0))).re)
      (cexp (θ * I) * (p' * γ'₀)).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((h1.sub_const (p (γ 0))).const_mul (cexp (θ * I)))
    simpa [Function.comp_def] using this
  have hloc : IsLocalMin (fun u : ℝ => (cexp (θ * I) * (p (γ u) - p (γ 0))).re) 0 := by
    filter_upwards [hmin] with u hu
    simpa using hu
  exact hloc.hasDerivAt_eq_zero h2

/-- Hence, when `p′(t₀) ≠ 0` (`μ = 1`, `ph p′(t₀) = φ₀`, direction `ω`), the branch condition
2.4.13 cannot hold strictly: `cos(θ + ω + φ₀) = 0`. The case of §2.4(iii) with equality in 2.4.13
is the only one available, and it is not covered by Laplace's method. -/
theorem not_branch_lt_of_isLocalMin {p : ℂ → ℂ} {γ : ℝ → ℂ} {p' γ'₀ : ℂ} {θ ω φ₀ : ℝ}
    (hp : HasDerivAt p p' (γ 0)) (hγ : HasDerivAt γ γ'₀ 0)
    (hmin : ∀ᶠ u in 𝓝 0, 0 ≤ (cexp (θ * I) * (p (γ u) - p (γ 0))).re)
    (hp' : p' = (‖p'‖ : ℂ) * cexp (φ₀ * I)) (hp0 : p' ≠ 0)
    (hγ' : γ'₀ = (‖γ'₀‖ : ℂ) * cexp (ω * I)) (hγ0 : γ'₀ ≠ 0) :
    ¬ |θ + ω + φ₀| < Real.pi / 2 := by
  intro hlt
  have h0 := re_deriv_eq_zero_of_isLocalMin hp hγ hmin
  have : cexp (θ * I) * (p' * γ'₀) =
      ((‖p'‖ * ‖γ'₀‖ : ℝ) : ℂ) * cexp (((θ + ω + φ₀ : ℝ) : ℂ) * I) := by
    conv_lhs => rw [hp', hγ']
    push_cast
    rw [add_mul, add_mul, Complex.exp_add, Complex.exp_add]
    ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at h0
  have hcos : 0 < Real.cos (θ + ω + φ₀) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_lt.mp hlt], by linarith [abs_lt.mp hlt]⟩
  have : 0 < ‖p'‖ * ‖γ'₀‖ * Real.cos (θ + ω + φ₀) :=
    mul_pos (mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hγ0)) hcos
  linarith

end Azurite.DLMF
