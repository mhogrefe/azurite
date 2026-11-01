/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section8
import Azurite.DLMF.Chapter2.Section4Inverse

/-!
# DLMF §2.4(ii): Haar's method (2.4.6–2.4.9)

Given `q = ℒ^{−1}Q` and a comparison function `f = ℒ^{−1}F` (2.4.3, 2.4.6: hypotheses
`Tendsto (bromwichPartial Q σ t) atTop (𝓝 (q t))` and the same for `F`, `f`),
* 2.4.7 (`dlmf_2_4_7`): `q(t) − f(t) = (e^{σt}/2π) lim_{η→∞} ∫_{−η}^{η} e^{itτ}(Q − F)(σ+iτ) dτ`.
* "The integral converges uniformly at each limit for all sufficiently large `t`" is
  `UnifConvTails T g`: the tails `∫_{η₁}^{η₂}` and `∫_{−η₂}^{−η₁}` of `∫ e^{itτ} g(τ) dτ` are
  uniformly small for `t ≥ T`. Then the symmetric partial integrals converge
  (`fourierLim_exists`) and the limit tends to `0` as `t → ∞` (`tendsto_fourierLim_zero`), by the
  Riemann–Lebesgue lemma 1.8.10 on `[−η₀, η₀]` and the uniform tails.
* 2.4.8 (`dlmf_2_4_8`): `q(t) = f(t) + o(e^{ct})` as `t → +∞`.
* 2.4.9 (`dlmf_2_4_9`): if moreover the integrals with `(Q − F)^{(j)}`, `j ≤ m`, converge
  uniformly, then `q(t) = f(t) + o(t^{−m} e^{ct})`. Each integration by parts needs the boundary
  terms `e^{itη}(Q − F)^{(j)}(c + iη)` to vanish as `η → ±∞`; DLMF does not say so, but it follows
  from the uniform convergence for two frequencies (`tendsto_zero_of_tail_cauchy`): the boundary
  values `e^{itη} g(η)` converge for each `t`, and `|g(η)| → L ≠ 0` would force `e^{iη}` to
  converge as `η → ∞`.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-! ### The symmetric partial integrals -/

/-- `∫_{−η}^{η} g(τ) e^{itτ} dτ`. -/
noncomputable def fourierPartial (g : ℝ → ℂ) (t η : ℝ) : ℂ :=
  ∫ τ in (-η)..η, g τ * cexp (t * τ * I)

/-- `lim_{η→∞} ∫_{−η}^{η} g(τ) e^{itτ} dτ`. -/
noncomputable def fourierLim (g : ℝ → ℂ) (t : ℝ) : ℂ := limUnder atTop (fourierPartial g t)

/-- "`∫_{−∞}^{∞} e^{itτ} g(τ) dτ` converges uniformly at each limit for all `t ≥ T`": the tails
over `[η₁, η₂]` and `[−η₂, −η₁]` are uniformly small. -/
def UnifConvTails (T : ℝ) (g : ℝ → ℂ) : Prop :=
  ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ → ∀ t, T ≤ t →
    ‖∫ τ in η₁..η₂, g τ * cexp (t * τ * I)‖ ≤ ε ∧
    ‖∫ τ in (-η₂)..(-η₁), g τ * cexp (t * τ * I)‖ ≤ ε

theorem UnifConvTails.mono {T T' : ℝ} {g : ℝ → ℂ} (h : UnifConvTails T g) (hT : T ≤ T') :
    UnifConvTails T' g := fun ε hε => by
  obtain ⟨η₀, hη₀⟩ := h ε hε
  exact ⟨η₀, fun η₁ η₂ h1 h2 t ht => hη₀ η₁ η₂ h1 h2 t (hT.trans ht)⟩

theorem UnifConvTails.const_mul {T : ℝ} {g : ℝ → ℂ} (h : UnifConvTails T g) {k : ℂ}
    (hk : ‖k‖ = 1) : UnifConvTails T (fun τ => k * g τ) := fun ε hε => by
  obtain ⟨η₀, hη₀⟩ := h ε hε
  refine ⟨η₀, fun η₁ η₂ h1 h2 t ht => ?_⟩
  obtain ⟨ha, hb⟩ := hη₀ η₁ η₂ h1 h2 t ht
  have e : ∀ a b : ℝ, ∫ τ in a..b, (fun τ => k * g τ) τ * cexp (t * τ * I) =
      k * ∫ τ in a..b, g τ * cexp (t * τ * I) := fun a b => by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun τ _ => by ring
  rw [e, e, norm_mul, norm_mul, hk, one_mul, one_mul]
  exact ⟨ha, hb⟩

theorem UnifConvTails.of_const_mul {T : ℝ} {g : ℝ → ℂ} {k : ℂ} (hk : ‖k‖ = 1)
    (h : UnifConvTails T (fun τ => k * g τ)) : UnifConvTails T g := by
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hk
    exact zero_ne_one hk
  have := h.const_mul (k := k⁻¹) (by rw [norm_inv, hk, inv_one])
  simp only [← mul_assoc, inv_mul_cancel₀ hk0, one_mul] at this
  exact this

/-! ### 2.4.7 -/

theorem bromwichPartial_eq_fourierPartial {Q : ℂ → ℂ} (σ t η : ℝ) :
    bromwichPartial Q σ t η =
      (Real.exp (σ * t) : ℂ) / (2 * Real.pi) * fourierPartial (fun τ => Q (σ + τ * I)) t η := by
  unfold bromwichPartial fourierPartial
  rw [div_eq_inv_mul, mul_assoc,
    ← intervalIntegral.integral_const_mul (Real.exp (σ * t) : ℂ)]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [show ((σ : ℂ) + τ * I) * t = (σ * t : ℝ) + t * τ * I by push_cast; ring, Complex.exp_add,
    ofReal_exp]
  ring

theorem fourierPartial_sub (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h) (t η : ℝ) :
    fourierPartial (fun τ => g τ - h τ) t η = fourierPartial g t η - fourierPartial h t η := by
  unfold fourierPartial
  have h1 : IntervalIntegrable (fun τ : ℝ => g τ * cexp (t * τ * I)) volume (-η) η :=
    (hg.mul (by fun_prop : Continuous fun τ : ℝ => cexp (t * τ * I))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun τ : ℝ => h τ * cexp (t * τ * I)) volume (-η) η :=
    (hh.mul (by fun_prop : Continuous fun τ : ℝ => cexp (t * τ * I))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub h1 h2]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  ring

/-- **DLMF 2.4.7**: with `q = ℒ^{−1}Q` and `f = ℒ^{−1}F` (2.4.3, 2.4.6),
`q(t) − f(t) = (e^{σt}/2π) lim_{η→∞} ∫_{−η}^{η} e^{itτ}(Q(σ+iτ) − F(σ+iτ)) dτ`. -/
theorem dlmf_2_4_7 {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {σ t : ℝ}
    (hQc : Continuous fun τ : ℝ => Q (σ + τ * I)) (hFc : Continuous fun τ : ℝ => F (σ + τ * I))
    (hq : Tendsto (bromwichPartial Q σ t) atTop (𝓝 (q t)))
    (hf : Tendsto (bromwichPartial F σ t) atTop (𝓝 (f t))) :
    Tendsto (fun η => (Real.exp (σ * t) : ℂ) / (2 * Real.pi) *
      fourierPartial (fun τ => Q (σ + τ * I) - F (σ + τ * I)) t η) atTop (𝓝 (q t - f t)) ∧
    q t - f t = (Real.exp (σ * t) : ℂ) / (2 * Real.pi) *
      fourierLim (fun τ => Q (σ + τ * I) - F (σ + τ * I)) t := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact ofReal_ne_zero.mpr (by positivity)
  have hne : (Real.exp (σ * t) : ℂ) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne') hπ
  have h1 : Tendsto (fun η => (Real.exp (σ * t) : ℂ) / (2 * Real.pi) *
      fourierPartial (fun τ => Q (σ + τ * I) - F (σ + τ * I)) t η) atTop (𝓝 (q t - f t)) := by
    refine (hq.sub hf).congr fun η => ?_
    rw [bromwichPartial_eq_fourierPartial, bromwichPartial_eq_fourierPartial,
      fourierPartial_sub _ _ hQc hFc, mul_sub]
  refine ⟨h1, ?_⟩
  have h2 : Tendsto (fourierPartial (fun τ => Q (σ + τ * I) - F (σ + τ * I)) t) atTop
      (𝓝 ((q t - f t) / ((Real.exp (σ * t) : ℂ) / (2 * Real.pi)))) := by
    have := h1.const_mul ((Real.exp (σ * t) : ℂ) / (2 * Real.pi))⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at this
    rw [div_eq_inv_mul]
    exact this
  rw [fourierLim, h2.limUnder_eq, mul_div_cancel₀ _ hne]

/-! ### Convergence and the Riemann–Lebesgue limit -/

theorem fourierPartial_sub_eq {g : ℝ → ℂ} (hg : Continuous g) (t η₁ η₂ : ℝ) :
    fourierPartial g t η₂ - fourierPartial g t η₁ =
      (∫ τ in η₁..η₂, g τ * cexp (t * τ * I)) + ∫ τ in (-η₂)..(-η₁), g τ * cexp (t * τ * I) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun τ => g τ * cexp (t * τ * I)) volume a b :=
    fun a b => (hg.mul (by fun_prop)).intervalIntegrable a b
  unfold fourierPartial
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-η₂) (-η₁)) (hi (-η₁) η₂),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-η₁) η₁) (hi η₁ η₂)]
  ring

theorem fourierPartial_sub_le {g : ℝ → ℂ} (hg : Continuous g) {T : ℝ} (hU : UnifConvTails T g)
    {ε : ℝ} (hε : 0 < ε) : ∃ η₀, 0 ≤ η₀ ∧ ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ → ∀ t, T ≤ t →
      ‖fourierPartial g t η₂ - fourierPartial g t η₁‖ ≤ 2 * ε := by
  obtain ⟨η₀, hη₀⟩ := hU ε hε
  refine ⟨max η₀ 0, le_max_right _ _, fun η₁ η₂ h1 h12 t ht => ?_⟩
  obtain ⟨ha, hb⟩ := hη₀ η₁ η₂ ((le_max_left _ _).trans h1) h12 t ht
  rw [fourierPartial_sub_eq hg t η₁ η₂]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε + ε := add_le_add ha hb
    _ = 2 * ε := by ring

/-- Under uniform convergence of the tails, the partial integrals converge for every `t ≥ T`. -/
theorem fourierLim_exists {g : ℝ → ℂ} (hg : Continuous g) {T : ℝ} (hU : UnifConvTails T g)
    {t : ℝ} (ht : T ≤ t) : Tendsto (fourierPartial g t) atTop (𝓝 (fourierLim g t)) := by
  have hc : CauchySeq (fourierPartial g t) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨η₀, -, hη₀⟩ := fourierPartial_sub_le hg hU (by positivity : 0 < ε / 4)
    refine ⟨η₀, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    rcases le_total n m with h | h
    · have := hη₀ n m hn h t ht
      linarith
    · have := hη₀ m n hm h t ht
      rw [← norm_neg, neg_sub]
      linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  rwa [fourierLim, hL.limUnder_eq]

/-- The limit `lim_{η→∞} ∫_{−η}^{η} g(τ) e^{itτ} dτ` tends to `0` as `t → +∞` (Riemann–Lebesgue
on `[−η₀, η₀]` and uniformly small tails). -/
theorem tendsto_fourierLim_zero {g : ℝ → ℂ} (hg : Continuous g) {T : ℝ}
    (hU : UnifConvTails T g) : Tendsto (fourierLim g) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η₀, hη₀0, hη₀⟩ := fourierPartial_sub_le hg hU (by positivity : 0 < ε / 6)
  have hRL := dlmf_1_8_10 g (-η₀) η₀
  rw [Metric.tendsto_nhds] at hRL
  filter_upwards [hRL (ε / 3) (by positivity), eventually_ge_atTop T] with t hRLt ht
  rw [dist_zero_right] at hRLt ⊢
  have hlim := fourierLim_exists hg hU ht
  have htail : ‖fourierLim g t - fourierPartial g t η₀‖ ≤ 2 * (ε / 6) := by
    refine le_of_tendsto (hlim.sub_const _).norm ?_
    filter_upwards [eventually_ge_atTop η₀] with η hη
    exact hη₀ η₀ η le_rfl hη t ht
  calc ‖fourierLim g t‖ = ‖(fourierLim g t - fourierPartial g t η₀) + fourierPartial g t η₀‖ := by
        ring_nf
    _ ≤ ‖fourierLim g t - fourierPartial g t η₀‖ + ‖fourierPartial g t η₀‖ := norm_add_le _ _
    _ < 2 * (ε / 6) + ε / 3 := by
        have : ‖fourierPartial g t η₀‖ < ε / 3 := hRLt
        linarith
    _ = 2 * ε / 3 := by ring
    _ < ε := by linarith

/-! ### 2.4.8 -/

/-- **DLMF 2.4.8**: if `∫ e^{itτ}(Q − F)(c + iτ) dτ` converges uniformly at each limit for
`t ≥ T`, then `q(t) = f(t) + o(e^{ct})` as `t → +∞`. -/
theorem dlmf_2_4_8 {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {c T : ℝ}
    (hQc : Continuous fun τ : ℝ => Q (c + τ * I)) (hFc : Continuous fun τ : ℝ => F (c + τ * I))
    (hq : ∀ t, T ≤ t → Tendsto (bromwichPartial Q c t) atTop (𝓝 (q t)))
    (hf : ∀ t, T ≤ t → Tendsto (bromwichPartial F c t) atTop (𝓝 (f t)))
    (hU : UnifConvTails T fun τ => Q (c + τ * I) - F (c + τ * I)) :
    IsLittleODLMF atTop (fun t => q t - f t) (fun t => (Real.exp (c * t) : ℂ)) := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact ofReal_ne_zero.mpr (by positivity)
  have hGc : Continuous fun τ : ℝ => Q (c + τ * I) - F (c + τ * I) := hQc.sub hFc
  have h0 := (tendsto_fourierLim_zero hGc hU).const_mul (2 * Real.pi : ℂ)⁻¹
  rw [mul_zero] at h0
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop T] with t ht
  obtain ⟨-, h7⟩ := dlmf_2_4_7 hQc hFc (hq t ht) (hf t ht)
  rw [h7, eq_div_iff (ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  ring

/-! ### Decay of the boundary terms -/

theorem norm_cexp_mul_mul_I (t η : ℝ) : ‖cexp (t * η * I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_cexp_mul_mul_I (t τ : ℝ) :
    HasDerivAt (fun η : ℝ => cexp (t * η * I)) (cexp (t * τ * I) * (t * I)) τ := by
  have h := (((hasDerivAt_id τ).ofReal_comp.const_mul (t : ℂ)).mul_const I).cexp
  simpa using h

/-- `e^{iη}` has no limit as `η → +∞`. -/
theorem not_tendsto_cexp_mul_I (r : ℂ) :
    ¬ Tendsto (fun η : ℝ => cexp (η * I)) atTop (𝓝 r) := by
  intro hr
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : Tendsto (fun k : ℕ => cexp (((2 * Real.pi * k : ℝ) : ℂ) * I)) atTop (𝓝 r) :=
    hr.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hπ)
  have h2 : Tendsto (fun k : ℕ => cexp (((2 * Real.pi * k + Real.pi : ℝ) : ℂ) * I)) atTop
      (𝓝 r) :=
    hr.comp ((tendsto_natCast_atTop_atTop.const_mul_atTop hπ).atTop_add tendsto_const_nhds)
  have e1 : ∀ k : ℕ, cexp (((2 * Real.pi * k : ℝ) : ℂ) * I) = 1 := fun k => by
    rw [show (((2 * Real.pi * k : ℝ) : ℂ) * I) = k * (2 * Real.pi * I) by push_cast; ring]
    exact exp_nat_mul_two_pi_mul_I k
  have e2 : ∀ k : ℕ, cexp (((2 * Real.pi * k + Real.pi : ℝ) : ℂ) * I) = -1 := fun k => by
    rw [show (((2 * Real.pi * k + Real.pi : ℝ) : ℂ) * I) = k * (2 * Real.pi * I) + Real.pi * I by
      push_cast; ring, Complex.exp_add, exp_nat_mul_two_pi_mul_I, exp_pi_mul_I, one_mul]
  simp only [e1] at h1
  simp only [e2] at h2
  rw [tendsto_const_nhds_iff] at h1 h2
  rw [← h1] at h2
  norm_num at h2

theorem not_tendsto_cexp_const_mul_I {d : ℝ} (hd : 0 < d) (r : ℂ) :
    ¬ Tendsto (fun η : ℝ => cexp (((d * η : ℝ) : ℂ) * I)) atTop (𝓝 r) := by
  intro h
  refine not_tendsto_cexp_mul_I r ?_
  have := h.comp (tendsto_id.atTop_div_const hd)
  refine this.congr fun u => ?_
  simp only [Function.comp_apply, id]
  rw [mul_div_cancel₀ _ hd.ne']

theorem ratio_cexp_eq {g : ℝ → ℂ} {η : ℝ} (hg : g η ≠ 0) (t₁ t₂ : ℝ) :
    g η * cexp (t₂ * η * I) / (g η * cexp (t₁ * η * I)) =
      cexp ((((t₂ - t₁) * η : ℝ) : ℂ) * I) := by
  rw [mul_div_mul_left _ _ hg, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- The boundary values `g(η) e^{itη}` converge as `η → +∞` when the tails of
`∫ g e^{itτ}` and `∫ g′ e^{itτ}` are small. -/
theorem tendsto_boundary_of_tail_cauchy {g g' : ℝ → ℂ} (hd : ∀ τ, HasDerivAt g (g' τ) τ)
    (hc : Continuous g') {t : ℝ}
    (hg : ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ →
      ‖∫ τ in η₁..η₂, g τ * cexp (t * τ * I)‖ ≤ ε)
    (hg' : ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ →
      ‖∫ τ in η₁..η₂, g' τ * cexp (t * τ * I)‖ ≤ ε) :
    ∃ ℓ, Tendsto (fun η => g η * cexp (t * η * I)) atTop (𝓝 ℓ) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun τ => (hd τ).continuousAt
  have hder : ∀ τ, HasDerivAt (fun η => g η * cexp (t * η * I))
      (g' τ * cexp (t * τ * I) + g τ * (cexp (t * τ * I) * (t * I))) τ := fun τ =>
    (hd τ).mul (hasDerivAt_cexp_mul_mul_I t τ)
  have hec : Continuous fun τ : ℝ => cexp (t * τ * I) := by fun_prop
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨η₀, hη₀⟩ := hg (ε / (2 * (|t| + 1))) (by positivity)
  obtain ⟨η₀', hη₀'⟩ := hg' (ε / 4) (by positivity)
  have key : ∀ a b, max η₀ η₀' ≤ a → a ≤ b →
      ‖g b * cexp (t * b * I) - g a * cexp (t * a * I)‖ < ε := by
    intro a b ha hab
    have hi1 : IntervalIntegrable (fun τ : ℝ => g' τ * cexp (t * τ * I)) volume a b :=
      (hc.mul hec).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun τ : ℝ => g τ * (cexp (t * τ * I) * (t * I))) volume a b :=
      (hgc.mul (hec.mul continuous_const)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hder τ) (hi1.add hi2),
      intervalIntegral.integral_add hi1 hi2]
    have e : ∫ τ in a..b, g τ * (cexp (t * τ * I) * (t * I)) =
        ((t : ℂ) * I) * ∫ τ in a..b, g τ * cexp (t * τ * I) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun τ _ => by ring
    rw [e]
    have h1 := hη₀' a b ((le_max_right _ _).trans ha) hab
    have h2 := hη₀ a b ((le_max_left _ _).trans ha) hab
    have h3 : |t| * (ε / (2 * (|t| + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg t]
    calc _ ≤ ‖∫ τ in a..b, g' τ * cexp (t * τ * I)‖ +
          ‖((t : ℂ) * I) * ∫ τ in a..b, g τ * cexp (t * τ * I)‖ := norm_add_le _ _
      _ ≤ ε / 4 + |t| * (ε / (2 * (|t| + 1))) := by
          rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          gcongr
      _ < ε := by linarith
  refine ⟨max η₀ η₀', fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  rcases le_total n m with h | h
  · exact key n m hn h
  · rw [← norm_neg, neg_sub]
    exact key m n hm h

/-- If the tails of `∫ g e^{itτ}` and `∫ g′ e^{itτ}` over `[η₁, η₂]` are uniformly small for two
frequencies `t₁ ≠ t₂`, then `g(η) → 0` as `η → +∞`. -/
theorem tendsto_zero_of_tail_cauchy {g g' : ℝ → ℂ} (hd : ∀ τ, HasDerivAt g (g' τ) τ)
    (hc : Continuous g') {t₁ t₂ : ℝ} (hne : t₁ ≠ t₂)
    (hg : ∀ t, t = t₁ ∨ t = t₂ → ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ →
      ‖∫ τ in η₁..η₂, g τ * cexp (t * τ * I)‖ ≤ ε)
    (hg' : ∀ t, t = t₁ ∨ t = t₂ → ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ →
      ‖∫ τ in η₁..η₂, g' τ * cexp (t * τ * I)‖ ≤ ε) :
    Tendsto g atTop (𝓝 0) := by
  obtain ⟨ℓ₁, hℓ₁⟩ := tendsto_boundary_of_tail_cauchy hd hc (hg t₁ (Or.inl rfl))
    (hg' t₁ (Or.inl rfl))
  obtain ⟨ℓ₂, hℓ₂⟩ := tendsto_boundary_of_tail_cauchy hd hc (hg t₂ (Or.inr rfl))
    (hg' t₂ (Or.inr rfl))
  have hn : ∀ (t : ℝ) (ℓ : ℂ), Tendsto (fun η => g η * cexp (t * η * I)) atTop (𝓝 ℓ) →
      Tendsto (fun η => ‖g η‖) atTop (𝓝 ‖ℓ‖) := fun t ℓ h => by
    have := h.norm
    simpa only [norm_mul, norm_cexp_mul_mul_I, mul_one] using this
  have hn1 := hn t₁ ℓ₁ hℓ₁
  have hn2 := hn t₂ ℓ₂ hℓ₂
  by_cases h0 : ℓ₁ = 0
  · rw [h0, norm_zero] at hn1
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hn1
  · exfalso
    have h0' : ℓ₂ ≠ 0 := by
      intro h2
      rw [h2, norm_zero] at hn2
      have := tendsto_nhds_unique hn1 hn2
      exact h0 (norm_eq_zero.mp this)
    have hpos : 0 < ‖ℓ₁‖ := norm_pos_iff.mpr h0
    have hev : ∀ᶠ η in atTop, g η ≠ 0 := by
      filter_upwards [hn1.eventually (eventually_gt_nhds (half_lt_self hpos))] with η hη
      exact norm_pos_iff.mp (lt_trans (by positivity) hη)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hdiv := hℓ₂.div hℓ₁ h0
      refine not_tendsto_cexp_const_mul_I (sub_pos.mpr hlt) (ℓ₂ / ℓ₁) (hdiv.congr' ?_)
      filter_upwards [hev] with η hη
      exact ratio_cexp_eq hη t₁ t₂
    · have hdiv := hℓ₁.div hℓ₂ h0'
      refine not_tendsto_cexp_const_mul_I (sub_pos.mpr hlt) (ℓ₁ / ℓ₂) (hdiv.congr' ?_)
      filter_upwards [hev] with η hη
      exact ratio_cexp_eq hη t₂ t₁

/-- The same as `η → −∞`, from the tails over `[−η₂, −η₁]`. -/
theorem tendsto_zero_atBot_of_tail_cauchy {g g' : ℝ → ℂ} (hd : ∀ τ, HasDerivAt g (g' τ) τ)
    (hc : Continuous g') {t₁ t₂ : ℝ} (hne : t₁ ≠ t₂)
    (hg : ∀ t, t = t₁ ∨ t = t₂ → ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ →
      ‖∫ τ in (-η₂)..(-η₁), g τ * cexp (t * τ * I)‖ ≤ ε)
    (hg' : ∀ t, t = t₁ ∨ t = t₂ → ∀ ε > 0, ∃ η₀, ∀ η₁ η₂, η₀ ≤ η₁ → η₁ ≤ η₂ →
      ‖∫ τ in (-η₂)..(-η₁), g' τ * cexp (t * τ * I)‖ ≤ ε) :
    Tendsto g atBot (𝓝 0) := by
  have hflip : ∀ (h : ℝ → ℂ) (t a b : ℝ), ∫ τ in a..b, h (-τ) * cexp ((-t : ℝ) * τ * I) =
      ∫ τ in (-b)..(-a), h τ * cexp (t * τ * I) := by
    intro h t a b
    rw [← intervalIntegral.integral_comp_neg]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    push_cast
    ring_nf
  have hd' : ∀ τ, HasDerivAt (fun τ => g (-τ)) (-g' (-τ)) τ := fun τ => by
    have := (hd (-τ)).scomp τ (hasDerivAt_neg τ)
    have e : (g ∘ Neg.neg : ℝ → ℂ) = fun τ => g (-τ) := rfl
    rw [e] at this
    simpa using this
  have hc' : Continuous fun τ => -g' (-τ) := (hc.comp continuous_neg).neg
  have := tendsto_zero_of_tail_cauchy hd' hc' (t₁ := -t₁) (t₂ := -t₂) (neg_inj.not.mpr hne)
    (fun t ht ε hε => ?_) (fun t ht ε hε => ?_)
  · have h2 := this.comp tendsto_neg_atBot_atTop
    refine h2.congr fun τ => ?_
    simp
  · obtain ⟨η₀, hη₀⟩ := hg (-t) (by rcases ht with rfl | rfl <;> simp) ε hε
    refine ⟨η₀, fun η₁ η₂ h1 h2 => ?_⟩
    have := hη₀ η₁ η₂ h1 h2
    rwa [← hflip g (-t), neg_neg] at this
  · obtain ⟨η₀, hη₀⟩ := hg' (-t) (by rcases ht with rfl | rfl <;> simp) ε hε
    refine ⟨η₀, fun η₁ η₂ h1 h2 => ?_⟩
    have := hη₀ η₁ η₂ h1 h2
    rw [← hflip g' (-t), neg_neg] at this
    have e : ∫ τ in η₁..η₂, -g' (-τ) * cexp (t * τ * I) =
        -∫ τ in η₁..η₂, g' (-τ) * cexp (t * τ * I) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun τ _ => by ring
    rwa [e, norm_neg]

/-! ### Integration by parts and 2.4.9 -/

/-- One integration by parts: `lim ∫ g e^{itτ} = (i/t) lim ∫ g′ e^{itτ}` for `t ≥ T > 0`, the
boundary terms vanishing by the decay above. -/
theorem fourierLim_ibp {g g' : ℝ → ℂ} (hd : ∀ τ, HasDerivAt g (g' τ) τ) (hc : Continuous g')
    {T : ℝ} (hT : 0 < T) (hU : UnifConvTails T g) (hU' : UnifConvTails T g') {t : ℝ}
    (ht : T ≤ t) : fourierLim g t = (I / t) * fourierLim g' t := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun τ => (hd τ).continuousAt
  have ht0 : 0 < t := hT.trans_le ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have hec : Continuous fun τ : ℝ => cexp (t * τ * I) := by fun_prop
  have hmem : ∀ s : ℝ, s = t ∨ s = t + 1 → T ≤ s := fun s hs => by
    rcases hs with rfl | rfl <;> linarith
  have hdec : Tendsto g atTop (𝓝 0) :=
    tendsto_zero_of_tail_cauchy hd hc (t₁ := t) (t₂ := t + 1) (by linarith)
      (fun s hs ε hε => by
        obtain ⟨η₀, hη₀⟩ := hU ε hε
        exact ⟨η₀, fun η₁ η₂ h1 h2 => (hη₀ η₁ η₂ h1 h2 s (hmem s hs)).1⟩)
      (fun s hs ε hε => by
        obtain ⟨η₀, hη₀⟩ := hU' ε hε
        exact ⟨η₀, fun η₁ η₂ h1 h2 => (hη₀ η₁ η₂ h1 h2 s (hmem s hs)).1⟩)
  have hdecb : Tendsto g atBot (𝓝 0) :=
    tendsto_zero_atBot_of_tail_cauchy hd hc (t₁ := t) (t₂ := t + 1) (by linarith)
      (fun s hs ε hε => by
        obtain ⟨η₀, hη₀⟩ := hU ε hε
        exact ⟨η₀, fun η₁ η₂ h1 h2 => (hη₀ η₁ η₂ h1 h2 s (hmem s hs)).2⟩)
      (fun s hs ε hε => by
        obtain ⟨η₀, hη₀⟩ := hU' ε hε
        exact ⟨η₀, fun η₁ η₂ h1 h2 => (hη₀ η₁ η₂ h1 h2 s (hmem s hs)).2⟩)
  have hv : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => cexp (t * τ * I) / (t * I)) (cexp (t * τ * I)) τ :=
    fun τ => by
      have h := (hasDerivAt_cexp_mul_mul_I t τ).div_const ((t : ℂ) * I)
      convert h using 1
      field_simp
  have hibp : ∀ η, fourierPartial g t η =
      (g η * cexp (t * η * I) - g (-η) * cexp (t * (-η : ℝ) * I)) / (t * I) -
        (1 / ((t : ℂ) * I)) * fourierPartial g' t η := by
    intro η
    unfold fourierPartial
    have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -η) (b := η)
      (fun τ _ => hd τ) (fun τ _ => hv τ) (hc.intervalIntegrable _ _) (hec.intervalIntegrable _ _)
    rw [key]
    have e : ∫ τ in (-η)..η, g' τ * (cexp (t * τ * I) / (t * I)) =
        (1 / ((t : ℂ) * I)) * ∫ τ in (-η)..η, g' τ * cexp (t * τ * I) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun τ _ => by ring
    rw [e]
    ring
  have hlimg := fourierLim_exists hgc hU ht
  have hlimg' := fourierLim_exists hc hU' ht
  have h1 : Tendsto (fun η => g η * cexp (t * η * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_mul, norm_cexp_mul_mul_I, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp hdec
  have h2 : Tendsto (fun η => g (-η) * cexp (t * (-η : ℝ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_mul, norm_cexp_mul_mul_I, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (hdecb.comp tendsto_neg_atTop_atBot)
  have hB := (h1.sub h2).div_const ((t : ℂ) * I)
  rw [sub_zero, zero_div] at hB
  have h3 := (hB.sub (hlimg'.const_mul (1 / ((t : ℂ) * I)))).congr fun η => (hibp η).symm
  rw [zero_sub] at h3
  have huniq := tendsto_nhds_unique hlimg h3
  rw [huniq, one_div, mul_inv, Complex.inv_I]
  ring

/-- Repeated integration by parts: for a chain `D₀, D₁ = D₀′, …, Dₘ` with uniformly convergent
integrals, `lim ∫ D₀ e^{itτ} = (i/t)^m lim ∫ Dₘ e^{itτ}` for `t ≥ T > 0`. -/
theorem fourierLim_ibp_iter {D : ℕ → ℝ → ℂ} {T : ℝ} (hT : 0 < T) (m : ℕ)
    (hd : ∀ j < m, ∀ τ, HasDerivAt (D j) (D (j + 1) τ) τ) (hc : ∀ j ≤ m, Continuous (D j))
    (hU : ∀ j ≤ m, UnifConvTails T (D j)) {t : ℝ} (ht : T ≤ t) :
    fourierLim (D 0) t = (I / t) ^ m * fourierLim (D m) t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih (fun j hj => hd j (by omega)) (fun j hj => hc j (by omega))
        (fun j hj => hU j (by omega)),
      fourierLim_ibp (hd m (by omega)) (hc (m + 1) le_rfl) hT (hU m (by omega))
        (hU (m + 1) le_rfl) ht]
    ring

/-- For `H` analytic in `ℜz > c₀`, the derivatives of `τ ↦ H(c + iτ)` are
`i^j H^{(j)}(c + iτ)`. -/
theorem iteratedDeriv_comp_line {H : ℂ → ℂ} {c₀ c : ℝ}
    (hH : DifferentiableOn ℂ H {z | c₀ < z.re}) (hc : c₀ < c) (j : ℕ) :
    iteratedDeriv j (fun τ : ℝ => H (c + τ * I)) =
      fun τ : ℝ => I ^ j * iteratedDeriv j H (c + τ * I) := by
  have hU : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const continuous_re
  have hA : AnalyticOnNhd ℂ H {z | c₀ < z.re} := hH.analyticOnNhd hU
  induction j with
  | zero =>
    funext τ
    simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext τ
    have hj : AnalyticOnNhd ℂ (iteratedDeriv j H) {z | c₀ < z.re} := by
      rw [iteratedDeriv_eq_iterate]
      exact hA.iterated_deriv j
    have h1 : HasDerivAt (iteratedDeriv j H) (deriv (iteratedDeriv j H) (c + τ * I))
        ((c : ℂ) + τ * I) :=
      (hj.differentiableOn.differentiableAt (hU.mem_nhds (mem_halfPlane_line hc τ))).hasDerivAt
    have h2 : HasDerivAt (fun τ : ℝ => I ^ j * iteratedDeriv j H (c + τ * I))
        (I ^ j * (deriv (iteratedDeriv j H) (c + τ * I) * I)) τ :=
      (h1.comp τ (hasDerivAt_line c τ)).const_mul (I ^ j)
    rw [h2.deriv, iteratedDeriv_succ]
    ring

/-- **DLMF 2.4.9**: if the integrals `∫ e^{itτ} (Q − F)^{(j)}(c + iτ) dτ`, `j ≤ m`, all converge
uniformly at each limit for `t ≥ T > 0`, then `q(t) = f(t) + o(t^{−m} e^{ct})` as `t → +∞`.
`Q` and `F` are analytic in `ℜz > c₀`, `c₀ < c`. -/
theorem dlmf_2_4_9 {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {c₀ c T : ℝ} {m : ℕ} (hc : c₀ < c) (hT : 0 < T)
    (hQd : DifferentiableOn ℂ Q {z | c₀ < z.re}) (hFd : DifferentiableOn ℂ F {z | c₀ < z.re})
    (hq : ∀ t, T ≤ t → Tendsto (bromwichPartial Q c t) atTop (𝓝 (q t)))
    (hf : ∀ t, T ≤ t → Tendsto (bromwichPartial F c t) atTop (𝓝 (f t)))
    (hU : ∀ j ≤ m, UnifConvTails T fun τ => iteratedDeriv j (fun z => Q z - F z) (c + τ * I)) :
    IsLittleODLMF atTop (fun t => q t - f t)
      (fun t => ((Real.exp (c * t) / t ^ m : ℝ) : ℂ)) := by
  have hU0 : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const continuous_re
  set H : ℂ → ℂ := fun z => Q z - F z with hHdef
  have hHd : DifferentiableOn ℂ H {z | c₀ < z.re} := hQd.sub hFd
  have hHA : AnalyticOnNhd ℂ H {z | c₀ < z.re} := hHd.analyticOnNhd hU0
  have hQc : Continuous fun τ : ℝ => Q (c + τ * I) :=
    continuous_line_comp hQd.continuousOn fun τ => mem_halfPlane_line hc τ
  have hFc : Continuous fun τ : ℝ => F (c + τ * I) :=
    continuous_line_comp hFd.continuousOn fun τ => mem_halfPlane_line hc τ
  set D : ℕ → ℝ → ℂ := fun j τ => I ^ j * iteratedDeriv j H (c + τ * I) with hDdef
  have hDj : ∀ j, AnalyticOnNhd ℂ (iteratedDeriv j H) {z | c₀ < z.re} := fun j => by
    rw [iteratedDeriv_eq_iterate]
    exact hHA.iterated_deriv j
  have hd : ∀ j < m, ∀ τ, HasDerivAt (D j) (D (j + 1) τ) τ := fun j _ τ => by
    have h1 : HasDerivAt (iteratedDeriv j H) (deriv (iteratedDeriv j H) (c + τ * I))
        ((c : ℂ) + τ * I) :=
      ((hDj j).differentiableOn.differentiableAt
        (hU0.mem_nhds (mem_halfPlane_line hc τ))).hasDerivAt
    have h2 : HasDerivAt (fun τ : ℝ => I ^ j * iteratedDeriv j H (c + τ * I))
        (I ^ j * (deriv (iteratedDeriv j H) (c + τ * I) * I)) τ :=
      (h1.comp τ (hasDerivAt_line c τ)).const_mul (I ^ j)
    refine h2.congr_deriv ?_
    simp only [hDdef, iteratedDeriv_succ]
    ring
  have hcont : ∀ j ≤ m, Continuous (D j) := fun j _ =>
    continuous_const.mul (continuous_line_comp (hDj j).continuousOn fun τ =>
      mem_halfPlane_line hc τ)
  have hUD : ∀ j ≤ m, UnifConvTails T (D j) := fun j hj =>
    (hU j hj).const_mul (by rw [norm_pow, Complex.norm_I, one_pow])
  have hD0 : D 0 = fun τ : ℝ => Q (c + τ * I) - F (c + τ * I) := by
    funext τ
    simp [hDdef, hHdef]
  have hiter := fun t (ht : T ≤ t) => fourierLim_ibp_iter hT m hd hcont hUD ht
  have hlim := (tendsto_fourierLim_zero (hcont m le_rfl) (hUD m le_rfl)).const_mul
    ((2 * Real.pi : ℂ)⁻¹ * I ^ m)
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop T, eventually_gt_atTop 0] with t ht ht0
  obtain ⟨-, h7⟩ := dlmf_2_4_7 hQc hFc (hq t ht) (hf t ht)
  rw [h7, ← hD0, hiter t ht]
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact ofReal_ne_zero.mpr (by positivity)
  have he : (Real.exp (c * t) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  push_cast
  field_simp
  rw [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero m htc)]
  ring

end Azurite.DLMF
