/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4Inverse
import Azurite.DLMF.Chapter2.Section4LaplaceUnif
import Azurite.DLMF.Chapter2.Section4LaplaceDeform
import Azurite.DLMF.Chapter2.Section4WatsonRotation

/-!
# DLMF §2.4(iii): Laplace's method for contour integrals (2.4.10–2.4.13)

`I(z) = ∫_𝒫 e^{−zp(t)} q(t) dt` (2.4.10) for a `C¹` path `t = γ(u)`, `u ∈ (0, B)`, from
`a = γ(0)` with slope angle `ω` at `a` (`γ′(0) = |γ′(0)| e^{iω}`). The hypotheses of DLMF are
collected in `LaplaceContour`:

* (a) near `a`, `p(t) = p(a) + (t − a)^μ P(t)` and `q(t) = (t − a)^{λ−1} Q(t)` with `P`, `Q`
  analytic, `P(a) = p₀ = |p₀| e^{iφ₀} ≠ 0`, `ℜλ > 0`, `μ > 0`, the powers having
  `ph(t − a) → ω` (`brPow ω`); these hold on a sector `|ph(t − a) − ω| < α` around the path.
* (b) `z` ranges over `θ₁ ≤ ph z ≤ θ₂`, `θ₂ − θ₁ < π`, `|z| ≥ Z`; `I(z)` converges at `b`
  absolutely and uniformly in `z` (integrability, and uniformly small tails).
* (c) `ℜ(e^{iθ}(p(t) − p(a))) > 0` on `𝒫 ∖ {a}`, bounded away from `0` as `t → b`, uniformly
  in `θ`.
* 2.4.13, `|θ + μω + ph p₀| ≤ π/2`, is assumed with strict inequality (see the errata: with
  equality the integral near `a` is of Fourier type and condition (c) gives no decay).

**Theorem** (`dlmf_2_4_12`): `e^{zp(a)} I(z) ∼ ∑ Γ((s+λ)/μ) bₛ z^{−(s+λ)/μ}` as `z → ∞` in the
sector, with principal powers and `bₛ = gₛ/μ`, `gₛ` the Taylor coefficients at `w = 0` of
`laplaceG` = `q(t) dt/dw · w^{1−λ}` (the coefficients of 2.3.16, "determined as in §2.3(iii)").

**Proof.** The path near `a` is mapped by `w = (t − a)P(t)^{1/μ}` into a thin sector around
`ω' = ω + φ₀/μ`, where the integrand is `e^{−zw^μ} w^{λ−1} laplaceG(w) dw`; this is moved onto
the ray `ph w = ω'` (`deform_to_ray`), where it is a Laplace transform in `v = w^μ`, and Watson's
lemma 2.4.1 applies with the parameter `z e^{iμω'}`, `|ph(z e^{iμω'})| ≤ π/2 − δ`. The arc
joining the ray to the path and the rest of the path are `O(e^{−c|z|})` by (b), (c).
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-- The contour integral 2.4.10 along `t = γ(u)`, `0 < u < B`. -/
noncomputable def laplaceContour (p q : ℂ → ℂ) (γ γ' : ℝ → ℂ) (B : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioo 0 B, cexp (-(z * p (γ u))) * q (γ u) * γ' u

/-- The hypotheses of DLMF §2.4(iii) (see the module docstring). -/
structure LaplaceContour (p q : ℂ → ℂ) (γ γ' : ℝ → ℂ) (B : ℝ) (a : ℂ) (ω : ℝ) (T : Set ℂ)
    (P Q : ℂ → ℂ) (lam : ℂ) (μ φ₀ ρ α : ℝ) (θ₁ θ₂ Z : ℝ) : Prop where
  B_pos : 0 < B
  γ_zero : γ 0 = a
  γ_deriv : ∀ u ∈ Ico 0 B, HasDerivAt γ (γ' u) u
  γ'_cont : ContinuousOn γ' (Ioo 0 B)
  γ'_ne : γ' 0 ≠ 0
  γ'_dir : γ' 0 = (‖γ' 0‖ : ℂ) * cexp (ω * I)
  T_open : IsOpen T
  γ_mem : ∀ u ∈ Ioo 0 B, γ u ∈ T
  p_diff : DifferentiableOn ℂ p T
  q_diff : DifferentiableOn ℂ q T
  -- (a)
  uset : UnifSetup a φ₀ μ ρ P
  lam_re : 0 < lam.re
  Q_diff : DifferentiableOn ℂ Q (Metric.ball a ρ)
  α_pos : 0 < α
  α_le : α ≤ Real.pi / 2
  p_eq : ∀ t, t - a ∈ sectorBr ω α → ‖t - a‖ < ρ → p t = p a + brPow ω μ (t - a) * P t
  q_eq : ∀ t, t - a ∈ sectorBr ω α → ‖t - a‖ < ρ → q t = brPow ω (lam - 1) (t - a) * Q t
  -- (b)
  θ_lt : θ₂ - θ₁ < Real.pi
  θ₁_gt : -Real.pi < θ₁
  θ₂_le : θ₂ ≤ Real.pi
  θ_le : θ₁ ≤ θ₂
  Z_pos : 0 < Z
  integrable : ∀ z : ℂ, θ₁ ≤ arg z → arg z ≤ θ₂ → Z ≤ ‖z‖ →
    IntegrableOn (fun u => cexp (-(z * p (γ u))) * q (γ u) * γ' u) (Ioo 0 B)
  unif_tail : ∀ ε > 0, ∃ U ∈ Ioo 0 B, ∀ z : ℂ, θ₁ ≤ arg z → arg z ≤ θ₂ → Z ≤ ‖z‖ →
    ∫ u in Ioo U B, ‖cexp (-(z * p (γ u))) * q (γ u) * γ' u‖ ≤ ε
  -- (c)
  re_pos : ∀ θ ∈ Icc θ₁ θ₂, ∀ u ∈ Ioo 0 B, 0 < (cexp (θ * I) * (p (γ u) - p a)).re
  re_tail : ∃ c > 0, ∃ U ∈ Ioo 0 B, ∀ θ ∈ Icc θ₁ θ₂, ∀ u ∈ Ioo U B,
    c ≤ (cexp (θ * I) * (p (γ u) - p a)).re
  -- 2.4.13 (strict)
  branch₁ : |θ₁ + μ * ω + φ₀| < Real.pi / 2
  branch₂ : |θ₂ + μ * ω + φ₀| < Real.pi / 2

/-- The coefficients `bₛ = gₛ/μ` of 2.4.12: `gₛ` are the Taylor coefficients of `laplaceG` at
`w = 0`. -/
noncomputable def laplaceCoeff {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P)
    (lam : ℂ) (Q : ℂ → ℂ) (s : ℕ) : ℂ :=
  ((1 / μ : ℝ) : ℂ) * (iteratedDeriv s (laplaceG h lam Q) 0 / (s.factorial : ℂ))

/-! ### Two general facts on expansions -/

/-- Adding a term that is `O(φₙ)` for every `n` does not change a generalized expansion. -/
theorem IsGenAsympExpansionDLMF.add_isBigO {α : Type*} {l : Filter α} {φ : ℕ → α → ℂ}
    {f E : α → ℂ} {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs)
    (hE : ∀ n, IsBigODLMF l E (φ n)) :
    IsGenAsympExpansionDLMF l φ (fun x => f x + E x) fs := by
  refine ⟨h.1, fun n => ?_⟩
  obtain ⟨K, hK⟩ := h.2 n
  obtain ⟨K', hK'⟩ := hE n
  refine ⟨K + K', ?_⟩
  rw [eventually_map] at hK hK' ⊢
  filter_upwards [hK, hK'] with x h1 h2
  calc ‖(f x + E x - ∑ s ∈ Finset.range n, fs s x) / φ n x‖
      = ‖(f x - ∑ s ∈ Finset.range n, fs s x) / φ n x + E x / φ n x‖ := by
        rw [← add_div]
        ring_nf
    _ ≤ ‖(f x - ∑ s ∈ Finset.range n, fs s x) / φ n x‖ + ‖E x / φ n x‖ := norm_add_le _ _
    _ ≤ K + K' := add_le_add h1 h2

/-- A generalized expansion is preserved by multiplying `f`, the terms and the scale by a
nonvanishing function. -/
theorem IsGenAsympExpansionDLMF.mul_fun {α : Type*} {l : Filter α} {φ : ℕ → α → ℂ}
    {f : α → ℂ} {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs) {g : α → ℂ}
    (hg : ∀ᶠ x in l, g x ≠ 0) :
    IsGenAsympExpansionDLMF l (fun s x => g x * φ s x) (fun x => g x * f x)
      (fun s x => g x * fs s x) := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · refine (h.1 s).congr' ?_
    filter_upwards [hg] with x hx
    rw [mul_div_mul_left _ _ hx]
  · obtain ⟨K, hK⟩ := h.2 n
    refine ⟨K, ?_⟩
    rw [eventually_map] at hK ⊢
    filter_upwards [hK, hg] with x h1 hx
    rw [← Finset.mul_sum, ← mul_sub, mul_div_mul_left _ _ hx]
    exact h1

/-! ### Angles -/

theorem abs_le_max_of_mem_Icc {θ θ₁ θ₂ c : ℝ} (hθ : θ ∈ Icc θ₁ θ₂) :
    |θ + c| ≤ max |θ₁ + c| |θ₂ + c| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (θ₁ + c), le_max_left |θ₁ + c| |θ₂ + c|, hθ.1]
  · linarith [le_abs_self (θ₂ + c), le_max_right |θ₁ + c| |θ₂ + c|, hθ.2]


namespace LaplaceContour

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {B : ℝ} {a : ℂ} {ω : ℝ} {T : Set ℂ} {P Q : ℂ → ℂ}
  {lam : ℂ} {μ φ₀ ρ α θ₁ θ₂ Z : ℝ}

theorem μ_pos (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) : 0 < μ :=
  h.uset.μ_pos

theorem analyticAt_Q (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) :
    AnalyticAt ℂ Q a :=
  h.Q_diff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self h.uset.ρ_pos))

theorem continuousAt_γ (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) {u : ℝ}
    (hu : u ∈ Ico 0 B) : ContinuousAt γ u := (h.γ_deriv u hu).continuousAt

/-- The direction of the path at `a`: `ph(γ(u) − a) → ω` as `u → 0+`, so that `γ(u) − a` is in
the sector `|ph − ω| < α₀` for small `u`. -/
theorem eventually_mem_sectorBr (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z)
    {α₀ : ℝ} (hα₀ : 0 < α₀) : ∀ᶠ u in 𝓝[>] 0, γ u - a ∈ sectorBr ω α₀ := by
  have hd : HasDerivAt γ (γ' 0) 0 := h.γ_deriv 0 ⟨by linarith, h.B_pos⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hd
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ fun t (ht : t ∈ Ioi 0) => ne_of_gt ht
  have h1 : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) * ((γ t - a) * cexp (-(ω * I)))) (𝓝[>] 0)
      (𝓝 (‖γ' 0‖ : ℂ)) := by
    have h2 := (hslope.mono_left hle).mul_const (cexp (-(ω * I)))
    have e : γ' 0 * cexp (-(ω * I)) = (‖γ' 0‖ : ℂ) := by
      conv_lhs => rw [h.γ'_dir]
      rw [mul_assoc, mul_comm (cexp (ω * I)), exp_neg_mul_I_mul_exp, mul_one]
    rw [e] at h2
    refine h2.congr' (Eventually.of_forall fun t => ?_)
    simp only [zero_add, h.γ_zero, Complex.real_smul]
    ring
  have hslit : ((‖γ' 0‖ : ℝ) : ℂ) ∈ slitPlane :=
    mem_slitPlane_of_re_pos' (by simpa using norm_pos_iff.mpr h.γ'_ne)
  have harg : Tendsto (fun t : ℝ => arg (((t⁻¹ : ℝ) : ℂ) * ((γ t - a) * cexp (-(ω * I)))))
      (𝓝[>] 0) (𝓝 0) := by
    have := (continuousAt_arg hslit).tendsto.comp h1
    rwa [arg_ofReal_of_nonneg (norm_nonneg _)] at this
  have hne := h1.eventually_ne (ofReal_ne_zero.mpr (norm_pos_iff.mpr h.γ'_ne).ne')
  filter_upwards [harg.eventually (Metric.ball_mem_nhds 0 hα₀), hne, self_mem_nhdsWithin]
    with t ht hne' ht0
  have ht0 : (0 : ℝ) < t := ht0
  rw [Complex.arg_real_mul _ (inv_pos.mpr ht0)] at ht
  rw [mem_sectorBr_iff]
  refine ⟨fun h0 => hne' (by rw [h0, zero_mul, mul_zero]), ?_⟩
  simpa [Real.dist_eq] using ht

/-- The local data near `a`: a parameter range `(0, u₁]`, a radius `δ₀` and a sector half-angle
`α'` in the `w`-plane, with the branch identities for `p`, `q` along the path, the uniformized
path `σ = w ∘ γ` and its derivative, and a bound on `laplaceG`. -/
theorem exists_local (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) :
    ∃ (u₁ δ₀ α' δ' M : ℝ), 0 < u₁ ∧ u₁ < B ∧ 0 < δ₀ ∧ 0 < α' ∧ α' ≤ Real.pi / 4 ∧ 0 < δ' ∧
      (∀ θ ∈ Icc θ₁ θ₂, ∀ ψ : ℝ, |ψ - (ω + φ₀ / μ)| < α' → |θ + μ * ψ| ≤ Real.pi / 2 - δ') ∧
      DifferentiableOn ℂ (laplaceG h.uset lam Q) (Metric.ball 0 δ₀) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖laplaceG h.uset lam Q w‖ ≤ M) ∧
      (∀ u ∈ Ioc 0 u₁, unif a φ₀ μ P (γ u) ∈ sectorDisc (ω + φ₀ / μ) α' δ₀) ∧
      (∀ u ∈ Ioc 0 u₁, p (γ u) - p a = brPow (ω + φ₀ / μ) μ (unif a φ₀ μ P (γ u))) ∧
      (∀ u ∈ Ioc 0 u₁, q (γ u) * γ' u = brPow (ω + φ₀ / μ) (lam - 1) (unif a φ₀ μ P (γ u)) *
        laplaceG h.uset lam Q (unif a φ₀ μ P (γ u)) * (deriv (unif a φ₀ μ P) (γ u) * γ' u)) ∧
      (∀ u ∈ Ioc 0 u₁, HasDerivAt (fun u => unif a φ₀ μ P (γ u))
        (deriv (unif a φ₀ μ P) (γ u) * γ' u) u) ∧
      Tendsto (fun u => unif a φ₀ μ P (γ u)) (𝓝[>] 0) (𝓝 0) := by
  have hμ := h.μ_pos
  have hπ := Real.pi_pos
  set ω' := ω + φ₀ / μ with hω'
  have hμω' : μ * ω' = μ * ω + φ₀ := by rw [hω']; field_simp
  -- the angular slack `δ'`
  set m := max |θ₁ + (μ * ω + φ₀)| |θ₂ + (μ * ω + φ₀)| with hm
  have hm_lt : m < Real.pi / 2 :=
    max_lt (by rw [← add_assoc]; exact h.branch₁) (by rw [← add_assoc]; exact h.branch₂)
  set δ' := (Real.pi / 2 - m) / 2 with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  set α' := min (δ' / (2 * μ)) (Real.pi / 4) with hα'
  have hα'0 : 0 < α' := lt_min (by positivity) (by positivity)
  have hα'1 : α' ≤ δ' / (2 * μ) := min_le_left _ _
  have hα'2 : α' ≤ Real.pi / 4 := min_le_right _ _
  have hμα' : μ * α' ≤ δ' / 2 := by
    calc μ * α' ≤ μ * (δ' / (2 * μ)) := by gcongr
      _ = δ' / 2 := by field_simp
  have hangle : ∀ θ ∈ Icc θ₁ θ₂, ∀ ψ : ℝ, |ψ - ω'| < α' → |θ + μ * ψ| ≤ Real.pi / 2 - δ' := by
    intro θ hθ ψ hψ
    have h1 := abs_le_max_of_mem_Icc (c := μ * ω + φ₀) hθ
    have h2 : |μ * (ψ - ω')| < δ' / 2 := by
      rw [abs_mul, abs_of_pos hμ]
      calc μ * |ψ - ω'| < μ * α' := by gcongr
        _ ≤ δ' / 2 := hμα'
    have e : θ + μ * ψ = (θ + (μ * ω + φ₀)) + μ * (ψ - ω') := by rw [mul_sub, hμω']; ring
    rw [e]
    calc |(θ + (μ * ω + φ₀)) + μ * (ψ - ω')| ≤ |θ + (μ * ω + φ₀)| + |μ * (ψ - ω')| :=
          abs_add_le _ _
      _ ≤ m + δ' / 2 := add_le_add h1 h2.le
      _ ≤ Real.pi / 2 - δ' := by rw [hδ']; linarith
  -- the sector in the `t`-plane and the tolerance `β` for `Im LogP`
  set α₀ := min α (α' / 2) with hα₀
  have hα₀0 : 0 < α₀ := lt_min h.α_pos (by positivity)
  have hα₀α : α₀ ≤ α := min_le_left _ _
  set β := μ * α' / 2 with hβ
  have hβ0 : 0 < β := by positivity
  have hαβ : α₀ + β / μ ≤ α' := by
    have : β / μ = α' / 2 := by rw [hβ]; field_simp
    rw [this]
    linarith [min_le_right α (α' / 2)]
  have hαβπ : α₀ + β / μ ≤ Real.pi := by linarith
  obtain ⟨ε, hε, hερ, hball⟩ := h.uset.exists_eps hβ0
  -- `laplaceG` on a disc
  have hGa : AnalyticAt ℂ (laplaceG h.uset lam Q) 0 := h.uset.analyticAt_laplaceG lam h.analyticAt_Q
  obtain ⟨δ₁, hδ₁, hGan⟩ := Metric.eventually_nhds_iff.mp hGa.eventually_analyticAt
  have hGd : DifferentiableOn ℂ (laplaceG h.uset lam Q) (Metric.ball 0 δ₁) := fun w hw =>
    (hGan (by simpa [Metric.mem_ball] using hw)).differentiableAt.differentiableWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (δ₁ / 2)).exists_bound_of_continuousOn
    (hGd.continuousOn.mono (Metric.closedBall_subset_ball (by linarith)))
  -- the local inverse identities
  obtain ⟨δ₂, hδ₂, hright⟩ := Metric.eventually_nhds_iff.mp
    (h.uset.eventually_unif_unifInv.and h.uset.eventually_deriv_unifInv)
  obtain ⟨ε₂, hε₂, hleft⟩ := Metric.eventually_nhds_iff.mp h.uset.eventually_unifInv_unif
  set δ₀ := min (δ₁ / 2) δ₂ with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by positivity) hδ₂
  -- analyticity of `unif` near `a`
  have hunif : ∀ t ∈ Metric.ball a ε, AnalyticAt ℂ (unif a φ₀ μ P) t := fun t ht =>
    h.uset.analyticAt_unif hερ (fun t ht => (hball t ht).1) ht
  -- the parameter range `(0, u₁]`
  have hγc : ContinuousAt γ 0 := h.continuousAt_γ ⟨by linarith, h.B_pos⟩
  have hγ0 : Tendsto γ (𝓝[>] 0) (𝓝 a) := by
    have := hγc.tendsto
    rw [h.γ_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hσ0 : Tendsto (fun u => unif a φ₀ μ P (γ u)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (hunif a (Metric.mem_ball_self hε)).continuousAt.tendsto
    rw [UnifSetup.unif_a] at hc
    exact hc.comp hγ0
  have hev : ∀ᶠ u in 𝓝[>] 0, γ u - a ∈ sectorBr ω α₀ ∧ ‖γ u - a‖ < ε ∧ dist (γ u) a < ε₂ ∧
      ‖unif a φ₀ μ P (γ u)‖ < δ₀ ∧ u < B ∧ -1 < u := by
    have e1 := h.eventually_mem_sectorBr hα₀0
    have e2 : ∀ᶠ u in 𝓝[>] 0, ‖γ u - a‖ < ε := by
      have := hγ0.eventually (Metric.ball_mem_nhds a hε)
      filter_upwards [this] with u hu
      simpa [dist_eq_norm] using hu
    have e3 : ∀ᶠ u in 𝓝[>] 0, dist (γ u) a < ε₂ := hγ0.eventually (Metric.ball_mem_nhds a hε₂)
    have e4 : ∀ᶠ u in 𝓝[>] 0, ‖unif a φ₀ μ P (γ u)‖ < δ₀ := by
      have := hσ0.eventually (Metric.ball_mem_nhds 0 hδ₀0)
      filter_upwards [this] with u hu
      simpa using hu
    have e5 : ∀ᶠ u in 𝓝[>] 0, u < B ∧ -1 < u := by
      filter_upwards [Ioo_mem_nhdsGT h.B_pos] with u hu
      exact ⟨hu.2, by linarith [hu.1]⟩
    filter_upwards [e1, e2, e3, e4, e5] with u h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5.1, h5.2⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hηu⟩ := hev
  set u₁ := min (η / 2) (B / 2) with hu₁def
  have hu₁0 : 0 < u₁ := lt_min (by positivity) (by linarith [h.B_pos])
  have hu₁B : u₁ < B := lt_of_le_of_lt (min_le_right _ _) (by linarith [h.B_pos])
  have hloc : ∀ u ∈ Ioc 0 u₁, γ u - a ∈ sectorBr ω α₀ ∧ ‖γ u - a‖ < ε ∧ dist (γ u) a < ε₂ ∧
      ‖unif a φ₀ μ P (γ u)‖ < δ₀ ∧ u < B ∧ -1 < u := fun u hu =>
    hηu (by rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]
            linarith [hu.2, min_le_left (η / 2) (B / 2)]) hu.1
  have hδ₀1 : δ₀ ≤ δ₁ / 2 := min_le_left _ _
  refine ⟨u₁, δ₀, α', δ', M, hu₁0, hu₁B, hδ₀0, hα'0, hα'2, hδ'0, hangle,
    hGd.mono (Metric.ball_subset_ball (by linarith)),
    fun w hw => hM w (Metric.ball_subset_closedBall (Metric.ball_subset_ball hδ₀1 hw)),
    ?_, ?_, ?_, ?_, hσ0⟩
  · intro u hu
    obtain ⟨hsec, hε', -, hδ, -, -⟩ := hloc u hu
    have hb := hball (γ u) (by simpa [Metric.mem_ball, dist_eq_norm] using hε')
    exact ⟨sectorBr_mono hαβ (h.uset.unif_mem_sectorBr hαβπ hsec hb.2.1), hδ⟩
  · intro u hu
    obtain ⟨hsec, hε', -, -, -, -⟩ := hloc u hu
    have hb := hball (γ u) (by simpa [Metric.mem_ball, dist_eq_norm] using hε')
    rw [h.p_eq (γ u) (sectorBr_mono hα₀α hsec) (hε'.trans_le hερ),
      h.uset.brPow_unif_mu hαβπ hsec hb.2.1 hb.2.2]
    ring
  · intro u hu
    obtain ⟨hsec, hε', hε₂', hδ, -, -⟩ := hloc u hu
    have hb := hball (γ u) (by simpa [Metric.mem_ball, dist_eq_norm] using hε')
    have hL := hleft hε₂'
    have hw : dist (unif a φ₀ μ P (γ u)) 0 < δ₂ := by
      rw [dist_zero_right]
      exact hδ.trans_le (min_le_right _ _)
    obtain ⟨-, hR2⟩ := hright hw
    rw [hL] at hR2
    rw [h.q_eq (γ u) (sectorBr_mono hα₀α hsec) (hε'.trans_le hερ),
      h.uset.brPow_unif hαβπ hsec hb.2.1 (lam - 1), laplaceG, hL]
    have e : -((lam - 1) * ((1 / μ : ℝ) : ℂ)) = -((lam - 1) / μ) := by push_cast; ring
    rw [e]
    linear_combination (-(brPow (ω + φ₀ / μ) (lam - 1) (unif a φ₀ μ P (γ u)) *
      cexp (-((lam - 1) / μ) * LogP φ₀ P (γ u)) * Q (γ u) * γ' u)) * hR2
  · intro u hu
    obtain ⟨-, hε', -, -, huB, -⟩ := hloc u hu
    have h1 := (hunif (γ u) (by simpa [Metric.mem_ball, dist_eq_norm] using hε'))
      |>.differentiableAt.hasDerivAt
    exact h1.comp u (h.γ_deriv u ⟨hu.1.le, huB⟩)

end LaplaceContour

/-! ### The integrand in the `w`-plane -/

/-- `e^{−z w^μ} w^{λ−1} G(w)`, with the branches of `ph w` near `ω'`. -/
noncomputable def laplaceF (ω' μ : ℝ) (lam : ℂ) (G : ℂ → ℂ) (z w : ℂ) : ℂ :=
  cexp (-(z * brPow ω' μ w)) * (brPow ω' (lam - 1) w * G w)

/-- `brPow ω' μ w = |w|^μ e^{iμψ}` with `ψ = Im logBr ω' w`. -/
theorem brPow_eq_polar {ω' : ℝ} (μ : ℝ) {w : ℂ} (hw : w ≠ 0) :
    brPow ω' μ w = ((‖w‖ ^ μ : ℝ) : ℂ) * cexp (((μ * (logBr ω' w).im : ℝ) : ℂ) * I) := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set ψ := (logBr ω' w).im with hψ
  have hL : logBr ω' w = (Real.log ‖w‖ : ℂ) + ψ * I := by
    conv_lhs => rw [← re_add_im (logBr ω' w)]
    rw [logBr_re w]
  rw [brPow, hL, mul_add, Complex.exp_add, Real.rpow_def_of_pos hw0, ofReal_exp]
  push_cast
  ring_nf

theorem re_mul_brPow {ω' μ : ℝ} {z w : ℂ} (hw : w ≠ 0) :
    (z * brPow ω' μ w).re = ‖z‖ * ‖w‖ ^ μ * Real.cos (arg z + μ * (logBr ω' w).im) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z, brPow_eq_polar μ hw]
  have e : (‖z‖ : ℂ) * cexp (arg z * I) * (((‖w‖ ^ μ : ℝ) : ℂ) *
      cexp (((μ * (logBr ω' w).im : ℝ) : ℂ) * I)) =
      ((‖z‖ * ‖w‖ ^ μ : ℝ) : ℂ) * cexp (((arg z + μ * (logBr ω' w).im : ℝ) : ℂ) * I) := by
    rw [ofReal_add, add_mul, Complex.exp_add]
    push_cast
    ring
  rw [e, re_ofReal_mul, exp_ofReal_mul_I_re]

theorem norm_cexp_neg_mul_brPow {ω' μ : ℝ} {z w : ℂ} (hw : w ≠ 0) :
    ‖cexp (-(z * brPow ω' μ w))‖ =
      Real.exp (-(‖z‖ * ‖w‖ ^ μ * Real.cos (arg z + μ * (logBr ω' w).im))) := by
  rw [Complex.norm_exp, neg_re, re_mul_brPow hw]

/-- On the sector, `cos(θ + μψ) ≥ sin δ'`, so `|e^{−z w^μ}| ≤ e^{−sin δ' |z| |w|^μ}`. -/
theorem norm_cexp_neg_mul_brPow_le {ω' μ δ' θ₁ θ₂ : ℝ} {α' : ℝ} (hδ' : 0 < δ')
    (hδ'π : δ' ≤ Real.pi / 2)
    (hangle : ∀ θ ∈ Icc θ₁ θ₂, ∀ ψ : ℝ, |ψ - ω'| < α' → |θ + μ * ψ| ≤ Real.pi / 2 - δ')
    {z : ℂ} (hz : θ₁ ≤ arg z ∧ arg z ≤ θ₂) {w : ℂ} (hw : w ∈ sectorBr ω' α') :
    ‖cexp (-(z * brPow ω' μ w))‖ ≤ Real.exp (-(Real.sin δ' * ‖z‖ * ‖w‖ ^ μ)) := by
  rw [norm_cexp_neg_mul_brPow hw.1]
  apply Real.exp_le_exp.mpr
  have hc : Real.sin δ' ≤ Real.cos (arg z + μ * (logBr ω' w).im) := by
    rw [← Real.cos_pi_div_two_sub, ← Real.cos_abs (arg z + _)]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    exact hangle (arg z) hz _ hw.2
  have hpos : 0 ≤ ‖z‖ * ‖w‖ ^ μ := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  nlinarith

theorem norm_brPow_lam {ω' : ℝ} (lam : ℂ) {w : ℂ} (hw : w ≠ 0) :
    ‖brPow ω' (lam - 1) w‖ ≤ ‖w‖ ^ (lam.re - 1) * Real.exp (|lam.im| * (|ω'| + Real.pi)) := by
  have := norm_brPow_le (ω := ω') (lam - 1) hw
  rwa [sub_re, one_re, sub_im, one_im, sub_zero] at this

/-- The bound `|laplaceF z w| ≤ e^{−sin δ' |z||w|^μ} C |w|^{ℜλ−1}` on the sector-disc. -/
theorem norm_laplaceF_le {ω' μ δ' θ₁ θ₂ α' δ₀ M : ℝ} {lam : ℂ} {G : ℂ → ℂ} (hδ' : 0 < δ')
    (hδ'π : δ' ≤ Real.pi / 2)
    (hangle : ∀ θ ∈ Icc θ₁ θ₂, ∀ ψ : ℝ, |ψ - ω'| < α' → |θ + μ * ψ| ≤ Real.pi / 2 - δ')
    (hM : ∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖G w‖ ≤ M) {z : ℂ} (hz : θ₁ ≤ arg z ∧ arg z ≤ θ₂)
    {w : ℂ} (hw : w ∈ sectorDisc ω' α' δ₀) :
    ‖laplaceF ω' μ lam G z w‖ ≤ Real.exp (-(Real.sin δ' * ‖z‖ * ‖w‖ ^ μ)) *
      (Real.exp (|lam.im| * (|ω'| + Real.pi)) * M * ‖w‖ ^ (lam.re - 1)) := by
  have hM' := hM w (by simpa [Metric.mem_ball] using hw.2)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM'
  rw [laplaceF, norm_mul, norm_mul]
  have h1 := norm_cexp_neg_mul_brPow_le hδ' hδ'π hangle hz hw.1
  have h2 := norm_brPow_lam (ω' := ω') lam hw.1.1
  calc ‖cexp (-(z * brPow ω' μ w))‖ * (‖brPow ω' (lam - 1) w‖ * ‖G w‖)
      ≤ Real.exp (-(Real.sin δ' * ‖z‖ * ‖w‖ ^ μ)) *
        ((‖w‖ ^ (lam.re - 1) * Real.exp (|lam.im| * (|ω'| + Real.pi))) * M) := by gcongr
    _ = _ := by ring

theorem norm_laplaceF_le' {ω' μ δ' θ₁ θ₂ α' δ₀ M : ℝ} {lam : ℂ} {G : ℂ → ℂ} (hδ' : 0 < δ')
    (hδ'π : δ' ≤ Real.pi / 2)
    (hangle : ∀ θ ∈ Icc θ₁ θ₂, ∀ ψ : ℝ, |ψ - ω'| < α' → |θ + μ * ψ| ≤ Real.pi / 2 - δ')
    (hM : ∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖G w‖ ≤ M) {z : ℂ} (hz : θ₁ ≤ arg z ∧ arg z ≤ θ₂)
    {w : ℂ} (hw : w ∈ sectorDisc ω' α' δ₀) :
    ‖laplaceF ω' μ lam G z w‖ ≤
      Real.exp (|lam.im| * (|ω'| + Real.pi)) * M * ‖w‖ ^ (lam.re - 1) := by
  refine (norm_laplaceF_le hδ' hδ'π hangle hM hz hw).trans ?_
  have hM' := hM w (by simpa [Metric.mem_ball] using hw.2)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM'
  have h1 : Real.exp (-(Real.sin δ' * ‖z‖ * ‖w‖ ^ μ)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have := Real.sin_pos_of_pos_of_lt_pi hδ' (by linarith [Real.pi_pos])
    positivity
  calc _ ≤ 1 * (Real.exp (|lam.im| * (|ω'| + Real.pi)) * M * ‖w‖ ^ (lam.re - 1)) := by
        gcongr
    _ = _ := one_mul _

theorem differentiableOn_laplaceF {ω' μ α' δ₀ : ℝ} (hα' : α' ≤ Real.pi) {lam : ℂ} {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (Metric.ball 0 δ₀)) (z : ℂ) :
    DifferentiableOn ℂ (laplaceF ω' μ lam G z) (sectorDisc ω' α' δ₀) := by
  intro w hw
  have hs := mem_slitPlane_of_mem_sectorBr hα' hw.1
  have h1 : DifferentiableAt ℂ (brPow ω' μ) w := (hasDerivAt_brPow _ hs).differentiableAt
  have h2 : DifferentiableAt ℂ (brPow ω' (lam - 1)) w := (hasDerivAt_brPow _ hs).differentiableAt
  have h3 : DifferentiableAt ℂ G w :=
    hG.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball] using hw.2))
  exact ((h1.const_mul z).neg.cexp.mul (h2.mul h3)).differentiableWithinAt

/-! ### The ray integral as a Laplace transform -/

/-- `q̃(v) = v^{(λ−μ)/μ} G(v^{1/μ} e^{iω'})` for `0 < v < R`, `0` otherwise. -/
noncomputable def watsonQ (ω' μ : ℝ) (lam : ℂ) (G : ℂ → ℂ) (R : ℝ) (v : ℝ) : ℂ :=
  (Ioo 0 R).indicator
    (fun v => (v : ℂ) ^ ((lam - μ) / μ) * G (((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I))) v

theorem ofReal_rpow_cpow {r : ℝ} (hr : 0 < r) (μ : ℝ) (c : ℂ) :
    ((r ^ μ : ℝ) : ℂ) ^ c = (r : ℂ) ^ ((μ : ℂ) * c) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hr μ).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log (Real.rpow_pos_of_pos hr μ).le,
    Real.log_rpow hr, ← ofReal_log hr.le]
  push_cast
  ring_nf

theorem div_re_ofReal (c : ℂ) {μ : ℝ} (hμ : 0 < μ) : (c / μ).re = c.re / μ := by
  simp [div_re, normSq_ofReal]
  field_simp

theorem norm_laplaceF_polar {ω' μ : ℝ} (lam : ℂ) (G : ℂ → ℂ) (z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    laplaceF ω' μ lam G z ((r : ℂ) * cexp (ω' * I)) * cexp (ω' * I) =
      cexp (lam * ω' * I) * (cexp (-(z * cexp (μ * ω' * I) * ((r ^ μ : ℝ) : ℂ))) *
        ((r : ℂ) ^ (lam - 1) * G ((r : ℂ) * cexp (ω' * I)))) := by
  rw [laplaceF, brPow_polar hr (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
    brPow_polar hr (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]), ← ofReal_cpow hr.le,
    show (ω' : ℂ) * I * (μ : ℂ) = (μ : ℂ) * ω' * I by ring,
    show (ω' : ℂ) * I * (lam - 1) = lam * ω' * I - ω' * I by ring, Complex.exp_sub]
  have hne : cexp (ω' * I) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The substitution `v = r^μ`: the ray integral is `e^{iλω'}/μ` times the Laplace transform of
`q̃` at `z e^{iμω'}`. -/
theorem integral_ray_eq_laplace {ω' μ : ℝ} (hμ : 0 < μ) (lam : ℂ) (G : ℂ → ℂ) (z : ℂ) {r₁ : ℝ}
    (hr₁ : 0 < r₁) :
    ∫ r in Ioo 0 r₁, laplaceF ω' μ lam G z ((r : ℂ) * cexp (ω' * I)) * cexp (ω' * I) =
      cexp (lam * ω' * I) * ((1 / μ : ℝ) : ℂ) *
        ∫ v in Ioi (0 : ℝ), cexp (-(z * cexp (μ * ω' * I) * v)) *
          watsonQ ω' μ lam G (r₁ ^ μ) v := by
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  set ζ := z * cexp (μ * ω' * I) with hζ
  set g : ℝ → ℂ := fun v => cexp (-(ζ * v)) * watsonQ ω' μ lam G (r₁ ^ μ) v with hg
  have hsub := integral_comp_rpow_Ioi g (p := μ) hμ.ne'
  rw [abs_of_pos hμ] at hsub
  -- the pointwise identity for `r > 0`
  have hpt : ∀ r ∈ Ioi (0 : ℝ), (μ * r ^ (μ - 1)) • g (r ^ μ) =
      (Ioo 0 r₁).indicator (fun r : ℝ => ((μ : ℝ) : ℂ) * cexp (-(lam * ω' * I)) *
        (laplaceF ω' μ lam G z ((r : ℂ) * cexp (ω' * I)) * cexp (ω' * I))) r := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    have hrμ : 0 < r ^ μ := Real.rpow_pos_of_pos hr μ
    simp only [hg, watsonQ, Complex.real_smul]
    by_cases hrr : r < r₁
    · have hmem : r ^ μ ∈ Ioo 0 (r₁ ^ μ) := ⟨hrμ, (Real.rpow_lt_rpow_iff hr.le hr₁.le hμ).mpr hrr⟩
      rw [indicator_of_mem hmem, indicator_of_mem (show r ∈ Ioo 0 r₁ from ⟨hr, hrr⟩),
        norm_laplaceF_polar lam G z hr, ← Real.rpow_mul hr.le,
        show μ * (1 / μ) = 1 by field_simp, Real.rpow_one, ofReal_rpow_cpow hr,
        show (μ : ℂ) * ((lam - μ) / μ) = lam - μ by field_simp]
      have e1 : ((μ * r ^ (μ - 1) : ℝ) : ℂ) = (μ : ℂ) * (r : ℂ) ^ ((μ - 1 : ℝ) : ℂ) := by
        rw [ofReal_mul, ofReal_cpow hr.le]
      have e2 : (r : ℂ) ^ ((μ - 1 : ℝ) : ℂ) * (r : ℂ) ^ (lam - μ) = (r : ℂ) ^ (lam - 1) := by
        rw [← cpow_add _ _ (ofReal_ne_zero.mpr hr.ne')]
        congr 1
        push_cast
        ring
      have h3 : cexp (-(lam * ω' * I)) * cexp (lam * ω' * I) = 1 := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      rw [e1, hζ]
      linear_combination ((μ : ℂ) * cexp (-(z * cexp (μ * ω' * I) * ((r ^ μ : ℝ) : ℂ))) *
        G (((r : ℝ) : ℂ) * cexp (ω' * I))) * e2 +
        (-((μ : ℂ) * cexp (-(z * cexp (μ * ω' * I) * ((r ^ μ : ℝ) : ℂ))) *
          G (((r : ℝ) : ℂ) * cexp (ω' * I)) * (r : ℂ) ^ (lam - 1))) * h3
    · have hmem : r ^ μ ∉ Ioo 0 (r₁ ^ μ) := fun hm =>
        hrr ((Real.rpow_lt_rpow_iff hr.le hr₁.le hμ).mp hm.2)
      rw [indicator_of_notMem hmem, indicator_of_notMem (show r ∉ Ioo 0 r₁ from fun hm => hrr hm.2)]
      simp
  rw [← hsub, setIntegral_congr_fun measurableSet_Ioi hpt, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self,
    integral_const_mul]
  have h1 : cexp (lam * ω' * I) * ((1 / μ : ℝ) : ℂ) * ((μ : ℂ) * cexp (-(lam * ω' * I))) = 1 := by
    have e : ((1 / μ : ℝ) : ℂ) * (μ : ℂ) = 1 := by
      rw [← ofReal_mul, show (1 / μ * μ : ℝ) = 1 by field_simp, ofReal_one]
    calc cexp (lam * ω' * I) * ((1 / μ : ℝ) : ℂ) * ((μ : ℂ) * cexp (-(lam * ω' * I)))
        = (((1 / μ : ℝ) : ℂ) * (μ : ℂ)) * (cexp (lam * ω' * I) * cexp (-(lam * ω' * I))) := by
          ring
      _ = 1 := by rw [e, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  linear_combination (-(∫ r in Ioo 0 r₁,
    laplaceF ω' μ lam G z ((r : ℂ) * cexp (ω' * I)) * cexp (ω' * I))) * h1

/-- `q̃` is bounded by `M v^{(ℜλ−μ)/μ}` on `(0, R)`, hence the Laplace integrand is integrable. -/
theorem integrableOn_watsonQ {ω' μ δ₀ M : ℝ} (hμ : 0 < μ) {lam : ℂ} (hlam : 0 < lam.re)
    {G : ℂ → ℂ} (hGc : ContinuousOn G (Metric.ball 0 δ₀))
    (hM : ∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖G w‖ ≤ M) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁δ : r₁ < δ₀)
    (ζ : ℂ) :
    IntegrableOn (fun v : ℝ => cexp (-(ζ * v)) * watsonQ ω' μ lam G (r₁ ^ μ) v) (Ioi 0) := by
  set R := r₁ ^ μ with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hr₁ μ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_ball_self (hr₁.trans hr₁δ)))
  have hmem : ∀ v ∈ Ioo 0 R, ((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I) ∈ Metric.ball (0 : ℂ) δ₀ := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right, norm_polar (Real.rpow_nonneg hv.1.le _)]
    have : v ^ (1 / μ) < R ^ (1 / μ) := Real.rpow_lt_rpow hv.1.le hv.2 (one_div_pos.mpr hμ)
    rw [hR, ← Real.rpow_mul hr₁.le, show μ * (1 / μ) = 1 by field_simp, Real.rpow_one] at this
    linarith
  have hre : ((lam - μ) / μ).re = (lam.re - μ) / μ := by rw [div_re_ofReal _ hμ, sub_re, ofReal_re]
  have hexp : -1 < (lam.re - μ) / μ := by
    rw [lt_div_iff₀ hμ]
    linarith
  -- the integrand vanishes off `(0, R)`
  have heq : (fun v : ℝ => cexp (-(ζ * v)) * watsonQ ω' μ lam G R v) =
      (Ioo 0 R).indicator (fun v : ℝ => cexp (-(ζ * v)) *
        ((v : ℂ) ^ ((lam - μ) / μ) * G (((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I)))) := by
    funext v
    by_cases hv : v ∈ Ioo 0 R
    · simp [watsonQ, indicator_of_mem hv]
    · simp [watsonQ, indicator_of_notMem hv]
  rw [heq]
  refine ((integrable_indicator_iff measurableSet_Ioo).mpr ?_).integrableOn
  have hcont : ContinuousOn (fun v : ℝ => cexp (-(ζ * v)) *
      ((v : ℂ) ^ ((lam - μ) / μ) * G (((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I)))) (Ioo 0 R) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.mul ?_ ?_)
    · exact continuous_ofReal.continuousOn.cpow_const fun v hv => ofReal_mem_slitPlane.mpr hv.1
    · refine hGc.comp ?_ hmem
      refine ContinuousOn.mul ?_ continuousOn_const
      refine continuous_ofReal.comp_continuousOn fun v hv => ?_
      exact (Real.continuousAt_rpow_const v (1 / μ) (Or.inl hv.1.ne')).continuousWithinAt
  have hb : IntegrableOn (fun v : ℝ => Real.exp (|ζ.re| * R) * M * v ^ ((lam.re - μ) / μ))
      (Ioo 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) hexp).const_mul
      (Real.exp (|ζ.re| * R) * M)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  refine Integrable.mono' hb (hcont.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun v hv => ?_))
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hv.1, hre]
  have h1 : Real.exp (-(ζ * v)).re ≤ Real.exp (|ζ.re| * R) := by
    apply Real.exp_le_exp.mpr
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have := mul_le_mul_of_nonneg_right (neg_le_abs ζ.re) hv.1.le
    have := mul_le_mul_of_nonneg_left hv.2.le (abs_nonneg ζ.re)
    linarith
  have h2 := hM _ (hmem v hv)
  have hv0 : 0 < v := hv.1
  calc Real.exp (-(ζ * v)).re * (v ^ ((lam.re - μ) / μ) *
        ‖G (((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I))‖)
      ≤ Real.exp (|ζ.re| * R) * (v ^ ((lam.re - μ) / μ) * M) := by gcongr
    _ = _ := by ring

theorem tendsto_laplace_watsonQ {ω' μ : ℝ} {lam : ℂ} {G : ℂ → ℂ} {R : ℝ} {ζ : ℂ}
    (hint : IntegrableOn (fun v : ℝ => cexp (-(ζ * v)) * watsonQ ω' μ lam G R v) (Ioi 0)) :
    Tendsto (fun R' => ∫ t in (0 : ℝ)..R', cexp (-ζ * t) * watsonQ ω' μ lam G R t) atTop
      (𝓝 (∫ v in Ioi (0 : ℝ), cexp (-(ζ * v)) * watsonQ ω' μ lam G R v)) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  refine h.congr fun R' => ?_
  simp only [id, neg_mul]

theorem laplaceIntegralC_watsonQ {ω' μ : ℝ} {lam : ℂ} {G : ℂ → ℂ} {R : ℝ} {ζ : ℂ}
    (hint : IntegrableOn (fun v : ℝ => cexp (-(ζ * v)) * watsonQ ω' μ lam G R v) (Ioi 0)) :
    laplaceIntegralC (watsonQ ω' μ lam G R) ζ =
      ∫ v in Ioi (0 : ℝ), cexp (-(ζ * v)) * watsonQ ω' μ lam G R v :=
  (tendsto_laplace_watsonQ hint).limUnder_eq

/-! ### Watson's lemma for `q̃` -/

/-- The Taylor coefficients of `G` at `0`. -/
noncomputable def taylorCoeff (G : ℂ → ℂ) (s : ℕ) : ℂ := iteratedDeriv s G 0 / (s.factorial : ℂ)

/-- 2.3.7 for `q̃`: `q̃(v) ∼ ∑ gₛ e^{isω'} v^{(s+λ−μ)/μ}` as `v → 0+`, from the Taylor series of
`G` at `0`. -/
theorem watsonQ_expansion {ω' μ : ℝ} (hμ : 0 < μ) {lam : ℂ} {G : ℂ → ℂ}
    (hGa : AnalyticAt ℂ G 0) {R : ℝ} (hR : 0 < R) :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun s (v : ℝ) => (v : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) (watsonQ ω' μ lam G R)
      (fun s (v : ℝ) => taylorCoeff G s * cexp (s * ω' * I) *
        (v : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) := by
  refine ⟨isAsympScale_cpow_nhdsGT hμ, fun n => ?_⟩
  have hp := hGa.hasFPowerSeriesAt
  obtain ⟨K, hK⟩ := (hp.isBigO_sub_partialSum_pow n).bound
  rw [Metric.eventually_nhds_iff] at hK
  obtain ⟨η, hη, hKη⟩ := hK
  have hμ' : 0 < 1 / μ := one_div_pos.mpr hμ
  refine isBigODLMF_of_bound (K := K) ?_ ?_
  · have hev : ∀ᶠ v in 𝓝[>] (0 : ℝ), v < R ∧ v ^ (1 / μ) < η := by
      have h1 : Tendsto (fun v : ℝ => v ^ (1 / μ)) (𝓝[>] 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (1 / μ) (Or.inr hμ'.le)).tendsto
        rw [Real.zero_rpow hμ'.ne'] at this
        exact this.mono_left nhdsWithin_le_nhds
      filter_upwards [Ioo_mem_nhdsGT hR, h1.eventually (gt_mem_nhds hη)] with v hv h2
      exact ⟨hv.2, h2⟩
    filter_upwards [hev, self_mem_nhdsWithin] with v hv hv0
    have hv0 : (0 : ℝ) < v := hv0
    set y : ℂ := ((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I) with hy
    have hyn : ‖y‖ = v ^ (1 / μ) := norm_polar (Real.rpow_nonneg hv0.le _) _
    have hKy := hKη (y := y) (by rw [dist_zero_right, hyn]; exact hv.2)
    rw [zero_add] at hKy
    have hps : (FormalMultilinearSeries.ofScalars ℂ fun k => iteratedDeriv k G 0 /
        (k.factorial : ℂ)).partialSum n y = ∑ k ∈ Finset.range n, taylorCoeff G k * y ^ k := by
      simp only [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
        smul_eq_mul, taylorCoeff]
    rw [hps] at hKy
    have hyk : ∀ k : ℕ, y ^ k = ((v ^ ((k : ℝ) / μ) : ℝ) : ℂ) * cexp (k * ω' * I) := fun k => by
      rw [hy, mul_pow, ← ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv0.le,
        ← Complex.exp_nat_mul, show (1 / μ * (k : ℝ)) = (k : ℝ) / μ by ring,
        show ((k : ℂ) * (ω' * I)) = k * ω' * I by ring]
    have hmem : v ∈ Ioo 0 R := ⟨hv0, hv.1⟩
    have hexp : ∀ k : ℕ, (v : ℂ) ^ ((lam - μ) / μ) * ((v ^ ((k : ℝ) / μ) : ℝ) : ℂ) =
        (v : ℂ) ^ (((k : ℂ) + lam - μ) / μ) := fun k => by
      rw [ofReal_cpow hv0.le, ← cpow_add _ _ (ofReal_ne_zero.mpr hv0.ne')]
      congr 1
      push_cast
      ring
    have heq : watsonQ ω' μ lam G R v - ∑ s ∈ Finset.range n,
        taylorCoeff G s * cexp (s * ω' * I) * (v : ℂ) ^ (((s : ℂ) + lam - μ) / μ) =
        (v : ℂ) ^ ((lam - μ) / μ) * (G y - ∑ k ∈ Finset.range n, taylorCoeff G k * y ^ k) := by
      rw [watsonQ, indicator_of_mem hmem, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hyk, ← hexp k]
      ring
    rw [heq, norm_mul, norm_cpow_eq_rpow_re_of_pos hv0, norm_cpow_eq_rpow_re_of_pos hv0]
    have hre1 : ((lam - μ) / μ).re = (lam.re - μ) / μ := by
      rw [div_re_ofReal _ hμ, sub_re, ofReal_re]
    have hre2 : (((n : ℂ) + lam - μ) / μ).re = (n + lam.re - μ) / μ := by
      rw [div_re_ofReal _ hμ, sub_re, add_re, natCast_re, ofReal_re]
    rw [hre1, hre2]
    have hKv : ‖G y - ∑ k ∈ Finset.range n, taylorCoeff G k * y ^ k‖ ≤ K * v ^ ((n : ℝ) / μ) := by
      refine hKy.trans (le_of_eq ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hyn, ← Real.rpow_natCast,
        ← Real.rpow_mul hv0.le]
      congr 2
      ring
    calc v ^ ((lam.re - μ) / μ) * ‖G y - ∑ k ∈ Finset.range n, taylorCoeff G k * y ^ k‖
        ≤ v ^ ((lam.re - μ) / μ) * (K * v ^ ((n : ℝ) / μ)) := by gcongr
      _ = K * v ^ ((n + lam.re - μ) / μ) := by
          rw [show (n + lam.re - μ) / μ = (lam.re - μ) / μ + (n : ℝ) / μ by ring,
            Real.rpow_add hv0]
          ring
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hv)) _

theorem measurable_watsonQ {ω' μ δ₀ : ℝ} (hμ : 0 < μ) (lam : ℂ) {G : ℂ → ℂ}
    (hGc : ContinuousOn G (Metric.ball 0 δ₀)) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁δ : r₁ < δ₀) :
    Measurable (watsonQ ω' μ lam G (r₁ ^ μ)) := by
  set R := r₁ ^ μ with hR
  have hmem : ∀ v ∈ Ioo 0 R, ((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I) ∈ Metric.ball (0 : ℂ) δ₀ := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right, norm_polar (Real.rpow_nonneg hv.1.le _)]
    have : v ^ (1 / μ) < R ^ (1 / μ) := Real.rpow_lt_rpow hv.1.le hv.2 (one_div_pos.mpr hμ)
    rw [hR, ← Real.rpow_mul hr₁.le, show μ * (1 / μ) = 1 by field_simp, Real.rpow_one] at this
    linarith
  have hcont : ContinuousOn (fun v : ℝ =>
      (v : ℂ) ^ ((lam - μ) / μ) * G (((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I))) (Ioo 0 R) := by
    refine ContinuousOn.mul ?_ ?_
    · exact continuous_ofReal.continuousOn.cpow_const fun v hv => ofReal_mem_slitPlane.mpr hv.1
    · refine hGc.comp ?_ hmem
      refine ContinuousOn.mul ?_ continuousOn_const
      refine continuous_ofReal.comp_continuousOn fun v hv => ?_
      exact (Real.continuousAt_rpow_const v (1 / μ) (Or.inl hv.1.ne')).continuousWithinAt
  have e : watsonQ ω' μ lam G R = (Ioo 0 R).indicator (fun v : ℝ =>
      (v : ℂ) ^ ((lam - μ) / μ) * G (((v ^ (1 / μ) : ℝ) : ℂ) * cexp (ω' * I))) := rfl
  rw [e, ← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const measurableSet_Ioo

/-- Watson's lemma 2.4.1 for `q̃`: the expansion of its Laplace transform in `|ph ζ| ≤ π/2 − δ'`.
-/
theorem watsonQ_laplace_expansion {ω' μ δ₀ M δ' : ℝ} (hμ : 0 < μ) {lam : ℂ} (hlam : 0 < lam.re)
    {G : ℂ → ℂ} (hGa : AnalyticAt ℂ G 0) (hGc : ContinuousOn G (Metric.ball 0 δ₀))
    (hM : ∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖G w‖ ≤ M) {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁δ : r₁ < δ₀)
    (hδ' : 0 < δ') (hδ'π : δ' ≤ Real.pi / 2) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ'))
      (fun s ζ => ζ ^ (-watsonExpC lam μ s)) (laplaceIntegralC (watsonQ ω' μ lam G (r₁ ^ μ)))
      (fun s ζ => Complex.Gamma (watsonExpC lam μ s) * (taylorCoeff G s * cexp (s * ω' * I)) *
        ζ ^ (-watsonExpC lam μ s)) := by
  have hint : ∀ ζ : ℂ, IntegrableOn (fun v : ℝ => cexp (-(ζ * v)) *
      watsonQ ω' μ lam G (r₁ ^ μ) v) (Ioi 0) := fun ζ =>
    integrableOn_watsonQ hμ hlam hGc hM hr₁ hr₁δ ζ
  have hq : IntegrableOn (watsonQ ω' μ lam G (r₁ ^ μ)) (Ioi 0) := by
    have := hint 0
    simpa using this
  refine dlmf_2_4_1 (x₀ := 1) hlam hμ hδ' hδ'π (measurable_watsonQ hμ lam hGc hr₁ hr₁δ)
    (fun c R' hc hcR => ?_) (watsonQ_expansion hμ hGa (Real.rpow_pos_of_pos hr₁ μ))
    (fun ζ _ => ⟨_, tendsto_laplace_watsonQ (hint ζ)⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcR]
  exact hq.mono_set fun v hv => hc.trans hv.1

/-! ### Exponentially small terms -/

/-- A term bounded by `K e^{−c|z|}`, `c > 0`, is `O(z^{−β})` for every `β`. -/
theorem isBigODLMF_cpow_of_exp_bound {l : Filter ℂ} (hl : l ≤ Bornology.cobounded ℂ)
    {E : ℂ → ℂ} {K c : ℝ} (hc : 0 < c) (hE : ∀ᶠ z in l, ‖E z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (β : ℂ) : IsBigODLMF l E (fun z => z ^ (-β)) := by
  have hcob : Tendsto (fun z : ℂ => ‖z‖) l atTop := tendsto_norm_cobounded_atTop.mono_left hl
  refine isBigODLMF_of_bound (K := |K| * Real.exp (Real.pi * |β.im|)) ?_ ?_
  · filter_upwards [hE, hcob.eventually (eventually_exp_neg_le_rpow_neg β.re hc),
      hcob.eventually (eventually_gt_atTop 0)] with z h1 h2 h3
    have hz0 : z ≠ 0 := norm_pos_iff.mp h3
    calc ‖E z‖ ≤ K * Real.exp (-(c * ‖z‖)) := h1
      _ ≤ |K| * ‖z‖ ^ (-β.re) :=
          (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le).trans
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg K))
      _ ≤ |K| * (Real.exp (Real.pi * |β.im|) * ‖z ^ (-β)‖) :=
          mul_le_mul_of_nonneg_left (norm_cpow_neg_ge hz0 β) (abs_nonneg K)
      _ = _ := by ring
  · filter_upwards [hcob.eventually (eventually_gt_atTop 0)] with z hz
    exact cpow_ne_zero_of_ne_zero (norm_pos_iff.mp hz) _

/-- Multiplying `f` and the terms of a generalized expansion by a nonzero constant. -/
theorem IsGenAsympExpansionDLMF.const_mul' {α : Type*} {l : Filter α} {φ : ℕ → α → ℂ}
    {f : α → ℂ} {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs) {k : ℂ} (hk : k ≠ 0) :
    IsGenAsympExpansionDLMF l φ (fun x => k * f x) (fun s x => k * fs s x) := by
  have h1 := (h.mul_fun (g := fun _ => k) (Eventually.of_forall fun _ => hk)).scale_const_mul
    (c := fun _ => k⁻¹) (fun _ => inv_ne_zero hk)
  refine h1.congr' (fun s => Eventually.of_forall fun x => ?_) (EventuallyEq.refl _ _)
    (fun s => EventuallyEq.refl _ _)
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]

/-- The arc of radius `r₁` from the ray to the end of the path is exponentially small. -/
theorem norm_arc_le {ω' μ δ' θ₁ θ₂ α' δ₀ M : ℝ} {lam : ℂ} {G : ℂ → ℂ} (hδ' : 0 < δ')
    (hδ'π : δ' ≤ Real.pi / 2)
    (hangle : ∀ θ ∈ Icc θ₁ θ₂, ∀ ψ : ℝ, |ψ - ω'| < α' → |θ + μ * ψ| ≤ Real.pi / 2 - δ')
    (hM : ∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖G w‖ ≤ M) (hα'π : α' ≤ Real.pi) {r₁ φ₁ : ℝ}
    (hr₁ : 0 < r₁) (hr₁δ : r₁ < δ₀) (hφ₁ : |φ₁ - ω'| < α') {z : ℂ}
    (hz : θ₁ ≤ arg z ∧ arg z ≤ θ₂) :
    ‖∫ y in ω'..φ₁, laplaceF ω' μ lam G z ((r₁ : ℂ) * cexp (y * I)) *
        ((r₁ : ℂ) * cexp (y * I) * I)‖ ≤
      (Real.exp (|lam.im| * (|ω'| + Real.pi)) * M * r₁ ^ (lam.re - 1) * r₁ * α') *
        Real.exp (-(Real.sin δ' * r₁ ^ μ * ‖z‖)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_ball_self (hr₁.trans hr₁δ)))
  set C := Real.exp (|lam.im| * (|ω'| + Real.pi)) * M * r₁ ^ (lam.re - 1) with hC
  have hC0 : 0 ≤ C := by positivity
  have hE : Real.exp (-(Real.sin δ' * ‖z‖ * r₁ ^ μ)) =
      Real.exp (-(Real.sin δ' * r₁ ^ μ * ‖z‖)) := by ring_nf
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp (-(Real.sin δ' * r₁ ^ μ * ‖z‖)) * C * r₁) fun y hy => ?_).trans ?_
  · have hy' := uIoc_subset_uIcc hy
    have hmem : (r₁ : ℂ) * cexp (y * I) ∈ sectorDisc ω' α' δ₀ := by
      refine ⟨polar_mem_sectorBr hr₁ ?_ hα'π, by rw [norm_polar hr₁.le]; exact hr₁δ⟩
      rw [uIcc_eq_union] at hy'
      have h1 := abs_lt.mp hφ₁
      rcases hy' with hy' | hy' <;> rw [abs_lt] <;> constructor <;> linarith [hy'.1, hy'.2]
    have hb := norm_laplaceF_le (lam := lam) hδ' hδ'π hangle hM hz hmem
    rw [norm_polar hr₁.le, hE] at hb
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_polar hr₁.le]
    calc ‖laplaceF ω' μ lam G z ((r₁ : ℂ) * cexp (y * I))‖ * r₁
        ≤ (Real.exp (-(Real.sin δ' * r₁ ^ μ * ‖z‖)) * C) * r₁ := by gcongr
      _ = _ := rfl
  · have h1 : |φ₁ - ω'| ≤ α' := hφ₁.le
    calc Real.exp (-(Real.sin δ' * r₁ ^ μ * ‖z‖)) * C * r₁ * |φ₁ - ω'|
        ≤ Real.exp (-(Real.sin δ' * r₁ ^ μ * ‖z‖)) * C * r₁ * α' := by gcongr
      _ = _ := by ring

namespace LaplaceContour

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {B : ℝ} {a : ℂ} {ω : ℝ} {T : Set ℂ} {P Q : ℂ → ℂ}
  {lam : ℂ} {μ φ₀ ρ α θ₁ θ₂ Z : ℝ}

theorem continuousOn_pγ (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) :
    ContinuousOn (fun u => p (γ u)) (Ioo 0 B) := fun u hu =>
  ((h.p_diff.differentiableAt (h.T_open.mem_nhds (h.γ_mem u hu))).continuousAt.comp
    (h.continuousAt_γ ⟨by linarith [hu.1], hu.2⟩)).continuousWithinAt

theorem continuousOn_qγ (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) :
    ContinuousOn (fun u => q (γ u) * γ' u) (Ioo 0 B) := fun u hu =>
  (((h.q_diff.differentiableAt (h.T_open.mem_nhds (h.γ_mem u hu))).continuousAt.comp
    (h.continuousAt_γ ⟨by linarith [hu.1], hu.2⟩)).continuousWithinAt.mul
    (h.γ'_cont u hu))

theorem arg_mem_Ioc (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) {θ : ℝ}
    (hθ : θ ∈ Icc θ₁ θ₂) : θ ∈ Ioc (-Real.pi) Real.pi :=
  ⟨h.θ₁_gt.trans_le hθ.1, hθ.2.trans h.θ₂_le⟩

/-- `ℜ(z X) = |z| ℜ(e^{iθ} X)` for `θ = ph z`. -/
theorem re_mul_eq (z X : ℂ) : (z * X).re = ‖z‖ * (cexp (arg z * I) * X).re := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_assoc, re_ofReal_mul]

/-- The part of the path away from `a` is exponentially small relative to `e^{−zp(a)}`. -/
theorem tail_bound (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) {u₁ : ℝ}
    (hu₁ : 0 < u₁) (hu₁B : u₁ < B) :
    ∃ K c : ℝ, 0 < c ∧ ∀ z : ℂ, θ₁ ≤ arg z → arg z ≤ θ₂ → Z ≤ ‖z‖ →
      ‖∫ u in Ico u₁ B, cexp (-(z * (p (γ u) - p a))) * q (γ u) * γ' u‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨c, hc, Uc, hUc, hre⟩ := h.re_tail
  obtain ⟨Ub, hUb, htail⟩ := h.unif_tail 1 one_pos
  set U := max (max Uc Ub) ((u₁ + B) / 2) with hU
  have hUu₁ : u₁ < U := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hUB : U < B := max_lt (max_lt hUc.2 hUb.2) (by linarith)
  have hUcU : Uc ≤ U := (le_max_left _ _).trans (le_max_left _ _)
  have hUbU : Ub ≤ U := (le_max_right _ _).trans (le_max_left _ _)
  have hsub : Icc u₁ U ⊆ Ioo 0 B := fun u hu => ⟨hu₁.trans_le hu.1, hu.2.trans_lt hUB⟩
  -- the compact middle
  set f : ℝ × ℝ → ℝ := fun x => (cexp (x.1 * I) * (p (γ x.2) - p a)).re with hf
  have hfc : ContinuousOn f (Icc θ₁ θ₂ ×ˢ Icc u₁ U) := by
    refine Continuous.comp_continuousOn continuous_re ?_
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.sub ?_ continuousOn_const)
    exact (h.continuousOn_pγ.mono hsub).comp continuousOn_snd fun x hx => hx.2
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ((nonempty_Icc.mpr h.θ_le).prod (nonempty_Icc.mpr hUu₁.le)) hfc
  set c₂ := f xm with hc₂
  have hc₂0 : 0 < c₂ := h.re_pos xm.1 hxm.1 xm.2 (hsub hxm.2)
  have hc₂le : ∀ θ ∈ Icc θ₁ θ₂, ∀ u ∈ Icc u₁ U, c₂ ≤ (cexp (θ * I) * (p (γ u) - p a)).re := by
    intro θ hθ u hu
    have := hmin (show (θ, u) ∈ Icc θ₁ θ₂ ×ˢ Icc u₁ U from mem_prod.mpr ⟨hθ, hu⟩)
    exact this
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (h.continuousOn_qγ.mono hsub)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ u₁ ⟨le_rfl, hUu₁.le⟩)
  set c' := min c c₂ with hc'
  have hc'0 : 0 < c' := lt_min hc hc₂0
  refine ⟨M₂ * (U - u₁) + Real.exp (Z * c + Z * ‖p a‖), c', hc'0, fun z hz1 hz2 hzZ => ?_⟩
  have hθ : arg z ∈ Icc θ₁ θ₂ := ⟨hz1, hz2⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzZ
    linarith [h.Z_pos]
  -- the integrand and its integrability
  set F : ℝ → ℂ := fun u => cexp (-(z * (p (γ u) - p a))) * q (γ u) * γ' u with hF
  have hFeq : ∀ u, F u = cexp (z * p a) * (cexp (-(z * p (γ u))) * q (γ u) * γ' u) := fun u => by
    simp only [hF]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add]
    congr 3
    ring
  have hFI : IntegrableOn F (Ioo 0 B) := by
    have := (h.integrable z hz1 hz2 hzZ).const_mul (cexp (z * p a))
    exact IntegrableOn.congr_fun this (fun u _ => (hFeq u).symm) measurableSet_Ioo
  have hnormF : ∀ u, ‖F u‖ = Real.exp (-(‖z‖ * (cexp (arg z * I) * (p (γ u) - p a)).re)) *
      ‖q (γ u) * γ' u‖ := fun u => by
    simp only [hF]
    rw [mul_assoc, norm_mul, Complex.norm_exp, neg_re, re_mul_eq]
  -- split
  have hsplit : ∫ u in Ico u₁ B, F u = (∫ u in Ico u₁ U, F u) + ∫ u in Ico U B, F u := by
    rw [← setIntegral_union
      (Set.disjoint_left.mpr fun x hx hx' => lt_irrefl _ (hx.2.trans_le hx'.1))
      measurableSet_Ico (hFI.mono_set fun u hu => ⟨hu₁.trans_le hu.1, hu.2.trans hUB⟩)
      (hFI.mono_set fun u hu => ⟨(hu₁.trans hUu₁).trans_le hu.1, hu.2⟩),
      Ico_union_Ico_eq_Ico hUu₁.le hUB.le]
  -- the middle
  have hmid : ‖∫ u in Ico u₁ U, F u‖ ≤ M₂ * (U - u₁) * Real.exp (-(c₂ * ‖z‖)) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ico u₁ U) (f := F)
      (C := Real.exp (-(c₂ * ‖z‖)) * M₂) measure_Ico_lt_top fun u hu => by
        rw [hnormF]
        have h1 := hc₂le (arg z) hθ u (Ico_subset_Icc_self hu)
        have h2 := hM₂ u (Ico_subset_Icc_self hu)
        have h3 : Real.exp (-(‖z‖ * (cexp (arg z * I) * (p (γ u) - p a)).re)) ≤
            Real.exp (-(c₂ * ‖z‖)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [norm_nonneg z]
        exact mul_le_mul h3 h2 (norm_nonneg _) (Real.exp_pos _).le
    rw [Real.volume_real_Ico, max_eq_left (by linarith)] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  -- the far part
  have hfar : ‖∫ u in Ico U B, F u‖ ≤ Real.exp (Z * c + Z * ‖p a‖) * Real.exp (-(c * ‖z‖)) := by
    rw [integral_Ico_eq_integral_Ioo (x := U) (y := B)]
    set z₀ : ℂ := (Z : ℂ) * cexp (arg z * I) with hz₀
    have hz₀arg : arg z₀ = arg z := arg_polar h.Z_pos (h.arg_mem_Ioc hθ)
    have hz₀n : ‖z₀‖ = Z := norm_polar h.Z_pos.le _
    have hI₀ := h.integrable z₀ (by rw [hz₀arg]; exact hz1) (by rw [hz₀arg]; exact hz2)
      (by rw [hz₀n])
    have htail₀ := htail z₀ (by rw [hz₀arg]; exact hz1) (by rw [hz₀arg]; exact hz2) (by rw [hz₀n])
    set g : ℝ → ℂ := fun u => cexp (-(z₀ * p (γ u))) * q (γ u) * γ' u with hg
    have hgn : ∀ u, ‖g u‖ = Real.exp (-(Z * (cexp (arg z * I) * p (γ u)).re)) *
        ‖q (γ u) * γ' u‖ := fun u => by
      simp only [hg, hz₀]
      rw [mul_assoc, norm_mul, Complex.norm_exp, neg_re, mul_assoc, re_ofReal_mul]
    have hpa : ∀ u, Real.exp (-(Z * (cexp (arg z * I) * (p (γ u) - p a)).re)) ≤
        Real.exp (Z * ‖p a‖) * Real.exp (-(Z * (cexp (arg z * I) * p (γ u)).re)) := by
      intro u
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [mul_sub, sub_re]
      have h1 : (cexp (arg z * I) * p a).re ≤ ‖p a‖ := by
        calc (cexp (arg z * I) * p a).re ≤ ‖cexp (arg z * I) * p a‖ := re_le_norm _
          _ = ‖p a‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
      have := mul_le_mul_of_nonneg_left h1 h.Z_pos.le
      linarith
    have hbound : ∀ u ∈ Ioo U B, ‖F u‖ ≤
        Real.exp (-((‖z‖ - Z) * c)) * Real.exp (Z * ‖p a‖) * ‖g u‖ := by
      intro u hu
      rw [hnormF, hgn]
      have hre_u := hre (arg z) hθ u ⟨hUcU.trans_lt hu.1, hu.2⟩
      have h1 : Real.exp (-(‖z‖ * (cexp (arg z * I) * (p (γ u) - p a)).re)) ≤
          Real.exp (-((‖z‖ - Z) * c)) *
            Real.exp (-(Z * (cexp (arg z * I) * (p (γ u) - p a)).re)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hre_u (sub_nonneg.mpr hzZ)]
      calc Real.exp (-(‖z‖ * (cexp (arg z * I) * (p (γ u) - p a)).re)) * ‖q (γ u) * γ' u‖
          ≤ (Real.exp (-((‖z‖ - Z) * c)) *
              Real.exp (-(Z * (cexp (arg z * I) * (p (γ u) - p a)).re))) * ‖q (γ u) * γ' u‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ (Real.exp (-((‖z‖ - Z) * c)) * (Real.exp (Z * ‖p a‖) *
              Real.exp (-(Z * (cexp (arg z * I) * p (γ u)).re)))) * ‖q (γ u) * γ' u‖ := by
            gcongr
            exact hpa u
        _ = _ := by ring
    have hgI : IntegrableOn (fun u => Real.exp (-((‖z‖ - Z) * c)) * Real.exp (Z * ‖p a‖) *
        ‖g u‖) (Ioo U B) :=
      (IntegrableOn.mono_set hI₀.norm fun u hu => ⟨(hu₁.trans hUu₁).trans hu.1, hu.2⟩).const_mul _
    calc ‖∫ u in Ioo U B, F u‖
        ≤ ∫ u in Ioo U B, Real.exp (-((‖z‖ - Z) * c)) * Real.exp (Z * ‖p a‖) * ‖g u‖ :=
          norm_integral_le_of_norm_le hgI ((ae_restrict_iff' measurableSet_Ioo).mpr
            (Eventually.of_forall hbound))
      _ = Real.exp (-((‖z‖ - Z) * c)) * Real.exp (Z * ‖p a‖) * ∫ u in Ioo U B, ‖g u‖ := by
          rw [integral_const_mul]
      _ ≤ Real.exp (-((‖z‖ - Z) * c)) * Real.exp (Z * ‖p a‖) * 1 := by
          gcongr
          calc ∫ u in Ioo U B, ‖g u‖ ≤ ∫ u in Ioo Ub B, ‖g u‖ :=
                setIntegral_mono_set (IntegrableOn.mono_set hI₀.norm
                  (Ioo_subset_Ioo_left hUb.1.le))
                  (ae_of_all _ fun u => norm_nonneg _) (Ioo_subset_Ioo_left hUbU).eventuallyLE
            _ ≤ 1 := htail₀
      _ = Real.exp (Z * c + Z * ‖p a‖) * Real.exp (-(c * ‖z‖)) := by
          rw [mul_one, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  rw [hsplit]
  have h1 : Real.exp (-(c₂ * ‖z‖)) ≤ Real.exp (-(c' * ‖z‖)) := by
    apply Real.exp_le_exp.mpr
    have := min_le_right c c₂
    nlinarith [norm_nonneg z]
  have h2 : Real.exp (-(c * ‖z‖)) ≤ Real.exp (-(c' * ‖z‖)) := by
    apply Real.exp_le_exp.mpr
    have := min_le_left c c₂
    nlinarith [norm_nonneg z]
  have hU0 : 0 ≤ M₂ * (U - u₁) := mul_nonneg hM₂0 (by linarith)
  calc ‖(∫ u in Ico u₁ U, F u) + ∫ u in Ico U B, F u‖
      ≤ ‖∫ u in Ico u₁ U, F u‖ + ‖∫ u in Ico U B, F u‖ := norm_add_le _ _
    _ ≤ M₂ * (U - u₁) * Real.exp (-(c₂ * ‖z‖)) +
        Real.exp (Z * c + Z * ‖p a‖) * Real.exp (-(c * ‖z‖)) := add_le_add hmid hfar
    _ ≤ M₂ * (U - u₁) * Real.exp (-(c' * ‖z‖)) +
        Real.exp (Z * c + Z * ‖p a‖) * Real.exp (-(c' * ‖z‖)) := by gcongr
    _ = _ := by ring

end LaplaceContour

/-! ### The theorem -/

theorem branch_eq' {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h : |arg z + θ| ≤ Real.pi / 2) (α : ℂ) :
    (z * cexp (θ * I)) ^ (-α) = cexp (-(θ * I * α)) * z ^ (-α) := by
  have := WatsonSector.branch_eq hz h α
  rw [← this, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

namespace LaplaceContour

variable {p q : ℂ → ℂ} {γ γ' : ℝ → ℂ} {B : ℝ} {a : ℂ} {ω : ℝ} {T : Set ℂ} {P Q : ℂ → ℂ}
  {lam : ℂ} {μ φ₀ ρ α θ₁ θ₂ Z : ℝ}

/-- **DLMF 2.4.12 (Laplace's method for contour integrals)**: under the hypotheses
`LaplaceContour` (DLMF (a)–(c), 2.4.13 strict),
`e^{zp(a)} I(z) ∼ ∑ Γ((s+λ)/μ) bₛ z^{−(s+λ)/μ}` as `z → ∞` in `θ₁ ≤ ph z ≤ θ₂`, with principal
powers and `bₛ = laplaceCoeff` (`gₛ/μ`, `gₛ` the Taylor coefficients of `laplaceG`). -/
theorem dlmf_2_4_12 (h : LaplaceContour p q γ γ' B a ω T P Q lam μ φ₀ ρ α θ₁ θ₂ Z) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | θ₁ ≤ arg z ∧ arg z ≤ θ₂})
      (fun s z => z ^ (-watsonExpC lam μ s))
      (fun z => cexp (z * p a) * laplaceContour p q γ γ' B z)
      (fun s z => Complex.Gamma (watsonExpC lam μ s) * laplaceCoeff h.uset lam Q s *
        z ^ (-watsonExpC lam μ s)) := by
  obtain ⟨u₁, δ₀, α', δ', M, hu₁, hu₁B, hδ₀, hα'0, hα'π4, hδ'0, hangle, hGd, hM, hσS, hpeq, hqeq,
    hσd, hσ0⟩ := h.exists_local
  have hμ := h.μ_pos
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hπ := Real.pi_pos
  set ω' := ω + φ₀ / μ with hω'
  set G := laplaceG h.uset lam Q with hG
  set S := {z : ℂ | θ₁ ≤ arg z ∧ arg z ≤ θ₂} with hS
  set l := Bornology.cobounded ℂ ⊓ 𝓟 S with hl
  have hα'π : α' ≤ Real.pi := by linarith
  have hδ'π : δ' ≤ Real.pi / 2 := by
    have := hangle θ₁ ⟨le_rfl, h.θ_le⟩ ω' (by simpa using hα'0)
    linarith [abs_nonneg (θ₁ + μ * ω')]
  set r₁ := ‖unif a φ₀ μ P (γ u₁)‖ with hr₁def
  set φ₁ := (logBr ω' (unif a φ₀ μ P (γ u₁))).im with hφ₁def
  have hS₁ := hσS u₁ ⟨hu₁, le_rfl⟩
  have hr₁ : 0 < r₁ := norm_pos_iff.mpr hS₁.1.1
  have hr₁δ : r₁ < δ₀ := hS₁.2
  have hφ₁ : |φ₁ - ω'| < α' := hS₁.1.2
  have hGa : AnalyticAt ℂ G 0 := h.uset.analyticAt_laplaceG lam h.analyticAt_Q
  have hGc : ContinuousOn G (Metric.ball 0 δ₀) := hGd.continuousOn
  set c₀ : ℂ := cexp (((μ * ω' : ℝ) : ℂ) * I) with hc₀
  have hc₀' : cexp ((μ : ℂ) * ω' * I) = c₀ := by rw [hc₀]; push_cast; ring_nf
  set k : ℂ := cexp (lam * ω' * I) * ((1 / μ : ℝ) : ℂ) with hk
  have hk0 : k ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (ofReal_ne_zero.mpr (by positivity))
  set L : ℂ → ℂ := fun z => laplaceIntegralC (watsonQ ω' μ lam G (r₁ ^ μ)) (z * c₀) with hL
  set Arc : ℂ → ℂ := fun z => ∫ y in ω'..φ₁, laplaceF ω' μ lam G z ((r₁ : ℂ) * cexp (y * I)) *
    ((r₁ : ℂ) * cexp (y * I) * I) with hArc
  set Tail : ℂ → ℂ := fun z => ∫ u in Ico u₁ B,
    cexp (-(z * (p (γ u) - p a))) * q (γ u) * γ' u with hTail
  have hangle' : ∀ z ∈ S, |arg z + μ * ω'| ≤ Real.pi / 2 - δ' := fun z hz =>
    hangle (arg z) hz ω' (by simpa using hα'0)
  -- (1) the identity `e^{zp(a)} I(z) = k L(z) + Arc(z) + Tail(z)`
  have hkey : ∀ z ∈ S, Z ≤ ‖z‖ →
      cexp (z * p a) * laplaceContour p q γ γ' B z = k * L z + (Arc z + Tail z) := by
    intro z hz hzZ
    have hI := h.integrable z hz.1 hz.2 hzZ
    set F : ℝ → ℂ := fun u => cexp (-(z * (p (γ u) - p a))) * q (γ u) * γ' u with hF
    have hFeq : ∀ u, F u = cexp (z * p a) * (cexp (-(z * p (γ u))) * q (γ u) * γ' u) := fun u => by
      simp only [hF]
      rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add]
      congr 3
      ring
    have hFI : IntegrableOn F (Ioo 0 B) :=
      IntegrableOn.congr_fun (hI.const_mul (cexp (z * p a))) (fun u _ => (hFeq u).symm)
        measurableSet_Ioo
    have e1 : cexp (z * p a) * laplaceContour p q γ γ' B z = ∫ u in Ioo 0 B, F u := by
      rw [laplaceContour, ← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioo fun u _ => (hFeq u).symm
    have e2 : ∫ u in Ioo 0 B, F u = (∫ u in Ioo 0 u₁, F u) + Tail z := by
      rw [← Ioo_union_Ico_eq_Ioo hu₁ hu₁B.le, setIntegral_union
        (Set.disjoint_left.mpr fun x hx hx' => lt_irrefl _ (hx.2.trans_le hx'.1))
        measurableSet_Ico (hFI.mono_set fun u hu => ⟨hu.1, hu.2.trans hu₁B⟩)
        (hFI.mono_set fun u hu => ⟨hu₁.trans_le hu.1, hu.2⟩)]
    have hloc : ∀ u ∈ Ioo 0 u₁, F u = laplaceF ω' μ lam G z (unif a φ₀ μ P (γ u)) *
        (deriv (unif a φ₀ μ P) (γ u) * γ' u) := fun u hu => by
      simp only [hF]
      rw [hpeq u ⟨hu.1, hu.2.le⟩, laplaceF, mul_assoc, hqeq u ⟨hu.1, hu.2.le⟩]
      ring
    have e3 : ∫ u in Ioo 0 u₁, F u = ∫ u in Ioo 0 u₁, laplaceF ω' μ lam G z
        (unif a φ₀ μ P (γ u)) * (deriv (unif a φ₀ μ P) (γ u) * γ' u) :=
      setIntegral_congr_fun measurableSet_Ioo hloc
    have hdef := deform_to_ray hα'0 hα'π hδ₀ (differentiableOn_laplaceF hα'π hGd z)
      (C := Real.exp (|lam.im| * (|ω'| + Real.pi)) * M) (β := lam.re) h.lam_re
      (fun w hw => norm_laplaceF_le' hδ'0 hδ'π hangle hM hz hw) hu₁ hσd hσS hσ0
      (IntegrableOn.congr_fun (hFI.mono_set fun u hu => ⟨hu.1, hu.2.trans hu₁B⟩) hloc
        measurableSet_Ioo)
    have hint := integrableOn_watsonQ (ω' := ω') hμ h.lam_re hGc hM hr₁ hr₁δ
      (z * cexp (μ * ω' * I))
    rw [e1, e2, e3, hdef, integral_ray_eq_laplace hμ lam G z hr₁,
      ← laplaceIntegralC_watsonQ hint]
    simp only [hL, hk, hArc, hTail, hc₀']
    ring
  -- (2) the expansion of `L`, transported from the sector `|ph ζ| ≤ π/2 − δ'`
  have hmap : Tendsto (fun z : ℂ => z * c₀) l (Bornology.cobounded ℂ ⊓ 𝓟 (watsonSector δ')) := by
    refine Tendsto.inf ?_ (tendsto_principal_principal.mpr fun z hz => ?_)
    · refine Filter.hasBasis_cobounded_norm.tendsto_right_iff.mpr fun r _ => ?_
      filter_upwards [Filter.hasBasis_cobounded_norm.mem_of_mem (i := r) trivial] with z hz
      simp only [norm_mul, hc₀, norm_exp_ofReal_mul_I, mul_one] at hz ⊢
      exact hz
    · show |arg (z * c₀)| ≤ Real.pi / 2 - δ'
      by_cases hz0 : z = 0
      · rw [hz0, zero_mul, arg_zero, abs_zero]
        linarith
      · rw [hc₀, WatsonSector.arg_mul_exp_of_abs_le hz0 (by linarith [hangle' z hz])]
        exact hangle' z hz
  have hLexp := (watsonQ_laplace_expansion (ω' := ω') hμ h.lam_re hGa hGc hM hr₁ hr₁δ hδ'0
    hδ'π).comp_tendsto' hmap
  have hev : ∀ᶠ z in l, z ≠ 0 ∧ |arg z + μ * ω'| ≤ Real.pi / 2 := by
    filter_upwards [mem_inf_of_left (Filter.hasBasis_cobounded_norm.mem_of_mem (i := 1) trivial),
      mem_inf_of_right (mem_principal_self S)] with z h1 h2
    exact ⟨norm_pos_iff.mp (lt_of_lt_of_le one_pos h1), by linarith [hangle' z h2]⟩
  have hL2 := (hLexp.scale_const_mul
    (c := fun s => cexp (((μ * ω' : ℝ) : ℂ) * I * watsonExpC lam μ s))
    fun s => Complex.exp_ne_zero _).const_mul' hk0
  have hL3 : IsGenAsympExpansionDLMF l (fun s z => z ^ (-watsonExpC lam μ s))
      (fun z => k * L z) (fun s z => Complex.Gamma (watsonExpC lam μ s) *
        laplaceCoeff h.uset lam Q s * z ^ (-watsonExpC lam μ s)) := by
    refine hL2.congr' (fun s => ?_) (EventuallyEq.refl _ _) (fun s => ?_)
    · filter_upwards [hev] with z hz
      exact WatsonSector.branch_eq hz.1 hz.2 _
    · filter_upwards [hev] with z hz
      rw [branch_eq' hz.1 hz.2]
      simp only [laplaceCoeff, taylorCoeff, hk, hG]
      have hexp : cexp (lam * ω' * I) * cexp (s * ω' * I) *
          cexp (-(((μ * ω' : ℝ) : ℂ) * I * watsonExpC lam μ s)) = 1 := by
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
        congr 1
        rw [watsonExpC]
        push_cast
        field_simp
        ring
      linear_combination (Complex.Gamma (watsonExpC lam μ s) *
        (iteratedDeriv s (laplaceG h.uset lam Q) 0 / (s.factorial : ℂ)) * ((1 / μ : ℝ) : ℂ) *
        z ^ (-watsonExpC lam μ s)) * hexp
  -- (3) the arc and the tail are `O(z^{−αₙ})` for every `n`
  have hle : l ≤ Bornology.cobounded ℂ := inf_le_left
  have hZ : ∀ᶠ z in l, Z ≤ ‖z‖ :=
    mem_inf_of_left (Filter.hasBasis_cobounded_norm.mem_of_mem (i := Z) trivial)
  have hSz : ∀ᶠ z in l, z ∈ S := mem_inf_of_right (mem_principal_self S)
  have hArcO : ∀ n, IsBigODLMF l Arc (fun z => z ^ (-watsonExpC lam μ n)) := fun n => by
    refine isBigODLMF_cpow_of_exp_bound hle
      (K := Real.exp (|lam.im| * (|ω'| + Real.pi)) * M * r₁ ^ (lam.re - 1) * r₁ * α')
      (c := Real.sin δ' * r₁ ^ μ)
      (mul_pos (Real.sin_pos_of_pos_of_lt_pi hδ'0 (by linarith)) (Real.rpow_pos_of_pos hr₁ μ))
      ?_ (watsonExpC lam μ n)
    filter_upwards [hSz] with z hz
    exact norm_arc_le hδ'0 hδ'π hangle hM hα'π hr₁ hr₁δ hφ₁ hz
  obtain ⟨K, c, hc, hK⟩ := h.tail_bound hu₁ hu₁B
  have hTailO : ∀ n, IsBigODLMF l Tail (fun z => z ^ (-watsonExpC lam μ n)) := fun n => by
    refine isBigODLMF_cpow_of_exp_bound hle (K := K) hc ?_ (watsonExpC lam μ n)
    filter_upwards [hSz, hZ] with z hz hzZ
    exact hK z hz.1 hz.2 hzZ
  have hfinal := (hL3.add_isBigO hArcO).add_isBigO hTailO
  refine hfinal.congr' (fun s => EventuallyEq.refl _ _) ?_ (fun s => EventuallyEq.refl _ _)
  filter_upwards [hSz, hZ] with z hz hzZ
  rw [hkey z hz hzZ]
  ring

end LaplaceContour

end Azurite.DLMF
