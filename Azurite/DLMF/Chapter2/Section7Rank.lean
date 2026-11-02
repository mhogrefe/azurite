/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7Series
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# DLMF §2.7(ii): Irregular Singularities of Rank 1 — rank, 2.7.7, 2.7.9, 2.7.10

* The *rank* of a singularity (`PoleOrderCond`, `HasRank`): if the singularities of `f` and `g` at
  `z₀` are no worse than poles, `z₀` has rank `ℓ − 1`, `ℓ` the least integer such that
  `(z − z₀)^ℓ f(z)` and `(z − z₀)^{2ℓ} g(z)` are analytic at `z₀`; `HasRank.unique`,
  `HasRank.not_ordinary`. A regular singularity has rank 0 (`HasRank.isRegularSingularity`,
  `IsRegularSingularity.hasRank_zero_or`): the only exception is a point at which `f` and `g`
  have removable singularities (`PoleOrderCond f g z₀ 0`), which is ordinary as soon as `f`, `g`
  are continuous there (`PoleOrderCond.isOrdinaryPoint`).
* 2.7.7 (`RankOneData`, `RankOneData.dlmf_2_7_7`): `f(z) = ∑ fₛ z^{−s}`, `g(z) = ∑ gₛ z^{−s}`,
  the series converging for `|z| > a`.
* The point at infinity (classified by `ζ = 1/z`, `infinityF`, `infinityG` of §2.7(i)) is an
  irregular singularity of rank 1 exactly when one of `f₀, g₀, g₁` is nonzero
  (`RankOneData.hasRank_one_iff`, `RankOneData.isIrregularSingularity`); it is at worst a regular
  singularity when `f₀ = g₀ = g₁ = 0` (`RankOneData.hasRegularCoefficients_iff`).
* 2.7.9 (`rankOneChar`, `exists_charRoots`): the characteristic equation `λ² + f₀λ + g₀ = 0`.
* 2.7.10 (`rankOneMu`): `μ = −(f₁λ + g₁)/(f₀ + 2λ)`. The construction fails iff `λ₁ = λ₂`, that is,
  when `f₀² = 4g₀` (`fc0_add_two_mul_eq_zero_iff`, `charRoots_eq_iff`).
-/

open Filter Topology Set Complex Metric Finset

namespace Azurite.DLMF

/-! ### Power-series helpers -/

/-- The tail `n ↦ c (n + 1)` of a coefficient sequence. -/
def seqTail (c : ℕ → ℂ) (n : ℕ) : ℂ := c (n + 1)

theorem HasRadiusGE.tail {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) :
    HasRadiusGE (seqTail c) R := by
  intro ρ hρ hρR
  obtain ⟨K, hK⟩ := h ρ hρ hρR
  refine ⟨K / ρ, fun s => ?_⟩
  rw [le_div_iff₀ hρ, seqTail, mul_assoc, ← pow_succ]
  exact hK (s + 1)

/-- `∑ cₙ ζⁿ = c₀ + ζ ∑ c_{n+1} ζⁿ`. -/
theorem HasRadiusGE.powerSeriesSum_eq_zero_add {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) R) :
    powerSeriesSum c 0 ζ = c 0 + ζ * powerSeriesSum (seqTail c) 0 ζ := by
  unfold powerSeriesSum
  rw [(h.summable hζ).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [sub_zero, pow_zero, mul_one, seqTail]
  congr 1
  exact tsum_congr fun n => by ring

theorem HasRadiusGE.analyticAt {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) (hR : 0 < R) :
    AnalyticAt ℂ (powerSeriesSum c 0) 0 :=
  DifferentiableOn.analyticAt (s := ball (0 : ℂ) R)
    (fun _ hz => (h.hasDerivAt hz).differentiableAt.differentiableWithinAt)
    (isOpen_ball.mem_nhds (mem_ball_self hR))

theorem HasRadiusGE.tendsto_nhdsNE {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) (hR : 0 < R) :
    Tendsto (powerSeriesSum c 0) (𝓝[≠] 0) (𝓝 (c 0)) := by
  have := (h.continuousAt (z₀ := 0) (mem_ball_self hR)).tendsto
  rw [powerSeriesSum_self] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_pow_mul_nhdsNE {H : ℂ → ℂ} (hH : ContinuousAt H 0) {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun ζ : ℂ => ζ ^ k * H ζ) (𝓝[≠] 0) (𝓝 0) := by
  have h : ContinuousAt (fun ζ : ℂ => ζ ^ k * H ζ) 0 :=
    ((continuous_pow k).continuousAt (x := (0 : ℂ))).mul hH
  have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  simpa [zero_pow hk] using this

/-! ### The rank of a singularity -/

/-- `(z − z₀)^ℓ f(z)` and `(z − z₀)^{2ℓ} g(z)` extend analytically to `z₀`. -/
def PoleOrderCond (f g : ℂ → ℂ) (z₀ : ℂ) (ℓ : ℕ) : Prop :=
  (∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) ^ ℓ * f z = F z) ∧
  ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) ^ (2 * ℓ) * g z = G z

variable {f g : ℂ → ℂ} {z₀ : ℂ}

theorem poleOrderCond_one_iff : PoleOrderCond f g z₀ 1 ↔ HasRegularCoefficients f g z₀ := by
  simp only [PoleOrderCond, HasRegularCoefficients, pow_one, mul_one]

theorem PoleOrderCond.mono {ℓ ℓ' : ℕ} (h : PoleOrderCond f g z₀ ℓ) (hle : ℓ ≤ ℓ') :
    PoleOrderCond f g z₀ ℓ' := by
  obtain ⟨⟨F, hF, hfF⟩, ⟨G, hG, hgG⟩⟩ := h
  refine ⟨⟨fun z => (z - z₀) ^ (ℓ' - ℓ) * F z,
      ((analyticAt_id.sub analyticAt_const).pow _).mul hF, hfF.mono fun z hz => ?_⟩,
    ⟨fun z => (z - z₀) ^ (2 * ℓ' - 2 * ℓ) * G z,
      ((analyticAt_id.sub analyticAt_const).pow _).mul hG, hgG.mono fun z hz => ?_⟩⟩
  · show _ = (z - z₀) ^ (ℓ' - ℓ) * F z
    rw [← hz, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  · show _ = (z - z₀) ^ (2 * ℓ' - 2 * ℓ) * G z
    rw [← hz, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]

theorem IsOrdinaryPoint.poleOrderCond_zero (h : IsOrdinaryPoint f g z₀) :
    PoleOrderCond f g z₀ 0 :=
  ⟨⟨f, h.1, Eventually.of_forall fun z => by rw [pow_zero, one_mul]⟩,
    ⟨g, h.2, Eventually.of_forall fun z => by rw [mul_zero, pow_zero, one_mul]⟩⟩

/-- Removable singularities at which `f` and `g` are continuous are ordinary points. -/
theorem PoleOrderCond.isOrdinaryPoint (h : PoleOrderCond f g z₀ 0) (hf : ContinuousAt f z₀)
    (hg : ContinuousAt g z₀) : IsOrdinaryPoint f g z₀ := by
  obtain ⟨⟨F, hF, hfF⟩, ⟨G, hG, hgG⟩⟩ := h
  simp only [pow_zero, one_mul, mul_zero] at hfF hgG
  have key : ∀ {u U : ℂ → ℂ}, AnalyticAt ℂ U z₀ → ContinuousAt u z₀ →
      (∀ᶠ z in 𝓝[≠] z₀, u z = U z) → AnalyticAt ℂ u z₀ := by
    intro u U hU hu huU
    have h1 : Tendsto u (𝓝[≠] z₀) (𝓝 (u z₀)) := hu.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto u (𝓝[≠] z₀) (𝓝 (U z₀)) :=
      (hU.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (huU.mono fun _ h => h.symm)
    have h0 : u z₀ = U z₀ := tendsto_nhds_unique h1 h2
    refine hU.congr ?_
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure, eventually_sup]
    exact ⟨huU.mono fun _ h => h.symm, by simpa using h0.symm⟩
  exact ⟨key hF hf hfF, key hG hg hgG⟩

/-- **DLMF §2.7(ii)**: `z₀` has *rank* `r`: `ℓ = r + 1` is the least integer such that
`(z − z₀)^ℓ f(z)` and `(z − z₀)^{2ℓ} g(z)` are analytic at `z₀` (by `PoleOrderCond.mono`, failure
at `ℓ = r` is failure at every `ℓ ≤ r`). -/
def HasRank (f g : ℂ → ℂ) (z₀ : ℂ) (r : ℕ) : Prop :=
  PoleOrderCond f g z₀ (r + 1) ∧ ¬ PoleOrderCond f g z₀ r

theorem HasRank.least {r ℓ : ℕ} (h : HasRank f g z₀ r) (hℓ : PoleOrderCond f g z₀ ℓ) :
    r + 1 ≤ ℓ := by
  by_contra hlt
  exact h.2 (hℓ.mono (by omega))

theorem HasRank.unique {r₁ r₂ : ℕ} (h₁ : HasRank f g z₀ r₁) (h₂ : HasRank f g z₀ r₂) :
    r₁ = r₂ := by
  have := h₁.least h₂.1
  have := h₂.least h₁.1
  omega

theorem HasRank.not_ordinary {r : ℕ} (h : HasRank f g z₀ r) : ¬ IsOrdinaryPoint f g z₀ :=
  fun ho => h.2 (ho.poleOrderCond_zero.mono (Nat.zero_le r))

/-- **DLMF §2.7(ii)**: a point of rank 0 is a regular singularity. -/
theorem HasRank.isRegularSingularity (h : HasRank f g z₀ 0) : IsRegularSingularity f g z₀ :=
  ⟨h.not_ordinary, poleOrderCond_one_iff.mp h.1⟩

/-- A point of rank `r ≥ 1` is an irregular singularity. -/
theorem HasRank.isIrregularSingularity {r : ℕ} (h : HasRank f g z₀ r) (hr : 1 ≤ r) :
    IsIrregularSingularity f g z₀ :=
  ⟨h.not_ordinary, fun hreg => h.2 ((poleOrderCond_one_iff.mpr hreg).mono hr)⟩

/-- **DLMF §2.7(ii)**: "a regular singularity has rank 0", unless `f` and `g` both have removable
singularities at `z₀` (then `z₀` is ordinary after redefining `f`, `g` there, see
`PoleOrderCond.isOrdinaryPoint`). -/
theorem IsRegularSingularity.hasRank_zero_or (h : IsRegularSingularity f g z₀) :
    HasRank f g z₀ 0 ∨ PoleOrderCond f g z₀ 0 := by
  by_cases h0 : PoleOrderCond f g z₀ 0
  · exact Or.inr h0
  · exact Or.inl ⟨poleOrderCond_one_iff.mpr h.2, h0⟩

/-! ### 2.7.7: the expansions at an irregular singularity of rank 1 at infinity -/

/-- **DLMF 2.7.7**: `f(z) = ∑ fₛ z^{−s}`, `g(z) = ∑ gₛ z^{−s}` for `|z| > a`, the series
converging there (equivalently, the power series `∑ fₛ ζ^s`, `∑ gₛ ζ^s` have radius of convergence
at least `1/a`, `HasRadiusGE`). -/
structure RankOneData (f g : ℂ → ℂ) (a : ℝ) (fc gc : ℕ → ℂ) : Prop where
  a_pos : 0 < a
  f_radius : HasRadiusGE fc a⁻¹
  g_radius : HasRadiusGE gc a⁻¹
  f_eq : ∀ z : ℂ, a < ‖z‖ → f z = powerSeriesSum fc 0 z⁻¹
  g_eq : ∀ z : ℂ, a < ‖z‖ → g z = powerSeriesSum gc 0 z⁻¹

namespace RankOneData

variable {a : ℝ} {fc gc : ℕ → ℂ} (D : RankOneData f g a fc gc)
include D

theorem inv_mem_ball {z : ℂ} (hz : a < ‖z‖) : z⁻¹ ∈ ball (0 : ℂ) a⁻¹ := by
  have hz0 : 0 < ‖z‖ := D.a_pos.trans hz
  rw [mem_ball, dist_zero_right, norm_inv]
  exact (inv_lt_inv₀ hz0 D.a_pos).mpr hz

theorem lt_norm_inv {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) a⁻¹) (hζ0 : ζ ≠ 0) : a < ‖ζ⁻¹‖ := by
  rw [mem_ball, dist_zero_right] at hζ
  rw [norm_inv]
  exact (lt_inv_comm₀ D.a_pos (norm_pos_iff.mpr hζ0)).mpr hζ

/-- **DLMF 2.7.7**: `f(z) = ∑ fₛ/z^s`, `g(z) = ∑ gₛ/z^s` for `|z| > a`, absolutely convergent. -/
theorem dlmf_2_7_7 {z : ℂ} (hz : a < ‖z‖) :
    (f z = ∑' s, fc s / z ^ s ∧ Summable fun s => ‖fc s / z ^ s‖) ∧
      (g z = ∑' s, gc s / z ^ s ∧ Summable fun s => ‖gc s / z ^ s‖) := by
  have hb := D.inv_mem_ball hz
  have e : ∀ c : ℕ → ℂ, (fun s => c s * (z⁻¹ - 0) ^ s) = fun s => c s / z ^ s := fun c => by
    funext s; rw [sub_zero, inv_pow, div_eq_mul_inv]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [D.f_eq z hz, powerSeriesSum, e]
  · exact (D.f_radius.summable_norm hb).congr fun s => by rw [sub_zero, inv_pow, div_eq_mul_inv]
  · rw [D.g_eq z hz, powerSeriesSum, e]
  · exact (D.g_radius.summable_norm hb).congr fun s => by rw [sub_zero, inv_pow, div_eq_mul_inv]

theorem eventually_nhdsNE :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ∈ ball (0 : ℂ) a⁻¹ ∧ ζ ≠ 0 :=
  (eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds _ (inv_pos.mpr D.a_pos))).and
    self_mem_nhdsWithin

theorem f_inv {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) a⁻¹) (hζ0 : ζ ≠ 0) :
    f ζ⁻¹ = powerSeriesSum fc 0 ζ := by
  rw [D.f_eq _ (D.lt_norm_inv hζ hζ0), inv_inv]

theorem g_inv {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) a⁻¹) (hζ0 : ζ ≠ 0) :
    g ζ⁻¹ = powerSeriesSum gc 0 ζ := by
  rw [D.g_eq _ (D.lt_norm_inv hζ hζ0), inv_inv]

/-- The point at infinity always satisfies the rank condition with `ℓ = 2`. -/
theorem poleOrderCond_two : PoleOrderCond (infinityF f) (infinityG g) 0 2 := by
  have hR : (0 : ℝ) < a⁻¹ := inv_pos.mpr D.a_pos
  refine ⟨⟨fun ζ => 2 * ζ - powerSeriesSum fc 0 ζ,
      (analyticAt_const.mul analyticAt_id).sub (D.f_radius.analyticAt hR),
      D.eventually_nhdsNE.mono fun ζ ⟨hζ, hζ0⟩ => ?_⟩,
    ⟨powerSeriesSum gc 0, D.g_radius.analyticAt hR,
      D.eventually_nhdsNE.mono fun ζ ⟨hζ, hζ0⟩ => ?_⟩⟩
  · simp only [infinityF, sub_zero, D.f_inv hζ hζ0]
    field_simp
  · simp only [infinityG, sub_zero, D.g_inv hζ hζ0]
    field_simp
    ring

/-- `∞` satisfies the regular-singularity condition iff `f₀ = g₀ = g₁ = 0`. -/
theorem hasRegularCoefficients_iff :
    HasRegularCoefficients (infinityF f) (infinityG g) 0 ↔ fc 0 = 0 ∧ gc 0 = 0 ∧ gc 1 = 0 := by
  have hR : (0 : ℝ) < a⁻¹ := inv_pos.mpr D.a_pos
  have hf₁ := D.f_radius.tail
  have hg₁ := D.g_radius.tail
  have hg₂ := hg₁.tail
  constructor
  · rintro ⟨⟨F, hF, hfF⟩, ⟨G, hG, hgG⟩⟩
    -- `∑ fₛ ζ^s = ζ (2 − F(ζ))` near `0`
    have hf : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ^ 1 * (2 - F ζ) = powerSeriesSum fc 0 ζ := by
      filter_upwards [hfF, D.eventually_nhdsNE] with ζ h ⟨hζ, hζ0⟩
      rw [← h]
      simp only [infinityF, sub_zero, D.f_inv hζ hζ0]
      field_simp
      ring
    have hg : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ^ 2 * G ζ = powerSeriesSum gc 0 ζ := by
      filter_upwards [hgG, D.eventually_nhdsNE] with ζ h ⟨hζ, hζ0⟩
      rw [← h]
      simp only [infinityG, sub_zero, D.g_inv hζ hζ0]
      field_simp
    have hFt := tendsto_pow_mul_nhdsNE (H := fun ζ => 2 - F ζ)
      (continuousAt_const.sub hF.continuousAt) one_ne_zero
    have hGt := tendsto_pow_mul_nhdsNE hG.continuousAt two_ne_zero
    have hf0 : fc 0 = 0 := tendsto_nhds_unique (D.f_radius.tendsto_nhdsNE hR) (hFt.congr' hf)
    have hg0 : gc 0 = 0 := tendsto_nhds_unique (D.g_radius.tendsto_nhdsNE hR) (hGt.congr' hg)
    -- `∑ g_{s+1} ζ^s = ζ G(ζ)` near `0`
    have hg' : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ^ 1 * G ζ = powerSeriesSum (seqTail gc) 0 ζ := by
      filter_upwards [hg, D.eventually_nhdsNE] with ζ h ⟨hζ, hζ0⟩
      rw [D.g_radius.powerSeriesSum_eq_zero_add hζ, hg0, zero_add] at h
      have : ζ * (ζ ^ 1 * G ζ) = ζ * powerSeriesSum (seqTail gc) 0 ζ := by rw [← h]; ring
      exact mul_left_cancel₀ hζ0 this
    have hGt' := tendsto_pow_mul_nhdsNE hG.continuousAt one_ne_zero
    have hg1 : gc 1 = 0 :=
      tendsto_nhds_unique (hg₁.tendsto_nhdsNE hR) (hGt'.congr' hg')
    exact ⟨hf0, hg0, hg1⟩
  · rintro ⟨hf0, hg0, hg1⟩
    refine ⟨⟨fun ζ => 2 - powerSeriesSum (seqTail fc) 0 ζ,
        analyticAt_const.sub (hf₁.analyticAt hR),
        D.eventually_nhdsNE.mono fun ζ ⟨hζ, hζ0⟩ => ?_⟩,
      ⟨powerSeriesSum (seqTail (seqTail gc)) 0, hg₂.analyticAt hR,
        D.eventually_nhdsNE.mono fun ζ ⟨hζ, hζ0⟩ => ?_⟩⟩
    · simp only [infinityF, sub_zero, D.f_inv hζ hζ0, D.f_radius.powerSeriesSum_eq_zero_add hζ,
        hf0, zero_add]
      field_simp
    · simp only [infinityG, sub_zero, D.g_inv hζ hζ0, D.g_radius.powerSeriesSum_eq_zero_add hζ,
        hg₁.powerSeriesSum_eq_zero_add hζ, hg0, zero_add]
      have h1 : seqTail gc 0 = 0 := hg1
      rw [h1, zero_add]
      field_simp

/-- **DLMF §2.7(ii)**: under 2.7.7 the point at infinity has rank 1 iff at least one of
`f₀, g₀, g₁` is nonzero. -/
theorem hasRank_one_iff :
    HasRank (infinityF f) (infinityG g) 0 1 ↔ fc 0 ≠ 0 ∨ gc 0 ≠ 0 ∨ gc 1 ≠ 0 := by
  rw [HasRank, poleOrderCond_one_iff, D.hasRegularCoefficients_iff]
  simp only [D.poleOrderCond_two, true_and]
  tauto

/-- Under 2.7.7 with one of `f₀, g₀, g₁` nonzero, the point at infinity is an irregular
singularity. -/
theorem isIrregularSingularity (h : fc 0 ≠ 0 ∨ gc 0 ≠ 0 ∨ gc 1 ≠ 0) :
    IsIrregularSingularity (infinityF f) (infinityG g) 0 :=
  (D.hasRank_one_iff.mpr h).isIrregularSingularity le_rfl

end RankOneData

/-! ### 2.7.9 and 2.7.10 -/

/-- **DLMF 2.7.9**: the characteristic polynomial `λ² + f₀λ + g₀`. -/
def rankOneChar (fc gc : ℕ → ℂ) (lam : ℂ) : ℂ := lam ^ 2 + fc 0 * lam + gc 0

/-- The two roots `λ₁, λ₂` of the characteristic equation 2.7.9. -/
theorem exists_charRoots (fc gc : ℕ → ℂ) :
    ∃ l₁ l₂ : ℂ, ∀ lam, rankOneChar fc gc lam = (lam - l₁) * (lam - l₂) := by
  set d : ℂ := fc 0 ^ 2 - 4 * gc 0 with hd
  set s : ℂ := d ^ (((2 : ℕ) : ℂ)⁻¹) with hs
  have hs2 : s ^ 2 = d := cpow_nat_inv_pow d two_ne_zero
  refine ⟨(-fc 0 + s) / 2, (-fc 0 - s) / 2, fun lam => ?_⟩
  simp only [rankOneChar]
  linear_combination (1 / 4 : ℂ) * hs2

/-- **DLMF 2.7.10**: `μ = −(f₁λ + g₁)/(f₀ + 2λ)`. -/
noncomputable def rankOneMu (fc gc : ℕ → ℂ) (lam : ℂ) : ℂ :=
  -(fc 1 * lam + gc 1) / (fc 0 + 2 * lam)

theorem rankOneMu_mul {fc gc : ℕ → ℂ} {lam : ℂ} (h : fc 0 + 2 * lam ≠ 0) :
    (fc 0 + 2 * lam) * rankOneMu fc gc lam = -(fc 1 * lam + gc 1) := by
  rw [rankOneMu, mul_div_cancel₀ _ h]

/-- `f₀ + 2λ₁ = λ₁ − λ₂`: the denominator of 2.7.10 vanishes iff `λ₁ = λ₂`. -/
theorem fc0_add_two_mul_eq {fc gc : ℕ → ℂ} {l₁ l₂ : ℂ}
    (h : ∀ lam, rankOneChar fc gc lam = (lam - l₁) * (lam - l₂)) :
    fc 0 + 2 * l₁ = l₁ - l₂ ∧ fc 0 + 2 * l₂ = l₂ - l₁ := by
  have h0 := h 0
  have h1 := h 1
  simp only [rankOneChar] at h0 h1
  constructor <;> linear_combination h1 - h0

theorem fc0_add_two_mul_eq_zero_iff {fc gc : ℕ → ℂ} {l₁ l₂ : ℂ}
    (h : ∀ lam, rankOneChar fc gc lam = (lam - l₁) * (lam - l₂)) :
    fc 0 + 2 * l₁ = 0 ↔ l₁ = l₂ := by
  rw [(fc0_add_two_mul_eq h).1, sub_eq_zero]

/-- **DLMF §2.7(ii)**: `λ₁ = λ₂` iff `f₀² = 4g₀`. -/
theorem charRoots_eq_iff {fc gc : ℕ → ℂ} {l₁ l₂ : ℂ}
    (h : ∀ lam, rankOneChar fc gc lam = (lam - l₁) * (lam - l₂)) :
    l₁ = l₂ ↔ fc 0 ^ 2 = 4 * gc 0 := by
  have h0 := h 0
  have h1 := h 1
  simp only [rankOneChar] at h0 h1
  have hd : fc 0 ^ 2 - 4 * gc 0 = (l₁ - l₂) ^ 2 := by
    linear_combination (fc 0 - l₁ - l₂) * (h1 - h0) - 4 * h0
  rw [← sub_eq_zero (a := fc 0 ^ 2), hd, sq_eq_zero_iff, sub_eq_zero]

end Azurite.DLMF
