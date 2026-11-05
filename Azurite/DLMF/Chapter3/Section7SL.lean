/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18ODE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §3.7(iv): Sturm–Liouville eigenvalue problems

For a finite interval `[a, b]` and `q` continuous on `[a, b]`, 3.7.15–3.7.16 is
`IsDirichletEigenfunction` / `IsDirichletEigenvalue`. The proof uses the shooting solution `u_λ`
(`u″ = (q − λ) u`, `u(a) = 0`, `u′(a) = 1`; `slU`, built with `Section18ODE` from `q` extended by
constants, `slQ`) and its **Prüfer angle**
`θ(x) = ∫ₐˣ (u′² + (λ − q) u²)/(u² + u′²)` (`prufer`, `slTheta`).

* Prüfer theory (`IsPruferData`): `u cos θ = u′ sin θ` (`prufer_S`), so the zeros of `u` are where
  `θ ∈ πℤ` (`sin_prufer_eq_zero_iff`). `θ′ = cos² θ + μ sin² θ` (`rate_eq`), so `θ` crosses each
  multiple of `π` upwards and never returns (`prufer_lt_of_zero`, `prufer_add_pi_le`). The Sturm
  comparison is `prufer_le_of_le` and `prufer_lt_of_lt`, via `(θ₂ − θ₁) e^{−G}` with
  `G′ = (μ₂ − 1) sin(θ₁ + θ₂) sinc(θ₂ − θ₁)`.
* Simplicity: every solution with `w(a) = 0` is `w′(a) u_λ` (`eq_mul_slU`), so `λ` is an eigenvalue
  iff `u_λ(b) = 0` (`isDirichletEigenvalue_iff`), and eigenfunctions are proportional
  (`dlmf_3_7_iv_simple`).
* 3.7.17 (`dlmf_3_7_17`): `λ ↦ θ(λ, b)` is continuous (`continuous_slTheta`), strictly increasing
  (`slTheta_strictMono`) and positive. It is `< π` for `λ ≤ −max |q|` (`exists_slTheta_lt_pi`) and
  `≥ kπ` for large `λ` (`exists_slTheta_ge`, by comparison with `sin(ω(x − a))`). The eigenvalues
  are exactly the solutions of `θ(λ, b) = kπ`, `k = 1, 2, …`.
* Infinite intervals: DLMF's claims need hypotheses on `q`. For `q = 0` on `(0, ∞)` there is no
  eigenvalue (`dlmf_3_7_iv_infinite_no_eigenvalue`).

Not formalized: piecewise continuous `q`; the remark that the discretized form 3.7.13 gives a
tridiagonal problem whose entries are polynomials in `λ` (after truncating 3.7.8), the step-size
remark, and the reference (Pryce 1993).
-/

open Filter Topology Set Real

namespace Azurite.DLMF

/-! ### Slopes -/

theorem eventually_lt_right_of_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hpos : 0 < f') : ∀ᶠ y in 𝓝[>] x, f x < f y := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
    (nhdsWithin_mono x (fun y (hy : x < y) => ne_of_gt hy))
  filter_upwards [h.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with y hy hxy
  rw [slope_def_field] at hy
  have : 0 < y - x := sub_pos.mpr hxy
  have := (div_pos_iff_of_pos_right this).mp hy
  linarith

theorem eventually_lt_left_of_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hpos : 0 < f') : ∀ᶠ y in 𝓝[<] x, f y < f x := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
    (nhdsWithin_mono x (fun y (hy : y < x) => ne_of_lt hy))
  filter_upwards [h.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with y hy hxy
  rw [slope_def_field] at hy
  have h1 : y - x < 0 := sub_neg.mpr hxy
  have := (div_pos_iff.mp hy)
  rcases this with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · linarith
  · linarith

theorem sinc_mul_self (d : ℝ) : sinc d * d = sin d := by
  by_cases h : d = 0
  · simp [h]
  · rw [sinc_of_ne_zero h, div_mul_cancel₀ _ h]

theorem sin_add_mul_sin_sub (A B : ℝ) : sin (B + A) * sin (A - B) = sin A ^ 2 - sin B ^ 2 := by
  rw [sin_add, sin_sub]
  linear_combination sin A ^ 2 * sin_sq_add_cos_sq B - sin B ^ 2 * sin_sq_add_cos_sq A

/-! ### The Prüfer angle -/

/-- The rate `(u′² + μ u²)/(u² + u′²)` of the Prüfer angle of a solution of `u″ = −μ u`. -/
noncomputable def pruferRate (μ u u' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (u' x ^ 2 + μ x * u x ^ 2) / (u x ^ 2 + u' x ^ 2)

/-- The Prüfer angle `θ(x) = ∫ₐˣ (u′² + μ u²)/(u² + u′²)`: `u = ρ sin θ`, `u′ = ρ cos θ`
(`IsPruferData.prufer_S`). -/
noncomputable def prufer (μ u u' : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ t in a..x, pruferRate μ u u' t

/-- `u″ = −μ u` on `ℝ` with `u(a) = 0`, `u′(a) = 1` (and `(u, u′)` never `(0, 0)`). -/
structure IsPruferData (μ u u' : ℝ → ℝ) (a : ℝ) : Prop where
  cont : Continuous μ
  du : ∀ x, HasDerivAt u (u' x) x
  du' : ∀ x, HasDerivAt u' (-(μ x * u x)) x
  init0 : u a = 0
  init1 : u' a = 1
  ne : ∀ x, u x ^ 2 + u' x ^ 2 ≠ 0

namespace IsPruferData

variable {μ u u' : ℝ → ℝ} {a : ℝ} (h : IsPruferData μ u u' a)
include h

theorem continuous_u : Continuous u :=
  continuous_iff_continuousAt.mpr fun x => (h.du x).continuousAt

theorem continuous_u' : Continuous u' :=
  continuous_iff_continuousAt.mpr fun x => (h.du' x).continuousAt

theorem continuous_rate : Continuous (pruferRate μ u u') :=
  ((h.continuous_u'.pow 2).add (h.cont.mul (h.continuous_u.pow 2))).div
    ((h.continuous_u.pow 2).add (h.continuous_u'.pow 2)) h.ne

theorem hasDerivAt_prufer (x : ℝ) :
    HasDerivAt (prufer μ u u' a) (pruferRate μ u u' x) x :=
  (h.continuous_rate.integral_hasStrictDerivAt a x).hasDerivAt

theorem continuous_prufer : Continuous (prufer μ u u' a) :=
  continuous_iff_continuousAt.mpr fun x => (h.hasDerivAt_prufer x).continuousAt

omit h in
theorem prufer_self : prufer μ u u' a a = 0 := intervalIntegral.integral_same

/-- `u cos θ = u′ sin θ`, i.e. `(u, u′)` is parallel to `(sin θ, cos θ)`. -/
theorem prufer_S {x : ℝ} (hx : a ≤ x) :
    u x * cos (prufer μ u u' a x) - u' x * sin (prufer μ u u' a x) = 0 := by
  set θ := prufer μ u u' a
  set S : ℝ → ℝ := fun y => u y * cos (θ y) - u' y * sin (θ y)
  set c : ℝ → ℝ := fun y => (1 - μ y) * u y * u' y / (u y ^ 2 + u' y ^ 2)
  have hS : ∀ y, HasDerivAt S (c y * S y) y := by
    intro y
    have hθ := h.hasDerivAt_prufer y
    have d := ((h.du y).mul hθ.cos).sub ((h.du' y).mul hθ.sin)
    refine d.congr_deriv ?_
    have hne := h.ne y
    simp only [S, c, pruferRate]
    field_simp
    ring
  have hc : Continuous c :=
    (((continuous_const.sub h.cont).mul h.continuous_u).mul h.continuous_u').div
      ((h.continuous_u.pow 2).add (h.continuous_u'.pow 2)) h.ne
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a x) hc.continuousOn
  have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := S)
    (f' := fun y => c y * S y) (K := K) (a := a) (b := x)
    (fun y _ => (hS y).continuousAt.continuousWithinAt) (fun y _ => (hS y).hasDerivWithinAt)
    (by simp [S, θ, prufer_self, h.init0]) (fun y hy => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK y (Ico_subset_Icc_self hy)) (norm_nonneg _))
    x ⟨hx, le_rfl⟩
  exact this

/-- **Zeros of `u` are the points where `θ ∈ πℤ`.** -/
theorem sin_prufer_eq_zero_iff {x : ℝ} (hx : a ≤ x) :
    sin (prufer μ u u' a x) = 0 ↔ u x = 0 := by
  have hS := h.prufer_S hx
  have hp := sin_sq_add_cos_sq (prufer μ u u' a x)
  constructor
  · intro hs
    rw [hs, mul_zero, sub_zero] at hS
    have hc : cos (prufer μ u u' a x) ≠ 0 := by
      intro hc; rw [hs, hc] at hp; norm_num at hp
    exact (mul_eq_zero.mp hS).resolve_right hc
  · intro hu
    rw [hu, zero_mul, zero_sub, neg_eq_zero] at hS
    have hu' : u' x ≠ 0 := by
      intro h0; exact h.ne x (by rw [hu, h0]; ring)
    exact (mul_eq_zero.mp hS).resolve_left hu'

/-- The Prüfer equation `θ′ = cos² θ + μ sin² θ`. -/
theorem rate_eq {x : ℝ} (hx : a ≤ x) :
    pruferRate μ u u' x = cos (prufer μ u u' a x) ^ 2 + μ x * sin (prufer μ u u' a x) ^ 2 := by
  have hS := h.prufer_S hx
  set s := sin (prufer μ u u' a x)
  set c := cos (prufer μ u u' a x)
  have hp : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
  set R := u' x * c + u x * s
  have e1 : u x = R * s := by linear_combination c * hS - u x * hp
  have e2 : u' x = R * c := by linear_combination (-s) * hS - u' x * hp
  have hne := h.ne x
  unfold pruferRate
  rw [div_eq_iff hne, e1, e2]
  linear_combination (-(R ^ 2) * (c ^ 2 + μ x * s ^ 2)) * hp

theorem rate_of_zero {x : ℝ} (hu : u x = 0) : pruferRate μ u u' x = 1 := by
  have hne := h.ne x
  rw [hu] at hne
  simp only [pruferRate, hu]
  field_simp
  ring

/-- **`θ` crosses each multiple of `π` upwards and never returns**: after a zero `x₀ ≥ a` of `u`,
`θ(x) > θ(x₀)`. -/
theorem prufer_lt_of_zero {x₀ : ℝ} (hx₀ : a ≤ x₀) (hz : u x₀ = 0) {x₁ : ℝ} (h01 : x₀ < x₁) :
    prufer μ u u' a x₀ < prufer μ u u' a x₁ := by
  set θ := prufer μ u u' a
  have hθc := h.continuous_prufer
  have hloc := eventually_lt_right_of_hasDerivAt (h.hasDerivAt_prufer x₀)
    (by rw [h.rate_of_zero hz]; norm_num)
  obtain ⟨ε', hε'0, hε'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' h01).mp hloc
  have hε'0' : x₀ < ε' := hε'0
  by_contra hcon
  push Not at hcon
  set ε := (x₀ + min ε' x₁) / 2
  have hm1 := min_le_left ε' x₁
  have hm2 := min_le_right ε' x₁
  have hm3 : x₀ < min ε' x₁ := lt_min hε'0' h01
  have hε : x₀ < ε := by simp only [ε]; linarith
  have hεx : ε < x₁ := by simp only [ε]; linarith
  have hθε : θ x₀ < θ ε := hε' ⟨hε, by simp only [ε]; linarith⟩
  set K := {y ∈ Icc ε x₁ | θ y ≤ θ x₀}
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le hθc continuous_const)
  have hKne : K.Nonempty := ⟨x₁, ⟨hεx.le, le_rfl⟩, hcon⟩
  set x₂ := sInf K
  have hx₂K : x₂ ∈ K := hKc.sInf_mem hKne
  have hmin : ∀ y ∈ K, x₂ ≤ y := fun y hy => csInf_le hKc.bddBelow hy
  have hx₂ε : ε < x₂ := by
    rcases hx₂K.1.1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso; have := hx₂K.2; rw [← h1] at this; linarith
  -- `θ(x₂) = θ(x₀)`
  have heq : θ x₂ = θ x₀ := by
    refine le_antisymm hx₂K.2 ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc' hx₂ε.le hθc.continuousOn
      ⟨hlt.le, hθε.le⟩
    have : x₂ ≤ y := hmin y ⟨⟨hy.1, hy.2.trans hx₂K.1.2⟩, hyv.le⟩
    have hyx : y = x₂ := le_antisymm hy.2 this
    rw [hyx] at hyv
    linarith
  -- `u(x₂) = 0`, so `θ′(x₂) = 1`
  have hzx₂ : u x₂ = 0 := by
    rw [← h.sin_prufer_eq_zero_iff (by linarith), show prufer μ u u' a x₂ = θ x₂ from rfl, heq]
    exact (h.sin_prufer_eq_zero_iff hx₀).mpr hz
  have hleft := eventually_lt_left_of_hasDerivAt (h.hasDerivAt_prufer x₂)
    (by rw [h.rate_of_zero hzx₂]; norm_num)
  obtain ⟨y, hy1, hy2⟩ := ((hleft.and (Ioo_mem_nhdsLT hx₂ε)).exists)
  -- on `(ε, x₂)`, `θ > θ(x₀)`
  have : θ x₀ < θ y := by
    by_contra hle
    push Not at hle
    have := hmin y ⟨⟨hy2.1.le, hy2.2.le.trans hx₂K.1.2⟩, hle⟩
    linarith [hy2.2]
  have hy1' : θ y < θ x₂ := hy1
  rw [heq] at hy1'
  linarith

theorem prufer_pos {x : ℝ} (hx : a < x) : 0 < prufer μ u u' a x := by
  have := h.prufer_lt_of_zero le_rfl h.init0 hx
  rwa [prufer_self] at this

/-- Between consecutive zeros `x₀ < x₁` (`x₀ ≥ a`) of `u`, `θ` grows by at least `π`. -/
theorem prufer_add_pi_le {x₀ x₁ : ℝ} (hx₀ : a ≤ x₀) (h01 : x₀ < x₁) (hz₀ : u x₀ = 0)
    (hz₁ : u x₁ = 0) : prufer μ u u' a x₀ + π ≤ prufer μ u u' a x₁ := by
  obtain ⟨n₀, hn₀⟩ := sin_eq_zero_iff.mp ((h.sin_prufer_eq_zero_iff hx₀).mpr hz₀)
  obtain ⟨n₁, hn₁⟩ := sin_eq_zero_iff.mp ((h.sin_prufer_eq_zero_iff (hx₀.trans h01.le)).mpr hz₁)
  have hlt := h.prufer_lt_of_zero hx₀ hz₀ h01
  rw [← hn₀, ← hn₁] at hlt ⊢
  have hn : n₀ < n₁ := by
    by_contra hc; push Not at hc
    have : (n₁ : ℝ) ≤ n₀ := by exact_mod_cast hc
    nlinarith [pi_pos]
  have : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast hn
  nlinarith [pi_pos]

end IsPruferData

/-! ### Comparison of Prüfer angles -/

section Comparison

variable {μ₁ u₁ u₁' μ₂ u₂ u₂' : ℝ → ℝ} {a : ℝ} (h₁ : IsPruferData μ₁ u₁ u₁' a)
  (h₂ : IsPruferData μ₂ u₂ u₂' a)
include h₁ h₂

/-- The comparison function `D = (θ₂ − θ₁) e^{−G}`, `G′ = (μ₂ − 1) sin(θ₁ + θ₂) sinc(θ₂ − θ₁)`,
has derivative `(μ₂ − μ₁) sin² θ₁ e^{−G}` on `[a, ∞)`. -/
theorem prufer_compare_core :
    ∃ D E : ℝ → ℝ, Continuous D ∧ (∀ y, 0 < E y) ∧ D a = 0 ∧
      (∀ y, D y = (prufer μ₂ u₂ u₂' a y - prufer μ₁ u₁ u₁' a y) * E y) ∧
      ∀ y, a ≤ y → HasDerivAt D ((μ₂ y - μ₁ y) * sin (prufer μ₁ u₁ u₁' a y) ^ 2 * E y) y := by
  set θ₁ := prufer μ₁ u₁ u₁' a
  set θ₂ := prufer μ₂ u₂ u₂' a
  set g : ℝ → ℝ := fun y => (μ₂ y - 1) * sin (θ₁ y + θ₂ y) * sinc (θ₂ y - θ₁ y)
  have hg : Continuous g :=
    ((h₂.cont.sub continuous_const).mul
      (continuous_sin.comp (h₁.continuous_prufer.add h₂.continuous_prufer))).mul
      (continuous_sinc.comp (h₂.continuous_prufer.sub h₁.continuous_prufer))
  set G : ℝ → ℝ := fun y => ∫ t in a..y, g t
  have hG : ∀ y, HasDerivAt G (g y) y := fun y => (hg.integral_hasStrictDerivAt a y).hasDerivAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun y => (hG y).continuousAt
  refine ⟨fun y => (θ₂ y - θ₁ y) * exp (-G y), fun y => exp (-G y),
    (h₂.continuous_prufer.sub h₁.continuous_prufer).mul hGc.neg.rexp, fun y => exp_pos _, ?_,
    fun y => rfl, ?_⟩
  · simp [θ₁, θ₂, IsPruferData.prufer_self]
  · intro y hy
    have d := ((h₂.hasDerivAt_prufer y).sub (h₁.hasDerivAt_prufer y)).mul (hG y).neg.exp
    refine d.congr_deriv ?_
    rw [h₁.rate_eq hy, h₂.rate_eq hy]
    have e1 := sinc_mul_self (θ₂ y - θ₁ y)
    have e2 := sin_add_mul_sin_sub (θ₂ y) (θ₁ y)
    have p1 := sin_sq_add_cos_sq (θ₁ y)
    have p2 := sin_sq_add_cos_sq (θ₂ y)
    simp only [g, Pi.sub_apply, Pi.neg_apply]
    linear_combination exp (-G y) *
      (p2 - p1 - (μ₂ y - 1) * sin (θ₁ y + θ₂ y) * e1 - (μ₂ y - 1) * e2)

/-- **Sturm comparison** for Prüfer angles: `μ₁ ≤ μ₂` gives `θ₁ ≤ θ₂` on `[a, ∞)`. -/
theorem prufer_le_of_le (hμ : ∀ x, μ₁ x ≤ μ₂ x) {x : ℝ} (hx : a ≤ x) :
    prufer μ₁ u₁ u₁' a x ≤ prufer μ₂ u₂ u₂' a x := by
  obtain ⟨D, E, hDc, hE, hDa, hDdef, hD⟩ := prufer_compare_core h₁ h₂
  have hmono : MonotoneOn D (Ici a) := monotoneOn_of_deriv_nonneg (convex_Ici a)
    hDc.continuousOn
    (fun y hy => (hD y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    fun y hy => by
      rw [(hD y (interior_subset hy)).deriv]
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr (hμ y)) (sq_nonneg _)) (hE y).le
  have := hmono self_mem_Ici hx hx
  rw [hDa, hDdef] at this
  have := hE x
  nlinarith

/-- Strict comparison: `μ₁ + δ ≤ μ₂` with `δ > 0` gives `θ₁ < θ₂` on `(a, ∞)`. -/
theorem prufer_lt_of_lt {δ : ℝ} (hδ : 0 < δ) (hμ : ∀ x, μ₁ x + δ ≤ μ₂ x) {x : ℝ} (hx : a < x) :
    prufer μ₁ u₁ u₁' a x < prufer μ₂ u₂ u₂' a x := by
  obtain ⟨D, E, hDc, hE, hDa, hDdef, hD⟩ := prufer_compare_core h₁ h₂
  have hmono : MonotoneOn D (Ici a) := monotoneOn_of_deriv_nonneg (convex_Ici a)
    hDc.continuousOn
    (fun y hy => (hD y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    fun y hy => by
      rw [(hD y (interior_subset hy)).deriv]
      exact mul_nonneg (mul_nonneg (by linarith [hμ y]) (sq_nonneg _)) (hE y).le
  have hc : ∀ᶠ y in 𝓝 a, prufer μ₁ u₁ u₁' a y < π :=
    h₁.continuous_prufer.continuousAt.eventually_lt continuousAt_const
      (by rw [IsPruferData.prufer_self]; exact pi_pos)
  obtain ⟨ε, hε, hεc⟩ := Metric.eventually_nhds_iff.mp hc
  set m := min x (a + ε / 2)
  have ham : a < m := lt_min hx (by linarith)
  have hstrict : StrictMonoOn D (Icc a m) := strictMonoOn_of_deriv_pos (convex_Icc a m)
    hDc.continuousOn fun y hy => by
      rw [interior_Icc] at hy
      rw [(hD y hy.1.le).deriv]
      have hpos := h₁.prufer_pos hy.1
      have hlt : prufer μ₁ u₁ u₁' a y < π := hεc (by
        rw [Real.dist_eq, abs_of_pos (by linarith [hy.1])]
        linarith [hy.2, min_le_right x (a + ε / 2)])
      have hs := sin_pos_of_pos_of_lt_pi hpos hlt
      exact mul_pos (mul_pos (by linarith [hμ y]) (pow_pos hs 2)) (hE y)
  have h1 := hstrict ⟨le_rfl, ham.le⟩ ⟨ham.le, le_rfl⟩ ham
  have h2 := hmono (show a ≤ m from ham.le) (show a ≤ x from hx.le) (min_le_left _ _)
  rw [hDa] at h1
  have h3 : 0 < D x := lt_of_lt_of_le h1 h2
  rw [hDdef] at h3
  have := hE x
  nlinarith

end Comparison

/-! ### Uniqueness on `[a, b]` -/

/-- Uniqueness for `w″ = W w` on `[a, b]` with data at `a`. -/
theorem ode2_eq_zero_Icc {W w w' : ℝ → ℝ} {K a b : ℝ} (hK : ∀ x ∈ Icc a b, |W x| ≤ K)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Icc a b, HasDerivAt w' (W x * w x) x)
    (h0 : w a = 0) (h1 : w' a = 0) : ∀ x ∈ Icc a b, w x = 0 := by
  intro x hx
  set Y : ℝ → ℝ × ℝ := fun s => (w s, w' s)
  have hY : ∀ s ∈ Icc a b, HasDerivAt Y (w' s, W s * w s) s := fun s hs =>
    (hw s hs).prodMk (hw' s hs)
  have hsub : ∀ s ∈ Icc a x, s ∈ Icc a b := fun s hs => ⟨hs.1, hs.2.trans hx.2⟩
  have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := Y)
    (f' := fun s => (w' s, W s * w s)) (K := max 1 K) (a := a) (b := x)
    (fun s hs => (hY s (hsub s hs)).continuousAt.continuousWithinAt)
    (fun s hs => (hY s (hsub s (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (by simp [Y, h0, h1]) fun s hs => by
      simp only [Prod.norm_def, Real.norm_eq_abs, Y]
      have hKs := hK s (hsub s (Ico_subset_Icc_self hs))
      refine max_le ?_ ?_
      · calc |w' s| ≤ max |w s| |w' s| := le_max_right _ _
          _ ≤ max 1 K * max |w s| |w' s| :=
            le_mul_of_one_le_left (by positivity) (le_max_left _ _)
      · rw [abs_mul]
        calc |W s| * |w s| ≤ K * max |w s| |w' s| := by
              gcongr
              · exact (abs_nonneg _).trans hKs
              · exact le_max_left _ _
          _ ≤ max 1 K * max |w s| |w' s| := by gcongr; exact le_max_right _ _
  exact congrArg Prod.fst (h x ⟨hx.1, le_rfl⟩)

/-! ### The shooting solutions -/

section Shooting

variable {q : ℝ → ℝ} {a b : ℝ}

/-- `q` extended from `[a, b]` to `ℝ` by constants. -/
noncomputable def slQ (q : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℝ := q (max a (min b x))

theorem slQ_eq {x : ℝ} (hx : x ∈ Icc a b) : slQ q a b x = q x := by
  simp [slQ, min_eq_right hx.2, max_eq_right hx.1]

theorem mem_Icc_clamp (hab : a ≤ b) (x : ℝ) : max a (min b x) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem continuous_slQ (hab : a ≤ b) (hq : ContinuousOn q (Icc a b)) : Continuous (slQ q a b) :=
  hq.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    (mem_Icc_clamp hab)

theorem exists_bound_slQ (hab : a ≤ b) (hq : ContinuousOn q (Icc a b)) :
    ∃ M, 0 ≤ M ∧ ∀ x, |slQ q a b x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have := hM _ (mem_Icc_clamp hab x)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- `λ` clamped to `[−L, L]`. -/
noncomputable def slClamp (L l : ℝ) : ℝ := max (-L) (min l L)

theorem slClamp_eq {L l : ℝ} (hl : |l| ≤ L) : slClamp L l = l := by
  rw [abs_le] at hl
  simp [slClamp, min_eq_left hl.2, max_eq_right hl.1]

theorem continuous_slClamp (L : ℝ) : Continuous (slClamp L) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem abs_slClamp_le {L : ℝ} (hL : 0 ≤ L) (l : ℝ) : |slClamp L l| ≤ L := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- The potential `q − λ` of 3.7.15 with `λ` clamped. -/
noncomputable def slV (q : ℝ → ℝ) (a b L l x : ℝ) : ℝ := slQ q a b x - slClamp L l

/-- The solution of `u″ = (q − λ) u`, `u(a) = 0`, `u′(a) = 1` (clamped `λ`). -/
noncomputable def slUL (q : ℝ → ℝ) (a b L l x : ℝ) : ℝ :=
  odeSol (slV q a b L) (fun _ => 0) (fun _ => 1) a l x

noncomputable def slUDL (q : ℝ → ℝ) (a b L l x : ℝ) : ℝ :=
  odeSolD (slV q a b L) (fun _ => 0) (fun _ => 1) a l x

/-- The shooting solution `u_λ`: `u″ = (q − λ) u`, `u(a) = 0`, `u′(a) = 1`. -/
noncomputable def slU (q : ℝ → ℝ) (a b l x : ℝ) : ℝ := slUL q a b (|l| + 1) l x

/-- `u_λ′`. -/
noncomputable def slUD (q : ℝ → ℝ) (a b l x : ℝ) : ℝ := slUDL q a b (|l| + 1) l x

variable (hab : a ≤ b) (hq : ContinuousOn q (Icc a b))
include hab hq

theorem slUL_spec {L : ℝ} (hL : 0 ≤ L) :
    Continuous (fun p : ℝ × ℝ => slUL q a b L p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => slUDL q a b L p.1 p.2) ∧
      ∀ l x, HasDerivAt (slUL q a b L l) (slUDL q a b L l x) x ∧
        HasDerivAt (slUDL q a b L l) (slV q a b L l x * slUL q a b L l x) x ∧
        slUL q a b L l a = 0 ∧ slUDL q a b L l a = 1 := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_slQ hab hq
  have hV : Continuous fun p : ℝ × ℝ => slV q a b L p.1 p.2 :=
    ((continuous_slQ hab hq).comp continuous_snd).sub ((continuous_slClamp L).comp continuous_fst)
  have hVb : ∀ κ t, |slV q a b L κ t| ≤ M + L := fun κ t => by
    simp only [slV]
    exact (abs_sub _ _).trans (add_le_add (hM t) (abs_slClamp_le hL κ))
  have h0 : ∀ κ, |(fun _ : ℝ => (0 : ℝ)) κ| ≤ 1 := fun _ => by norm_num
  have h1 : ∀ κ, |(fun _ : ℝ => (1 : ℝ)) κ| ≤ 1 := fun _ => by norm_num
  refine ⟨continuous_odeSol a hV continuous_const continuous_const hVb h0 h1,
    continuous_odeSolD a hV continuous_const continuous_const hVb h0 h1, fun l x =>
    ⟨hasDerivAt_odeSol a hV continuous_const continuous_const hVb h0 h1 l x,
      hasDerivAt_odeSolD a hV continuous_const continuous_const hVb h0 h1 l x,
      odeSol_init a hV continuous_const continuous_const hVb h0 h1 l, odeSolD_init a l⟩⟩

/-- The clamped solutions agree with `u_λ` whenever `|λ| ≤ L`. -/
theorem slUL_eq_slU {L l : ℝ} (hl : |l| ≤ L) : slUL q a b L l = slU q a b l ∧
    slUDL q a b L l = slUD q a b l := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_slQ hab hq
  have hL : 0 ≤ L := (abs_nonneg l).trans hl
  have hL' : (0 : ℝ) ≤ |l| + 1 := by positivity
  obtain ⟨-, -, h1⟩ := slUL_spec hab hq hL
  obtain ⟨-, -, h2⟩ := slUL_spec hab hq hL'
  have c1 : slClamp L l = l := slClamp_eq hl
  have c2 : slClamp (|l| + 1) l = l := slClamp_eq (by linarith)
  have hW : ∀ x, |slQ q a b x - l| ≤ M + |l| := fun x => (abs_sub _ _).trans (by linarith [hM x])
  have hz := ode2_eq_zero (W := fun x => slQ q a b x - l)
    (w := fun x => slUL q a b L l x - slUL q a b (|l| + 1) l x)
    (w' := fun x => slUDL q a b L l x - slUDL q a b (|l| + 1) l x) hW
    (fun x => (h1 l x).1.sub (h2 l x).1)
    (fun x => ((h1 l x).2.1.sub (h2 l x).2.1).congr_deriv (by simp only [slV, c1, c2]; ring))
    (x1 := a) (by simp [(h1 l a).2.2.1, (h2 l a).2.2.1])
    (by simp [(h1 l a).2.2.2, (h2 l a).2.2.2])
  have e1 : slUL q a b L l = slU q a b l := funext fun x => sub_eq_zero.mp (hz x)
  refine ⟨e1, funext fun x => ?_⟩
  have d1 := (h1 l x).1
  have d2 := (h2 l x).1
  rw [e1] at d1
  exact d1.unique d2

theorem continuous_slU :
    Continuous (fun p : ℝ × ℝ => slU q a b p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => slUD q a b p.1 p.2) := by
  constructor <;> refine continuous_iff_continuousAt.mpr fun p => ?_ <;>
  · set L := |p.1| + 1
    obtain ⟨hc1, hc2, -⟩ := slUL_spec hab hq (show (0 : ℝ) ≤ L by positivity)
    have hev : ∀ᶠ r in 𝓝 p, |r.1| ≤ L :=
      (((continuous_abs.comp continuous_fst).continuousAt (x := p)).eventually_lt
        continuousAt_const (by simp [L])).mono fun r hr => hr.le
    first
    | exact hc1.continuousAt.congr (hev.mono fun r hr => congrFun (slUL_eq_slU hab hq hr).1 r.2)
    | exact hc2.continuousAt.congr (hev.mono fun r hr => congrFun (slUL_eq_slU hab hq hr).2 r.2)

/-- `u_λ` is Prüfer data for `μ = λ − q`. -/
theorem isPruferData_slU (l : ℝ) :
    IsPruferData (fun x => l - slQ q a b x) (slU q a b l) (slUD q a b l) a := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_slQ hab hq
  obtain ⟨-, -, h⟩ := slUL_spec hab hq (show (0 : ℝ) ≤ |l| + 1 by positivity)
  have c : slClamp (|l| + 1) l = l := slClamp_eq (by linarith)
  have hdu : ∀ x, HasDerivAt (slU q a b l) (slUD q a b l x) x := fun x => (h l x).1
  have hdu' : ∀ x, HasDerivAt (slUD q a b l) ((slQ q a b x - l) * slU q a b l x) x :=
    fun x => (h l x).2.1.congr_deriv (by simp only [slV, c]; rfl)
  refine ⟨continuous_const.sub (continuous_slQ hab hq), hdu,
    fun x => (hdu' x).congr_deriv (by ring), (h l a).2.2.1, (h l a).2.2.2, fun x hx => ?_⟩
  have hs1 := sq_nonneg (slU q a b l x)
  have hs2 := sq_nonneg (slUD q a b l x)
  have hu0 : slU q a b l x = 0 := by nlinarith
  have hu1 : slUD q a b l x = 0 := by nlinarith
  have hz := ode2_eq_zero (W := fun x => slQ q a b x - l) (w := slU q a b l)
    (w' := slUD q a b l) (K := M + |l|) (fun y => (abs_sub _ _).trans (by linarith [hM y]))
    hdu hdu' hu0 hu1
  have : slU q a b l = fun _ => 0 := funext hz
  have hd := hdu a
  rw [this] at hd
  have := hd.unique (hasDerivAt_const a (0 : ℝ))
  have h1 : slUD q a b l a = 1 := (h l a).2.2.2
  rw [h1] at this
  norm_num at this

end Shooting

/-! ### The comparison problem `u″ = −ω² u` -/

theorem isPruferData_sin {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    IsPruferData (fun _ => ω ^ 2) (fun x => sin (ω * (x - a)) / ω) (fun x => cos (ω * (x - a)))
      a := by
  have hω' := hω.ne'
  have hlin : ∀ x, HasDerivAt (fun x => ω * (x - a)) ω x := fun x => by
    simpa using ((hasDerivAt_id x).sub_const a).const_mul ω
  refine ⟨continuous_const, fun x => ((hlin x).sin.div_const ω).congr_deriv (by field_simp),
    fun x => (hlin x).cos.congr_deriv (by field_simp), by simp, by simp, fun x h0 => ?_⟩
  have hp := sin_sq_add_cos_sq (ω * (x - a))
  have h1 := sq_nonneg (sin (ω * (x - a)) / ω)
  have h2 := sq_nonneg (cos (ω * (x - a)))
  have hc : cos (ω * (x - a)) ^ 2 = 0 := by linarith
  have hs : (sin (ω * (x - a)) / ω) ^ 2 = 0 := by linarith
  rw [div_pow, div_eq_zero_iff] at hs
  rcases hs with hs | hs
  · rw [hs, hc] at hp; norm_num at hp
  · exact absurd hs (pow_ne_zero 2 hω')

theorem prufer_sin_ge {ω : ℝ} (hω : 0 < ω) (a : ℝ) (k : ℕ) :
    (k : ℝ) * π ≤ prufer (fun _ => ω ^ 2) (fun x => sin (ω * (x - a)) / ω)
      (fun x => cos (ω * (x - a))) a (a + k * π / ω) := by
  have h := isPruferData_sin hω a
  have hz : ∀ j : ℕ, sin (ω * (a + j * π / ω - a)) / ω = 0 := fun j => by
    rw [show ω * (a + j * π / ω - a) = j * π by field_simp; ring, sin_nat_mul_pi, zero_div]
  induction k with
  | zero => simp [IsPruferData.prufer_self]
  | succ k ih =>
    have := h.prufer_add_pi_le (x₀ := a + k * π / ω) (x₁ := a + (k + 1 : ℕ) * π / ω)
      (by have := pi_pos; have : 0 ≤ (k : ℝ) * π / ω := by positivity
          linarith) (by push_cast; gcongr; linarith) (hz k) (hz (k + 1))
    push_cast at this ⊢
    linarith

/-! ### Eigenvalues and eigenfunctions -/

/-- **DLMF 3.7.15–3.7.16** on a finite interval `[a, b]`: `w` is a nontrivial solution of
`w″ + (λ − q(x)) w = 0` on `[a, b]` with `w(a) = w(b) = 0`. -/
def IsDirichletEigenfunction (q : ℝ → ℝ) (a b l : ℝ) (w : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc a b, HasDerivAt w (deriv w x) x ∧ HasDerivAt (deriv w) (-((l - q x) * w x)) x) ∧
    w a = 0 ∧ w b = 0 ∧ ∃ x ∈ Icc a b, w x ≠ 0

/-- `λ` is an eigenvalue of 3.7.15–3.7.16. -/
def IsDirichletEigenvalue (q : ℝ → ℝ) (a b l : ℝ) : Prop :=
  ∃ w, IsDirichletEigenfunction q a b l w

/-- The Prüfer angle of the shooting solution `u_λ`. -/
noncomputable def slTheta (q : ℝ → ℝ) (a b l x : ℝ) : ℝ :=
  prufer (fun x => l - slQ q a b x) (slU q a b l) (slUD q a b l) a x

section Eigen

variable {q : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hq : ContinuousOn q (Icc a b))
include hab hq

/-- Every solution of 3.7.15 on `[a, b]` with `w(a) = 0` is `w′(a) u_λ`. -/
theorem eq_mul_slU {l : ℝ} {w : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (deriv w x) x ∧
      HasDerivAt (deriv w) (-((l - q x) * w x)) x) (h0 : w a = 0) :
    ∀ x ∈ Icc a b, w x = deriv w a * slU q a b l x := by
  have hP := isPruferData_slU hab.le hq l
  obtain ⟨M, hM0, hM⟩ := exists_bound_slQ hab.le hq
  set c := deriv w a
  have := ode2_eq_zero_Icc (W := fun x => q x - l) (w := fun x => w x - c * slU q a b l x)
    (w' := fun x => deriv w x - c * slUD q a b l x) (K := M + |l|)
    (fun x hx => by
      rw [← slQ_eq (q := q) hx]; exact (abs_sub _ _).trans (by linarith [hM x]))
    (fun x hx => (hw x hx).1.sub ((hP.du x).const_mul c))
    (fun x hx => ((hw x hx).2.sub ((hP.du' x).const_mul c)).congr_deriv
      (by rw [slQ_eq (q := q) hx]; ring))
    (by simp [h0, hP.init0]) (by simp [hP.init1, c])
  intro x hx
  linear_combination this x hx

theorem exists_slU_ne_zero (l : ℝ) : ∃ x ∈ Ioo a b, 0 < slU q a b l x := by
  have hP := isPruferData_slU hab.le hq l
  have hev := eventually_lt_right_of_hasDerivAt (hP.du a) (by rw [hP.init1]; norm_num)
  obtain ⟨y, hy1, hy2⟩ := (hev.and (Ioo_mem_nhdsGT hab)).exists
  exact ⟨y, hy2, by rw [hP.init0] at hy1; exact hy1⟩

theorem isDirichletEigenfunction_slU {l : ℝ} (hb : slU q a b l b = 0) :
    IsDirichletEigenfunction q a b l (slU q a b l) := by
  have hP := isPruferData_slU hab.le hq l
  have hd : deriv (slU q a b l) = slUD q a b l := funext fun x => (hP.du x).deriv
  obtain ⟨x, hx, hx0⟩ := exists_slU_ne_zero hab hq l
  refine ⟨fun x hx => ?_, hP.init0, hb, x, Ioo_subset_Icc_self hx, hx0.ne'⟩
  rw [hd]
  refine ⟨hP.du x, ?_⟩
  have := hP.du' x
  simp only [slQ_eq hx] at this
  exact this

/-- **DLMF §3.7(iv)**: `λ` is an eigenvalue iff the shooting solution vanishes at `b`. -/
theorem isDirichletEigenvalue_iff (l : ℝ) :
    IsDirichletEigenvalue q a b l ↔ slU q a b l b = 0 := by
  constructor
  · rintro ⟨w, hw, h0, hb, x, hx, hwx⟩
    have he := eq_mul_slU hab hq hw h0
    have hc : deriv w a ≠ 0 := fun hc => hwx (by rw [he x hx, hc, zero_mul])
    rw [he b ⟨hab.le, le_rfl⟩] at hb
    exact (mul_eq_zero.mp hb).resolve_left hc
  · intro hb
    exact ⟨_, isDirichletEigenfunction_slU hab hq hb⟩

/-- **DLMF §3.7(iv)**: "The eigenvalues `λ_k` are simple, that is, there is only one
corresponding eigenfunction (apart from a normalization factor)". -/
theorem dlmf_3_7_iv_simple {l : ℝ} {w₁ w₂ : ℝ → ℝ} (h₁ : IsDirichletEigenfunction q a b l w₁)
    (h₂ : IsDirichletEigenfunction q a b l w₂) : ∃ c : ℝ, ∀ x ∈ Icc a b, w₂ x = c * w₁ x := by
  have e₁ := eq_mul_slU hab hq h₁.1 h₁.2.1
  have e₂ := eq_mul_slU hab hq h₂.1 h₂.2.1
  obtain ⟨x, hx, hwx⟩ := h₁.2.2.2
  have hc : deriv w₁ a ≠ 0 := fun hc => hwx (by rw [e₁ x hx, hc, zero_mul])
  refine ⟨deriv w₂ a / deriv w₁ a, fun y hy => ?_⟩
  rw [e₁ y hy, e₂ y hy]
  field_simp

theorem isDirichletEigenvalue_iff_sin (l : ℝ) :
    IsDirichletEigenvalue q a b l ↔ sin (slTheta q a b l b) = 0 := by
  rw [isDirichletEigenvalue_iff hab hq, slTheta,
    (isPruferData_slU hab.le hq l).sin_prufer_eq_zero_iff hab.le]

theorem slTheta_strictMono : StrictMono fun l => slTheta q a b l b := fun l₁ l₂ h12 =>
  prufer_lt_of_lt (isPruferData_slU hab.le hq l₁) (isPruferData_slU hab.le hq l₂)
    (sub_pos.mpr h12) (fun x => by linarith) hab

theorem continuous_slTheta : Continuous fun l => slTheta q a b l b := by
  obtain ⟨hU, hD⟩ := continuous_slU hab.le hq
  have hf : Continuous (Function.uncurry fun l t =>
      pruferRate (fun x => l - slQ q a b x) (slU q a b l) (slUD q a b l) t) := by
    show Continuous fun p : ℝ × ℝ => (slUD q a b p.1 p.2 ^ 2 +
      (p.1 - slQ q a b p.2) * slU q a b p.1 p.2 ^ 2) /
      (slU q a b p.1 p.2 ^ 2 + slUD q a b p.1 p.2 ^ 2)
    exact ((hD.pow 2).add ((continuous_fst.sub ((continuous_slQ hab.le hq).comp
      continuous_snd)).mul (hU.pow 2))).div ((hU.pow 2).add (hD.pow 2))
      fun p => (isPruferData_slU hab.le hq p.1).ne p.2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := a) hf continuous_const

theorem slTheta_pos (l : ℝ) : 0 < slTheta q a b l b :=
  (isPruferData_slU hab.le hq l).prufer_pos hab

/-- For `λ ≤ −max |q|`, `u_λ` has no zero in `(a, b]`, so `θ(b) < π`. -/
theorem exists_slTheta_lt_pi : ∃ l, slTheta q a b l b < π := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_slQ hab.le hq
  set l := -M
  have hP := isPruferData_slU hab.le hq l
  set u := slU q a b l
  set u' := slUD q a b l
  have hF : Monotone fun x => u x * u' x := monotone_of_hasDerivAt_nonneg
    (fun x => (hP.du x).mul (hP.du' x)) fun x => by
      simp only [Pi.zero_apply]
      have := hM x
      have := abs_le.mp this
      have h1 : 0 ≤ (slQ q a b x - l) * u x ^ 2 :=
        mul_nonneg (by simp only [l]; linarith) (sq_nonneg _)
      nlinarith [sq_nonneg (u' x)]
  have hF0 : ∀ x, a ≤ x → 0 ≤ u x * u' x := fun x hx => by
    have := hF hx
    simp only [hP.init0, zero_mul] at this
    exact this
  have hG : MonotoneOn (fun x => u x * u x) (Ici a) := monotoneOn_of_deriv_nonneg
    (convex_Ici a)
    (fun x _ => ((hP.du x).mul (hP.du x)).continuousAt.continuousWithinAt)
    (fun x _ => ((hP.du x).mul (hP.du x)).differentiableAt.differentiableWithinAt) fun x hx => by
      have hd : HasDerivAt (fun y => u y * u y) (u' x * u x + u x * u' x) x :=
        (hP.du x).mul (hP.du x)
      rw [hd.deriv]
      have := hF0 x (interior_subset hx)
      nlinarith
  have hnz : ∀ x ∈ Ioc a b, u x ≠ 0 := by
    intro x hx hux
    obtain ⟨y, hy1, hy2⟩ := ((eventually_lt_right_of_hasDerivAt (hP.du a)
      (by rw [hP.init1]; norm_num)).and (Ioo_mem_nhdsGT hx.1)).exists
    rw [hP.init0] at hy1
    have := hG (show a ≤ y from hy2.1.le) (show a ≤ x from hx.1.le) hy2.2.le
    simp only [hux] at this
    nlinarith
  refine ⟨l, ?_⟩
  by_contra hcon
  push Not at hcon
  have hθ := hP.continuous_prufer
  obtain ⟨x, hx, hxπ⟩ := intermediate_value_Icc hab.le hθ.continuousOn
    ⟨by rw [IsPruferData.prufer_self]; exact pi_pos.le, hcon⟩
  have hsx : sin (prufer (fun x => l - slQ q a b x) u u' a x) = 0 := by rw [hxπ, sin_pi]
  have hux := (hP.sin_prufer_eq_zero_iff hx.1).mp hsx
  have hxa : x ≠ a := by
    rintro rfl
    rw [IsPruferData.prufer_self] at hxπ
    exact pi_ne_zero hxπ.symm
  exact hnz x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩ hux

/-- For large `λ`, `θ(b) ≥ kπ`: compare with `u″ = −ω² u`, `ω = kπ/(b − a)`. -/
theorem exists_slTheta_ge (k : ℕ) : ∃ l, (k : ℝ) * π ≤ slTheta q a b l b := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, by simpa using (slTheta_pos hab hq 0).le⟩
  obtain ⟨M, hM0, hM⟩ := exists_bound_slQ hab.le hq
  set ω := k * π / (b - a)
  have hω : 0 < ω := by have := pi_pos; have : (0 : ℝ) < k := by exact_mod_cast hk
                        exact div_pos (by positivity) (by linarith)
  refine ⟨M + ω ^ 2, ?_⟩
  have hcmp := prufer_le_of_le (isPruferData_sin hω a) (isPruferData_slU hab.le hq (M + ω ^ 2))
    (fun x => by linarith [(abs_le.mp (hM x)).2]) hab.le
  have hb : a + k * π / ω = b := by
    simp only [ω]
    have : (k : ℝ) * π ≠ 0 := by have := pi_pos; have : (0 : ℝ) < k := by exact_mod_cast hk
                                 positivity
    field_simp
    ring
  have := prufer_sin_ge hω a k
  rw [hb] at this
  exact this.trans hcmp

/-- **DLMF 3.7.17**: the eigenvalues, ordered increasingly, form a sequence
`λ₁ < λ₂ < λ₃ < ⋯` (here `Λ 0 < Λ 1 < ⋯`) with `λ_k → ∞`, and there are no others. -/
theorem dlmf_3_7_17 : ∃ Λ : ℕ → ℝ, StrictMono Λ ∧ Tendsto Λ atTop atTop ∧
    ∀ l, IsDirichletEigenvalue q a b l ↔ ∃ k, Λ k = l := by
  set Θ := fun l => slTheta q a b l b
  have hmono : StrictMono Θ := slTheta_strictMono hab hq
  have hcont : Continuous Θ := continuous_slTheta hab hq
  have hex : ∀ k : ℕ, ∃ l, Θ l = ((k : ℝ) + 1) * π := by
    intro k
    obtain ⟨l₀, h₀⟩ := exists_slTheta_lt_pi hab hq
    obtain ⟨l₁, h₁⟩ := exists_slTheta_ge hab hq (k + 1)
    push_cast at h₁
    have hpi := pi_pos
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h01 : l₀ ≤ l₁ := by
      by_contra h; push Not at h
      have := hmono h
      simp only [Θ] at this
      nlinarith
    obtain ⟨l, -, hl⟩ := intermediate_value_Icc h01 hcont.continuousOn
      ⟨by simp only [Θ]; nlinarith, h₁⟩
    exact ⟨l, hl⟩
  choose Λ hΛ using hex
  have hpi := pi_pos
  refine ⟨Λ, strictMono_nat_of_lt_succ fun k => hmono.lt_iff_lt.mp (by
      rw [hΛ, hΛ]; push_cast; nlinarith), ?_, fun l => ?_⟩
  · refine tendsto_atTop_atTop.mpr fun B => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (Θ B / π)
    refine ⟨N, fun k hk => ?_⟩
    have hBN : B < Λ N := by
      refine hmono.lt_iff_lt.mp ?_
      rw [hΛ]
      rw [div_lt_iff₀ hpi] at hN
      nlinarith
    exact hBN.le.trans ((strictMono_nat_of_lt_succ fun k => hmono.lt_iff_lt.mp (by
      rw [hΛ, hΛ]; push_cast; nlinarith)).monotone hk)
  · rw [isDirichletEigenvalue_iff_sin hab hq]
    constructor
    · intro hs
      obtain ⟨m, hm⟩ := sin_eq_zero_iff.mp hs
      have hpos := slTheta_pos hab hq l
      rw [← hm] at hpos
      have hm1 : (1 : ℤ) ≤ m := by
        by_contra h; push Not at h
        have : (m : ℝ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp h
        nlinarith
      refine ⟨(m - 1).toNat, hmono.injective ?_⟩
      rw [hΛ]
      simp only [Θ]
      rw [← hm]
      have : (((m - 1).toNat : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [show (((m - 1).toNat : ℕ) : ℝ) = (((m - 1).toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg (by omega)]
        push_cast; ring
      rw [this]; ring
    · rintro ⟨k, rfl⟩
      have := hΛ k
      simp only [Θ] at this
      rw [this, show ((k : ℝ) + 1) * π = ((k + 1 : ℕ) : ℝ) * π by push_cast; ring,
        sin_nat_mul_pi]

end Eigen

/-! ### Infinite intervals -/

theorem eq_zero_of_tendsto_mul {c δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ)
    (hf : ∀ N, ∃ x, N ≤ x ∧ δ ≤ |f x|) (ht : Tendsto (fun x => c * f x) atTop (𝓝 0)) :
    c = 0 := by
  by_contra hc
  have hcδ : 0 < |c| * δ := mul_pos (abs_pos.mpr hc) hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (Metric.ball_mem_nhds 0 hcδ))
  obtain ⟨x, hx, hfx⟩ := hf N
  have := hN x hx
  rw [Real.dist_eq, sub_zero, abs_mul] at this
  nlinarith [abs_nonneg c]

/-- **DLMF §3.7(iv), infinite intervals**: the claims fail without further hypotheses on `q`. For
`q = 0` on `(0, ∞)` there is no eigenvalue at all: every solution of `w″ + λ w = 0` with
`w(0) = 0` and `w(x) → 0` as `x → ∞` vanishes identically. -/
theorem dlmf_3_7_iv_infinite_no_eigenvalue (l : ℝ) {w : ℝ → ℝ}
    (hw : ∀ x, 0 ≤ x → HasDerivAt w (deriv w x) x ∧ HasDerivAt (deriv w) (-(l * w x)) x)
    (h0 : w 0 = 0) (hlim : Tendsto w atTop (𝓝 0)) : ∀ x, 0 ≤ x → w x = 0 := by
  -- the solution `s` with `s(0) = 0`, `s′(0) = 1`, and a lower bound on `|s|` far out
  obtain ⟨s, s', hs, hs', hs0, hs1, δ, hδ, hbig⟩ : ∃ s s' : ℝ → ℝ,
      (∀ x, HasDerivAt s (s' x) x) ∧ (∀ x, HasDerivAt s' (-(l * s x)) x) ∧ s 0 = 0 ∧
      s' 0 = 1 ∧ ∃ δ, 0 < δ ∧ ∀ N, ∃ x, N ≤ x ∧ δ ≤ |s x| := by
    rcases lt_trichotomy l 0 with hl | rfl | hl
    · set k := √(-l)
      have hk : 0 < k := Real.sqrt_pos.mpr (by linarith)
      have hk2 : k ^ 2 = -l := Real.sq_sqrt (by linarith)
      have hlin : ∀ x, HasDerivAt (fun x => k * x) k x := fun x => by
        simpa using (hasDerivAt_id x).const_mul k
      refine ⟨fun x => sinh (k * x) / k, fun x => cosh (k * x),
        fun x => (((Real.hasDerivAt_sinh (k * x)).comp x (hlin x)).div_const k).congr_deriv
          (by field_simp),
        fun x => ((Real.hasDerivAt_cosh (k * x)).comp x (hlin x)).congr_deriv
          (by field_simp; rw [hk2]; ring), by simp, by simp,
        sinh k / k, div_pos (sinh_pos_iff.mpr hk) hk, fun N => ⟨max N 1, le_max_left _ _, ?_⟩⟩
      rw [abs_of_nonneg (div_nonneg (sinh_nonneg_iff.mpr (by positivity)) hk.le)]
      gcongr
      exact sinh_le_sinh.mpr (le_mul_of_one_le_right hk.le (le_max_right _ _))
    · refine ⟨fun x => x, fun _ => 1, fun x => hasDerivAt_id x,
        fun x => (hasDerivAt_const x (1 : ℝ)).congr_deriv (by ring), rfl, rfl, 1, one_pos,
        fun N => ⟨max N 1, le_max_left _ _, ?_⟩⟩
      rw [abs_of_nonneg (by linarith [le_max_right N 1])]
      exact le_max_right _ _
    · set k := √l
      have hk : 0 < k := Real.sqrt_pos.mpr hl
      have hk2 : k ^ 2 = l := Real.sq_sqrt hl.le
      have hlin : ∀ x, HasDerivAt (fun x => k * x) k x := fun x => by
        simpa using (hasDerivAt_id x).const_mul k
      refine ⟨fun x => sin (k * x) / k, fun x => cos (k * x),
        fun x => ((hlin x).sin.div_const k).congr_deriv (by field_simp),
        fun x => (hlin x).cos.congr_deriv (by field_simp; rw [← hk2]; ring), by simp, by simp,
        1 / k, one_div_pos.mpr hk, fun N => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (N * k / (2 * π))
      have hpi := pi_pos
      refine ⟨(π / 2 + n * (2 * π)) / k, ?_, ?_⟩
      · rw [le_div_iff₀ hk]
        rw [div_lt_iff₀ (by positivity)] at hn
        nlinarith
      · show 1 / k ≤ |sin (k * ((π / 2 + n * (2 * π)) / k)) / k|
        rw [mul_div_cancel₀ _ hk.ne', sin_add_nat_mul_two_pi, sin_pi_div_two,
          abs_of_pos (one_div_pos.mpr hk)]
  -- `w = w′(0) s` on `[0, ∞)`
  have he := ode2_eq_zero_right (W := fun _ => -l) (w := fun x => w x - deriv w 0 * s x)
    (w' := fun x => deriv w x - deriv w 0 * s' x) (K := |l|) (x1 := 0)
    (fun x _ => by simp)
    (fun x hx => (hw x hx).1.sub ((hs x).const_mul _))
    (fun x hx => ((hw x hx).2.sub ((hs' x).const_mul _)).congr_deriv (by ring))
    (by simp [h0, hs0]) (by simp [hs1])
  have hc : deriv w 0 = 0 := by
    refine eq_zero_of_tendsto_mul hδ hbig (hlim.congr' ?_)
    filter_upwards [eventually_ge_atTop 0] with x hx
    linear_combination he x hx
  intro x hx
  have := he x hx
  rw [hc, zero_mul, sub_zero] at this
  exact this

end Azurite.DLMF
