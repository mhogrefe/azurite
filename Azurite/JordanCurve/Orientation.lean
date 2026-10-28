/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.JordanCurve.Green
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Orientation of Jordan curves

For a closed piecewise-`C¹` Jordan curve the winding number is `1` or `−1` on the interior.

Proof.  Some piece `gᵢ` has a point `s₀` with `gᵢ'(s₀) = u ≠ 0` (otherwise a piece is constant,
contradicting injectivity).  With `z₀ = gᵢ(s₀)` and `p±(ε) = z₀ ± εiu`,
`W(p₊) − W(p₋) = (2πi)⁻¹ ∮ ((z − p₊)⁻¹ − (z − p₋)⁻¹) dz`.  The pieces other than `gᵢ` stay at a
positive distance from `z₀` and contribute `O(ε)`; on `gᵢ`, with `G = (gᵢ − z₀)/u`, the integrand is
`G'(s) · 2iε/(G(s)² + ε²)`, and the substitution `s = s₀ + ετ` and dominated convergence
(`tendsto_integral_jump`, using the lower bound `exists_jump_lower_bound`) give the limit
`2i ∫ dτ/(1 + τ²) = 2πi`.  Since winding numbers are integers, `W(p₊) − W(p₋) = 1` for small `ε`
(`exists_windingNumber_sub_eq_one`).  Both points lie in the interior or the exterior, where
`W = 0`; they cannot both lie in the connected interior, where `W` is constant, so one of them is
exterior and the other interior with `W = ±1` (`exists_windingNumber_eq_one_or_neg_one`).

Reversing the parametrization (`ClosedPiecewiseC1.reverse`, `t ↦ c(a + b − t)`) negates the
contour integral and the winding number, so every Jordan curve is positively oriented in one of
its two directions (`isPositivelyOriented_or_reverse`).
-/

namespace Azurite.JordanCurve

open Set Filter Topology MeasureTheory Complex
open scoped Real

/-! ### The jump of the Cauchy kernel across a regular arc -/

/-- Lower bound for `G² + ε²` near a regular zero `s₀` of `G` with `G'(s₀) = 1`. -/
theorem exists_jump_lower_bound {G : ℝ → ℂ} (hG : ContDiff ℝ 1 G) {α β s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo α β) (hG0 : G s₀ = 0) (hG1 : deriv G s₀ = 1)
    (hne : ∀ s ∈ Icc α β, s ≠ s₀ → G s ≠ 0) :
    ∃ κ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s ∈ Icc α β,
      κ * ((s - s₀) ^ 2 + ε ^ 2) ≤ ‖G s ^ 2 + (ε : ℂ) ^ 2‖ := by
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hG'c.continuousAt (1 / 4) (by norm_num)
  set η := δ / 2 with hη
  have hη0 : 0 < η := half_pos hδ
  -- near `s₀`, `G(s) ≈ s − s₀`
  have hnear : ∀ s, |s - s₀| ≤ η → ‖G s - ((s - s₀ : ℝ) : ℂ)‖ ≤ |s - s₀| / 4 := by
    intro s hs
    have hd : ∀ x, HasDerivAt (fun y => G y - ((y - s₀ : ℝ) : ℂ)) (deriv G x - 1) x :=
      fun x => (hGd x).hasDerivAt.sub (((hasDerivAt_id x).sub_const s₀).ofReal_comp)
    have hball : ∀ x ∈ Metric.closedBall s₀ η,
        ‖deriv (fun y => G y - ((y - s₀ : ℝ) : ℂ)) x‖ ≤ 1 / 4 := by
      intro x hx
      rw [(hd x).deriv]
      have hx' : dist x s₀ < δ := lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)
      have := hδ' hx'
      rw [dist_eq_norm, hG1] at this
      exact this.le
    have h := (convex_closedBall s₀ η).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (hd x).differentiableAt) hball (Metric.mem_closedBall_self hη0.le)
      (by rw [Metric.mem_closedBall, Real.dist_eq]; exact hs)
    have h0 : G s₀ - ((s₀ - s₀ : ℝ) : ℂ) = 0 := by simp [hG0]
    rw [h0, sub_zero, Real.norm_eq_abs] at h
    linarith
  -- away from `s₀`, `G` is bounded below
  set K := Icc α β ∩ {s | η ≤ |s - s₀|} with hKdef
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const)))
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ s ∈ K, m ≤ ‖G s‖ := by
    rcases K.eq_empty_or_nonempty with he | hne'
    · exact ⟨1, one_pos, fun s hs => by rw [he] at hs; exact hs.elim⟩
    · obtain ⟨s₁, hs₁, hmin⟩ := hK.exists_isMinOn hne' hG.continuous.norm.continuousOn
      refine ⟨‖G s₁‖, norm_pos_iff.mpr (hne s₁ hs₁.1 fun h => ?_), isMinOn_iff.mp hmin⟩
      have := hs₁.2
      simp only [mem_ofPred_eq, h, sub_self, abs_zero] at this
      linarith
  set D := (β - α) ^ 2 + 1 with hD
  have hD0 : 0 < D := by positivity
  refine ⟨min (1 / 4) (m ^ 2 / (2 * D)), lt_min (by norm_num) (by positivity),
    min 1 (m / 2), lt_min one_pos (half_pos hm0), fun ε hε hε₀ s hs => ?_⟩
  have hε1 : ε < 1 := hε₀.trans_le (min_le_left _ _)
  have hεm : ε < m / 2 := hε₀.trans_le (min_le_right _ _)
  by_cases hsη : |s - s₀| ≤ η
  · -- near: real part estimate
    have he := hnear s hsη
    set σ := s - s₀ with hσ
    set x := (G s).re
    set y := (G s).im
    have hsq : (x - σ) ^ 2 + y ^ 2 ≤ σ ^ 2 / 16 := by
      have h2 : ‖G s - (σ : ℂ)‖ ^ 2 ≤ (|σ| / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      rw [Complex.sq_norm, Complex.normSq_apply, div_pow, sq_abs] at h2
      simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h2
      nlinarith [h2]
    have hre : (G s ^ 2 + (ε : ℂ) ^ 2).re = x ^ 2 - y ^ 2 + ε ^ 2 := by
      simp only [add_re, sq, mul_re, ← ofReal_mul, ofReal_re, x, y]
    have h1 : (σ ^ 2 + ε ^ 2) / 4 ≤ ‖G s ^ 2 + (ε : ℂ) ^ 2‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      rw [hre]
      nlinarith [sq_nonneg (σ / 2 + 2 * (x - σ)), sq_nonneg y, sq_nonneg ε]
    calc min (1 / 4) (m ^ 2 / (2 * D)) * (σ ^ 2 + ε ^ 2)
        ≤ 1 / 4 * (σ ^ 2 + ε ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (σ ^ 2 + ε ^ 2) / 4 := by ring
      _ ≤ _ := h1
  · -- far: `‖G s‖ ≥ m`
    have hGm : m ≤ ‖G s‖ := hm s ⟨hs, (not_le.mp hsη).le⟩
    have h1 : 3 * m ^ 2 / 4 ≤ ‖G s ^ 2 + (ε : ℂ) ^ 2‖ := by
      have := norm_sub_le (G s ^ 2 + (ε : ℂ) ^ 2) ((ε : ℂ) ^ 2)
      rw [add_sub_cancel_right, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs] at this
      have hε2 : ε ^ 2 ≤ m ^ 2 / 4 := by nlinarith
      nlinarith [pow_le_pow_left₀ hm0.le hGm 2]
    have hsσ : (s - s₀) ^ 2 + ε ^ 2 ≤ D := by
      have : (s - s₀) ^ 2 ≤ (β - α) ^ 2 := by
        have h1 := hs.1; have h2 := hs.2; have h3 := hs₀.1; have h4 := hs₀.2
        nlinarith
      nlinarith
    calc min (1 / 4) (m ^ 2 / (2 * D)) * ((s - s₀) ^ 2 + ε ^ 2)
        ≤ m ^ 2 / (2 * D) * D :=
          mul_le_mul (min_le_right _ _) hsσ (by positivity) (by positivity)
      _ = m ^ 2 / 2 := by field_simp
      _ ≤ _ := by nlinarith

/-- **The jump of the Cauchy kernel.**  If `G` is `C¹`, vanishes only at `s₀ ∈ (α, β)` on
`[α, β]` and `G'(s₀) = 1`, then `∫_α^β G'(s) · 2iε/(G(s)² + ε²) ds → 2πi` as `ε → 0⁺`. -/
theorem tendsto_integral_jump {G : ℝ → ℂ} (hG : ContDiff ℝ 1 G) {α β s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo α β) (hG0 : G s₀ = 0) (hG1 : deriv G s₀ = 1)
    (hne : ∀ s ∈ Icc α β, s ≠ s₀ → G s ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ s in α..β, deriv G s * (2 * I * ε * (G s ^ 2 + (ε : ℂ) ^ 2)⁻¹))
      (𝓝[>] 0) (𝓝 (2 * π * I)) := by
  obtain ⟨κ, hκ, ε₀, hε₀, hbd⟩ := exists_jump_lower_bound hG hs₀ hG0 hG1 hne
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc α β) hG'c.continuousOn
  set L' := max L 0 with hL'
  have hL'b : ∀ s ∈ Icc α β, ‖deriv G s‖ ≤ L' := fun s hs => (hL s hs).trans (le_max_left _ _)
  have hαβ : α ≤ β := (hs₀.1.trans hs₀.2).le
  -- the rescaled integrands
  set f : ℝ → ℝ → ℂ := fun ε s => deriv G s * (2 * I * (ε : ℂ) ^ 2 * (G s ^ 2 + (ε : ℂ) ^ 2)⁻¹)
    with hfdef
  set H : ℝ → ℝ → ℂ := fun ε τ => (Ioc α β).indicator (f ε) (ε * τ + s₀) with hHdef
  -- the integral over `[α, β]` is the integral of `H ε` over `ℝ`
  have hrescale : ∀ ε : ℝ, 0 < ε →
      ∫ s in α..β, deriv G s * (2 * I * ε * (G s ^ 2 + (ε : ℂ) ^ 2)⁻¹) = ∫ τ, H ε τ := by
    intro ε hε
    have h1 : ∫ τ, H ε τ = |ε⁻¹| • ∫ y, (Ioc α β).indicator (f ε) (y + s₀) :=
      Measure.integral_comp_mul_left (fun y => (Ioc α β).indicator (f ε) (y + s₀)) ε
    rw [h1, integral_add_right_eq_self (fun s => (Ioc α β).indicator (f ε) s) s₀,
      integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hαβ]
    have h2 : (fun s => f ε s) = fun s =>
        (ε : ℂ) * (deriv G s * (2 * I * ε * (G s ^ 2 + (ε : ℂ) ^ 2)⁻¹)) := by
      funext s; simp only [hfdef]; ring
    rw [h2, intervalIntegral.integral_const_mul, abs_of_pos (inv_pos.mpr hε), Complex.real_smul,
      ← mul_assoc, ofReal_inv, inv_mul_cancel₀ (ofReal_ne_zero.mpr hε.ne'), one_mul]
  -- dominated convergence
  have hlim : Tendsto (fun ε => ∫ τ, H ε τ) (𝓝[>] 0)
      (𝓝 (∫ τ : ℝ, 2 * I * (((1 + τ ^ 2)⁻¹ : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => 2 * L' / κ * (1 + τ ^ 2)⁻¹) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun ε => ?_
      have hfm : Measurable (f ε) :=
        hG'c.measurable.mul (measurable_const.mul
          ((hG.continuous.measurable.pow_const 2).add_const _).inv)
      exact ((hfm.indicator measurableSet_Ioc).comp
        ((measurable_id.const_mul ε).add_const s₀)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
      refine ae_of_all _ fun τ => ?_
      simp only [hHdef]
      by_cases hmem : ε * τ + s₀ ∈ Ioc α β
      · rw [indicator_of_mem hmem]
        have hs : ε * τ + s₀ ∈ Icc α β := Ioc_subset_Icc_self hmem
        have hN := hbd ε hε.1 hε.2 _ hs
        rw [show ε * τ + s₀ - s₀ = ε * τ by ring] at hN
        set N := ‖G (ε * τ + s₀) ^ 2 + (ε : ℂ) ^ 2‖
        have hτ : 0 < 1 + τ ^ 2 := by positivity
        have hN' : κ * ε ^ 2 * (1 + τ ^ 2) ≤ N := by nlinarith
        have hNpos : 0 < N := lt_of_lt_of_le (by have := hε.1; positivity) hN'
        simp only [hfdef, norm_mul, norm_inv, norm_ofNat, norm_I, Complex.norm_real,
          Real.norm_eq_abs, norm_pow, sq_abs]
        have hb := hL'b _ hs
        calc ‖deriv G (ε * τ + s₀)‖ * (2 * 1 * ε ^ 2 * N⁻¹)
            ≤ L' * (2 * ε ^ 2 * (κ * ε ^ 2 * (1 + τ ^ 2))⁻¹) := by
              refine mul_le_mul hb ?_ (by positivity) (le_max_right _ _)
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left (inv_anti₀ (by have := hε.1; positivity) hN')
                (by positivity)
          _ = 2 * L' / κ * (1 + τ ^ 2)⁻¹ := by
              have := hε.1.ne'
              field_simp
      · rw [indicator_of_notMem hmem, norm_zero]
        exact mul_nonneg (div_nonneg (by positivity) hκ.le) (by positivity)
    · exact integrable_inv_one_add_sq.const_mul _
    · refine ae_of_all _ fun τ => ?_
      have hc : Tendsto (fun ε : ℝ => ε * τ + s₀) (𝓝[>] 0) (𝓝 s₀) := by
        have h := (Continuous.tendsto (f := fun ε : ℝ => ε * τ + s₀) (by fun_prop) 0)
        rw [zero_mul, zero_add] at h
        exact tendsto_nhdsWithin_of_tendsto_nhds h
      -- the indicator is eventually `1`
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * τ + s₀ ∈ Ioc α β :=
        hc.eventually (mem_of_superset (isOpen_Ioo.mem_nhds hs₀) Ioo_subset_Ioc_self)
      -- the slope `G(ετ + s₀)/ε → τ`
      have hslope : Tendsto (fun ε : ℝ => (ε : ℂ)⁻¹ * G (ε * τ + s₀)) (𝓝[>] 0) (𝓝 (τ : ℂ)) := by
        have hφ : HasDerivAt (fun ε : ℝ => G (ε * τ + s₀)) ((τ : ℝ) • deriv G s₀) 0 := by
          have h1 : HasDerivAt (fun ε : ℝ => ε * τ + s₀) τ 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).mul_const τ).add_const s₀
          have h2 : HasDerivAt G (deriv G (0 * τ + s₀)) (0 * τ + s₀) := (hGd _).hasDerivAt
          have h3 := h2.scomp (0 : ℝ) h1
          simp only [zero_mul, zero_add] at h3
          exact h3
        rw [hG1] at hφ
        have := (hasDerivAt_iff_tendsto_slope_zero.mp hφ).mono_left
          (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')
        rw [show (τ • (1 : ℂ)) = (τ : ℂ) by simp] at this
        refine this.congr fun ε => ?_
        simp [hG0, Complex.real_smul]
      have hcont : ContinuousAt (fun w : ℂ => 2 * I * (w ^ 2 + 1)⁻¹) (τ : ℂ) := by
        have h0 : (τ : ℂ) ^ 2 + 1 ≠ 0 := by
          rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
          exact ofReal_ne_zero.mpr (by positivity)
        have h1 : ContinuousAt (fun w : ℂ => w ^ 2 + 1) (τ : ℂ) := by fun_prop
        exact continuousAt_const.mul (h1.inv₀ h0)
      have hlim1 := (hG'c.tendsto s₀).comp hc
      have hprod := (hlim1.mul (hcont.tendsto.comp hslope))
      rw [hG1, one_mul] at hprod
      have hval : 2 * I * (((1 + τ ^ 2)⁻¹ : ℝ) : ℂ) = 2 * I * ((τ : ℂ) ^ 2 + 1)⁻¹ := by
        push_cast; ring
      rw [hval]
      refine hprod.congr' ?_
      filter_upwards [hev, self_mem_nhdsWithin] with ε hε hεpos
      have hε0 : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hεpos)
      simp only [Function.comp_apply, hHdef, indicator_of_mem hε, hfdef]
      congr 1
      rw [show ((ε : ℂ)⁻¹ * G (ε * τ + s₀)) ^ 2 + 1 =
          ((ε : ℂ) ^ 2)⁻¹ * (G (ε * τ + s₀) ^ 2 + (ε : ℂ) ^ 2) by field_simp,
        mul_inv, inv_inv]
      ring
  have hval : ∫ τ : ℝ, 2 * I * (((1 + τ ^ 2)⁻¹ : ℝ) : ℂ) = 2 * π * I := by
    rw [integral_const_mul, integral_complex_ofReal, integral_univ_inv_one_add_sq]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hrescale ε hε).symm

/-! ### Regular points and the jump of the winding number -/

namespace IsJordanCurve

variable {c : ℝ → ℂ} {a b : ℝ}

/-- On a Jordan curve, a parameter in `(a, b)` is the only one in `[a, b]` with its image. -/
theorem apply_ne (h : IsJordanCurve c a b) {s₀ s : ℝ} (hs₀ : s₀ ∈ Ioo a b) (hs : s ∈ Icc a b)
    (hne : s ≠ s₀) : c s ≠ c s₀ := by
  intro heq
  have hs₀' : s₀ ∈ Ico a b := Ioo_subset_Ico_self hs₀
  rcases eq_or_lt_of_le hs.2 with hb | hb
  · rw [hb, ← h.closed] at heq
    exact absurd (h.injOn (left_mem_Ico.mpr h.lt) hs₀' heq) (ne_of_lt hs₀.1)
  · exact hne (h.injOn ⟨hs.1, hb⟩ hs₀' heq)

end IsJordanCurve

/-- The algebra behind the jump: `((uA)⁻¹ − (uB)⁻¹) uD = D · 2iε/(AB)` when `B − A = 2εi`. -/
theorem kernel_diff_eq {u A B D : ℂ} {ε : ℝ} (hu : u ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hBA : B - A = 2 * ε * I) :
    ((u * A)⁻¹ - (u * B)⁻¹) * (u * D) = D * (2 * I * ε * (A * B)⁻¹) := by
  have h : (u * A)⁻¹ - (u * B)⁻¹ = u⁻¹ * (A⁻¹ - B⁻¹) := by rw [mul_inv, mul_inv]; ring
  rw [h, inv_sub_inv hA hB, hBA]
  field_simp

namespace ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

/-- A Jordan curve has a regular point: some piece has nonzero derivative inside its interval. -/
theorem exists_regular_point (h : IsJordanCurve c a b) :
    ∃ i < P.n, ∃ s₀ ∈ Ioo (P.t i) (P.t (i + 1)), deriv (P.g i) s₀ ≠ 0 := by
  have hn : 0 < P.n := by
    rcases Nat.eq_zero_or_pos P.n with h0 | h0
    · have h1 := P.first
      have h2 := P.last
      rw [h0] at h2
      exact absurd (h1.symm.trans h2) h.lt.ne
    · exact h0
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0 hn
  have hlt := P.lt 0 hn
  have hgc := P.contDiff 0 hn
  have hcl : Icc (P.t 0) (P.t 1) ⊆ {s | deriv (P.g 0) s = 0} := by
    rw [← closure_Ioo hlt.ne]
    exact (isClosed_eq (hgc.continuous_deriv le_rfl) continuous_const).closure_subset_iff.mpr
      fun s hs => h0 s hs
  set m := (P.t 0 + P.t 1) / 2 with hm
  have hmI : m ∈ Icc (P.t 0) (P.t 1) := ⟨by linarith, by linarith⟩
  have hconst := (convex_Icc (P.t 0) (P.t 1)).norm_image_sub_le_of_norm_deriv_le (f := P.g 0)
    (C := 0) (fun x _ => (hgc.differentiable one_ne_zero) x)
    (fun x hx => by rw [hcl hx, norm_zero]) (left_mem_Icc.mpr hlt.le) hmI
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hconst
  have e1 : c m = P.g 0 m := P.eqOn 0 hn hmI
  have e0 : c (P.t 0) = P.g 0 (P.t 0) := P.eqOn 0 hn (left_mem_Icc.mpr hlt.le)
  have hb1 : P.t 1 ≤ b := (P.t_mem_Icc (Nat.succ_le_of_lt hn)).2
  have ha := P.first
  have := h.injOn (x₁ := P.t 0) (x₂ := m) ⟨ha.ge, by linarith⟩ ⟨by linarith, by linarith⟩
    (by rw [e0, e1, hconst])
  linarith

/-- **The jump of the winding number across a regular arc**: there are two points off a Jordan
curve whose winding numbers differ by `1`. -/
theorem exists_windingNumber_sub_eq_one (h : IsJordanCurve c a b) :
    ∃ p q : ℂ, p ∉ P.curve ∧ q ∉ P.curve ∧ P.windingNumber p - P.windingNumber q = 1 := by
  obtain ⟨i, hi, s₀, hs₀, hu⟩ := P.exists_regular_point h
  have hn : 0 < P.n := (Nat.zero_le i).trans_lt hi
  set u := deriv (P.g i) s₀ with hudef
  set z₀ := P.g i s₀ with hz₀def
  have hgi := P.contDiff i hi
  have hgid : Differentiable ℝ (P.g i) := hgi.differentiable one_ne_zero
  set G : ℝ → ℂ := fun s => (P.g i s - z₀) / u with hGdef
  have hGd : ∀ s, HasDerivAt G (deriv (P.g i) s / u) s := fun s =>
    ((hgid s).hasDerivAt.sub_const z₀).div_const u
  have hG : ContDiff ℝ 1 G := (hgi.sub contDiff_const).div_const u
  have hG0 : G s₀ = 0 := by simp [hGdef, z₀]
  have hG1 : deriv G s₀ = 1 := by rw [(hGd s₀).deriv]; exact div_self hu
  have hgG : ∀ s, P.g i s = z₀ + u * G s := fun s => by
    simp only [hGdef]
    field_simp
    ring
  have hderiv : ∀ s, deriv (P.g i) s = u * deriv G s := fun s => by
    rw [(hGd s).deriv]
    field_simp
  have hti := P.t_mem_Icc hi.le
  have hti1 := P.t_mem_Icc hi
  have hs₀ab : s₀ ∈ Ioo a b := ⟨hti.1.trans_lt hs₀.1, hs₀.2.trans_le hti1.2⟩
  have hcz : c s₀ = z₀ := P.eqOn i hi (Ioo_subset_Icc_self hs₀)
  have hcs : ∀ s ∈ Icc a b, s ≠ s₀ → c s ≠ z₀ := fun s hs hne =>
    hcz ▸ h.apply_ne hs₀ab hs hne
  have hGne : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), s ≠ s₀ → G s ≠ 0 := by
    intro s hs hne hG0'
    apply hcs s (Icc_subset_Icc hti.1 hti1.2 hs) hne
    rw [P.eqOn i hi hs, hgG s, hG0', mul_zero, add_zero]
  have hjump := tendsto_integral_jump hG hs₀ hG0 hG1 hGne
  obtain ⟨κ, hκ, ε₀, hε₀, hbd⟩ := exists_jump_lower_bound hG hs₀ hG0 hG1 hGne
  -- the rest of the curve stays away from `z₀`
  set K' := Icc a b ∩ (Ioo (P.t i) (P.t (i + 1)))ᶜ with hK'def
  have hK' : IsCompact (c '' K') :=
    (isCompact_Icc.inter_right isOpen_Ioo.isClosed_compl).image_of_continuousOn
      (P.continuousOn.mono inter_subset_left)
  have hz₀ : z₀ ∉ c '' K' := by
    rintro ⟨s, hs, hcs'⟩
    exact hcs s hs.1 (fun h' => hs.2 (h' ▸ hs₀)) hcs'
  obtain ⟨m, hm0, hm⟩ := Metric.mem_nhds_iff.mp (hK'.isClosed.isOpen_compl.mem_nhds hz₀)
  have hfar : ∀ j < P.n, j ≠ i → ∀ s ∈ Icc (P.t j) (P.t (j + 1)), m ≤ ‖P.g j s - z₀‖ := by
    intro j hj hji s hs
    by_contra hlt
    push Not at hlt
    have hmem : P.g j s ∈ Metric.ball z₀ m := by rw [Metric.mem_ball, dist_eq_norm]; exact hlt
    refine hm hmem ⟨s, ⟨Icc_subset_Icc (P.t_mem_Icc hj.le).1 (P.t_mem_Icc hj).2 hs, ?_⟩,
      (P.eqOn j hj hs)⟩
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hji with hlt' | hlt'
    · have := P.t_mono (Nat.succ_le_of_lt hlt') hi.le
      linarith [hs.2]
    · have := P.t_mono (Nat.succ_le_of_lt hlt') hj.le
      linarith [hs.1]
  -- the two test points `z₀ ± εiu`
  set w : ℝ → ℂ → ℂ := fun ε σ => z₀ + σ * ((ε : ℂ) * I * u) with hwdef
  have hwz : ∀ ε : ℝ, 0 < ε → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) → ‖w ε σ - z₀‖ = ε * ‖u‖ := by
    intro ε hε σ hσ
    simp only [hwdef, add_sub_cancel_left, norm_mul, norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε, mul_one]
    rcases hσ with rfl | rfl <;> simp
  have hGsq : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s ∈ Icc (P.t i) (P.t (i + 1)),
      G s ^ 2 + (ε : ℂ) ^ 2 ≠ 0 := by
    intro ε hε hε' s hs h0
    have := hbd ε hε hε' s hs
    rw [h0, norm_zero] at this
    have : 0 < κ * ((s - s₀) ^ 2 + ε ^ 2) := by positivity
    linarith
  have hoff : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε * ‖u‖ < m / 2 → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
      ∀ j < P.n, ∀ s ∈ Icc (P.t j) (P.t (j + 1)), P.g j s ≠ w ε σ := by
    intro ε hε hε' hεm σ hσ j hj s hs heq
    by_cases hji : j = i
    · rw [hji] at heq hs
      apply hGsq ε hε hε' s hs
      have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
      have hGs : G s = σ * ((ε : ℂ) * I) := by
        rw [hgG s] at heq
        simp only [hwdef] at heq
        have h2 := add_left_cancel heq
        refine mul_left_cancel₀ hu ?_
        rw [h2]
        ring
      rw [hGs]
      linear_combination ((ε : ℂ) ^ 2 * I ^ 2) * hσ2 + (ε : ℂ) ^ 2 * I_sq
    · have h1 := hfar j hj hji s hs
      rw [heq, hwz ε hε σ hσ] at h1
      linarith
  have hoffc : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε * ‖u‖ < m / 2 → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
      w ε σ ∉ P.curve := by
    rintro ε hε hε' hεm σ hσ ⟨t, ht, hct⟩
    obtain ⟨j, hj, htj⟩ := P.exists_piece ht hn
    exact hoff ε hε hε' hεm σ hσ j hj t htj ((P.eqOn j hj htj).symm.trans hct)
  -- the difference of contour integrals, piece by piece
  set term : ℕ → ℝ → ℂ := fun j ε => ∫ s in P.t j..P.t (j + 1),
    ((P.g j s - w ε 1)⁻¹ - (P.g j s - w ε (-1))⁻¹) * deriv (P.g j) s with htermdef
  have hii : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε * ‖u‖ < m / 2 → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
      ∀ j < P.n, IntervalIntegrable (fun s => (P.g j s - w ε σ)⁻¹ * deriv (P.g j) s) volume
        (P.t j) (P.t (j + 1)) := by
    intro ε hε hε' hεm σ hσ j hj
    have hgj := P.contDiff j hj
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (P.lt j hj).le]
    exact ((hgj.continuous.sub continuous_const).continuousOn.inv₀ fun s hs =>
      sub_ne_zero.mpr (hoff ε hε hε' hεm σ hσ j hj s hs)).mul
      (hgj.continuous_deriv le_rfl).continuousOn
  have hdiff : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε * ‖u‖ < m / 2 →
      2 * π * I * (((P.windingNumber (w ε 1) - P.windingNumber (w ε (-1)) : ℤ)) : ℂ) =
        ∑ j ∈ Finset.range P.n, term j ε := by
    intro ε hε hε' hεm
    have h1 := P.contourIntegral_inv_eq (hoffc ε hε hε' hεm 1 (Or.inl rfl))
    have h2 := P.contourIntegral_inv_eq (hoffc ε hε hε' hεm (-1) (Or.inr rfl))
    push_cast
    rw [mul_sub, ← h1, ← h2]
    simp only [contourIntegral]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [← intervalIntegral.integral_sub (hii ε hε hε' hεm 1 (Or.inl rfl) j hj')
      (hii ε hε hε' hεm (-1) (Or.inr rfl) j hj')]
    simp only [htermdef]
    congr 1
    funext s
    ring
  -- eventually all smallness conditions hold
  have hE : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ε₀ ∧ ε * ‖u‖ < m / 2 := by
    have h3 : Tendsto (fun ε : ℝ => ε * ‖u‖) (𝓝[>] 0) (𝓝 0) := by
      have h := (Continuous.tendsto (f := fun ε : ℝ => ε * ‖u‖) (by fun_prop) 0)
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hε₀,
      h3.eventually (gt_mem_nhds (half_pos hm0))] with ε h1 h2 h3
    exact ⟨h1, h2.2, h3⟩
  -- limits of the pieces
  have hterm : ∀ j ∈ Finset.range P.n,
      Tendsto (term j) (𝓝[>] 0) (𝓝 (if j = i then 2 * π * I else 0)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte]
      refine hjump.congr' ?_
      filter_upwards [hE] with ε ⟨hε, hε', hεm⟩
      simp only [htermdef]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (P.lt i hi).le] at hs
      have hprod : (G s - ε * I) * (G s + ε * I) = G s ^ 2 + (ε : ℂ) ^ 2 := by
        linear_combination (-(ε : ℂ) ^ 2) * I_sq
      have hAB := hGsq ε hε hε' s hs
      rw [← hprod] at hAB
      have hA : G s - ε * I ≠ 0 := left_ne_zero_of_mul hAB
      have hB : G s + ε * I ≠ 0 := right_ne_zero_of_mul hAB
      have e1 : P.g i s - w ε 1 = u * (G s - ε * I) := by
        rw [hgG s]; simp only [hwdef]; ring
      have e2 : P.g i s - w ε (-1) = u * (G s + ε * I) := by
        rw [hgG s]; simp only [hwdef]; ring
      rw [e1, e2, hderiv, ← hprod]
      exact (kernel_diff_eq hu hA hB (by ring)).symm
    · simp only [hji, ↓reduceIte]
      have hgj := P.contDiff j hj'
      obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (s := Icc (P.t j) (P.t (j + 1))) (hgj.continuous_deriv le_rfl).continuousOn
      set L' := max L 0
      set C := 8 * ‖u‖ * L' / m ^ 2 * |P.t (j + 1) - P.t j|
      have hC : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
        have h := (Continuous.tendsto (f := fun ε : ℝ => C * ε) (by fun_prop) 0)
        rw [mul_zero] at h
        exact tendsto_nhdsWithin_of_tendsto_nhds h
      refine squeeze_zero_norm' ?_ hC
      filter_upwards [hE] with ε ⟨hε, hε', hεm⟩
      simp only [htermdef]
      have hb : ∀ s ∈ uIoc (P.t j) (P.t (j + 1)),
          ‖((P.g j s - w ε 1)⁻¹ - (P.g j s - w ε (-1))⁻¹) * deriv (P.g j) s‖ ≤
            8 * ‖u‖ * L' / m ^ 2 * ε := by
        intro s hs
        rw [uIoc_of_le (P.lt j hj').le] at hs
        have hs' : s ∈ Icc (P.t j) (P.t (j + 1)) := Ioc_subset_Icc_self hs
        have hfj := hfar j hj' hji s hs'
        have hlow : ∀ σ : ℂ, (σ = 1 ∨ σ = -1) → m / 2 ≤ ‖P.g j s - w ε σ‖ := by
          intro σ hσ
          have := norm_sub_norm_le (P.g j s - z₀) (w ε σ - z₀)
          rw [sub_sub_sub_cancel_right, hwz ε hε σ hσ] at this
          linarith
        have hA := hlow 1 (Or.inl rfl)
        have hB := hlow (-1) (Or.inr rfl)
        have hA0 : P.g j s - w ε 1 ≠ 0 := norm_pos_iff.mp (by linarith)
        have hB0 : P.g j s - w ε (-1) ≠ 0 := norm_pos_iff.mp (by linarith)
        have hnum : ‖(P.g j s - w ε (-1)) - (P.g j s - w ε 1)‖ = 2 * (ε * ‖u‖) := by
          rw [sub_sub_sub_cancel_left]
          simp only [hwdef, add_sub_add_left_eq_sub, ← sub_mul, norm_mul, norm_I,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, mul_one]
          norm_num
        rw [inv_sub_inv hA0 hB0, norm_mul, norm_div, norm_mul, hnum]
        have hLs : ‖deriv (P.g j) s‖ ≤ L' := (hL s hs').trans (le_max_left _ _)
        have hm2 : 0 < m / 2 * (m / 2) := by positivity
        calc 2 * (ε * ‖u‖) / (‖P.g j s - w ε 1‖ * ‖P.g j s - w ε (-1)‖) * ‖deriv (P.g j) s‖
            ≤ 2 * (ε * ‖u‖) / (m / 2 * (m / 2)) * L' := by
              refine mul_le_mul (div_le_div_of_nonneg_left (by positivity) hm2
                (mul_le_mul hA hB (by positivity) (norm_nonneg _))) hLs (norm_nonneg _)
                (by positivity)
          _ = 8 * ‖u‖ * L' / m ^ 2 * ε := by field_simp; ring
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      calc _ ≤ 8 * ‖u‖ * L' / m ^ 2 * ε * |P.t (j + 1) - P.t j| := this
        _ = C * ε := by ring
  have hsum := tendsto_finsetSum (Finset.range P.n) hterm
  have hic : i ∈ Finset.range P.n := Finset.mem_range.mpr hi
  rw [Finset.sum_ite_eq' (Finset.range P.n) i] at hsum
  simp only [hic, ↓reduceIte] at hsum
  -- the integer `W(p₊) − W(p₋)` tends to `1`
  set k : ℝ → ℤ := fun ε => P.windingNumber (w ε 1) - P.windingNumber (w ε (-1)) with hkdef
  have hk : Tendsto (fun ε => ((k ε : ℤ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have h2 : Tendsto (fun ε => 2 * π * I * ((k ε : ℤ) : ℂ)) (𝓝[>] 0) (𝓝 (2 * π * I)) := by
      refine hsum.congr' ?_
      filter_upwards [hE] with ε ⟨hε, hε', hεm⟩
      exact (hdiff ε hε hε' hεm).symm
    have h3 := h2.const_mul (2 * π * I)⁻¹
    rw [inv_mul_cancel₀ two_pi_I_ne_zero] at h3
    refine h3.congr fun ε => ?_
    rw [← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have hk1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dist ((k ε : ℤ) : ℂ) 1 < 1 :=
    hk.eventually (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨ε, ⟨hε, hε', hεm⟩, hd⟩ := (hE.and hk1).exists
  refine ⟨w ε 1, w ε (-1), hoffc ε hε hε' hεm 1 (Or.inl rfl),
    hoffc ε hε hε' hεm (-1) (Or.inr rfl), ?_⟩
  rw [dist_eq_norm, ← Int.cast_one, ← Int.cast_sub, Complex.norm_intCast] at hd
  have hd' : |k ε - 1| < 1 := by exact_mod_cast hd
  have := Int.abs_lt_one_iff.mp hd'
  simp only [hkdef] at this
  omega

/-- **The winding number of a Jordan curve is `±1` on its interior.** -/
theorem exists_windingNumber_eq_one_or_neg_one (h : IsJordanCurve c a b) :
    ∃ w : ℤ, (w = 1 ∨ w = -1) ∧ ∀ p ∈ jordanInterior c a b, P.windingNumber p = w := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.exists_windingNumber_sub_eq_one h
  have hp' := (compl_image_eq_union (c := c) (a := a) (b := b)).subset
    (show p ∈ (c '' Icc a b)ᶜ from hp)
  have hq' := (compl_image_eq_union (c := c) (a := a) (b := b)).subset
    (show q ∈ (c '' Icc a b)ᶜ from hq)
  rcases hp' with hpi | hpe <;> rcases hq' with hqi | hqe
  · have := P.windingNumber_eq_of_mem_jordanInterior h hpi hqi
    omega
  · have h0 := P.windingNumber_eq_zero_of_mem_jordanExterior hqe
    exact ⟨1, Or.inl rfl, fun r hr => by
      rw [P.windingNumber_eq_of_mem_jordanInterior h hr hpi]; omega⟩
  · have h0 := P.windingNumber_eq_zero_of_mem_jordanExterior hpe
    exact ⟨-1, Or.inr rfl, fun r hr => by
      rw [P.windingNumber_eq_of_mem_jordanInterior h hr hqi]; omega⟩
  · have h0 := P.windingNumber_eq_zero_of_mem_jordanExterior hpe
    have h1 := P.windingNumber_eq_zero_of_mem_jordanExterior hqe
    omega

/-- A closed curve is *negatively oriented* when its winding number is `−1` on its interior. -/
def IsNegativelyOriented : Prop := ∀ p ∈ jordanInterior c a b, P.windingNumber p = -1

/-- A Jordan curve is positively or negatively oriented. -/
theorem isPositivelyOriented_or_isNegativelyOriented (h : IsJordanCurve c a b) :
    P.IsPositivelyOriented ∨ P.IsNegativelyOriented := by
  obtain ⟨w, hw | hw, hall⟩ := P.exists_windingNumber_eq_one_or_neg_one h
  · exact Or.inl fun p hp => (hall p hp).trans hw
  · exact Or.inr fun p hp => (hall p hp).trans hw

/-! ### Reversing the orientation -/

/-- The reversed path `t ↦ c (a + b − t)` on `[a, b]`. -/
def reverse : ClosedPiecewiseC1 (fun t => c (a + b - t)) a b where
  n := P.n
  t k := a + b - P.t (P.n - k)
  g k s := P.g (P.n - 1 - k) (a + b - s)
  lt k hk := by
    have h := P.lt (P.n - 1 - k) (by omega)
    rw [show P.n - 1 - k + 1 = P.n - k by omega] at h
    show a + b - P.t (P.n - k) < a + b - P.t (P.n - (k + 1))
    rw [show P.n - (k + 1) = P.n - 1 - k by omega]
    linarith
  first := by
    show a + b - P.t (P.n - 0) = a
    rw [Nat.sub_zero, P.last]
    ring
  last := by
    show a + b - P.t (P.n - P.n) = b
    rw [Nat.sub_self, P.first]
    ring
  contDiff k hk := (P.contDiff _ (by omega)).comp (contDiff_const.sub contDiff_id)
  eqOn k hk s hs := by
    have hs : s ∈ Icc (a + b - P.t (P.n - k)) (a + b - P.t (P.n - (k + 1))) := hs
    have hk' : P.n - 1 - k < P.n := by omega
    rw [show P.n - (k + 1) = P.n - 1 - k by omega,
      show P.n - k = P.n - 1 - k + 1 by omega] at hs
    have hs' : a + b - s ∈ Icc (P.t (P.n - 1 - k)) (P.t (P.n - 1 - k + 1)) :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact P.eqOn _ hk' hs'
  closed := by
    show c (a + b - a) = c (a + b - b)
    rw [add_sub_cancel_left, add_sub_cancel_right]
    exact P.closed.symm

/-- The reversed path has the same image. -/
theorem image_reverse (c : ℝ → ℂ) (a b : ℝ) :
    (fun t => c (a + b - t)) '' Icc a b = c '' Icc a b := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨a + b - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨a + b - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩

theorem curve_reverse : P.reverse.curve = P.curve := image_reverse c a b

theorem jordanInterior_reverse :
    jordanInterior (fun t => c (a + b - t)) a b = jordanInterior c a b := by
  simp only [jordanInterior, image_reverse]

/-- Reversing the path negates contour integrals. -/
theorem contourIntegral_reverse (f : ℂ → ℂ) :
    P.reverse.contourIntegral f = -P.contourIntegral f := by
  have hrefl := Finset.sum_range_reflect
    (fun j => ∫ s in P.t j..P.t (j + 1), f (P.g j s) * deriv (P.g j) s) P.n
  simp only [contourIntegral]
  rw [← hrefl, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  set j := P.n - 1 - k with hj
  have hjn : j < P.n := by omega
  have hd : ∀ s, deriv (fun s => P.g j (a + b - s)) s = -deriv (P.g j) (a + b - s) := fun s =>
    ((((P.contDiff j hjn).differentiable one_ne_zero) (a + b - s)).hasDerivAt.comp_const_sub
      (a + b) s).deriv
  show ∫ s in a + b - P.t (P.n - k)..a + b - P.t (P.n - (k + 1)),
      f (P.g j (a + b - s)) * deriv (fun s => P.g j (a + b - s)) s = _
  simp only [hd, mul_neg, intervalIntegral.integral_neg]
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := a + b - P.t (P.n - k)) (b := a + b - P.t (P.n - (k + 1)))
    (fun x => f (P.g j x) * deriv (P.g j) x) (a + b)
  rw [hsub, sub_sub_cancel, sub_sub_cancel, show P.n - (k + 1) = j by omega,
    show P.n - k = j + 1 by omega]

/-- Reversing the path negates the winding number. -/
theorem windingNumber_reverse {p : ℂ} (hp : p ∉ P.curve) :
    P.reverse.windingNumber p = -P.windingNumber p := by
  have hp' : p ∉ P.reverse.curve := by rwa [P.curve_reverse]
  have h1 := P.reverse.contourIntegral_inv_eq hp'
  rw [contourIntegral_reverse, P.contourIntegral_inv_eq hp] at h1
  have h2 : ((P.reverse.windingNumber p : ℤ) : ℂ) = ((-P.windingNumber p : ℤ) : ℂ) := by
    refine mul_left_cancel₀ two_pi_I_ne_zero ?_
    push_cast
    rw [← h1]
    ring
  exact_mod_cast h2

/-- **Every Jordan curve is positively oriented in one of its two directions.** -/
theorem isPositivelyOriented_or_reverse (h : IsJordanCurve c a b) :
    P.IsPositivelyOriented ∨ P.reverse.IsPositivelyOriented := by
  rcases P.isPositivelyOriented_or_isNegativelyOriented h with hpos | hneg
  · exact Or.inl hpos
  · refine Or.inr fun p hp => ?_
    rw [jordanInterior_reverse] at hp
    rw [P.windingNumber_reverse hp.1, hneg p hp]
    rfl

end ClosedPiecewiseC1

end Azurite.JordanCurve
