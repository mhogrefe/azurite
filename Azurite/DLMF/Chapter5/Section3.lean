/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section2
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# DLMF §5.3: Graphics

Formalizations of the mathematical content of the figures of <https://dlmf.nist.gov/5.3>.

## §5.3(i) Real Argument

* Figure 5.3.1, `Γ(x)` and `1/Γ(x)`: `Γ` is positive on `(0, ∞)` (`dlmf_5_3_F1_pos`) and has
  the sign `(−1)ⁿ⁺¹` on `(−n − 1, −n)` (`dlmf_5_3_F1_sign`); `1/Γ(x)` vanishes exactly at
  `x = 0, −1, −2, …` (`dlmf_5_3_F1_inv_zero`).  The minimum on the positive axis: there is
  exactly one minimizer `x₀` of `Γ` on `(0, ∞)` (`dlmf_5_3_F1_min_unique`, via the identity
  theorem — Mathlib's `Real.exists_isMinOn_Gamma_Ioi` leaves uniqueness as a TODO), with
  `1 < x₀ < 3/2` and `Γ(x₀) < 0.89` (`dlmf_5_3_F1_min`; `Γ(3/2) = √π/2`, and `ψ(3/2) > 0`).
  The caption's `x₀ = 1.46…` and the lower half of `Γ(x₀) = 0.88…` are DEFERRED to §5.4(iii),
  which gives fifteen digits of both (they need numerical values of `Γ` or `ψ` near `x₀` beyond
  the closed forms `ψ(1) = −γ`, `ψ(3/2) = 2 − 2 ln 2 − γ`, `Γ(3/2) = √π/2` used here).
* Figure 5.3.2, "`ln Γ(x)`. This function is convex on `(0, ∞)`" (`dlmf_5_3_F2`, Mathlib's
  `Real.convexOn_log_Gamma`).
* Figure 5.3.3, `ψ(x)`: real on the real axis (`dlmf_5_3_F3_real`), nondecreasing on `(0, ∞)`
  (`dlmf_5_3_F3_mono`), vanishing at the minimum `x₀` of `Γ` (`dlmf_5_3_F3_zero`); its poles
  are §5.2(i) (`dlmf_5_2_i_digamma_pole`).

## §5.3(ii) Complex Argument

* Figures 5.3.4–5.3.6, the surfaces `|Γ(x + iy)|`, `1/|Γ(x + iy)|`, `|ψ(x + iy)|`: symmetric
  under `y ↦ −y` (`dlmf_5_3_F4`, `dlmf_5_3_F5`, `dlmf_5_3_F6`; `digamma_conj`); the poles and
  zeros are §5.2(i).
-/

open Complex Filter Topology Set
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-! ### Figure 5.3.1: signs and zeros -/

/-- **Figure 5.3.1**: `Γ(x) > 0` for `x > 0`. -/
theorem dlmf_5_3_F1_pos {x : ℝ} (hx : 0 < x) : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx

/-- **Figure 5.3.1**: on `(−n − 1, −n)`, `Γ(x)` has the sign `(−1)ⁿ⁺¹`. -/
theorem dlmf_5_3_F1_sign (n : ℕ) {x : ℝ} (h1 : -((n : ℝ) + 1) < x) (h2 : x < -n) :
    0 < (-1) ^ (n + 1) * Real.Gamma x := by
  induction n generalizing x with
  | zero =>
    simp only [Nat.cast_zero, zero_add, neg_zero, pow_one, neg_one_mul] at h1 h2 ⊢
    have hp : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
    rw [Real.Gamma_add_one h2.ne] at hp
    nlinarith
  | succ n ih =>
    push_cast at h1 h2
    have hxneg : x < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h := ih (x := x + 1) (by linarith) (by linarith)
    rw [Real.Gamma_add_one hxneg.ne] at h
    have e1 : (-1 : ℝ) ^ (n + 1) * (x * Real.Gamma x) = x * ((-1) ^ (n + 1) * Real.Gamma x) := by
      ring
    have e2 : (-1 : ℝ) ^ (n + 1 + 1) * Real.Gamma x = -((-1) ^ (n + 1) * Real.Gamma x) := by
      ring
    rw [e1] at h
    rw [e2]
    nlinarith

/-- **Figure 5.3.1**: `1/Γ(x)` vanishes exactly at `x = 0, −1, −2, …`. -/
theorem dlmf_5_3_F1_inv_zero (x : ℝ) : (Real.Gamma x)⁻¹ = 0 ↔ ∃ n : ℕ, x = -n := by
  constructor
  · intro h
    by_contra hx
    push Not at hx
    exact Real.Gamma_ne_zero hx (inv_eq_zero.mp h)
  · rintro ⟨n, rfl⟩
    rw [Real.Gamma_neg_nat_eq_zero, inv_zero]

/-! ### `Γ′ = Γ ψ` on the real axis -/

theorem deriv_Gamma_eq_mul_digamma {z : ℂ} (hz : z ∉ gammaPoles) :
    deriv Gamma z = Gamma z * digamma z := by
  rw [dlmf_5_2_2]
  field_simp [dlmf_5_2_i_ne_zero hz]

theorem hasDerivAt_Gamma_real {x : ℝ} (hx : (x : ℂ) ∉ gammaPoles) :
    HasDerivAt Real.Gamma (Real.Gamma x * (digamma x).re) x := by
  have h := (differentiableAt_Gamma (x : ℂ) (not_mem_gammaPoles.mp hx)).hasDerivAt.real_of_complex
  rw [deriv_Gamma_eq_mul_digamma hx, Complex.Gamma_ofReal, re_ofReal_mul] at h
  convert h using 1
  funext t
  rw [Complex.Gamma_ofReal, ofReal_re]

/-- **Figure 5.3.3**: `ψ(x)` is real for real `x`. -/
theorem dlmf_5_3_F3_real (x : ℝ) : (digamma x).im = 0 := by
  by_cases hx : (x : ℂ) ∈ gammaPoles
  · obtain ⟨n, hn⟩ := hx
    rw [dlmf_5_2_2, ← hn, Gamma_neg_nat_eq_zero, div_zero, zero_im]
  · have hc := (differentiableAt_Gamma (x : ℂ) (not_mem_gammaPoles.mp hx)).hasDerivAt.comp_ofReal
    have hr := (hasDerivAt_Gamma_real hx).ofReal_comp
    have e : (fun y : ℝ => Gamma (y : ℂ)) = fun y : ℝ => ((Real.Gamma y : ℝ) : ℂ) :=
      funext fun y => Complex.Gamma_ofReal y
    rw [e] at hc
    rw [dlmf_5_2_2, hc.unique hr, Complex.Gamma_ofReal, ← ofReal_div, ofReal_im]

theorem hasDerivAt_log_Gamma_real {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (digamma x).re x := by
  have hp := (Real.Gamma_pos_of_pos hx).ne'
  have h := (hasDerivAt_Gamma_real (not_mem_gammaPoles_of_re_pos (by simpa using hx))).log hp
  rw [mul_div_cancel_left₀ _ hp] at h
  exact h

/-! ### The values `ψ(1)`, `ψ(3/2)` -/

theorem digamma_three_halves :
    digamma (3 / 2) = 2 - 2 * (Real.log 2 : ℂ) - Real.eulerMascheroniConstant := by
  have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := by
    intro m h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hl : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num)]; norm_num
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, digamma_apply_add_one _ hs, digamma_one_half, hl]
  norm_num
  ring

theorem digamma_three_halves_re_pos : 0 < (digamma ((3 / 2 : ℝ) : ℂ)).re := by
  have h := Real.log_two_lt_d9
  have hg := dlmf_3_12_4_partial.2
  push_cast
  rw [digamma_three_halves]
  simp only [sub_re, re_ofNat, mul_re, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
  norm_num at h hg ⊢
  linarith

theorem Gamma_three_halves_eq : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

/-! ### The minimum of `Γ` on `(0, ∞)` -/

/-- **Figure 5.3.3**: at a minimum `x₀` of `Γ` on `(0, ∞)`, `ψ(x₀) = 0`. -/
theorem dlmf_5_3_F3_zero {x₀ : ℝ} (hx₀ : 0 < x₀) (h : IsMinOn Real.Gamma (Ioi 0) x₀) :
    digamma x₀ = 0 := by
  have hd := hasDerivAt_Gamma_real (not_mem_gammaPoles_of_re_pos (by simpa using hx₀))
  have h0 := (h.isLocalMin (Ioi_mem_nhds hx₀)).hasDerivAt_eq_zero hd
  have hre : (digamma x₀).re = 0 :=
    (mul_eq_zero.mp h0).resolve_left (Real.Gamma_pos_of_pos hx₀).ne'
  exact Complex.ext (by rw [hre, zero_re]) (by rw [dlmf_5_3_F3_real, zero_im])

/-- `Γ` is constant on `[a, b]` when `a < b` are both minimizers on `(0, ∞)`. -/
theorem Gamma_eq_of_isMinOn {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hma : IsMinOn Real.Gamma (Ioi 0) a) (hmb : IsMinOn Real.Gamma (Ioi 0) b) {t : ℝ}
    (ht : t ∈ Icc a b) : Real.Gamma t = Real.Gamma a := by
  have hb : 0 < b := ha.trans hab
  have hle := Real.convexOn_Gamma.le_on_segment (mem_Ioi.mpr ha) (mem_Ioi.mpr hb)
    (by rw [segment_eq_Icc hab.le]; exact ht)
  have hba : Real.Gamma b = Real.Gamma a := le_antisymm (hmb (mem_Ioi.mpr ha)) (hma hb)
  rw [hba, max_self] at hle
  exact le_antisymm hle (hma (mem_Ioi.mpr (ha.trans_le ht.1)))

/-- **Figure 5.3.1**: the minimum of `Γ` on `(0, ∞)` is attained at only one point. -/
theorem dlmf_5_3_F1_min_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hma : IsMinOn Real.Gamma (Ioi 0) a) (hmb : IsMinOn Real.Gamma (Ioi 0) b) : a = b := by
  wlog hab : a < b generalizing a b
  · rcases lt_or_eq_of_le (not_lt.mp hab) with h | h
    · exact (this hb ha hmb hma h).symm
    · exact h.symm
  exfalso
  set m := Real.Gamma a with hm
  -- `Γ = m` near `a` on the right, hence everywhere off the poles
  set u : ℕ → ℂ := fun k => ((a + (b - a) / 2 * (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) with hu
  have hpos : ∀ k : ℕ, 0 < (b - a) / 2 * (1 / ((k : ℝ) + 1)) := fun k => by
    have : 0 < b - a := by linarith
    positivity
  have hle : ∀ k : ℕ, (b - a) / 2 * (1 / ((k : ℝ) + 1)) ≤ (b - a) / 2 := fun k => by
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have : 0 ≤ (b - a) / 2 := by linarith
    nlinarith
  have hlim : Tendsto u atTop (𝓝[≠] (a : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((b - a) / 2)
      have h1 := (h0.const_add a)
      rw [mul_zero, add_zero] at h1
      exact (continuous_ofReal.tendsto a).comp h1
    · intro h
      have := ofReal_injective h
      linarith [hpos k]
  have hfreq : ∃ᶠ z in 𝓝[≠] (a : ℂ), Gamma z = (m : ℂ) := by
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    rw [hu, Complex.Gamma_ofReal]
    congr 1
    exact Gamma_eq_of_isMinOn ha hab hma hmb ⟨by linarith [hpos k], by linarith [hle k]⟩
  have heq := dlmf_5_2_i_analytic.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_compl_gammaPoles (not_mem_gammaPoles_of_re_pos (by simpa using ha)) hfreq
  have h1 := heq (not_mem_gammaPoles_of_re_pos (show (0 : ℝ) < (1 : ℂ).re by simp))
  have h32 := heq (not_mem_gammaPoles_of_re_pos (show (0 : ℝ) < ((3 / 2 : ℝ) : ℂ).re by
    simp only [ofReal_re]; norm_num))
  rw [Gamma_one] at h1
  rw [Complex.Gamma_ofReal, ← h1] at h32
  have := Real.Gamma_three_div_two_lt_one
  have h32' : Real.Gamma (3 / 2) = 1 := by exact_mod_cast h32
  linarith

/-- **Figure 5.3.1**: `Γ` has a minimum on `(0, ∞)` at a point `x₀` with `1 < x₀ < 3/2`,
`Γ(x₀) < 0.89` and `ψ(x₀) = 0` (the caption's `x₀ = 1.46…`, `Γ(x₀) = 0.88…` are deferred to
§5.4(iii)). -/
theorem dlmf_5_3_F1_min :
    ∃ x₀ : ℝ, 1 < x₀ ∧ x₀ < 3 / 2 ∧ IsMinOn Real.Gamma (Ioi 0) x₀ ∧ Real.Gamma x₀ < 0.89 ∧
      digamma x₀ = 0 := by
  obtain ⟨x₀, ⟨h1, -⟩, hmin⟩ := Real.exists_isMinOn_Gamma_Ioi
  have hx₀ : 0 < x₀ := by linarith
  have hψ := dlmf_5_3_F3_zero hx₀ hmin
  have h32 : (0 : ℝ) < 3 / 2 := by norm_num
  have hG : Real.Gamma x₀ ≤ Real.Gamma (3 / 2) := hmin (mem_Ioi.mpr h32)
  refine ⟨x₀, h1, ?_, hmin, ?_, hψ⟩
  · by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le hc with hlt | heq
    · have hd := hasDerivAt_log_Gamma_real h32
      have hs := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt (mem_Ioi.mpr h32)
        (mem_Ioi.mpr hx₀) hlt hd
      rw [slope_def_field] at hs
      have hnum : (Real.log ∘ Real.Gamma) x₀ - (Real.log ∘ Real.Gamma) (3 / 2) ≤ 0 := by
        simp only [Function.comp_apply, sub_nonpos]
        exact Real.log_le_log (Real.Gamma_pos_of_pos hx₀) hG
      have : ((Real.log ∘ Real.Gamma) x₀ - (Real.log ∘ Real.Gamma) (3 / 2)) / (x₀ - 3 / 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnum (by linarith)
      linarith [digamma_three_halves_re_pos]
    · have := digamma_three_halves_re_pos
      rw [heq, hψ, zero_re] at this
      exact lt_irrefl _ this
  · have hs : √π < 1.78 := by
      rw [Real.sqrt_lt' (by norm_num)]
      nlinarith [Real.pi_lt_d2]
    rw [Gamma_three_halves_eq] at hG
    linarith

/-! ### Figures 5.3.2 and 5.3.3 -/

/-- **Figure 5.3.2**: "`ln Γ(x)`. This function is convex on `(0, ∞)`" (Mathlib's
`Real.convexOn_log_Gamma`). -/
theorem dlmf_5_3_F2 : ConvexOn ℝ (Ioi 0) (Real.log ∘ Real.Gamma) := Real.convexOn_log_Gamma

/-- **Figure 5.3.3**: `ψ(x)` is nondecreasing on `(0, ∞)` (the derivative of the convex
`ln Γ`). -/
theorem dlmf_5_3_F3_mono : MonotoneOn (fun x : ℝ => (digamma x).re) (Ioi 0) := by
  intro x hx y hy hxy
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · have h1 := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt hx hy hlt
      (hasDerivAt_log_Gamma_real hx)
    have h2 := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt hx hy hlt
      (hasDerivAt_log_Gamma_real hy)
    exact h1.trans h2
  · exact le_rfl

/-! ### §5.3(ii): symmetry of the surfaces -/

/-- `ψ(z̄) = conj ψ(z)`. -/
theorem digamma_conj (z : ℂ) : digamma (conj z) = conj (digamma z) := by
  by_cases hz : z ∈ gammaPoles
  · obtain ⟨n, rfl⟩ := hz
    have h0 : digamma (-(n : ℂ)) = 0 := by rw [dlmf_5_2_2, Gamma_neg_nat_eq_zero, div_zero]
    rw [show conj (-(n : ℂ)) = -(n : ℂ) by simp, h0, map_zero]
  · have hd := (differentiableAt_Gamma z (not_mem_gammaPoles.mp hz)).hasDerivAt
    have h2 := hd.conj_conj
    have e : (conj ∘ Gamma ∘ conj) = Gamma := by
      funext w
      rw [Function.comp_apply, Function.comp_apply, Gamma_conj, conj_conj]
    rw [e] at h2
    rw [dlmf_5_2_2, dlmf_5_2_2, h2.deriv, Gamma_conj, map_div₀]

/-- **Figure 5.3.4**: `|Γ(x − iy)| = |Γ(x + iy)|`. -/
theorem dlmf_5_3_F4 (z : ℂ) : ‖Gamma (conj z)‖ = ‖Gamma z‖ := by
  rw [Gamma_conj, Complex.norm_conj]

/-- **Figure 5.3.5**: `1/|Γ(x − iy)| = 1/|Γ(x + iy)|`. -/
theorem dlmf_5_3_F5 (z : ℂ) : ‖(Gamma (conj z))⁻¹‖ = ‖(Gamma z)⁻¹‖ := by
  rw [norm_inv, norm_inv, dlmf_5_3_F4]

/-- **Figure 5.3.6**: `|ψ(x − iy)| = |ψ(x + iy)|`. -/
theorem dlmf_5_3_F6 (z : ℂ) : ‖digamma (conj z)‖ = ‖digamma z‖ := by
  rw [digamma_conj, Complex.norm_conj]

end Azurite.DLMF
