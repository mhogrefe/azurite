/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Aomoto

/-!
# DLMF 5.14.4 on the full range of `c`

DLMF states 5.14.4 for `ℜc > −min(1/n, ℜa/(n − 1), ℜb/(n − 1))`. For `ℜc ≤ 0` the integrand is
singular on the diagonals `tᵢ = tⱼ`, and convergence is the issue. We prove it by **Landau's
theorem** for Laplace transforms of positive measures: with `L = 2 ln|Δ| ≤ 0` and real `a, b`,
`F(c) = ∫ e^{cL} ∏ tᵢ^{a−1}(1 − tᵢ)^{b−1}` has nonnegative Taylor coefficients
`(−1)ᵏF⁽ᵏ⁾(1) = ∫ (−L)ᵏ e^{L} ⋯ ≥ 0` at `c = 1`, and agrees near `1` with the closed form, which is
holomorphic on `ℜc > c₀` (all Gamma poles are real and `≤ c₀`). So the Taylor series at `1`
converges on the disc of radius `1 − c₀`; at a real point `c < 1` all its terms are nonnegative, and
Tonelli turns it back into `∫ e^{cL} ⋯`, which is therefore finite
(`integrable_exp_of_taylor`). Analytic continuation in `c` then extends 5.14.4.
-/

open Finset MeasureTheory

namespace Azurite.DLMF

/-! ### Landau's theorem for Laplace transforms of positive measures -/

/-- `|u|^m e^{σu} ≤ m!/(σ/2)^m · e^{(σ/2)u}` for `u ≤ 0`, `σ > 0`. -/
theorem abs_pow_mul_exp_le {u σ : ℝ} (hu : u ≤ 0) (hσ : 0 < σ) (m : ℕ) :
    |u| ^ m * Real.exp (σ * u) ≤ m.factorial / (σ / 2) ^ m * Real.exp (σ / 2 * u) := by
  have h := Real.pow_div_factorial_le_exp (σ / 2 * |u|) (by positivity) m
  rw [abs_of_nonpos hu] at h ⊢
  have hpos : 0 < (σ / 2) ^ m := by positivity
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [mul_pow, div_le_iff₀ hf] at h
  set E := Real.exp (σ / 2 * u)
  have he : Real.exp (σ * u) = E * E := by rw [← Real.exp_add]; ring_nf
  have he2 : Real.exp (σ / 2 * -u) * E = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [he, div_mul_eq_mul_div, le_div_iff₀ hpos]
  calc (-u) ^ m * (E * E) * (σ / 2) ^ m = ((σ / 2) ^ m * (-u) ^ m) * (E * E) := by ring
    _ ≤ (Real.exp (σ / 2 * -u) * m.factorial) * (E * E) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = m.factorial * E := by
        rw [show Real.exp (σ / 2 * -u) * m.factorial * (E * E) =
          m.factorial * (Real.exp (σ / 2 * -u) * E) * E by ring, he2, mul_one]

theorem hasSum_exp_div (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / k.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

section Landau

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {L g : α → ℝ}

/-- `∫ Lᵏ e^{zL} g`. -/
noncomputable def momentF (μ : Measure α) (L g : α → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t, (L t : ℂ) ^ k * Complex.exp (z * L t) * g t ∂μ

omit [MeasurableSpace α] in
theorem norm_moment_integrand (k : ℕ) (z : ℂ) (t : α) (hg : 0 ≤ g t) :
    ‖(L t : ℂ) ^ k * Complex.exp (z * L t) * g t‖ =
      |L t| ^ k * Real.exp (z.re * L t) * g t := by
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hg, Complex.norm_exp]
  simp

omit [MeasurableSpace α] in
theorem norm_moment_integrand_le (k : ℕ) {z : ℂ} {σ : ℝ} (hσ : 0 < σ) (hz : σ ≤ z.re) (t : α)
    (hL : L t ≤ 0) (hg : 0 ≤ g t) :
    ‖(L t : ℂ) ^ k * Complex.exp (z * L t) * g t‖ ≤
      k.factorial / (σ / 2) ^ k * (Real.exp (σ / 2 * L t) * g t) := by
  rw [norm_moment_integrand k z t hg]
  have h1 : Real.exp (z.re * L t) ≤ Real.exp (σ * L t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hz hL)
  calc |L t| ^ k * Real.exp (z.re * L t) * g t ≤ |L t| ^ k * Real.exp (σ * L t) * g t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hg
    _ ≤ k.factorial / (σ / 2) ^ k * Real.exp (σ / 2 * L t) * g t :=
        mul_le_mul_of_nonneg_right (abs_pow_mul_exp_le hL hσ k) hg
    _ = _ := by ring

variable (hLm : Measurable L) (hgm : Measurable g) (hL0 : ∀ᵐ t ∂μ, L t ≤ 0)
  (hg0 : ∀ᵐ t ∂μ, 0 ≤ g t)
  (hI : ∀ σ : ℝ, 0 < σ → Integrable (fun t => Real.exp (σ * L t) * g t) μ)
include hLm hgm hL0 hg0 hI

theorem integrable_moment (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t => (L t : ℂ) ^ k * Complex.exp (z * L t) * g t) μ := by
  refine Integrable.mono' ((hI (z.re / 2) (by positivity)).const_mul
    (k.factorial / (z.re / 2) ^ k)) (by fun_prop) ?_
  filter_upwards [hL0, hg0] with t ht hgt
  exact norm_moment_integrand_le k hz le_rfl t ht hgt

theorem integrable_pow_mul_exp (k : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t => L t ^ k * (Real.exp (σ * L t) * g t)) μ := by
  have h := (integrable_moment hLm hgm hL0 hg0 hI k (z := (σ : ℂ)) (by simpa)).norm
  refine h.mono' (by fun_prop) ?_
  filter_upwards [hg0] with t hgt
  rw [norm_moment_integrand k _ t hgt, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg
    (mul_nonneg (Real.exp_pos _).le hgt), Complex.ofReal_re, mul_assoc]

theorem hasDerivAt_momentF (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (momentF μ L g k) (momentF μ L g (k + 1) z) z := by
  have hball : ∀ w ∈ Metric.ball z (z.re / 2), z.re / 2 ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re] at this
    linarith [(abs_le.mp (this.trans hw.le)).1]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun w t => (L t : ℂ) ^ k * Complex.exp (w * L t) * g t)
    (F' := fun w t => (L t : ℂ) ^ (k + 1) * Complex.exp (w * L t) * g t)
    (bound := fun t => (k + 1).factorial / (z.re / 2 / 2) ^ (k + 1) *
      (Real.exp (z.re / 2 / 2 * L t) * g t))
    (Metric.ball_mem_nhds z (half_pos hz))
    (Filter.Eventually.of_forall fun w => by fun_prop)
    (integrable_moment hLm hgm hL0 hg0 hI k hz) (by fun_prop)
    (by
      filter_upwards [hL0, hg0] with t ht hgt
      intro w hw
      exact norm_moment_integrand_le (k + 1) (by positivity) (hball w hw) t ht hgt)
    ((hI _ (by positivity)).const_mul _)
    (ae_of_all _ fun t w _ => by
      have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w * L t))
          (Complex.exp (w * L t) * (1 * L t)) w :=
        ((hasDerivAt_id w).mul_const (L t : ℂ)).cexp
      convert (h1.const_mul ((L t : ℂ) ^ k)).mul_const (g t : ℂ) using 1
      ring)
  exact h.2

theorem iteratedDeriv_momentF (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv k (momentF μ L g 0) z = momentF μ L g k z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (momentF μ L g 0) =ᶠ[nhds z] momentF μ L g k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using ih hw
    rw [hev.deriv_eq]
    exact (hasDerivAt_momentF hLm hgm hL0 hg0 hI k hz).deriv

/-- **Landau's theorem** (Laplace transform of a positive measure): if
`F(z) = ∫ e^{zL} g` (`L ≤ 0`, `g ≥ 0`, finite for `z > 0`) agrees near `s₀ > 0` with a function
holomorphic on the disc of radius `R` about `s₀`, then `∫ e^{sL} g < ∞` for all real
`s > s₀ − R`. -/
theorem integrable_exp_of_taylor {s₀ R : ℝ} (hs₀ : 0 < s₀) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (Metric.ball (s₀ : ℂ) R))
    (hGF : G =ᶠ[nhds (s₀ : ℂ)] momentF μ L g 0) {s : ℝ} (hs : s₀ - R < s) :
    Integrable (fun t => Real.exp (s * L t) * g t) μ := by
  by_cases hss : s₀ ≤ s
  · exact hI s (by linarith)
  push Not at hss
  have hmem : (s : ℂ) ∈ Metric.ball (s₀ : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hsum := Complex.hasSum_taylorSeries_on_ball hG hmem
  have hder : ∀ k, iteratedDeriv k G s₀ = momentF μ L g k s₀ := fun k =>
    (hGF.iteratedDeriv_eq k).trans (iteratedDeriv_momentF hLm hgm hL0 hg0 hI k (by simpa))
  set a : ℕ → ℝ := fun k => ∫ t, ((s - s₀) * L t) ^ k / k.factorial *
    (Real.exp (s₀ * L t) * g t) ∂μ with ha
  have hterm : ∀ k : ℕ, ((k.factorial : ℂ))⁻¹ • ((s : ℂ) - s₀) ^ k • iteratedDeriv k G s₀ =
      (a k : ℂ) := by
    intro k
    rw [hder, momentF, smul_eq_mul, smul_eq_mul, ← integral_const_mul, ← integral_const_mul,
      ha, ← integral_complex_ofReal]
    congr 1; ext t
    rw [mul_pow]
    push_cast
    ring
  have h2 : HasSum (fun k => (a k : ℂ)) (G s) := by
    convert hsum using 1; ext k; exact (hterm k).symm
  have hsumR : HasSum a (G s).re := by
    simpa using Complex.reCLM.hasSum h2
  have hti : ∀ k : ℕ, Integrable (fun t => ((s - s₀) * L t) ^ k / k.factorial *
      (Real.exp (s₀ * L t) * g t)) μ := fun k => by
    refine ((integrable_pow_mul_exp hLm hgm hL0 hg0 hI k hs₀).const_mul
      ((s - s₀) ^ k / k.factorial)).congr (ae_of_all _ fun t => ?_)
    simp only; rw [mul_pow]; ring
  have htn : ∀ k : ℕ, 0 ≤ᵐ[μ] fun t => ((s - s₀) * L t) ^ k / k.factorial *
      (Real.exp (s₀ * L t) * g t) := fun k => by
    filter_upwards [hL0, hg0] with t ht hgt
    have : 0 ≤ (s - s₀) * L t := mul_nonneg_of_nonpos_of_nonpos (by linarith) ht
    simp only [Pi.zero_apply]
    positivity
  have ha0 : ∀ k, 0 ≤ a k := fun k => integral_nonneg_of_ae (htn k)
  have hfin : ∫⁻ t, ENNReal.ofReal (Real.exp (s * L t) * g t) ∂μ =
      ENNReal.ofReal (∑' k, a k) := by
    calc ∫⁻ t, ENNReal.ofReal (Real.exp (s * L t) * g t) ∂μ
        = ∫⁻ t, ∑' k : ℕ, ENNReal.ofReal (((s - s₀) * L t) ^ k / k.factorial *
            (Real.exp (s₀ * L t) * g t)) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hL0, hg0] with t ht hgt
          have hx : 0 ≤ (s - s₀) * L t := mul_nonneg_of_nonpos_of_nonpos (by linarith) ht
          have hS := (hasSum_exp_div ((s - s₀) * L t)).mul_right (Real.exp (s₀ * L t) * g t)
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hS.summable, hS.tsum_eq,
            ← mul_assoc, ← Real.exp_add]
          congr 3; ring
      _ = ∑' k : ℕ, ∫⁻ t, ENNReal.ofReal (((s - s₀) * L t) ^ k / k.factorial *
            (Real.exp (s₀ * L t) * g t)) ∂μ :=
          lintegral_tsum fun k => (hti k).aemeasurable.ennreal_ofReal
      _ = ∑' k, ENNReal.ofReal (a k) := by
          congr 1; ext k; rw [ha, ofReal_integral_eq_lintegral_ofReal (hti k) (htn k)]
      _ = ENNReal.ofReal (∑' k, a k) := (ENNReal.ofReal_tsum_of_nonneg ha0 hsumR.summable).symm
  refine ⟨(by fun_prop : Measurable fun t => Real.exp (s * L t) * g t).aestronglyMeasurable, ?_⟩
  have hnn : 0 ≤ᵐ[μ] fun t => Real.exp (s * L t) * g t := by
    filter_upwards [hg0] with t hgt; simp only [Pi.zero_apply]; positivity
  rw [hasFiniteIntegral_iff_ofReal hnn, hfin]
  exact ENNReal.ofReal_lt_top

end Landau

/-! ### The domain `ℜc > −min(1/n, ℜa/(n − 1), ℜb/(n − 1))` -/

variable {n : ℕ}

/-- DLMF's range of `c` in 5.14.4 (`ℜa, ℜb > 0` are assumed separately):
`n ℜc > −1`, `(n − 1) ℜc > −ℜa`, `(n − 1) ℜc > −ℜb`. -/
def selbergDomain (n : ℕ) (a b : ℂ) : Set ℂ :=
  {c | -1 < (n : ℝ) * c.re ∧ -a.re < ((n - 1 : ℕ) : ℝ) * c.re ∧
    -b.re < ((n - 1 : ℕ) : ℝ) * c.re}

theorem isOpen_selbergDomain (n : ℕ) (a b : ℂ) : IsOpen (selbergDomain n a b) := by
  simp only [selbergDomain, Set.ofPred_and]
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop)))

theorem convex_selbergDomain (n : ℕ) (a b : ℂ) : Convex ℝ (selbergDomain n a b) := by
  intro x hx y hy p q hp hq hpq
  simp only [selbergDomain, Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re,
    smul_eq_mul] at *
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨k1, k2, k3⟩ := hy
  have key : ∀ {A J : ℝ}, -A < J * x.re → -A < J * y.re → -A < J * (p * x.re + q * y.re) := by
    intro A J hu hv
    rw [show J * (p * x.re + q * y.re) = p * (J * x.re) + q * (J * y.re) by ring]
    rcases eq_or_lt_of_le hp with h | h
    · subst h; rw [zero_add] at hpq; subst hpq; simpa using hv
    · have hA : p * (-A) + q * (-A) = -A := by rw [← add_mul, hpq, one_mul]
      linarith [mul_lt_mul_of_pos_left hu h, mul_le_mul_of_nonneg_left hv.le hq]
  exact ⟨key h1 k1, key h2 k2, key h3 k3⟩

theorem pos_selbergDomain {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℂ} (hc : 0 < c.re) :
    c ∈ selbergDomain n a b := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    (Nat.cast_nonneg (n - 1) : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ))]

theorem mem_selbergDomain_of_re_le {a b : ℂ} {c z : ℂ} (hc : c ∈ selbergDomain n a b)
    (hcz : c.re ≤ z.re) : z ∈ selbergDomain n a b := by
  obtain ⟨h1, h2, h3⟩ := hc
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn' : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem add_mul_re_pos {p x J j : ℝ} (hp : 0 < p) (hJ : -p < J * x) (hj0 : 0 ≤ j)
    (hjJ : j ≤ J) : 0 < p + j * x := by
  rcases le_or_gt 0 x with hx | hx
  · nlinarith
  · nlinarith

theorem natSub_one_ge (n : ℕ) : (n : ℝ) - 1 ≤ ((n - 1 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [Nat.cast_sub h]; simp

theorem differentiableAt_Gamma_of_re {f : ℂ → ℂ} {c : ℂ} (hf : DifferentiableAt ℂ f c)
    (h : 0 < (f c).re) : DifferentiableAt ℂ (fun z => Complex.Gamma (f z)) c := by
  refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp c hf
  rw [hm] at h
  have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  simp at h
  linarith

theorem Gamma_ne_zero_of_re' {s : ℂ} (h : 0 < s.re) : Complex.Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m hm => ?_
  rw [hm] at h
  have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  simp at h
  linarith

/-- The closed form of 5.14.4 is holomorphic on DLMF's range. -/
theorem differentiableOn_selbergRHS {m : ℕ} (hm : m ≤ n) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) : DifferentiableOn ℂ (selbergRHS n m a b) (selbergDomain n a b) := by
  intro c hc
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨h1, h2, h3⟩ := hc
  have hsub := natSub_one_ge n
  have hab : -(a.re + b.re) < (2 * ((n - 1 : ℕ) : ℝ)) * c.re := by linarith
  have hfun : selbergRHS n m a b = fun c =>
      ((Complex.Gamma (1 + c))⁻¹) ^ n *
      (∏ k ∈ range m, (a + ((n : ℂ) - (k + 1)) * c) / (a + b + (2 * n - (k + 1) - 1) * c)) *
      ∏ k ∈ range n, Complex.Gamma (a + ((n : ℂ) - (k + 1)) * c) *
        Complex.Gamma (b + ((n : ℂ) - (k + 1)) * c) * Complex.Gamma (1 + (k + 1) * c) *
          (Complex.Gamma (a + b + (2 * n - (k + 1) - 1) * c))⁻¹ := by
    funext c; simp only [selbergRHS, inv_pow, div_eq_mul_inv]
  rw [hfun]
  refine (((Complex.differentiable_one_div_Gamma.comp
    (by fun_prop : Differentiable ℂ fun z : ℂ => 1 + z)) c).pow n).mul ?_ |>.mul ?_
  · refine DifferentiableAt.fun_finsetProd fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ n := by
      have := mem_range.mp hk; exact_mod_cast (by omega : k + 1 ≤ n)
    refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.zero_re] at this
    have hpos : 0 < a.re + b.re + (2 * (n : ℝ) - (k + 1) - 1) * c.re :=
      add_mul_re_pos (by linarith) hab (by linarith) (by linarith)
    simp at this
    linarith
  · refine DifferentiableAt.fun_finsetProd fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ n := by
      have := mem_range.mp hk; exact_mod_cast (by omega : k + 1 ≤ n)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine (((differentiableAt_Gamma_of_re (by fun_prop) ?_).mul
      (differentiableAt_Gamma_of_re (by fun_prop) ?_)).mul
      (differentiableAt_Gamma_of_re (by fun_prop) ?_)).mul
      ((Complex.differentiable_one_div_Gamma.comp (by fun_prop :
        Differentiable ℂ fun z : ℂ => a + b + (2 * n - (k + 1) - 1) * z)) c)
    · simp only [Complex.add_re]
      have := add_mul_re_pos (x := c.re) (j := (n : ℝ) - (k + 1)) ha h2 (by linarith)
        (by linarith)
      simpa using this
    · have := add_mul_re_pos (x := c.re) (j := (n : ℝ) - (k + 1)) hb h3 (by linarith)
        (by linarith)
      simpa using this
    · have := add_mul_re_pos (x := c.re) (j := (k : ℝ) + 1) one_pos h1 (by linarith)
        (by linarith)
      simpa using this

/-! ### Null sets -/

theorem ae_vandermondeDelta_ne_zero :
    ∀ᵐ t ∂(volume : Measure (Fin n → ℝ)), vandermondeDelta t ≠ 0 := by
  have h' : ∀ᵐ t ∂(volume : Measure (Fin n → ℝ)), ∀ i j : Fin n, i ≠ j → t i ≠ t j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact ae_of_all _ fun _ h => absurd hij h
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_coord_eq_null hij)] with t ht _
      exact ht
  filter_upwards [h'] with t ht
  exact prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr (ht i j (ne_of_lt (mem_Ioi.mp hj)))

theorem ae_interior :
    ∀ᵐ t ∂(volume : Measure (Fin n → ℝ)), ∀ i, t i ≠ 0 ∧ t i ≠ 1 := by
  rw [ae_all_iff]; intro i
  have h0 : volume {t : Fin n → ℝ | t i = 0} = 0 := by
    rw [volume_pi]; exact Measure.pi_hyperplane _ i 0
  have h1 : volume {t : Fin n → ℝ | t i = 1} = 0 := by
    rw [volume_pi]; exact Measure.pi_hyperplane _ i 1
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0, measure_eq_zero_iff_ae_notMem.mp h1]
    with t ht0 ht1 using ⟨ht0, ht1⟩

/-! ### Convergence -/

theorem jacobiWeight_ofReal_eq_norm {a b : ℝ} {t : Fin n → ℝ}
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) :
    jacobiWeight (a : ℂ) (b : ℂ) t = ((‖jacobiWeight (a : ℂ) (b : ℂ) t‖ : ℝ) : ℂ) := by
  have hJ : jacobiWeight (a : ℂ) (b : ℂ) t =
      ((∏ i, t i ^ (a - 1) * (1 - t i) ^ (b - 1) : ℝ) : ℂ) := by
    simp only [jacobiWeight]
    push_cast
    refine prod_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      Complex.ofReal_cpow (ht i).1, Complex.ofReal_cpow (by linarith [(ht i).2] : 0 ≤ 1 - t i)]
  rw [hJ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (prod_nonneg fun i _ =>
    mul_nonneg (Real.rpow_nonneg (ht i).1 _) (Real.rpow_nonneg (by linarith [(ht i).2]) _))]

theorem norm_jacobiWeight_re {a b : ℂ} {t : Fin n → ℝ} (ht : ∀ i, 0 < t i ∧ t i < 1) :
    ‖jacobiWeight a b t‖ = ‖jacobiWeight (a.re : ℂ) (b.re : ℂ) t‖ := by
  simp only [jacobiWeight, norm_prod, norm_mul]
  refine prod_congr rfl fun i _ => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht i).1, Complex.norm_cpow_eq_rpow_re_of_pos (ht i).1,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [(ht i).2] : 0 < 1 - t i),
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [(ht i).2] : 0 < 1 - t i)]
  simp

/-- `‖Φ‖ = e^{ℜc · 2 ln|Δ|} ‖w_{ℜa,ℜb}‖` on the open cube off the diagonals. -/
theorem norm_selbergF_eq {a b c : ℂ} {t : Fin n → ℝ} (ht : ∀ i, 0 < t i ∧ t i < 1)
    (hΔ : vandermondeDelta t ≠ 0) :
    ‖selbergF a b c t‖ = Real.exp (c.re * (2 * Real.log |vandermondeDelta t|)) *
      ‖jacobiWeight (a.re : ℂ) (b.re : ℂ) t‖ := by
  rw [selbergF, norm_mul, norm_jacobiWeight_re ht,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hΔ), Real.rpow_def_of_pos (abs_pos.mpr hΔ)]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [mul_comm]
  congr 2
  ring

theorem measurable_logDelta : Measurable fun t : Fin n → ℝ =>
    2 * Real.log |vandermondeDelta t| := by
  unfold vandermondeDelta; fun_prop

/-- **Convergence** of Selberg's integral for real `a, b > 0` and real `c` in DLMF's range. -/
theorem integrable_selberg_real {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : (c : ℂ) ∈ selbergDomain n a b) :
    Integrable (fun t => Real.exp (c * (2 * Real.log |vandermondeDelta t|)) *
      ‖jacobiWeight (a : ℂ) (b : ℂ) t‖) (volume.restrict (Set.Icc (0 : Fin n → ℝ) 1)) := by
  have ha' : 0 < (a : ℂ).re := by simpa
  have hb' : 0 < (b : ℂ).re := by simpa
  set μ := volume.restrict (Set.Icc (0 : Fin n → ℝ) 1)
  set L : (Fin n → ℝ) → ℝ := fun t => 2 * Real.log |vandermondeDelta t|
  set g : (Fin n → ℝ) → ℝ := fun t => ‖jacobiWeight (a : ℂ) (b : ℂ) t‖
  have hLm : Measurable L := measurable_logDelta
  have hgm : Measurable g := by
    have : Measurable (jacobiWeight (m := n) (a : ℂ) (b : ℂ)) := by unfold jacobiWeight; fun_prop
    exact this.norm
  have hL0 : ∀ᵐ t ∂μ, L t ≤ 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_)
    have := Real.log_nonpos (abs_nonneg _) (abs_vandermondeDelta_le_one (mem_cube_iff.mp ht))
    simp only [L]; linarith
  have hg0 : ∀ᵐ t ∂μ, 0 ≤ g t := ae_of_all _ fun _ => norm_nonneg _
  have hgood : ∀ᵐ t ∂μ, t ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧ (∀ i, 0 < t i ∧ t i < 1) ∧
      vandermondeDelta t ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ae_interior,
      ae_restrict_of_ae ae_vandermondeDelta_ne_zero] with t ht hi hΔ
    refine ⟨ht, fun i => ?_, hΔ⟩
    have := mem_cube_iff.mp ht i
    exact ⟨lt_of_le_of_ne this.1 (hi i).1.symm, lt_of_le_of_ne this.2 (hi i).2⟩
  have hI : ∀ σ : ℝ, 0 < σ → Integrable (fun t => Real.exp (σ * L t) * g t) μ := by
    intro σ hσ
    have h := (selberg_cube_pos (n := n) ha' hb' (c := (σ : ℂ)) (by simpa)).1.norm
    refine h.congr ?_
    filter_upwards [hgood] with t ⟨_, hi, hΔ⟩
    rw [norm_selbergF_eq hi hΔ]
    simp [L, g]
  -- the radius
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_selbergDomain n a b) _ hc
  set c' := c - ε / 2
  have hc' : (c' : ℂ) ∈ selbergDomain n a b := hball (by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_lt]; constructor <;> simp only [c'] <;> linarith)
  have hG : DifferentiableOn ℂ (selbergRHS n 0 (a : ℂ) (b : ℂ)) (Metric.ball (1 : ℂ) (1 - c')) := by
    refine (differentiableOn_selbergRHS (Nat.zero_le n) ha' hb').mono fun z hz => ?_
    refine mem_selbergDomain_of_re_le hc' ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re] at this
    have := (abs_lt.mp (lt_of_le_of_lt this hz)).1
    simp only [Complex.ofReal_re, Complex.one_re] at this ⊢
    linarith
  have hGF : selbergRHS n 0 (a : ℂ) (b : ℂ) =ᶠ[nhds ((1 : ℝ) : ℂ)] momentF μ L g 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < ((1 : ℝ) : ℂ).re by simp)] with z hz
    rw [← dlmf_5_14_4_selberg ha' hb' hz, momentF]
    refine integral_congr_ae ?_
    filter_upwards [hgood] with t ⟨ht, _, hΔ⟩
    rw [selbergF, jacobiWeight_ofReal_eq_norm (mem_cube_iff.mp ht),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hΔ)),
      ← Complex.ofReal_log (abs_nonneg _)]
    simp only [L, g, pow_zero, one_mul]
    push_cast
    ring_nf
  have h := integrable_exp_of_taylor hLm hgm hL0 hg0 hI (s₀ := 1) one_pos hG
    (by simpa using hGF) (s := c) (by simp only [c']; linarith)
  exact h

/-- **Convergence** of the Selberg integral on DLMF's range of parameters. -/
theorem integrableOn_selbergF {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : c ∈ selbergDomain n a b) :
    IntegrableOn (selbergF a b c) (Set.Icc (0 : Fin n → ℝ) 1) := by
  have hc' : ((c.re : ℝ) : ℂ) ∈ selbergDomain n (a.re : ℂ) (b.re : ℂ) := by
    simpa [selbergDomain] using hc
  have h := integrable_selberg_real ha hb hc'
  refine h.mono' (measurable_selbergF a b c).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ae_interior,
    ae_restrict_of_ae ae_vandermondeDelta_ne_zero] with t ht hi hΔ
  have hi' : ∀ i, 0 < t i ∧ t i < 1 := fun i => by
    have := mem_cube_iff.mp ht i
    exact ⟨lt_of_le_of_ne this.1 (hi i).1.symm, lt_of_le_of_ne this.2 (hi i).2⟩
  rw [norm_selbergF_eq hi' hΔ]

/-! ### Continuation -/

/-- `c ↦ ∫_{[0,1]ⁿ} t₁⋯tₘ Φ(t) dt` is holomorphic on DLMF's range. -/
theorem differentiableOn_selbergInt (m : ℕ) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun c => ∫ t in Set.Icc (0 : Fin n → ℝ) 1,
      initProd m t * selbergF a b c t) (selbergDomain n a b) := by
  refine differentiableOn_integral_of_holo
    (F := fun c t => initProd m t * selbergF a b c t)
    (F' := fun c t => initProd m t * (jacobiWeight a b t *
      (((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c) *
        Complex.log ((|vandermondeDelta t| : ℝ) : ℂ) * 2))) ?_ ?_ ?_
  · intro z _
    exact ((measurable_initProd m).mul (measurable_selbergF a b z)).aestronglyMeasurable
  · intro z _
    refine ((measurable_initProd m).mul ?_).aestronglyMeasurable
    unfold jacobiWeight vandermondeDelta
    fun_prop
  · intro z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_selbergDomain n a b) _ hz₀
    set w : ℂ := z₀ - ((ε / 2 : ℝ) : ℂ)
    have hw : w ∈ selbergDomain n a b := hball (by
      rw [Metric.mem_ball, dist_eq_norm, show w - z₀ = -((ε / 2 : ℝ) : ℂ) by simp [w], norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith)
    have hwre : w.re = z₀.re - ε / 2 := by simp [w]
    refine ⟨ε / 4, by positivity, (Metric.ball_subset_ball (by linarith)).trans hball,
      fun t => ‖selbergF a b w t‖, (integrableOn_selbergF ha hb hw).norm, ?_, ?_⟩
    · filter_upwards [ae_restrict_of_ae ae_vandermondeDelta_ne_zero] with t hΔ z _
      have h2 : HasDerivAt (fun c : ℂ => 2 * c) 2 z := by
        simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
      have h3 := h2.const_cpow (c := ((|vandermondeDelta t| : ℝ) : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hΔ)))
      simp only [selbergF]
      exact (h3.const_mul (jacobiWeight a b t)).const_mul (initProd m t)
    · filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ae_interior,
        ae_restrict_of_ae ae_vandermondeDelta_ne_zero] with t ht hi hΔ z hz
      have hi' : ∀ i, 0 < t i ∧ t i < 1 := fun i => by
        have := mem_cube_iff.mp ht i
        exact ⟨lt_of_le_of_ne this.1 (hi i).1.symm, lt_of_le_of_ne this.2 (hi i).2⟩
      have hzre : w.re ≤ z.re := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hz
        have := Complex.abs_re_le_norm (z - z₀)
        rw [Complex.sub_re] at this
        linarith [(abs_le.mp (this.trans hz)).1]
      have hL : 2 * Real.log |vandermondeDelta t| ≤ 0 := by
        have := Real.log_nonpos (abs_nonneg _) (abs_vandermondeDelta_le_one (mem_cube_iff.mp ht))
        linarith
      rw [norm_mul, norm_selbergF_eq hi' hΔ, norm_selbergF_eq hi' hΔ]
      calc ‖initProd m t‖ * (Real.exp (z.re * (2 * Real.log |vandermondeDelta t|)) *
            ‖jacobiWeight (a.re : ℂ) (b.re : ℂ) t‖)
          ≤ 1 * (Real.exp (w.re * (2 * Real.log |vandermondeDelta t|)) *
            ‖jacobiWeight (a.re : ℂ) (b.re : ℂ) t‖) :=
            mul_le_mul (norm_initProd_le (mem_cube_iff.mp ht))
              (mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hzre hL)) (norm_nonneg _))
              (by positivity) zero_le_one
        _ = _ := one_mul _

/-- **DLMF 5.14.4** (Selberg's integral with Aomoto's factor) on DLMF's full range:
`ℜa > 0`, `ℜb > 0`, `ℜc > −min(1/n, ℜa/(n − 1), ℜb/(n − 1))`, `0 ≤ m ≤ n`:
`∫_{[0,1]ⁿ} t₁⋯tₘ ∏ tₖ^{a−1}(1 − tₖ)^{b−1} |Δ(t)|^{2c} dt =
∏_{k=1}^m (a+(n−k)c)/(a+b+(2n−k−1)c) ·
∏_{k=1}^n Γ(a+(n−k)c)Γ(b+(n−k)c)Γ(1+kc)/(Γ(a+b+(2n−k−1)c)Γ(1+c))`.
The range is stated without division: `n ℜc > −1`, `(n − 1) ℜc > −ℜa`, `(n − 1) ℜc > −ℜb`. -/
theorem dlmf_5_14_4_full {m : ℕ} (hm : m ≤ n) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc1 : -1 < (n : ℝ) * c.re) (hca : -a.re < ((n - 1 : ℕ) : ℝ) * c.re)
    (hcb : -b.re < ((n - 1 : ℕ) : ℝ) * c.re) :
    ∫ t in Set.Icc (0 : Fin n → ℝ) 1,
      (∏ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < m), (t i : ℂ)) * selbergF a b c t =
        selbergRHS n m a b c := by
  show (fun c => ∫ t in Set.Icc (0 : Fin n → ℝ) 1, initProd m t * selbergF a b c t) c = _
  set f : ℂ → ℂ := fun c => (∫ t in Set.Icc (0 : Fin n → ℝ) 1, initProd m t * selbergF a b c t) -
    selbergRHS n m a b c with hfdef
  have hf : DifferentiableOn ℂ f (selbergDomain n a b) :=
    (differentiableOn_selbergInt m ha hb).sub (differentiableOn_selbergRHS hm ha hb)
  have hz : f =ᶠ[nhds 1] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by simp)] with z hz
    simp only [hfdef, Pi.zero_apply]
    rw [sub_eq_zero]
    exact dlmf_5_14_4 hm ha hb hz
  have h := (hf.analyticOnNhd
    (isOpen_selbergDomain n a b)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_selbergDomain n a b).isPreconnected (pos_selbergDomain ha hb (by simp)) hz
    (show c ∈ selbergDomain n a b from ⟨hc1, hca, hcb⟩)
  exact sub_eq_zero.mp h

end Azurite.DLMF
