/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Laplace
import Azurite.DLMF.Chapter2.Section3LaplaceCoeff

/-!
# DLMF §5.11(i): `gₖ = √2 (½)ₖ a_{2k}` (5.11.5)

Formalization of <https://dlmf.nist.gov/5.11>, equation 5.11.5, by Laplace's method.

* `Gamma_add_one_eq_laplace`: `Γ(x + 1) = x^{x+1} e^{−x} ∫₀^∞ e^{−x p(τ)} dτ`,
  `p(τ) = τ − 1 − ln τ` (`t = xτ`).
* DLMF 2.3.15 (`dlmf_2_3_15`) on `(1, ∞)` and, after `τ = −t`, on `(0, 1)`: with the expansions
  `p(1 ± u) = ∑ (∓1)ˢ u^{s+2}/(s + 2)` the coefficients are `laplaceB (∓1)`, i.e. `aₛ` and
  `(−1)ˢ aₛ` (`Section11Laplace.lean`), so the odd terms cancel and
  `√x ∫₀^∞ e^{−xp} ∼ ∑ Γ((s + 1)/2)(1 + (−1)ˢ) aₛ x^{−s/2}` (`hasPowExpansion_laplace`).
* `Γ*(x) = √x ∫₀^∞ e^{−xp}/√(2π)` and 5.11.3 give a second expansion of the same function in powers
  of `x^{−1/2}`; uniqueness (`HasPowExpansion.unique`) and `Γ(k + ½) = √π (½)ₖ` give
  `gₖ = √2 (½)ₖ a_{2k}` (`dlmf_5_11_5`).
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### From explicit bounds to DLMF expansions at `a+` -/

theorem isGenAsymp_real_of_bound {a : ℝ} {e : ℕ → ℝ} (he : ∀ s, e (s + 1) = e s + 1)
    {f : ℝ → ℝ} {cs : ℕ → ℝ}
    (hb : ∀ n : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ u : ℝ, 0 < u → u < δ →
      |f (a + u) - ∑ s ∈ Finset.range n, cs s * u ^ e s| ≤ C * u ^ e n) :
    IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ e s) f
      (fun s t => cs s * (t - a) ^ e s) := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · refine (tendsto_sub_self_nhdsGT a).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t - a := sub_pos.mpr ht
    rw [he, Real.rpow_add_one ht'.ne']
    have := Real.rpow_pos_of_pos ht' (e s)
    field_simp
  · obtain ⟨C, δ, hδ, hC⟩ := hb n
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [Ioo_mem_nhdsGT (show a < a + δ by linarith)] with t ht
    have hu : 0 < t - a := sub_pos.mpr ht.1
    have h := hC (t - a) hu (by linarith [ht.2])
    rw [add_sub_cancel] at h
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hu _),
      div_le_iff₀ (Real.rpow_pos_of_pos hu _)]
    exact h

/-- `p(τ) = τ − 1 − ln τ`. -/
noncomputable def laplaceP (τ : ℝ) : ℝ := τ - 1 - Real.log τ

theorem laplaceP_one : laplaceP 1 = 0 := by simp [laplaceP]

theorem laplaceP_nonneg {τ : ℝ} (hτ : 0 < τ) : 0 ≤ laplaceP τ := by
  have := Real.log_le_sub_one_of_pos hτ
  unfold laplaceP; linarith

/-- `p(1 + u) = ∑ (−1)ˢ u^{s+2}/(s + 2) + O(u^{n+2})`. -/
theorem laplaceP_right_bound (n : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1 / 2) :
    |laplaceP (1 + u) - ∑ s ∈ Finset.range n, laplacePs (-1) s * u ^ ((s : ℝ) + 2)| ≤
      2 * u ^ ((n : ℝ) + 2) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg, abs_of_pos hu]; linarith)
    (n + 1)
  rw [abs_neg, abs_of_pos hu, sub_neg_eq_add, Finset.sum_range_succ'] at h
  have e : ∑ s ∈ Finset.range n, laplacePs (-1) s * u ^ ((s : ℝ) + 2) =
      ∑ i ∈ Finset.range n, (-u) ^ (i + 1 + 1) / ((i + 1 : ℕ) + 1 : ℝ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [laplacePs, show (s : ℝ) + 2 = ((s + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      show s + 1 + 1 = s + 2 by ring, neg_pow u, pow_add (-1 : ℝ) s 2]
    push_cast
    ring
  rw [show ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, e,
    laplaceP, show (1 : ℝ) + u - 1 = u by ring]
  have hden : u ^ (n + 1 + 1) / (1 - u) ≤ 2 * u ^ (n + 2) := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_pos hu (n + 2)
    nlinarith
  calc |u - Real.log (1 + u) - ∑ i ∈ Finset.range n, (-u) ^ (i + 1 + 1) / ((i + 1 : ℕ) + 1 : ℝ)|
      = |∑ i ∈ Finset.range n, (-u) ^ (i + 1 + 1) / ((i + 1 : ℕ) + 1 : ℝ) +
          (-u) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + Real.log (1 + u)| := by
        rw [← abs_neg]; congr 1; push_cast; ring
    _ ≤ u ^ (n + 1 + 1) / (1 - u) := h
    _ ≤ 2 * u ^ (n + 2) := hden

/-- `p(1 − u) = ∑ u^{s+2}/(s + 2) + O(u^{n+2})`. -/
theorem laplaceP_left_bound (n : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1 / 2) :
    |laplaceP (1 - u) - ∑ s ∈ Finset.range n, laplacePs 1 s * u ^ ((s : ℝ) + 2)| ≤
      2 * u ^ ((n : ℝ) + 2) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := u) (by rw [abs_of_pos hu]; linarith) (n + 1)
  rw [abs_of_pos hu, Finset.sum_range_succ'] at h
  have e : ∑ s ∈ Finset.range n, laplacePs 1 s * u ^ ((s : ℝ) + 2) =
      ∑ i ∈ Finset.range n, u ^ (i + 1 + 1) / ((i + 1 : ℕ) + 1 : ℝ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [laplacePs, show (s : ℝ) + 2 = ((s + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      show s + 1 + 1 = s + 2 by ring, one_pow]
    push_cast
    ring
  rw [show ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, e,
    laplaceP, show (1 : ℝ) - u - 1 = -u by ring]
  have hden : u ^ (n + 1 + 1) / (1 - u) ≤ 2 * u ^ (n + 2) := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_pos hu (n + 2)
    nlinarith
  calc |-u - Real.log (1 - u) - ∑ i ∈ Finset.range n, u ^ (i + 1 + 1) / ((i + 1 : ℕ) + 1 : ℝ)|
      = |∑ i ∈ Finset.range n, u ^ (i + 1 + 1) / ((i + 1 : ℕ) + 1 : ℝ) +
          u ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + Real.log (1 - u)| := by
        rw [← abs_neg]; congr 1; push_cast; ring
    _ ≤ u ^ (n + 1 + 1) / (1 - u) := h
    _ ≤ 2 * u ^ (n + 2) := hden

/-- `u/(1 − σu) − ∑_{s<n} σˢ u^{s+1} = σⁿ u^{n+1}/(1 − σu)`. -/
theorem geom_div_sub_sum (σ u : ℝ) (hu : 1 - σ * u ≠ 0) (n : ℕ) :
    u / (1 - σ * u) - ∑ s ∈ Finset.range n, σ ^ s * u ^ (s + 1) =
      σ ^ n * u ^ (n + 1) / (1 - σ * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    field_simp
    ring

theorem laplaceDeriv_bound (σ : ℝ) (hσ : |σ| = 1) (n : ℕ) {u : ℝ} (hu : 0 < u)
    (hu1 : u < 1 / 2) :
    |u / (1 - σ * u) - ∑ s ∈ Finset.range n, ((s : ℝ) + 2) * laplacePs σ s *
      u ^ ((s : ℝ) + 2 - 1)| ≤ 2 * u ^ ((n : ℝ) + 2 - 1) := by
  have hσu : |σ * u| = u := by rw [abs_mul, hσ, one_mul, abs_of_pos hu]
  have h1 : 1 / 2 < 1 - σ * u := by
    have := neg_abs_le (σ * u); rw [hσu] at this; linarith [le_abs_self (σ * u)]
  have e : ∑ s ∈ Finset.range n, ((s : ℝ) + 2) * laplacePs σ s * u ^ ((s : ℝ) + 2 - 1) =
      ∑ s ∈ Finset.range n, σ ^ s * u ^ (s + 1) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [laplacePs, show (s : ℝ) + 2 - 1 = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have : (s : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  rw [e, geom_div_sub_sum σ u (by linarith) n,
    show (n : ℝ) + 2 - 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, abs_div,
    abs_mul, abs_pow, hσ, one_pow, one_mul, abs_of_pos (pow_pos hu _), abs_of_pos (by linarith),
    div_le_iff₀ (by linarith)]
  have := pow_pos hu (n + 1)
  nlinarith

theorem isGenAsymp_one {a : ℝ} :
    IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (((t - a) ^ ((s : ℝ) + 1 - 1) : ℝ) : ℂ))
      (fun _ => (1 : ℂ)) (fun s t => laplaceQs s * (((t - a) ^ ((s : ℝ) + 1 - 1) : ℝ) : ℂ)) := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_sub_self_nhdsGT a)
    rw [Complex.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t - a := sub_pos.mpr ht
    simp only [Function.comp_apply]
    push_cast
    rw [show (s : ℝ) + 1 + 1 - 1 = ((s : ℝ) + 1 - 1) + 1 by ring, Real.rpow_add_one ht'.ne']
    have := Real.rpow_pos_of_pos ht' ((s : ℝ) + 1 - 1)
    push_cast
    have h0 : (((t - a) ^ ((s : ℝ) + 1 - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    field_simp
  · refine isBoundedUnder_of_eventually_le (a := 1) (Eventually.of_forall fun t => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      dsimp only
      rw [Finset.sum_range_succ']
      have : ∀ i ∈ Finset.range m, laplaceQs (i + 1) * (((t - a) ^ (((i + 1 : ℕ) : ℝ) + 1 - 1) :
          ℝ) : ℂ) = 0 := fun i _ => by simp [laplaceQs]
      rw [Finset.sum_eq_zero this]
      simp [laplaceQs]

theorem laplaceP_sub_ge {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) :
    (τ - b) * (1 - 1 / b) ≤ laplaceP τ - laplaceP b := by
  have h := Real.log_le_sub_one_of_pos (div_pos hτ hb)
  rw [Real.log_div hτ.ne' hb.ne'] at h
  unfold laplaceP
  have : (τ - b) * (1 - 1 / b) = τ - b - (τ / b - 1) := by field_simp
  linarith

theorem laplaceP_pos {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≠ 1) : 0 < laplaceP τ := by
  have := Real.log_lt_sub_one_of_pos hτ h1
  unfold laplaceP; linarith

theorem hasDerivAt_laplaceP {τ : ℝ} (hτ : 0 < τ) : HasDerivAt laplaceP (1 - 1 / τ) τ := by
  have : HasDerivAt (fun τ => τ - 1 - Real.log τ) (1 - τ⁻¹) τ :=
    ((hasDerivAt_id τ).sub_const 1).sub (Real.hasDerivAt_log hτ.ne')
  rw [one_div]
  exact this

theorem continuousAt_laplaceP {τ : ℝ} (hτ : 0 < τ) : ContinuousAt laplaceP τ :=
  (hasDerivAt_laplaceP hτ).continuousAt

theorem integrableOn_exp_neg_laplaceP {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn (fun t => (Real.exp (-(x * laplaceP t)) : ℂ) * 1) (Ioi 1) := by
  have hG := ((Real.GammaIntegral_convergent (s := 2) two_pos).mono_set
    (Ioi_subset_Ioi zero_le_one)).const_mul (Real.exp 1)
  refine hG.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := lt_trans one_pos ht
    exact ((Complex.continuous_ofReal.continuousAt.comp (Real.continuous_exp.continuousAt.comp
      ((continuousAt_const.mul (continuousAt_laplaceP ht')).neg))).mul
      continuousAt_const).continuousWithinAt
  · have ht' : (0 : ℝ) < t := lt_trans one_pos ht
    have hp := laplaceP_nonneg ht'
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    calc Real.exp (-(x * laplaceP t)) ≤ Real.exp (-laplaceP t) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp 1 * (Real.exp (-t) * t) := by
          rw [laplaceP, show -(t - 1 - Real.log t) = 1 + (-t + Real.log t) by ring,
            Real.exp_add, Real.exp_add, Real.exp_log ht']

/-- Laplace's method on `(1, ∞)`: the coefficients are `laplaceB (−1)`. -/
theorem laplace_right :
    IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ))
      (fun x => ∫ t in Ioi (1 : ℝ), (Real.exp (-(x * laplaceP t)) : ℂ) * 1)
      (fun s x => (Real.Gamma (watsonExp 1 2 s) : ℂ) * laplaceB (-1) s *
        ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ)) := by
  have hreg : ∃ δ, 0 < δ ∧ (∀ t ∈ Ioo 1 (1 + δ), HasDerivAt laplaceP (1 - 1 / t) t) ∧
      ContinuousOn (fun t : ℝ => 1 - 1 / t) (Ioo 1 (1 + δ)) ∧
      ContinuousOn (fun _ : ℝ => (1 : ℂ)) (Ioo 1 (1 + δ)) :=
    ⟨1, one_pos, fun t ht => hasDerivAt_laplaceP (by linarith [ht.1]),
      continuousOn_const.sub (continuousOn_const.div continuousOn_id
        (fun t ht => ne_of_gt (by linarith [ht.1]))), continuousOn_const⟩
  have hmin : ∀ δ, 0 < δ → ∃ η, 0 < η ∧ ∀ t ∈ Ioi (1 : ℝ), 1 + δ ≤ t →
      laplaceP 1 + η ≤ laplaceP t := fun δ hδ => by
    refine ⟨laplaceP (1 + δ), laplaceP_pos (by linarith) (by linarith), fun t ht htδ => ?_⟩
    have ht' : (1 : ℝ) < t := ht
    have h := laplaceP_sub_ge (b := 1 + δ) (τ := t) (by linarith) (by linarith)
    have h2 : 0 ≤ (t - (1 + δ)) * (1 - 1 / (1 + δ)) :=
      mul_nonneg (by linarith) (by rw [sub_nonneg, div_le_one (by linarith)]; linarith)
    rw [laplaceP_one, zero_add]
    linarith
  have hp := isGenAsymp_real_of_bound (a := 1) (e := fun s => (s : ℝ) + 2)
    (fun s => by push_cast; ring) (f := fun t => laplaceP t - laplaceP 1)
    (cs := laplacePs (-1)) (fun n => ⟨2, 1 / 2, by norm_num, fun u hu hu1 => by
      simp only [laplaceP_one, sub_zero]; exact laplaceP_right_bound n hu hu1⟩)
  have hp' := isGenAsymp_real_of_bound (a := 1) (e := fun s => (s : ℝ) + 2 - 1)
    (fun s => by push_cast; ring) (f := fun t => 1 - 1 / t)
    (cs := fun s => ((s : ℝ) + 2) * laplacePs (-1) s) (fun n => ⟨2, 1 / 2, by norm_num,
      fun u hu hu1 => by
        have h := laplaceDeriv_bound (-1) (by norm_num) n hu hu1
        have h1u : (1 : ℝ) + u ≠ 0 := by linarith
        rwa [show (1 : ℝ) - 1 / (1 + u) = u / (1 - -1 * u) by
          rw [show (1 : ℝ) - -1 * u = 1 + u by ring, eq_div_iff h1u, sub_mul,
            one_div_mul_cancel h1u]; ring]⟩)
  have h := dlmf_2_3_15 (p := laplaceP) (p' := fun t => 1 - 1 / t) (q := fun _ => (1 : ℂ))
    (S := Ioi 1) (a := 1) (lam := 1) (μ := 2) (x₀ := 1) (ps := laplacePs (-1))
    (qs := laplaceQs) one_pos two_pos (by rw [laplacePs_zero]; norm_num) measurableSet_Ioi
    subset_rfl ⟨1, one_pos, Ioo_subset_Ioi_self⟩ hreg hmin hp hp' isGenAsymp_one
    (fun x hx => integrableOn_exp_neg_laplaceP hx)
  simp only [laplaceP_one, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] at h
  exact h

/-- Laplace's method on `(0, 1)` after `τ = −t` (`t ∈ (−1, 0)`): the coefficients are
`laplaceB 1`. -/
theorem laplace_left :
    IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ))
      (fun x => ∫ t in Ioo (-1 : ℝ) 0, (Real.exp (-(x * laplaceP (-t))) : ℂ) * 1)
      (fun s x => (Real.Gamma (watsonExp 1 2 s) : ℂ) * laplaceB 1 s *
        ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ)) := by
  have hreg : ∃ δ, 0 < δ ∧ (∀ t ∈ Ioo (-1) (-1 + δ), HasDerivAt (fun t => laplaceP (-t))
      (-1 - 1 / t) t) ∧ ContinuousOn (fun t : ℝ => -1 - 1 / t) (Ioo (-1) (-1 + δ)) ∧
      ContinuousOn (fun _ : ℝ => (1 : ℂ)) (Ioo (-1) (-1 + δ)) := by
    refine ⟨1, one_pos, fun t ht => ?_, continuousOn_const.sub (continuousOn_const.div
      continuousOn_id (fun t ht => ne_of_lt (by linarith [ht.2]))), continuousOn_const⟩
    have ht0 : t < 0 := by linarith [ht.2]
    have h := (hasDerivAt_laplaceP (τ := -t) (by linarith)).comp t (hasDerivAt_neg t)
    refine h.congr_deriv ?_
    have : t ≠ 0 := ht0.ne
    field_simp
    ring
  have hmin : ∀ δ, 0 < δ → ∃ η, 0 < η ∧ ∀ t ∈ Ioo (-1 : ℝ) 0, -1 + δ ≤ t →
      laplaceP (-(-1)) + η ≤ laplaceP (-t) := fun δ hδ => by
    simp only [neg_neg, laplaceP_one, zero_add]
    rcases lt_or_ge δ 1 with hδ1 | hδ1
    · refine ⟨laplaceP (1 - δ), laplaceP_pos (by linarith) (by linarith), fun t ht htδ => ?_⟩
      have h := laplaceP_sub_ge (b := 1 - δ) (τ := -t) (by linarith) (by linarith [ht.2])
      have h2 : 0 ≤ (-t - (1 - δ)) * (1 - 1 / (1 - δ)) := by
        apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
        rw [sub_nonpos, le_div_iff₀ (by linarith)]; linarith
      linarith
    · exact ⟨1, one_pos, fun t ht htδ => absurd htδ (by linarith [ht.2])⟩
  have hp := isGenAsymp_real_of_bound (a := -1) (e := fun s => (s : ℝ) + 2)
    (fun s => by push_cast; ring) (f := fun t => laplaceP (-t) - laplaceP (-(-1)))
    (cs := laplacePs 1) (fun n => ⟨2, 1 / 2, by norm_num, fun u hu hu1 => by
      simp only [neg_neg, laplaceP_one, sub_zero, show -(-1 + u) = 1 - u by ring]
      exact laplaceP_left_bound n hu hu1⟩)
  have hp' := isGenAsymp_real_of_bound (a := -1) (e := fun s => (s : ℝ) + 2 - 1)
    (fun s => by push_cast; ring) (f := fun t => -1 - 1 / t)
    (cs := fun s => ((s : ℝ) + 2) * laplacePs 1 s) (fun n => ⟨2, 1 / 2, by norm_num,
      fun u hu hu1 => by
        have h := laplaceDeriv_bound 1 (by norm_num) n hu hu1
        have h1u : (-1 : ℝ) + u ≠ 0 := by linarith
        have h1u' : (1 : ℝ) - 1 * u ≠ 0 := by linarith
        have h1u'' : (1 : ℝ) - u ≠ 0 := by linarith
        rwa [show (-1 : ℝ) - 1 / (-1 + u) = u / (1 - 1 * u) by
          rw [one_mul]; field_simp; ring]⟩)
  have hint : ∀ x, 1 ≤ x → IntegrableOn (fun t => (Real.exp (-(x * laplaceP (-t))) : ℂ) * 1)
      (Ioo (-1) 0) := fun x hx => by
    refine Integrable.mono' (g := fun _ => (1 : ℝ))
      ((continuous_const.integrableOn_Icc (a := -1) (b := 0)).mono_set Ioo_subset_Icc_self) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioo
      have ht' : (0 : ℝ) < -t := by linarith [ht.2]
      exact ((Complex.continuous_ofReal.continuousAt.comp (Real.continuous_exp.continuousAt.comp
        ((continuousAt_const.mul ((continuousAt_laplaceP ht').comp continuousAt_neg)).neg))).mul
        continuousAt_const).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => ?_)
      have ht' : (0 : ℝ) < -t := by linarith [ht.2]
      have hp := laplaceP_nonneg ht'
      rw [mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  have h := dlmf_2_3_15 (p := fun t => laplaceP (-t)) (p' := fun t => -1 - 1 / t)
    (q := fun _ => (1 : ℂ)) (S := Ioo (-1) 0) (a := -1) (lam := 1) (μ := 2) (x₀ := 1)
    (ps := laplacePs 1) (qs := laplaceQs) one_pos two_pos (by rw [laplacePs_zero]; norm_num)
    measurableSet_Ioo Ioo_subset_Ioi_self ⟨1, one_pos, by norm_num⟩ hreg hmin hp hp'
    isGenAsymp_one hint
  simp only [neg_neg, laplaceP_one, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
    one_mul] at h
  exact h

/-! ### The Laplace integral of `Γ` -/

/-- `Γ(x + 1) = x^{x+1} e^{−x} ∫₀^∞ e^{−x p(τ)} dτ` (`t = xτ`). -/
theorem Gamma_add_one_eq_laplace {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1) = x ^ (x + 1) * Real.exp (-x) *
      ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * laplaceP τ)) := by
  rw [Real.Gamma_eq_integral (by linarith), show x + 1 - 1 = x by ring]
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-t) * t ^ x) 0 hx
  rw [mul_zero, smul_eq_mul] at h
  rw [show (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ x) =
    x * ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * (x * τ) ^ x by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]]
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  have hτ' : (0 : ℝ) < τ := hτ
  rw [Real.mul_rpow hx.le hτ'.le, Real.rpow_def_of_pos hτ', Real.rpow_add_one hx.ne', laplaceP]
  have : Real.exp (-(x * τ)) * Real.exp (Real.log τ * x) =
      Real.exp (-x) * Real.exp (-(x * (τ - 1 - Real.log τ))) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc x * (Real.exp (-(x * τ)) * (x ^ x * Real.exp (Real.log τ * x)))
      = x * x ^ x * (Real.exp (-(x * τ)) * Real.exp (Real.log τ * x)) := by ring
    _ = _ := by rw [this]; ring

/-- The two halves: `∫₀^∞ e^{−xp} = ∫_{(−1,0)} e^{−xp(−t)} dt + ∫_{(1,∞)} e^{−xp}`. -/
theorem integral_laplace_split {x : ℝ} (hx : 1 ≤ x) :
    ((∫ τ in Ioi (0 : ℝ), Real.exp (-(x * laplaceP τ)) : ℝ) : ℂ) =
      (∫ t in Ioo (-1 : ℝ) 0, (Real.exp (-(x * laplaceP (-t))) : ℂ) * 1) +
        ∫ t in Ioi (1 : ℝ), (Real.exp (-(x * laplaceP t)) : ℂ) * 1 := by
  have hR : IntegrableOn (fun τ => Real.exp (-(x * laplaceP τ))) (Ioi 1) := by
    have := integrableOn_exp_neg_laplaceP hx
    simp only [mul_one] at this
    exact (IntegrableOn.iff_ofReal (𝕜 := ℂ)).mpr this
  have hL : IntegrableOn (fun τ => Real.exp (-(x * laplaceP τ))) (Ioc 0 1) := by
    refine Integrable.mono' (g := fun _ => (1 : ℝ))
      ((continuous_const.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
      exact (Real.continuous_exp.continuousAt.comp ((continuousAt_const.mul
        (continuousAt_laplaceP ht.1)).neg)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
      have hp := laplaceP_nonneg ht.1
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi hL hR, Complex.ofReal_add]
  congr 1
  · have e1 : ∫ τ in Ioc (0 : ℝ) 1, ((Real.exp (-(x * laplaceP τ)) : ℝ) : ℂ) =
        ∫ τ in (0 : ℝ)..1, ((Real.exp (-(x * laplaceP τ)) : ℝ) : ℂ) :=
      (intervalIntegral.integral_of_le zero_le_one).symm
    have e2 : ∫ t in Ioo (-1 : ℝ) 0, (Real.exp (-(x * laplaceP (-t))) : ℂ) * 1 =
        ∫ t in (-1 : ℝ)..0, ((Real.exp (-(x * laplaceP (-t))) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
      simp
    rw [← integral_complex_ofReal, e1, e2,
      intervalIntegral.integral_comp_neg (fun τ => ((Real.exp (-(x * laplaceP τ)) : ℝ) : ℂ))]
    simp
  · rw [← integral_complex_ofReal]
    simp

/-! ### Power expansions in `y = x^{−1/2}` -/

/-- A Laplace expansion in `x^{−(s+1)/2}` gives `√x f ∼ ∑ cₛ yˢ`, `y = x^{−1/2}`. -/
theorem hasPowExpansion_of_laplace {f : ℝ → ℂ} {c : ℕ → ℂ}
    (h : IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ)) f
      (fun s x => c s * ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ))) :
    HasPowExpansion atTop (fun x => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (fun x => ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * f x) (PowerSeries.mk c) := fun n => by
  obtain ⟨C, hC⟩ := h.2 n
  rw [eventually_map] at hC
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_gt_atTop 0] with x hx hx0
  have hw : ∀ s : ℕ, x ^ (1 / 2 : ℝ) * x ^ (-watsonExp 1 2 s) = (x ^ (-(1 / 2 : ℝ))) ^ s :=
    fun s => by
      rw [← Real.rpow_add hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, watsonExp]
      congr 1; ring
  have hpos : ∀ r : ℝ, 0 < x ^ r := fun r => Real.rpow_pos_of_pos hx0 r
  have e : ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * f x -
      (PowerSeries.trunc n (PowerSeries.mk c)).eval ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (f x - ∑ s ∈ Finset.range n,
        c s * ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ)) := by
    rw [eval_trunc_eq_sum, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [PowerSeries.coeff_mk, ← Complex.ofReal_pow, ← hw s]
    push_cast
    ring
  rw [e, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (hpos _).le, Real.norm_of_nonneg (hpos _).le, ← hw n]
  have hx' : ‖f x - ∑ s ∈ Finset.range n, c s * ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ)‖ /
      x ^ (-watsonExp 1 2 n) ≤ C := by
    have := hx
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg (hpos _).le] at this
    exact this
  rw [div_le_iff₀ (hpos _)] at hx'
  calc x ^ (1 / 2 : ℝ) * ‖f x - ∑ s ∈ Finset.range n, c s * ((x ^ (-watsonExp 1 2 s) : ℝ) : ℂ)‖
      ≤ x ^ (1 / 2 : ℝ) * (C * x ^ (-watsonExp 1 2 n)) := by gcongr
    _ = C * (x ^ (1 / 2 : ℝ) * x ^ (-watsonExp 1 2 n)) := by ring

/-- An expansion in powers of `y²` is one in powers of `y` with the odd coefficients `0`. -/
theorem hasPowExpansion_even {α : Type*} {l : Filter α} {y : α → ℂ} (hy : Tendsto y l (𝓝 0))
    {f : α → ℂ} {g : ℕ → ℂ} (h : HasPowExpansion l (fun x => y x ^ 2) f (PowerSeries.mk g)) :
    HasPowExpansion l y f (PowerSeries.mk fun s => if Even s then g (s / 2) else 0) := by
  set A := PowerSeries.mk fun s => if Even s then g (s / 2) else 0 with hA
  have hev : ∀ (m : ℕ) (t : ℂ), (PowerSeries.trunc (2 * m) A).eval t =
      (PowerSeries.trunc m (PowerSeries.mk g)).eval (t ^ 2) := fun m t => by
    rw [eval_trunc_eq_sum, eval_trunc_eq_sum]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      simp only [hA, PowerSeries.coeff_mk]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨m, by ring⟩),
        ite_eq_right_of_eq_false _ _ (eq_false (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩)),
        show 2 * m / 2 = m by omega, ← pow_mul]
      ring
  intro n
  have h1 : (fun x => f x - (PowerSeries.trunc n (PowerSeries.mk g)).eval (y x ^ 2)) =O[l]
      fun x => y x ^ n := by
    have hb : (fun x => y x ^ n) =O[l] fun _ => (1 : ℂ) := (hy.pow n).isBigO_one ℂ |>.trans
      (isBigO_refl _ _) |> fun h => by simpa using h
    refine (h n).trans ?_
    have : (fun x => (y x ^ 2) ^ n) = fun x => y x ^ n * y x ^ n := by
      funext x; rw [← pow_mul, ← pow_add]; ring_nf
    rw [this]
    simpa using (isBigO_refl (fun x => y x ^ n) l).mul hb
  have h2 : (fun x => (PowerSeries.trunc (2 * n) A - PowerSeries.trunc n A).eval (y x)) =O[l]
      fun x => y x ^ n := by
    refine isBigO_eval_of_coeff_eq_zero hy fun d hd => ?_
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, PowerSeries.coeff_trunc,
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hd),
      sub_self]
  refine (h1.add h2).congr_left fun x => ?_
  rw [Polynomial.eval_sub, hev]
  ring

theorem Gamma_nat_add_half_eq (k : ℕ) :
    Real.Gamma (k + 1 / 2) = Real.sqrt π * (ascPochhammer ℝ k).eval (1 / 2) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, ascPochhammer_zero, Polynomial.eval_one, mul_one]
    exact Real.Gamma_one_half_eq
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih, ascPochhammer_succ_eval]
    ring

theorem tendsto_rpow_neg_half :
    Tendsto (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) := by
  rw [← Complex.ofReal_zero]
  exact (Complex.continuous_ofReal.tendsto 0).comp (tendsto_rpow_neg_atTop (by norm_num))

/-- Stirling's formula 5.11.3 along `(0, ∞)` as an expansion in `y = x^{−1/2}`. -/
theorem hasPowExpansion_scaledGamma_real :
    HasPowExpansion atTop (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (fun x => scaledGamma x)
      (PowerSeries.mk fun s => if Even s then (BZ.stirlingCoeff (s / 2) : ℂ) else 0) := by
  have hS := isAsympExpansionDLMF_iff.mp (dlmf_5_11_3 Real.pi_pos le_rfl)
  have hk : Tendsto (fun x : ℝ => (x : ℂ)) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - π))) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
    · simpa using tendsto_abs_atTop_atTop
    · filter_upwards [eventually_gt_atTop 0] with x hx
      refine ⟨Complex.ofReal_ne_zero.mpr hx.ne', ?_⟩
      simp [arg_ofReal_of_nonneg hx.le]
  have h1 := hS.comp_tendsto hk
  have h2 : HasPowExpansion atTop (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ 2)
      (fun x => scaledGamma x) (PowerSeries.mk fun k => (BZ.stirlingCoeff k : ℂ)) := fun n => by
    have hinv : ∀ x : ℝ, 0 < x → ((x : ℂ))⁻¹ = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ 2 :=
      fun x hx => by
        rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        norm_num [Real.rpow_neg_one]
    refine (h1 n).congr' ?_ ?_ <;>
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Function.comp_apply, hinv x hx]
  exact hasPowExpansion_even (y := fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    (f := fun x => scaledGamma x) (g := fun k => (BZ.stirlingCoeff k : ℂ)) tendsto_rpow_neg_half h2

/-- `√(2π) Γ*(x) = √x ∫₀^∞ e^{−xp}` for `x ≥ 1`. -/
theorem sqrt_two_pi_mul_scaledGamma {x : ℝ} (hx : 1 ≤ x) :
    ((Real.sqrt (2 * π) : ℝ) : ℂ) * scaledGamma x = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      ((∫ t in Ioo (-1 : ℝ) 0, (Real.exp (-(x * laplaceP (-t))) : ℂ) * 1) +
        ∫ t in Ioi (1 : ℝ), (Real.exp (-(x * laplaceP t)) : ℂ) * 1) := by
  have hx0 : 0 < x := by linarith
  rw [← integral_laplace_split hx]
  have hpi : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  set I := ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * laplaceP τ)) with hI
  have hΓ : Real.Gamma x = x ^ x * Real.exp (-x) * I := by
    have h := Gamma_add_one_eq_laplace hx0
    rw [Real.Gamma_add_one hx0.ne', Real.rpow_add_one hx0.ne'] at h
    have : x * Real.Gamma x = x * (x ^ x * Real.exp (-x) * I) := by rw [h]; ring
    exact mul_left_cancel₀ hx0.ne' this
  have hcpow : (x : ℂ) ^ ((x : ℂ) - 1 / 2) = ((x ^ (x - 1 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
  rw [scaledGamma, Gamma_ofReal, hΓ, hcpow, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  have h1 : x ^ (x - 1 / 2) * x ^ (1 / 2 : ℝ) = x ^ x := by
    rw [← Real.rpow_add hx0]; ring_nf
  have h2 : 0 < x ^ (x - 1 / 2) := Real.rpow_pos_of_pos hx0 _
  have h3 := Real.exp_pos (-x)
  have key : Real.sqrt (2 * π) * (x ^ x * Real.exp (-x) * I /
      (Real.sqrt (2 * π) * Real.exp (-x) * x ^ (x - 1 / 2))) = x ^ (1 / 2 : ℝ) * I := by
    rw [← h1]; field_simp
  exact_mod_cast key

/-- **DLMF 5.11.5**: `gₖ = √2 (½)ₖ a_{2k}`, with `aₖ` of 5.11.6 (`stirlingA`). -/
theorem dlmf_5_11_5 (k : ℕ) :
    (BZ.stirlingCoeff k : ℝ) =
      Real.sqrt 2 * (ascPochhammer ℝ k).eval (1 / 2) * stirlingA (2 * k) := by
  set F : ℝ → ℂ := fun x => ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    ((∫ t in Ioo (-1 : ℝ) 0, (Real.exp (-(x * laplaceP (-t))) : ℂ) * 1) +
      ∫ t in Ioi (1 : ℝ), (Real.exp (-(x * laplaceP t)) : ℂ) * 1) with hF
  have hA : HasPowExpansion atTop (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F
      (PowerSeries.mk (fun s => (Real.Gamma (watsonExp 1 2 s) : ℂ) * laplaceB 1 s) +
        PowerSeries.mk (fun s => (Real.Gamma (watsonExp 1 2 s) : ℂ) * laplaceB (-1) s)) :=
    ((hasPowExpansion_of_laplace laplace_left).add
      (hasPowExpansion_of_laplace laplace_right)).congr'
      (Eventually.of_forall fun x => by simp only [hF, Pi.add_apply]; ring)
  have hB : HasPowExpansion atTop (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F
      (PowerSeries.C ((Real.sqrt (2 * π) : ℝ) : ℂ) *
        PowerSeries.mk fun s => if Even s then (BZ.stirlingCoeff (s / 2) : ℂ) else 0) :=
    (hasPowExpansion_scaledGamma_real.const_mul _).congr'
      (by filter_upwards [eventually_ge_atTop 1] with x hx using sqrt_two_pi_mul_scaledGamma hx)
  have hy0 : ∀ᶠ x : ℝ in atTop, ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'
  have heq := HasPowExpansion.unique tendsto_rpow_neg_half hy0 hA hB
  have hc := congrArg (PowerSeries.coeff (2 * k)) heq
  rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk, ite_eq_left_of_eq_true _ _ (eq_true ⟨k, by ring⟩),
    show 2 * k / 2 = k by omega,
    laplaceCoeff_one, laplaceCoeff_neg_one, watsonExp,
    show ((2 * k : ℕ) : ℝ) + 1 = 2 * ((k : ℝ) + 1 / 2) by push_cast; ring,
    show 2 * ((k : ℝ) + 1 / 2) / 2 = k + 1 / 2 by ring, Gamma_nat_add_half_eq,
    show (-1 : ℂ) ^ (2 * k) = 1 by rw [pow_mul]; norm_num] at hc
  have hpi : Real.sqrt (2 * π) = Real.sqrt 2 * Real.sqrt π := Real.sqrt_mul (by norm_num) π
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hreal : (BZ.stirlingCoeff k : ℝ) * (Real.sqrt 2 * Real.sqrt π) =
      2 * (Real.sqrt π * (ascPochhammer ℝ k).eval (1 / 2)) * stirlingA (2 * k) := by
    have := congrArg Complex.re hc
    simp at this
    norm_num at this ⊢
    linarith
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply mul_right_cancel₀ (mul_pos hs2 hsπ).ne'
  rw [hreal]
  linear_combination (-(Real.sqrt π * (ascPochhammer ℝ k).eval (1 / 2) * stirlingA (2 * k))) * h22

end Azurite.DLMF
