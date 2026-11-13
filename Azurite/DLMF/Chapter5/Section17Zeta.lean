/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section17Asymp
import Azurite.DLMF.Chapter2.Section10Example

/-!
# DLMF 5.17.7: Glaisher's constant and `ζ′`

Formalization of <https://dlmf.nist.gov/5.17> (part 4):
`C = (γ + ln(2π))/12 − ζ′(2)/(2π²) = 1/12 − ζ′(−1)` (`dlmf_5_17_7`; the limit form is
`tendsto_glaisherSeq`).

* `C = 1/12 − ζ′(−1)`: the Euler–Maclaurin formula (§2.10, `em_tail`) for `x^{−s}`, `s > 1`, gives
  `ζ(s) = ∑_{k=1}^{n} k^{−s} + n^{1−s}/(s − 1) − ½n^{−s} + (s/12)n^{−s−1}
    − s(s + 1)(s + 2)(s + 3)/24 ∫_n^∞ (B̃₄(x) − B₄) x^{−s−4} dx` (`zeta_em_real`). The right side
  (`zetaEM n`) is holomorphic on `ℜs > −3`, `s ≠ 1` (`differentiableAt_zetaEM`, differentiation
  under the integral sign), so it equals `ζ` there (identity theorem, `zeta_eventuallyEq_zetaEM`).
  Differentiating at `s = −1`: `ζ′(−1) = 1/12 − Cₙ + (1/12)∫_n^∞ (B̃₄ − B₄)x^{−3} dx`
  (`hasDerivAt_zetaEM_neg_one`), with `Cₙ` the sequence of 5.17.7; let `n → ∞`.
* `(γ + ln(2π))/12 − ζ′(2)/(2π²) = 1/12 − ζ′(−1)`: differentiate the functional equation
  `ζ(1 − s) = 2(2π)^{−s} Γ(s) cos(½πs) ζ(s)` at `s = 2` (`zeta_deriv_neg_one_eq`), using
  `ζ(2) = π²/6`, `Γ′(2) = 1 − γ`.

This also gives DLMF 2.10.6, whose constant is the same `C`.
-/

open Complex Filter Topology Set Finset MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Euler–Maclaurin for `ζ(s)`, `s > 1` real -/

/-- `D k x = (−s)(−s − 1)⋯(−s − k + 1) x^{−s−k}`, the derivatives of `x^{−s}`. -/
noncomputable def powD (s : ℝ) (k : ℕ) (x : ℝ) : ℝ := (∏ i ∈ range k, (-s - i)) * x ^ (-s - k)

theorem hasDerivAt_powD (s : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (powD s k) (powD s (k + 1) x) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -s - k) (Or.inl hx.ne')).const_mul
    (∏ i ∈ range k, (-s - i))
  refine h.congr_deriv ?_
  rw [powD, prod_range_succ, show (-s - ((k + 1 : ℕ) : ℝ)) = (-s - k) - 1 by push_cast; ring]
  ring

theorem powD_zero (s x : ℝ) : powD s 0 x = x ^ (-s) := by simp [powD]

theorem powD_one (s x : ℝ) : powD s 1 x = -s * x ^ (-s - 1) := by simp [powD]

theorem powD_four (s x : ℝ) :
    powD s 4 x = s * (s + 1) * (s + 2) * (s + 3) * x ^ (-s - 4) := by
  simp [powD, prod_range_succ]
  ring_nf

theorem integrableOn_powD_four {s : ℝ} (hs : -3 < s) : IntegrableOn (powD s 4) (Ioi 1) := by
  have h := (integrableOn_Ioi_rpow_of_lt (a := -s - 4) (by linarith) one_pos).const_mul
    (s * (s + 1) * (s + 2) * (s + 3))
  have e : powD s 4 = fun x => s * (s + 1) * (s + 2) * (s + 3) * x ^ (-s - 4) :=
    funext (powD_four s)
  rw [e]
  exact h

theorem tendsto_natCast_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop

theorem sum_Icc_powD {s : ℝ} (N : ℕ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) N, powD s 0 j = ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ s := by
  rw [show ((N : ℤ)) = ((N : ℕ) : ℤ) from rfl, sum_Icc_int_one (fun x => powD s 0 x) N,
    sum_Icc_one_eq_sum_range_real (fun r => powD s 0 r) N]
  refine sum_congr rfl fun k _ => ?_
  rw [powD_zero, Real.rpow_neg (by positivity)]
  push_cast
  ring

/-- `ζ(s) = ∑_{k=1}^{n} k^{−s} + n^{1−s}/(s − 1) − ½n^{−s} + (s/12)n^{−s−1} − Rₙ(s)` for real
`s > 1`, `Rₙ(s) = ∫_n^∞ (B̃₄ − B₄)/4! f⁗` (`emRem`). -/
theorem zeta_em_real {s : ℝ} (hs : 1 < s) {n : ℕ} (hn : 1 ≤ n) :
    ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s = ∑ k ∈ Icc 1 n, (k : ℝ) ^ (-s) +
      (n : ℝ) ^ (1 - s) / (s - 1) - (n : ℝ) ^ (-s) / 2 + s * (n : ℝ) ^ (-s - 1) / 12 -
        emRem 2 (powD s) n := by
  have hd : ∀ k < 2 * 2, ∀ x : ℝ, ((1 : ℤ) : ℝ) ≤ x → HasDerivAt (powD s k) (powD s (k + 1) x) x :=
    fun k _ x hx => hasDerivAt_powD s k (by push_cast at hx; linarith)
  have hint : IntegrableOn (powD s (2 * 2)) (Ioi ((1 : ℤ) : ℝ)) := by
    simpa using integrableOn_powD_four (s := s) (by linarith)
  have hem : ∀ N : ℕ, 1 ≤ N → ∑ j ∈ Finset.Icc (1 : ℤ) N, powD s 0 j =
      (∫ x in (1 : ℝ)..N, x ^ (-s)) + (N : ℝ) ^ (-s) / 2 + emConst ((1 : ℤ) : ℝ) 2 (powD s) -
        s * (N : ℝ) ^ (-s - 1) / 12 + emRem 2 (powD s) N := by
    intro N hN
    have h := em_tail (a := 1) (m := 2) (D := powD s) two_pos hd hint (n := N)
      (by exact_mod_cast hN)
    simp only [show (2 - 1 : ℕ) = 1 from rfl, Finset.Icc_self, sum_singleton,
      show 2 * 1 = 2 from rfl, bernoulli_two,
      Nat.factorial_two] at h
    rw [h, powD_zero, powD_one]
    push_cast
    simp only [powD_zero]
    ring
  have hint1 : ∀ N : ℕ, 1 ≤ N → ∫ x in (1 : ℝ)..N, x ^ (-s) =
      ((N : ℝ) ^ (1 - s) - 1) / (1 - s) := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hN1]; intro h; linarith [h.1]⟩), Real.one_rpow]
    ring_nf
  set K := emConst ((1 : ℤ) : ℝ) 2 (powD s)
  set Z := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s
  -- the limit `N → ∞`
  have hZ : Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ s) atTop (𝓝 Z) := by
    have hsum : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
      simpa using this
    exact hsum.hasSum.tendsto_sum_nat
  have hs1 : 0 < s - 1 := by linarith
  have hR : Tendsto (fun N : ℕ => (((N : ℝ) ^ (1 - s) - 1) / (1 - s)) + (N : ℝ) ^ (-s) / 2 + K -
      s * (N : ℝ) ^ (-s - 1) / 12 + emRem 2 (powD s) N) atTop
      (𝓝 (((0 : ℝ) - 1) / (1 - s) + 0 / 2 + K - s * 0 / 12 + 0)) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - s)) atTop (𝓝 0) := by
      have := tendsto_natCast_rpow_neg hs1
      rwa [neg_sub] at this
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-s)) atTop (𝓝 0) :=
      tendsto_natCast_rpow_neg (by linarith)
    have h3 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-s - 1)) atTop (𝓝 0) := by
      have := tendsto_natCast_rpow_neg (a := s + 1) (by linarith)
      rwa [show -(s + 1) = -s - 1 by ring] at this
    have hi4 : IntegrableOn (powD s (2 * 2)) (Ioi 1) := integrableOn_powD_four (by linarith)
    have h4 := tendsto_emRem (D := powD s) (a := 1) (m := 2) hi4
    exact (((((h1.sub_const 1).div_const _).add (h2.div_const 2)).add_const K).sub
      ((h3.const_mul s).div_const 12)).add h4
  have hK : Z = ((0 : ℝ) - 1) / (1 - s) + 0 / 2 + K - s * 0 / 12 + 0 := by
    refine tendsto_nhds_unique hZ (hR.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [← hint1 N hN, ← hem N hN, sum_Icc_powD]
  have hn' := hem n hn
  rw [sum_Icc_powD, hint1 n hn] at hn'
  have hsn : ∑ k ∈ Icc 1 n, (k : ℝ) ^ (-s) = ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ s := by
    rw [sum_Icc_one_eq_sum_range_real (fun r => (r : ℝ) ^ (-s)) n]
    refine sum_congr rfl fun k _ => ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast
    ring
  rw [hsn, hK, hn']
  have h1s : (1 : ℝ) - s ≠ 0 := by linarith
  have hs1' : s - 1 ≠ 0 := by linarith
  field_simp
  ring

/-! ### The continuation to `ℜs > −3` -/

/-- `B̃₄(x) − B₄`. -/
noncomputable def bernFourDiff (x : ℝ) : ℝ := periodicBernoulli 4 x - bernoulli 4

theorem measurable_bernFourDiff : Measurable bernFourDiff :=
  (measurable_periodicBernoulli 4).sub_const _

theorem bernFourDiff_bound : ∃ G, 0 ≤ G ∧ ∀ x, |bernFourDiff x| ≤ G := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound 4
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨C + |(bernoulli 4 : ℝ)|, by positivity, fun x => ?_⟩
  exact (abs_sub _ _).trans (add_le_add (hC x) le_rfl)

/-- `∫_n^∞ (B̃₄(x) − B₄) x^{−s−4} dx`. -/
noncomputable def emInt (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (n : ℝ), (bernFourDiff x : ℂ) * (x : ℂ) ^ (-s - 4)

/-- The Euler–Maclaurin form of `ζ(s)` on `ℜs > −3`:
`∑_{k=1}^{n} k^{−s} + n^{1−s}/(s − 1) − ½n^{−s} + (s/12)n^{−s−1}
− s(s + 1)(s + 2)(s + 3)/24 ∫_n^∞ (B̃₄(x) − B₄) x^{−s−4} dx`. -/
noncomputable def zetaEM (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 n, (k : ℂ) ^ (-s) + (n : ℂ) ^ (1 - s) / (s - 1) - (n : ℂ) ^ (-s) / 2 +
    s * (n : ℂ) ^ (-s - 1) / 12 - s * (s + 1) * (s + 2) * (s + 3) / 24 * emInt n s

theorem measurable_cpow_const (w : ℂ) : Measurable fun x : ℝ => (x : ℂ) ^ w :=
  Complex.measurable_ofReal.pow_const w

theorem norm_bernFourDiff_mul_cpow {G : ℝ} (hG : ∀ x, |bernFourDiff x| ≤ G) {x : ℝ} (hx : 0 < x)
    (w : ℂ) : ‖(bernFourDiff x : ℂ) * (x : ℂ) ^ w‖ ≤ G * x ^ w.re := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hx]
  exact mul_le_mul_of_nonneg_right (hG x) (by positivity)

theorem integrableOn_emInt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : -3 < s.re) :
    IntegrableOn (fun x : ℝ => (bernFourDiff x : ℂ) * (x : ℂ) ^ (-s - 4)) (Ioi n) := by
  obtain ⟨G, -, hG⟩ := bernFourDiff_bound
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := (integrableOn_Ioi_rpow_of_lt (a := -s.re - 4) (by linarith) hn0).const_mul G
  refine hb.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
  · exact ((Complex.measurable_ofReal.comp measurable_bernFourDiff).mul
      (measurable_cpow_const _)).aestronglyMeasurable
  · have hx0 : 0 < x := lt_trans hn0 hx
    have := norm_bernFourDiff_mul_cpow hG hx0 (-s - 4)
    simpa using this

/-- `emInt n` is holomorphic on `ℜs > −3`. -/
theorem hasDerivAt_emInt {n : ℕ} (hn : 1 ≤ n) {s₀ : ℂ} (hs₀ : -3 < s₀.re) :
    HasDerivAt (emInt n) (∫ x in Ioi (n : ℝ), (bernFourDiff x : ℂ) *
      ((x : ℂ) ^ (-s₀ - 4) * Complex.log x * (-1))) s₀ := by
  obtain ⟨G, hG0, hG⟩ := bernFourDiff_bound
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set ε := (s₀.re + 3) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set σ := s₀.re - ε with hσ
  have hσ3 : -3 < σ := by rw [hσ, hε]; linarith
  set δ := (σ + 3) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hre : ∀ s ∈ Metric.ball s₀ ε, σ ≤ s.re := fun s hs => by
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have := abs_re_le_norm (s - s₀)
    rw [sub_re] at this
    have := abs_lt.mp (lt_of_le_of_lt this hs)
    rw [hσ]; linarith [this.1]
  set bound : ℝ → ℝ := fun x => G / δ * x ^ (-σ - 4 + δ)
  have hbint : IntegrableOn bound (Ioi n) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ - 4 + δ) (by rw [hδ]; linarith) hn0).const_mul _
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable
      (fun x : ℝ => (bernFourDiff x : ℂ) * (x : ℂ) ^ (-s - 4)) (volume.restrict (Ioi (n : ℝ))) :=
    fun s => ((Complex.measurable_ofReal.comp measurable_bernFourDiff).mul
      (measurable_cpow_const _)).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (n : ℝ)))
    (F := fun s x => (bernFourDiff x : ℂ) * (x : ℂ) ^ (-s - 4))
    (F' := fun s x => (bernFourDiff x : ℂ) * ((x : ℂ) ^ (-s - 4) * Complex.log x * (-1)))
    (bound := bound) (Metric.ball_mem_nhds s₀ hε0) (Eventually.of_forall hmeas)
    (integrableOn_emInt hn hs₀)
    (((Complex.measurable_ofReal.comp measurable_bernFourDiff).mul
      (((measurable_cpow_const _).mul (Complex.measurable_ofReal.clog)).mul_const _)
      ).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx s hs => ?_)) hbint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx s _ => ?_))
  · exact h.2
  · have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hn) (le_of_lt hx)
    have hx0 : 0 < x := by linarith
    have hlog : ‖Complex.log (x : ℂ)‖ = Real.log x := by
      rw [← ofReal_log hx0.le, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx1)]
    rw [show (bernFourDiff x : ℂ) * ((x : ℂ) ^ (-s - 4) * Complex.log x * (-1)) =
      -(((bernFourDiff x : ℂ) * (x : ℂ) ^ (-s - 4)) * Complex.log x) by ring, norm_neg,
      norm_mul, hlog]
    have h1 := norm_bernFourDiff_mul_cpow hG hx0 (-s - 4)
    have h2 : x ^ (-s - 4).re ≤ x ^ (-σ - 4) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1
      simp only [sub_re, neg_re, re_ofNat]
      linarith [hre s hs]
    have h3 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    calc ‖(bernFourDiff x : ℂ) * (x : ℂ) ^ (-s - 4)‖ * Real.log x
        ≤ (G * x ^ (-σ - 4)) * (x ^ δ / δ) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hG0)
      _ = bound x := by
          simp only [bound]
          rw [Real.rpow_add hx0]
          ring
  · have hx0 : (x : ℂ) ≠ 0 := by
      have : (0 : ℝ) < x := lt_trans hn0 hx
      exact_mod_cast this.ne'
    have hd := ((hasDerivAt_id s).neg.sub_const (4 : ℂ)).const_cpow (c := (x : ℂ)) (Or.inl hx0)
    have := hd.const_mul (bernFourDiff x : ℂ)
    simpa using this

theorem differentiableAt_zetaEM {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (zetaEM n) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum : DifferentiableAt ℂ (fun s : ℂ => ∑ k ∈ Icc 1 n, (k : ℂ) ^ (-s)) s :=
    DifferentiableAt.fun_sum fun k hk => differentiableAt_id.neg.const_cpow
      (Or.inl (by have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)))
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (1 - s)) s :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl hn0)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hn0)
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (-s - 1)) s :=
    (differentiableAt_id.neg.sub_const _).const_cpow (Or.inl hn0)
  have h4 := (hasDerivAt_emInt hn hs).differentiableAt
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold zetaEM
  fun_prop (disch := assumption)

theorem zetaEM_ofReal {s : ℝ} (hs : 1 < s) {n : ℕ} (hn : 1 ≤ n) :
    zetaEM n s = riemannZeta s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  have ht : ∀ k : ℕ, 1 / ((k : ℂ) + 1) ^ (s : ℂ) = ((1 / ((k : ℝ) + 1) ^ s : ℝ) : ℂ) :=
    fun k => by
      rw [ofReal_div, ofReal_one, ofReal_cpow (by positivity)]
      push_cast; ring_nf
  rw [tsum_congr ht, ← ofReal_tsum, zeta_em_real hs hn]
  have hI : emInt n s = ((∫ x in Ioi (n : ℝ), bernFourDiff x * x ^ (-s - 4) : ℝ) : ℂ) := by
    rw [emInt, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := le_of_lt (lt_trans hn0 hx)
    rw [ofReal_mul, ofReal_cpow hx0]
    push_cast
    ring_nf
  have hR : emRem 2 (powD s) n =
      s * (s + 1) * (s + 2) * (s + 3) / 24 * ∫ x in Ioi (n : ℝ), bernFourDiff x * x ^ (-s - 4) := by
    rw [emRem, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [powD_four, bernFourDiff, show 2 * 2 = 4 from rfl]
    norm_num [Nat.factorial]
    ring
  rw [zetaEM, hI, hR]
  have hk : ∀ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-(s : ℂ)) = (((k : ℝ) ^ (-s) : ℝ) : ℂ) := fun k _ => by
    rw [ofReal_cpow k.cast_nonneg]; push_cast; ring_nf
  have c1 : (n : ℂ) ^ (1 - (s : ℂ)) = (((n : ℝ) ^ (1 - s) : ℝ) : ℂ) := by
    rw [ofReal_cpow hn0.le]; push_cast; ring_nf
  have c2 : (n : ℂ) ^ (-(s : ℂ)) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [ofReal_cpow hn0.le]; push_cast; ring_nf
  have c3 : (n : ℂ) ^ (-(s : ℂ) - 1) = (((n : ℝ) ^ (-s - 1) : ℝ) : ℂ) := by
    rw [ofReal_cpow hn0.le]; push_cast; ring_nf
  rw [sum_congr rfl hk, c1, c2, c3]
  push_cast
  ring

/-! ### `ζ = zetaEM n` on a connected region around `−1` and `2` -/

/-- An open connected region in `ℜs > −3`, avoiding `1`, containing `−1` and `2`. -/
def zetaRegion : Set ℂ :=
  ({s : ℂ | -3 < s.re} ∩ {s | s.re < 1}) ∪ ({s : ℂ | -3 < s.re} ∩ {s | 0 < s.im}) ∪
    {s : ℂ | 1 < s.re}

theorem isOpen_zetaRegion : IsOpen zetaRegion :=
  (((isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)).union
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im))).union
    (isOpen_lt continuous_const continuous_re)

theorem isPreconnected_zetaRegion : IsPreconnected zetaRegion := by
  have hA := ((convex_halfSpace_re_gt (r := -3)).inter
    (convex_halfSpace_re_lt (r := 1))).isPreconnected
  have hB := ((convex_halfSpace_re_gt (r := -3)).inter
    (convex_halfSpace_im_gt (r := 0))).isPreconnected
  have hD := (convex_halfSpace_re_gt (r := 1)).isPreconnected
  refine (IsPreconnected.union I ?_ ?_ hA hB).union (2 + I) ?_ ?_ hD
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩
  · exact Or.inr ⟨by norm_num, by simp⟩
  · show 1 < (2 + I).re; norm_num

theorem zetaRegion_re {s : ℂ} (hs : s ∈ zetaRegion) : -3 < s.re ∧ s ≠ 1 := by
  rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h
  · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
  · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
  · exact ⟨by simp only [Set.mem_ofPred_eq] at h; linarith, fun h' => by
      rw [h'] at h; simp at h⟩

theorem zeta_eqOn_zetaEM {n : ℕ} (hn : 1 ≤ n) : EqOn riemannZeta (zetaEM n) zetaRegion := by
  set U : Set ℂ := (fun w => w + 1) ⁻¹' zetaRegion
  have hUo : IsOpen U := isOpen_zetaRegion.preimage (continuous_id.add continuous_const)
  have hUc : IsPreconnected U :=
    (Homeomorph.addRight (1 : ℂ)).isPreconnected_preimage.mpr isPreconnected_zetaRegion
  have hf : AnalyticOnNhd ℂ (fun w => riemannZeta (w + 1)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      ((differentiableAt_riemannZeta (zetaRegion_re hw).2).comp w
        (differentiableAt_id.add_const 1)).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ (fun w => zetaEM n (w + 1)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      ((differentiableAt_zetaEM hn (zetaRegion_re hw).1 (zetaRegion_re hw).2).comp w
        (differentiableAt_id.add_const 1)).differentiableWithinAt) hUo
  have h1 : (1 : ℂ) ∈ U := by
    show (1 : ℂ) + 1 ∈ zetaRegion
    exact Or.inr (by show (1 : ℝ) < ((1 : ℂ) + 1).re; norm_num)
  have heq := eqOn_of_eq_on_pos_reals hf hg hUc hUo h1 (fun x hx _ => by
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
      zetaEM_ofReal (by linarith) hn])
  intro s hs
  have := heq (show s - 1 + 1 ∈ zetaRegion by simpa using hs)
  simpa using this

/-! ### Differentiating at `s = −1` -/

theorem hasDerivAt_zetaEM_neg_one {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (zetaEM n) (1 / 12 - glaisherSeq n + emInt n (-1) / 12) (-1) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  set x : ℂ := -1
  have hsum := HasDerivAt.fun_sum (u := Finset.Icc 1 n) (x := x)
    (A := fun k (s : ℂ) => (k : ℂ) ^ (-s))
    (A' := fun k => (k : ℂ) ^ (-x) * Complex.log k * (-1)) fun k hk =>
      (hasDerivAt_id x).neg.const_cpow
        (Or.inl (by have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)))
  have h1 := ((hasDerivAt_const x (1 : ℂ)).sub (hasDerivAt_id x)).const_cpow (c := (n : ℂ))
    (Or.inl hn0)
  have h1d := h1.div ((hasDerivAt_id x).sub_const 1) (by norm_num [x])
  have h2 := (hasDerivAt_id x).neg.const_cpow (c := (n : ℂ)) (Or.inl hn0)
  have h3 := (hasDerivAt_id x).mul
    (((hasDerivAt_id x).neg.sub_const 1).const_cpow (c := (n : ℂ)) (Or.inl hn0))
  have hp := (((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1)).mul
    ((hasDerivAt_id x).add_const 2)).mul ((hasDerivAt_id x).add_const 3)
  have h4 := (hp.div_const 24).mul (hasDerivAt_emInt hn (by norm_num [x]))
  have htot := (((hsum.add h1d).sub (h2.div_const 2)).add (h3.div_const 12)).sub h4
  refine (htot.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => rfl)
  simp only [id, x, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, neg_neg,
    show (1 : ℂ) - -1 = 2 by norm_num, sub_self, cpow_zero, cpow_one, cpow_ofNat]
  rw [glaisherSeq]
  push_cast
  simp only [mul_neg, mul_one, sum_neg_distrib]
  ring

theorem tendsto_emInt_neg_one : Tendsto (fun n : ℕ => emInt n (-1)) atTop (𝓝 0) := by
  obtain ⟨G, hG0, hG⟩ := bernFourDiff_bound
  refine squeeze_zero_norm' (a := fun n : ℕ => G * ((n : ℝ) ^ (-2 : ℝ) / 2)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hb : IntegrableOn (fun x : ℝ => G * x ^ (-3 : ℝ)) (Ioi n) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hn0).const_mul G
    have hle := norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun x hx => by
        have := norm_bernFourDiff_mul_cpow hG (lt_trans hn0 hx) (-(-1) - 4)
        refine this.trans (le_of_eq ?_)
        congr 2
        norm_num))
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hn0] at hle
    refine hle.trans (le_of_eq ?_)
    norm_num
  · have := (tendsto_natCast_rpow_neg (a := 2) two_pos).div_const 2 |>.const_mul G
    rw [zero_div, mul_zero] at this
    exact this

/-- `ζ′(−1) = 1/12 − C`. -/
theorem deriv_zeta_neg_one : deriv riemannZeta (-1) = 1 / 12 - glaisherC := by
  have hval : ∀ n : ℕ, 1 ≤ n →
      deriv riemannZeta (-1) = 1 / 12 - glaisherSeq n + emInt n (-1) / 12 := fun n hn => by
    have hev : riemannZeta =ᶠ[𝓝 (-1)] zetaEM n :=
      Filter.eventually_of_mem (isOpen_zetaRegion.mem_nhds (Or.inl (Or.inl ⟨by norm_num,
        by norm_num⟩))) (zeta_eqOn_zetaEM hn)
    rw [hev.deriv_eq, (hasDerivAt_zetaEM_neg_one hn).deriv]
  have hlim : Tendsto (fun n : ℕ => 1 / 12 - (glaisherSeq n : ℂ) + emInt n (-1) / 12) atTop
      (𝓝 (1 / 12 - (glaisherC : ℂ) + 0 / 12)) :=
    (tendsto_const_nhds.sub ((continuous_ofReal.tendsto _).comp tendsto_glaisherSeq)).add
      (tendsto_emInt_neg_one.div_const 12)
  rw [zero_div, add_zero] at hlim
  exact tendsto_nhds_unique (tendsto_const_nhds.congr'
    ((eventually_ge_atTop 1).mono fun n hn => hval n hn)) hlim

/-! ### The functional equation at `s = 2` -/

/-- `1/12 − ζ′(−1) = (γ + ln(2π))/12 − ζ′(2)/(2π²)`, from `ζ(1 − s) = 2(2π)^{−s} Γ(s) cos(½πs) ζ(s)`
differentiated at `s = 2`. -/
theorem zeta_deriv_neg_one_eq :
    (1 : ℂ) / 12 - deriv riemannZeta (-1) =
      ((γ + Real.log (2 * π)) / 12 : ℝ) - deriv riemannZeta 2 / (2 * π ^ 2) := by
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hev : (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 (2 : ℂ)]
      fun s => 2 * (2 * π) ^ (-s) * Gamma s * Complex.cos (π * s / 2) * riemannZeta s := by
    filter_upwards [Metric.ball_mem_nhds (2 : ℂ) one_pos] with s hs
    have hre : 1 < s.re := by
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - 2)
      rw [sub_re] at this
      have := abs_lt.mp (lt_of_le_of_lt this hs)
      simp at this; linarith [this.1]
    refine riemannZeta_one_sub (fun m h => ?_) (fun h => ?_)
    · rw [h] at hre; simp at hre; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · rw [h] at hre; simp at hre
  have hL : HasDerivAt (fun s => riemannZeta (1 - s)) (deriv riemannZeta (1 - 2) * (0 - 1)) 2 :=
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt.comp (2 : ℂ)
      ((hasDerivAt_const (2 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 2))
  have hΓ : HasDerivAt Gamma (deriv Gamma 2) 2 :=
    (Complex.differentiableAt_Gamma 2 fun m h => by
      have := congrArg Complex.re h; simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).hasDerivAt
  have hdΓ : deriv Gamma 2 = 1 - γ := by
    have hd := Complex.digamma_nat_add_one 1
    rw [Complex.digamma_def, logDeriv_apply] at hd
    norm_num at hd
    exact hd
  have ha := (hasDerivAt_id (2 : ℂ)).neg.const_cpow (c := (2 * π : ℂ)) (Or.inl h2π)
  have hc := (((hasDerivAt_id (2 : ℂ)).const_mul (π : ℂ)).div_const 2).ccos
  have hζ := (differentiableAt_riemannZeta (s := (2 : ℂ)) (by norm_num)).hasDerivAt
  have hR := (((((hasDerivAt_const (2 : ℂ) (2 : ℂ)).mul ha).mul hΓ).mul hc).mul hζ)
  have hu := hL.unique (hR.congr_of_eventuallyEq hev)
  have hG2 : Gamma (2 : ℂ) = 1 := by simp
  have hl : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [ofReal_log (by positivity)]; push_cast; ring_nf
  simp only [id, Pi.mul_apply, Pi.neg_apply, hdΓ, hG2, show (π : ℂ) * 2 / 2 = π by ring,
    Complex.cos_pi, Complex.sin_pi, riemannZeta_two, show (1 : ℂ) - 2 = -1 by norm_num, cpow_neg,
    cpow_ofNat, hl] at hu
  push_cast at hu ⊢
  field_simp at hu ⊢
  linear_combination hu

/-- **DLMF 5.17.7**: `C = lim_{n→∞} (∑_{k=1}^{n} k ln k − (½n² + ½n + 1/12) ln n + ¼n²)
= (γ + ln(2π))/12 − ζ′(2)/(2π²) = 1/12 − ζ′(−1)`. -/
theorem dlmf_5_17_7 :
    Tendsto glaisherSeq atTop (𝓝 glaisherC) ∧
      (glaisherC : ℂ) = ((γ + Real.log (2 * π)) / 12 : ℝ) - deriv riemannZeta 2 / (2 * π ^ 2) ∧
      (glaisherC : ℂ) = 1 / 12 - deriv riemannZeta (-1) := by
  refine ⟨tendsto_glaisherSeq, ?_, ?_⟩
  · rw [← zeta_deriv_neg_one_eq, deriv_zeta_neg_one]; ring
  · rw [deriv_zeta_neg_one]; ring

/-- **DLMF 2.10.6**: the constant `C` of 2.10.4 is Glaisher's `C`:
`C = (γ + ln(2π))/12 − ζ′(2)/(2π²) = 1/12 − ζ′(−1)`. -/
theorem dlmf_2_10_6 {C : ℝ} (hC : ∀ m, 2 ≤ m → ∀ n : ℕ, 1 ≤ n →
      exS n = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + (n : ℝ) / 2 * Real.log n +
        1 / 12 * Real.log n + C + ∑ s ∈ Finset.Icc 2 (m - 1), exTerm s n + jlogR m n) :
    C = glaisherC ∧
      (C : ℂ) = ((γ + Real.log (2 * π)) / 12 : ℝ) - deriv riemannZeta 2 / (2 * π ^ 2) ∧
      (C : ℂ) = 1 / 12 - deriv riemannZeta (-1) := by
  have hR : Tendsto (fun n : ℕ => jlogR 2 n) atTop (𝓝 0) := by
    have := tendsto_emRem (D := xlogD) (a := 1) (m := 2) (xlogD_integrable le_rfl)
    simpa only [emRem_xlog (show 1 ≤ 2 by norm_num)] using this
  have hseq : Tendsto glaisherSeq atTop (𝓝 C) := by
    have h := (tendsto_const_nhds (x := C)).add hR
    rw [add_zero] at h
    refine h.congr' ((eventually_ge_atTop 1).mono fun n hn => ?_)
    have e := hC 2 le_rfl n hn
    simp only [show 2 - 1 = 1 from rfl, Finset.Icc_eq_empty (show ¬ 2 ≤ 1 by norm_num),
      sum_empty, add_zero, exS] at e
    rw [glaisherSeq, e]
    ring
  have hCeq : C = glaisherC := tendsto_nhds_unique hseq tendsto_glaisherSeq
  obtain ⟨-, h2, h3⟩ := dlmf_5_17_7
  exact ⟨hCeq, hCeq ▸ h2, hCeq ▸ h3⟩

end Azurite.DLMF
