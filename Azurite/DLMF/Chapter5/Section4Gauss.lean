/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section4Series
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# DLMF 5.4.19: Gauss's digamma theorem

`dlmf_5_4_19`: for integers `0 < p < q`,
`ψ(p/q) = −γ − ln q − ½π cot(πp/q) + ½ ∑_{k=1}^{q−1} cos(2πkp/q) ln(2 − 2 cos(2πk/q))`.

Proof: by the limit formula (`tendsto_psiR_series`), `ψ(p/q) = lim (ln N − q ∑_{k<N} 1/(kq + p))`;
a roots-of-unity filter (`filter_identity`, `sum_rootQ_pow`) writes `q ∑_{k<N} 1/(kq + p)` as
`∑_{j<q} ω^{−jp} ∑_{m ≤ Nq} ω^{jm}/m`, `ω = e^{2πi/q}`; the `j = 0` term is the harmonic number
(`ln N − H_{Nq} → −ln q − γ`), and for `j ≠ 0`, `∑_{m ≤ M} zᵐ/m → −ln(1 − z)` on the unit circle
(`tendsto_sum_pow_div_succ`, from `∫₀¹ z/(1 − zt) dt` with an explicit `1/(δ(M + 1))` error).
Finally `ln(1 − e^{iθ}) = ½ ln(2 − 2 cos θ) + i(θ − π)/2` for `0 < θ < 2π` (`log_one_sub_exp`), and
`∑_{j<q} (πj/q − π/2) sin(2πjp/q) = −½π cot(πp/q)` (`sum_sin_mul`).
-/

open Complex Filter Topology Set Finset intervalIntegral
open scoped Real

namespace Azurite.DLMF

/-! ### Roots of unity -/

/-- `ω = e^{2πi/q}`. -/
noncomputable def rootQ (q : ℕ) : ℂ := cexp (2 * π * I / q)

theorem rootQ_pow (q n : ℕ) : rootQ q ^ n = cexp (((2 * π * n / q : ℝ) : ℂ) * I) := by
  rw [rootQ, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_rootQ_pow (q n : ℕ) : ‖rootQ q ^ n‖ = 1 := by
  rw [rootQ_pow, norm_exp_ofReal_mul_I]

/-- `∑_{j<q} (ω^a)^j = q` if `q ∣ a`, `0` otherwise. -/
theorem sum_rootQ_pow {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    ∑ j ∈ range q, (rootQ q ^ a) ^ j = if q ∣ a then (q : ℂ) else 0 := by
  have h := Complex.isPrimitiveRoot_exp q hq
  split_ifs with hd
  · rw [rootQ, (h.pow_eq_one_iff_dvd a).mpr hd]; simp
  · have hne : rootQ q ^ a ≠ 1 := fun h1 => hd ((h.pow_eq_one_iff_dvd a).mp h1)
    have hpow : (rootQ q ^ a) ^ q = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, rootQ, h.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

theorem sum_range_mul_decomp (g : ℕ → ℂ) (q N : ℕ) :
    ∑ m ∈ range (N * q), g m = ∑ k ∈ range N, ∑ r ∈ range q, g (k * q + r) := by
  induction N with
  | zero => simp
  | succ N ih => rw [show (N + 1) * q = N * q + q by ring, sum_range_add, ih, sum_range_succ]

/-- The inner sum of the filter: only `r = p − 1` survives. -/
theorem filter_inner {p q : ℕ} (hp : 0 < p) (hpq : p < q) (k : ℕ) :
    ∑ r ∈ range q, (1 / (((k * q + r : ℕ) : ℂ) + 1))
        * (if q ∣ k * q + r + 1 + (q - p) then (q : ℂ) else 0)
      = (q : ℂ) * (1 / ((k : ℂ) * q + p)) := by
  have hsplit : ∀ r, k * q + r + 1 + (q - p) = k * q + (r + 1 + (q - p)) := fun r => by ring
  rw [sum_eq_single (p - 1)]
  · have hd : q ∣ k * q + (p - 1) + 1 + (q - p) := by
      rw [hsplit, (Nat.dvd_add_right (dvd_mul_left q k))]
      rw [show p - 1 + 1 + (q - p) = q by omega]
    rw [ite_eq_left hd, mul_comm]
    congr 2
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  · intro r hr hne
    have hd : ¬ q ∣ k * q + r + 1 + (q - p) := by
      rw [hsplit, (Nat.dvd_add_right (dvd_mul_left q k))]
      rintro ⟨c, hc⟩
      have hrq := mem_range.mp hr
      have hc2 : c < 2 := by
        by_contra h
        push Not at h
        have : q * 2 ≤ q * c := Nat.mul_le_mul_left q h
        omega
      interval_cases c <;> omega
    rw [ite_eq_right hd, mul_zero]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-- **The roots-of-unity filter**:
`q ∑_{k<N} 1/(kq + p) = ∑_{j<q} (ω^{q−p})^j ∑_{m<Nq} (ω^j)^{m+1}/(m + 1)`. -/
theorem filter_identity {p q : ℕ} (hp : 0 < p) (hpq : p < q) (N : ℕ) :
    (q : ℂ) * ∑ k ∈ range N, 1 / ((k : ℂ) * q + p)
      = ∑ j ∈ range q, (rootQ q ^ (q - p)) ^ j
          * ∑ m ∈ range (N * q), (rootQ q ^ j) ^ (m + 1) / ((m : ℂ) + 1) := by
  have hq : q ≠ 0 := by omega
  have hR : ∑ j ∈ range q, (rootQ q ^ (q - p)) ^ j
        * ∑ m ∈ range (N * q), (rootQ q ^ j) ^ (m + 1) / ((m : ℂ) + 1)
      = ∑ m ∈ range (N * q), (1 / ((m : ℂ) + 1))
          * (if q ∣ m + 1 + (q - p) then (q : ℂ) else 0) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_rootQ_pow hq, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have e : (rootQ q ^ (m + 1 + (q - p))) ^ j
        = (rootQ q ^ (q - p)) ^ j * (rootQ q ^ j) ^ (m + 1) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [e]
    ring
  rw [hR, sum_range_mul_decomp, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← filter_inner hp hpq k]

/-! ### `∑ zᵐ/m → −ln(1 − z)` on the unit circle -/

/-- For `‖z‖ ≤ 1`, `ℜz < 1`: `∑_{m<M} z^{m+1}/(m + 1) → −ln(1 − z)`. -/
theorem tendsto_sum_pow_div_succ {z : ℂ} (hz : ‖z‖ ≤ 1) (hre : z.re < 1) :
    Tendsto (fun M : ℕ => ∑ m ∈ range M, z ^ (m + 1) / ((m : ℂ) + 1)) atTop
      (𝓝 (-Complex.log (1 - z))) := by
  set δ : ℝ := 1 - max z.re 0 with hδ
  have hδ0 : 0 < δ := by
    have := max_lt hre one_pos
    rw [hδ]; linarith
  have hre_t : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ (1 - z * t).re := by
    intro t ht
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have : z.re * t ≤ max z.re 0 := by
      rcases le_or_gt 0 z.re with h | h
      · calc z.re * t ≤ z.re * 1 := mul_le_mul_of_nonneg_left ht.2 h
          _ = z.re := mul_one _
          _ ≤ max z.re 0 := le_max_left _ _
      · have : z.re * t ≤ 0 := by nlinarith [ht.1]
        exact this.trans (le_max_right _ _)
    rw [hδ]; linarith
  have hslit : ∀ t ∈ Icc (0 : ℝ) 1, (1 - z * t) ∈ slitPlane := fun t ht =>
    mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hδ0 (hre_t t ht)))
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (1 - z * t) ≠ 0 := fun t ht => slitPlane_ne_zero (hslit t ht)
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖1 - z * t‖ := fun t ht =>
    (hre_t t ht).trans (re_le_norm _)
  have hint : IntervalIntegrable (fun t : ℝ => z / (1 - z * t)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.div (by fun_prop) hne
  have hF : ∫ t in (0 : ℝ)..1, z / (1 - z * t) = -Complex.log (1 - z) := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => -Complex.log (1 - z * t)) (z / (1 - z * t)) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
        simpa using (hasDerivAt_id t).ofReal_comp
      have h2 := ((h1.const_mul z).const_sub 1).clog_real (hslit t ht)
      convert h2.neg using 1
      ring
    rw [integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hS : ∀ M : ℕ, ∑ m ∈ range M, z ^ (m + 1) / ((m : ℂ) + 1)
      = ∫ t in (0 : ℝ)..1, ∑ m ∈ range M, z ^ (m + 1) * (t : ℂ) ^ m := by
    intro M
    rw [integral_finsetSum (fun m _ => by apply Continuous.intervalIntegrable; fun_prop)]
    refine sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul]
    have : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m = (((1 : ℝ) / (m + 1) : ℝ) : ℂ) := by
      rw [show (fun t : ℝ => (t : ℂ) ^ m) = fun t : ℝ => ((t ^ m : ℝ) : ℂ) by
          funext t; push_cast; rfl,
        intervalIntegral.integral_ofReal, integral_pow]
      norm_num
    rw [this]
    push_cast
    ring
  have hdiff : ∀ M : ℕ, -Complex.log (1 - z) - ∑ m ∈ range M, z ^ (m + 1) / ((m : ℂ) + 1)
      = ∫ t in (0 : ℝ)..1, z * (z * t) ^ M / (1 - z * t) := by
    intro M
    rw [← hF, hS, ← integral_sub hint (by apply Continuous.intervalIntegrable; fun_prop)]
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 := hne t ht
    have hg := mul_neg_geom_sum (z * (t : ℂ)) M
    have hsum : ∑ m ∈ range M, z ^ (m + 1) * (t : ℂ) ^ m = z * ∑ i ∈ range M, (z * t) ^ i := by
      rw [mul_sum]; refine sum_congr rfl fun i _ => by ring
    simp only
    rw [hsum, eq_div_iff h1, sub_mul, div_mul_cancel₀ _ h1]
    linear_combination (-z) * hg
  have hbound : ∀ M : ℕ, ‖-Complex.log (1 - z) - ∑ m ∈ range M, z ^ (m + 1) / ((m : ℂ) + 1)‖
      ≤ 1 / (δ * (M + 1)) := by
    intro M
    rw [hdiff]
    have hle : ‖∫ t in (0 : ℝ)..1, z * (z * t) ^ M / (1 - z * t)‖
        ≤ ∫ t in (0 : ℝ)..1, t ^ M / δ := by
      apply norm_integral_le_of_norm_le zero_le_one
      · filter_upwards with t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
        rw [norm_div, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht'.1]
        have h1 : ‖z‖ * (‖z‖ * t) ^ M ≤ t ^ M := by
          calc ‖z‖ * (‖z‖ * t) ^ M = ‖z‖ ^ (M + 1) * t ^ M := by ring
            _ ≤ 1 * t ^ M := mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hz)
                (pow_nonneg ht'.1 M)
            _ = t ^ M := one_mul _
        exact div_le_div₀ (pow_nonneg ht'.1 M) h1 hδ0 (hnorm t ht')
      · apply Continuous.intervalIntegrable; fun_prop
    have hint2 : ∫ t in (0 : ℝ)..1, t ^ M / δ = 1 / (δ * (M + 1)) := by
      rw [intervalIntegral.integral_div, integral_pow]
      simp
      ring
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun M : ℕ => 1 / δ * (1 / ((M : ℝ) + 1))) atTop (𝓝 (1 / δ * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at h0
  refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) h0
  rw [norm_sub_rev]
  calc _ ≤ 1 / (δ * (M + 1)) := hbound M
    _ = 1 / δ * (1 / ((M : ℝ) + 1)) := by field_simp

/-! ### `ln(1 − e^{iθ})` -/

/-- `ln(1 − e^{iθ}) = ½ ln(2 − 2 cos θ) + i(θ − π)/2` for `0 < θ < 2π`. -/
theorem log_one_sub_exp {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
    Complex.log (1 - cexp (θ * I))
      = ((1 / 2 * Real.log (2 - 2 * Real.cos θ) : ℝ) : ℂ) + (((θ - π) / 2 : ℝ) : ℂ) * I := by
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set φ := (θ - π) / 2 with hφ
  have hc : Real.cos φ = Real.sin (θ / 2) := by
    rw [hφ, show (θ - π) / 2 = θ / 2 - π / 2 by ring, Real.cos_sub_pi_div_two]
  have hsφ : Real.sin φ = -Real.cos (θ / 2) := by
    rw [hφ, show (θ - π) / 2 = θ / 2 - π / 2 by ring, Real.sin_sub_pi_div_two]
  have hcos2 := Real.cos_two_mul (θ / 2)
  have hsin2 := Real.sin_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hcos2 hsin2
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  have hrep : 1 - cexp (θ * I) = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) * (cos φ + sin φ * I) := by
    apply Complex.ext
    · simp only [sub_re, one_re, exp_ofReal_mul_I_re, mul_re, ofReal_re, ofReal_im, add_re,
        add_im, mul_im, I_re, I_im, ← ofReal_cos, ← ofReal_sin]
      simp only [mul_zero, sub_zero, mul_one, zero_mul, add_zero, zero_add]
      rw [hc]
      nlinarith
    · simp only [sub_im, one_im, exp_ofReal_mul_I_im, mul_im, ofReal_re, ofReal_im, add_re,
        add_im, mul_re, I_re, I_im, ← ofReal_cos, ← ofReal_sin]
      simp only [mul_zero, sub_zero, mul_one, zero_mul, add_zero, zero_add, zero_sub]
      rw [hsφ]
      linarith
  have hpos : 0 < 2 * Real.sin (θ / 2) := by linarith
  have hφmem : φ ∈ Set.Ioc (-π) π := ⟨by rw [hφ]; linarith, by rw [hφ]; linarith⟩
  apply Complex.ext
  · rw [log_re, hrep, norm_mul, Complex.norm_real, norm_cos_add_sin_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hpos]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, zero_mul,
      add_zero]
    have h22 : 2 - 2 * Real.cos θ = (2 * Real.sin (θ / 2)) ^ 2 := by nlinarith
    rw [h22, Real.log_pow]
    push_cast
    ring
  · rw [log_im, hrep, arg_real_mul _ hpos, arg_cos_add_sin_mul_I hφmem]
    simp

/-! ### The cotangent sum -/

theorem sum_mul_pow_identity (z : ℂ) (n : ℕ) :
    (z - 1) * ∑ j ∈ range n, (j : ℂ) * z ^ j = n * z ^ n - ∑ j ∈ range n, z ^ (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    push_cast
    ring

/-- `∑_{j<q} (2πj/q − π)/2 · sin(2πjp/q) = −½π cot(πp/q)` for `0 < p < q`. -/
theorem sum_sin_mul {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    ∑ j ∈ range q, Real.sin (2 * π * j * p / q) * ((2 * π * j / q - π) / 2)
      = -(π / 2) * Real.cot (π * p / q) := by
  have hq : q ≠ 0 := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  set z := rootQ q ^ p with hz
  have hnd : ¬ q ∣ p := Nat.not_dvd_of_pos_of_lt hp hpq
  have hS0 : ∑ j ∈ range q, z ^ j = 0 := by rw [hz, sum_rootQ_pow hq, ite_eq_right hnd]
  have hz1 : z ≠ 1 := by
    intro h
    exact hnd (((Complex.isPrimitiveRoot_exp q hq).pow_eq_one_iff_dvd p).mp h)
  have hzq : z ^ q = 1 := by
    rw [hz, ← pow_mul, mul_comm, pow_mul, rootQ, (Complex.isPrimitiveRoot_exp q hq).pow_eq_one,
      one_pow]
  have hS1 : ∑ j ∈ range q, (j : ℂ) * z ^ j = q / (z - 1) := by
    have h := sum_mul_pow_identity z q
    have hsh : ∑ j ∈ range q, z ^ (j + 1) = 0 := by
      rw [show ∑ j ∈ range q, z ^ (j + 1) = z * ∑ j ∈ range q, z ^ j by
        rw [mul_sum]; refine sum_congr rfl fun j _ => by ring, hS0, mul_zero]
    rw [hzq, hsh, mul_one, sub_zero] at h
    rw [eq_div_iff (sub_ne_zero.mpr hz1), mul_comm]
    exact h
  -- `z^j = e^{i·2πjp/q}`
  have hzj : ∀ j : ℕ, z ^ j = cexp (((2 * π * j * p / q : ℝ) : ℂ) * I) := by
    intro j
    rw [hz, ← pow_mul, rootQ_pow]
    congr 3
    push_cast
    ring
  have him0 : ∑ j ∈ range q, Real.sin (2 * π * j * p / q) = 0 := by
    have := congrArg im hS0
    rw [im_sum, zero_im] at this
    have hl0 : ∀ j ∈ range q, (z ^ j).im = Real.sin (2 * π * j * p / q) := fun j _ => by
      rw [hzj, exp_ofReal_mul_I_im]
    rwa [sum_congr rfl hl0] at this
  have him1 : ∑ j ∈ range q, (j : ℝ) * Real.sin (2 * π * j * p / q)
      = -(q / 2) * Real.cot (π * p / q) := by
    have h := congrArg im hS1
    rw [im_sum] at h
    have hl : ∀ j ∈ range q, ((j : ℂ) * z ^ j).im = (j : ℝ) * Real.sin (2 * π * j * p / q) := by
      intro j _
      rw [hzj, show (j : ℂ) = ((j : ℝ) : ℂ) by push_cast; rfl, im_ofReal_mul,
        exp_ofReal_mul_I_im]
    rw [sum_congr rfl hl] at h
    rw [h]
    -- the imaginary part of `q/(z − 1)`
    set α := π * p / q with hα
    have hφ : 2 * π * p / q = 2 * α := by rw [hα]; ring
    have hz' : z = cexp (((2 * α : ℝ) : ℂ) * I) := by
      have h1 := hzj 1
      rw [pow_one] at h1
      rw [h1]; congr 3; push_cast; rw [hα]; ring
    have hsα : 0 < Real.sin α := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · rw [hα]; positivity
      · rw [hα, div_lt_iff₀ hqR]
        have : (p : ℝ) < q := by exact_mod_cast hpq
        nlinarith [Real.pi_pos]
    have hc2 := Real.cos_two_mul α
    have hs2 := Real.sin_two_mul α
    have hpy := Real.sin_sq_add_cos_sq α
    rw [hz', exp_mul_I, ← ofReal_cos, ← ofReal_sin, div_im]
    simp only [natCast_im, natCast_re, sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, sub_zero, mul_one, one_re, sub_im, add_im, mul_im, zero_mul, add_zero, one_im,
      zero_add, zero_div, zero_sub, normSq_apply]
    rw [Real.cot_eq_cos_div_sin, hc2, hs2]
    have hden : (2 * Real.cos α ^ 2 - 1 - 1) * (2 * Real.cos α ^ 2 - 1 - 1)
        + 2 * Real.sin α * Real.cos α * (2 * Real.sin α * Real.cos α)
        = 4 * Real.sin α ^ 2 := by nlinarith
    rw [hden]
    field_simp
    ring
  have hsplit : ∀ j ∈ range q, Real.sin (2 * π * j * p / q) * ((2 * π * j / q - π) / 2)
      = π / q * ((j : ℝ) * Real.sin (2 * π * j * p / q))
        - π / 2 * Real.sin (2 * π * j * p / q) := by
    intro j _
    field_simp
  rw [sum_congr rfl hsplit, sum_sub_distrib, ← mul_sum, ← mul_sum, him0, him1]
  field_simp
  ring

/-! ### The main theorem -/

theorem re_lt_one_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1) : w.re < 1 := by
  by_contra h
  push Not at h
  have h1 : w.re ≤ 1 := hw ▸ re_le_norm w
  have hre : w.re = 1 := le_antisymm h1 h
  have hn : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, normSq_apply] at this
    nlinarith
  have him : w.im = 0 := by rw [hre] at hn; nlinarith
  exact hne (Complex.ext (by simp [hre]) (by simp [him]))

theorem sum_Ico_one_eq_range (f : ℕ → ℝ) (h0 : f 0 = 0) (q : ℕ) :
    ∑ k ∈ Ico 1 q, f k = ∑ k ∈ range q, f k := by
  cases q with
  | zero => simp
  | succ n =>
    rw [sum_range_succ', h0, add_zero, sum_Ico_eq_sum_range]
    refine sum_congr (by simp) fun i _ => by rw [add_comm]

/-- `∑_{k<q−1} f(k + 1) = ∑_{k=1}^{q−1} f(k)`. -/
theorem sum_range_pred_succ (f : ℕ → ℝ) (q : ℕ) :
    ∑ i ∈ range (q - 1), f (i + 1) = ∑ k ∈ Ico 1 q, f k := by
  rw [sum_Ico_eq_sum_range]
  refine sum_congr rfl fun i _ => by rw [add_comm]

theorem harmonic_eq_sum (M : ℕ) : ((harmonic M : ℚ) : ℂ) = ∑ m ∈ range M, 1 / ((m : ℂ) + 1) := by
  simp [harmonic]

theorem tendsto_mul_const_atTop {q : ℕ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => N * q) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_right a hq)⟩

/-- The real part of the `j`-th term. -/
theorem term_re {p q j : ℕ} (hpq : p < q) (hj1 : 1 ≤ j) (hjq : j < q) :
    ((rootQ q ^ (q - p)) ^ j * Complex.log (1 - rootQ q ^ j)).re
      = Real.cos (2 * π * j * p / q) * (1 / 2 * Real.log (2 - 2 * Real.cos (2 * π * j / q)))
        + Real.sin (2 * π * j * p / q) * ((2 * π * j / q - π) / 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hθ0 : 0 < 2 * π * j / q := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    positivity
  have hθ1 : 2 * π * j / q < 2 * π := by
    rw [div_lt_iff₀ hq]
    have : (j : ℝ) < q := by exact_mod_cast hjq
    nlinarith [Real.pi_pos]
  rw [rootQ_pow q j, log_one_sub_exp hθ0 hθ1, ← pow_mul, rootQ_pow, exp_mul_I, ← ofReal_cos,
    ← ofReal_sin]
  have hang : 2 * π * ((q - p) * j : ℕ) / q = (j : ℝ) * (2 * π) - 2 * π * j * p / q := by
    push_cast [Nat.cast_sub hpq.le]
    field_simp
  have hsj : Real.sin ((j : ℝ) * (2 * π)) = 0 := by
    rw [show (j : ℝ) * (2 * π) = ((2 * j : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [hang, Real.cos_sub, Real.sin_sub, Real.cos_nat_mul_two_pi, hsj]
  simp only [mul_re, add_re, ofReal_re, mul_im, add_im, ofReal_im, I_re, I_im]
  ring

/-- **DLMF 5.4.19** (Gauss's digamma theorem): for integers `0 < p < q`,
`ψ(p/q) = −γ − ln q − ½π cot(πp/q) + ½ ∑_{k=1}^{q−1} cos(2πkp/q) ln(2 − 2 cos(2πk/q))`. -/
theorem dlmf_5_4_19 {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    digamma ((p : ℂ) / q)
      = ((-Real.eulerMascheroniConstant - Real.log q - π / 2 * Real.cot (π * p / q)
          + 1 / 2 * ∑ k ∈ Ico 1 q,
          Real.cos (2 * π * k * p / q) * Real.log (2 - 2 * Real.cos (2 * π * k / q)) : ℝ) : ℂ) := by
  have hq0 : 0 < q := by omega
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hx : (0 : ℝ) < p / q := by
    have : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  rw [show (p : ℂ) / q = ((p / q : ℝ) : ℂ) by push_cast; rfl, digamma_ofReal]
  congr 1
  set ω := rootQ q
  -- the sequence
  set c : ℕ → ℂ := fun N => ((Real.log N : ℝ) : ℂ) - (q : ℂ) * ∑ k ∈ range N, 1 / ((k : ℂ) * q + p)
    with hc
  have hA : Tendsto c atTop (𝓝 (psiR (p / q) : ℂ)) := by
    refine ((continuous_ofReal.tendsto _).comp (tendsto_psiR_series hx)).congr fun N => ?_
    simp only [Function.comp, hc]
    push_cast
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have hk : (k : ℂ) * q + p ≠ 0 := by
      have : (0 : ℝ) < k * q + p := by
        have : (0 : ℝ) < p := by exact_mod_cast hp
        positivity
      exact_mod_cast this.ne'
    field_simp
    ring
  -- the filtered form
  set T : ℕ → ℕ → ℂ := fun j M => ∑ m ∈ range M, (ω ^ j) ^ (m + 1) / ((m : ℂ) + 1) with hT
  have hcB : ∀ N, c N = (((Real.log N - (harmonic (N * q) : ℚ) : ℝ)) : ℂ)
      - ∑ i ∈ range (q - 1), (ω ^ (q - p)) ^ (i + 1) * T (i + 1) (N * q) := by
    intro N
    simp only [hc, hT]
    rw [filter_identity hp hpq N, show q = q - 1 + 1 by omega, sum_range_succ']
    push_cast
    rw [show q - 1 + 1 = q by omega, harmonic_eq_sum]
    simp only [pow_zero, one_pow, one_mul]
    ring
  -- limits
  have hH : Tendsto (fun N : ℕ => Real.log N - (harmonic (N * q) : ℚ)) atTop
      (𝓝 (-Real.log q - Real.eulerMascheroniConstant)) := by
    have h1 := Real.tendsto_harmonic_sub_log.comp (tendsto_mul_const_atTop hq0)
    have h2 := (h1.neg).sub_const (Real.log q)
    rw [show -Real.log q - Real.eulerMascheroniConstant
        = -Real.eulerMascheroniConstant - Real.log q by ring]
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    rw [Real.log_mul hN0 hq]
    ring
  have hTlim : ∀ i ∈ range (q - 1), Tendsto (fun N : ℕ => T (i + 1) (N * q)) atTop
      (𝓝 (-Complex.log (1 - ω ^ (i + 1)))) := by
    intro i hi
    have hi' : i + 1 < q := by have := mem_range.mp hi; omega
    have hn1 : ‖ω ^ (i + 1)‖ = 1 := norm_rootQ_pow q (i + 1)
    have hne1 : ω ^ (i + 1) ≠ 1 := fun h => by
      have := ((Complex.isPrimitiveRoot_exp q hq0.ne').pow_eq_one_iff_dvd (i + 1)).mp h
      exact Nat.not_dvd_of_pos_of_lt (by omega) hi' this
    exact (tendsto_sum_pow_div_succ hn1.le (re_lt_one_of_norm_eq_one hn1 hne1)).comp
      (tendsto_mul_const_atTop hq0)
  have hlim : Tendsto c atTop
      (𝓝 ((((-Real.log q - Real.eulerMascheroniConstant) : ℝ) : ℂ)
        - ∑ i ∈ range (q - 1), (ω ^ (q - p)) ^ (i + 1) * (-Complex.log (1 - ω ^ (i + 1))))) := by
    have h1 := (continuous_ofReal.tendsto _).comp hH
    have h2 := tendsto_finsetSum (range (q - 1)) fun i hi =>
      (hTlim i hi).const_mul ((ω ^ (q - p)) ^ (i + 1))
    refine (h1.sub h2).congr fun N => ?_
    rw [hcB N]
    rfl
  have huniq := tendsto_nhds_unique hA hlim
  have hre := congrArg re huniq
  rw [ofReal_re, sub_re, ofReal_re, re_sum] at hre
  set A : ℕ → ℝ := fun j => Real.cos (2 * π * j * p / q)
    * (1 / 2 * Real.log (2 - 2 * Real.cos (2 * π * j / q))) with hAdef
  set B : ℕ → ℝ := fun j => Real.sin (2 * π * j * p / q) * ((2 * π * j / q - π) / 2) with hBdef
  have hterm : ∀ i ∈ range (q - 1),
      ((ω ^ (q - p)) ^ (i + 1) * (-Complex.log (1 - ω ^ (i + 1)))).re
        = -(A (i + 1) + B (i + 1)) := by
    intro i hi
    have hi' : i + 1 < q := by have := mem_range.mp hi; omega
    rw [mul_neg, neg_re, term_re hpq (by omega) hi']
  rw [sum_congr rfl hterm, sum_neg_distrib,
    sum_range_pred_succ (fun j => A j + B j) q, sum_add_distrib,
    sum_Ico_one_eq_range B (by simp [hBdef]) q] at hre
  have hBsum : ∑ k ∈ range q, B k = -(π / 2) * Real.cot (π * p / q) := sum_sin_mul hp hpq
  have hAsum : ∑ k ∈ Ico 1 q, A k = 1 / 2 * ∑ k ∈ Ico 1 q,
      Real.cos (2 * π * k * p / q) * Real.log (2 - 2 * Real.cos (2 * π * k / q)) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [hAdef]
    ring
  rw [hBsum, hAsum] at hre
  rw [hre]
  ring

end Azurite.DLMF
