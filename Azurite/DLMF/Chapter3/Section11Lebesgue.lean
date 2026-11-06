/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section15Fourier
import Azurite.DLMF.Chapter3.Section11ChebSeries

/-!
# DLMF §3.11(ii): the Lebesgue constants are increasing

"`Lₙ` is a monotonically increasing function of `n`" (`dlmf_3_11_ii_lebesgue_strictMono`).

Proof via Szegő's series (`dlmf_3_11_ii_szego`):
`Lₙ = (16/π²) ∑_{k ≥ 1} H′_{k(2n+1)} / (4k² − 1)`, `H′_M = ∑_{j=0}^{M−1} 1/(2j + 1)` (`hprime`),
in which every term increases with `n`. Ingredients:

* the Fourier series `|sin x| = (8/π) ∑_{k ≥ 1} sin²(kx)/(4k² − 1)` (`hasSum_abs_sin`), from §1.8
  with the coefficients `aₘ = (2/π)(1 + (−1)ᵐ)/(1 − m²)` (`fourierA_abs_sin`);
* `∫₀^{π/2} sin²(Mu)/sin u du = H′_M` (`integral_sin_sq_div_sin`), from
  `sin²(Mu) = sin u ∑_{j<M} sin((2j + 1)u)` (`sin_sq_nat_mul`);
* term-by-term integration of `|sin(Nu)|/sin u` (dominated convergence,
  `|sin(Nu)| ≤ N |sin u|`, `abs_sin_nat_mul_le` of §1.15),
  `Lₙ = (2/π) ∫₀^{π/2} |sin((2n + 1)u)|/sin u du` (`lebesgueConst_eq_half`).
-/

open Real Finset MeasureTheory Filter Topology Set

namespace Azurite.DLMF

/-! ### Elementary integrals -/

/-- `∫₀^b sin(cx) dx = (1 − cos(cb))/c` (both sides `0` for `c = 0`). -/
theorem integral_sin_mul_zero (c b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.sin (c * x) = (1 - Real.cos (c * b)) / c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin]
    simp [div_eq_inv_mul]

/-- `∫₀^π sin x cos(mx) dx = (1 + (−1)ᵐ)/(1 − m²)`. -/
theorem integral_sin_mul_cos (m : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.sin x * Real.cos (m * x) = (1 + (-1) ^ m) / (1 - (m : ℝ) ^ 2) := by
  have e : ∀ x : ℝ, Real.sin x * Real.cos (m * x) =
      1 / 2 * (Real.sin ((m + 1) * x) - Real.sin ((m - 1) * x)) := fun x => by
    rw [show ((m : ℝ) + 1) * x = m * x + x by ring, show ((m : ℝ) - 1) * x = m * x - x by ring,
      Real.sin_add, Real.sin_sub]
    ring
  rw [intervalIntegral.integral_congr fun x _ => e x, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun x : ℝ =>
      Real.sin ((m + 1) * x)).intervalIntegrable _ _) ((by fun_prop : Continuous fun x : ℝ =>
      Real.sin ((m - 1) * x)).intervalIntegrable _ _),
    integral_sin_mul_zero, integral_sin_mul_zero, add_mul, one_mul, Real.cos_add_pi,
    sub_mul, one_mul, Real.cos_sub_pi, Real.cos_nat_mul_pi]
  rcases eq_or_ne m 1 with rfl | hm
  · norm_num
  · have h1 : (m : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm)
    have h2 : (m : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 1 - (m : ℝ) ^ 2 ≠ 0 := by
      rw [show 1 - (m : ℝ) ^ 2 = -((m - 1) * (m + 1)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
    field_simp
    ring

/-! ### The Fourier series of `|sin x|` -/

theorem continuous_abs_sin_complex : Continuous fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ) := by
  fun_prop

theorem abs_sin_even (x : ℝ) :
    (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) (-x) = (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) x := by
  simp only [Real.sin_neg, abs_neg]

theorem abs_sin_periodic : Function.Periodic (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) (2 * π) :=
  fun x => by simp only [Real.sin_add_two_pi]

/-- The Fourier cosine coefficients of `|sin x|`: `aₘ = (2/π)(1 + (−1)ᵐ)/(1 − m²)`. -/
theorem fourierA_abs_sin (m : ℕ) :
    fourierA (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) m =
      ((2 / π * ((1 + (-1) ^ m) / (1 - (m : ℝ) ^ 2)) : ℝ) : ℂ) := by
  have hφc : Continuous fun x : ℝ => |Real.sin x| * Real.cos (m * x) := by fun_prop
  have hφe : ∀ x, (fun x : ℝ => |Real.sin x| * Real.cos (m * x)) (-x) =
      (fun x : ℝ => |Real.sin x| * Real.cos (m * x)) x := fun x => by
    simp only [Real.sin_neg, abs_neg, mul_neg, Real.cos_neg]
  rw [fourierA]
  have e : (∫ x in (-π)..π, ((|Real.sin x| : ℝ) : ℂ) * (Real.cos (m * x) : ℂ)) =
      ((∫ x in (-π)..π, |Real.sin x| * Real.cos (m * x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    push_cast
    rfl
  have e2 : ∫ x in (0 : ℝ)..π, |Real.sin x| * Real.cos (m * x) =
      ∫ x in (0 : ℝ)..π, Real.sin x * Real.cos (m * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le pi_pos.le] at hx
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]
  rw [e, integral_even_symm hφe hφc, e2, integral_sin_mul_cos, Complex.real_smul]
  push_cast
  ring

theorem fourierB_abs_sin (m : ℕ) : fourierB (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) m = 0 :=
  dlmf_1_8_i_even (f := fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) abs_sin_even m

theorem abs_coeff_abs_sin_le {n : ℕ} (hn : 2 ≤ n) :
    |(1 + (-1 : ℝ) ^ n) / (1 - (n : ℝ) ^ 2)| ≤ 4 / (n : ℝ) ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : |1 + (-1 : ℝ) ^ n| ≤ 2 := by
    calc |1 + (-1 : ℝ) ^ n| ≤ |1| + |(-1 : ℝ) ^ n| := abs_add_le _ _
      _ = 2 := by rw [abs_pow, abs_neg, abs_one, one_pow]; norm_num
  have h2 : |1 - (n : ℝ) ^ 2| = (n : ℝ) ^ 2 - 1 := by
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
  rw [abs_div, h2, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [abs_nonneg (1 + (-1 : ℝ) ^ n)]

theorem summable_fourierC_abs_sin :
    Summable (fourierC fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) := by
  have hi : IntervalIntegrable (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) volume (-π) π :=
    continuous_abs_sin_complex.intervalIntegrable _ _
  have hb : Summable fun n : ℕ => 2 / π * (4 / (n : ℝ) ^ 2) / 2 :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 / π * 4 / 2)).congr
      fun n => by ring
  have hev : ∀ᶠ n : ℕ in cofinite, 2 ≤ n := by
    rw [Nat.cofinite_eq_atTop]; exact eventually_ge_atTop 2
  have hc : ∀ n : ℕ, 2 ≤ n →
      ‖fourierA (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) n / 2‖ ≤ 2 / π * (4 / (n : ℝ) ^ 2) / 2 :=
    fun n hn => by
      rw [fourierA_abs_sin, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 / π), Complex.norm_two]
      gcongr
      exact abs_coeff_abs_sin_le hn
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_norm_bounded_eventually hb ?_
    filter_upwards [hev] with n hn
    rw [fourierC_natCast hi, fourierB_abs_sin, mul_zero, sub_zero]
    exact hc n hn
  · refine Summable.of_norm_bounded_eventually hb ?_
    filter_upwards [hev] with n hn
    rw [fourierC_neg_natCast hi, fourierB_abs_sin, mul_zero, add_zero]
    exact hc n hn

/-- `∑_{k ≥ 1} 1/(4k² − 1) = ½`. -/
theorem hasSum_inv_four_sq_sub_one :
    HasSum (fun k : ℕ => 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) (1 / 2) := by
  have hpos : ∀ k : ℕ, 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := fun k => by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hpart : ∀ K : ℕ, ∑ k ∈ range K, 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) =
      1 / 2 * (1 - 1 / (2 * (K : ℝ) + 1)) := fun K => by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ih]
      have h1 := hpos K
      have h2 : (0 : ℝ) < 2 * K + 1 := by positivity
      have h3 : (0 : ℝ) < 2 * ((K + 1 : ℕ) : ℝ) + 1 := by positivity
      push_cast at h3 ⊢
      field_simp
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (one_div_pos.mpr (hpos k)).le)]
  simp only [hpart]
  have ht : Tendsto (fun K : ℕ => 1 / (2 * (K : ℝ) + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun K : ℕ => 2 * (K : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    have h2 := this.inv_tendsto_atTop
    simp only [one_div]
    exact h2
  simpa using (ht.const_sub 1).const_mul (1 / 2 : ℝ)

/-- The Fourier series `|sin x| = (8/π) ∑_{k ≥ 1} sin²(kx)/(4k² − 1)`. -/
theorem hasSum_abs_sin (x : ℝ) :
    HasSum (fun k : ℕ => 8 / π * Real.sin (((k : ℝ) + 1) * x) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1))
      |Real.sin x| := by
  have h := dlmf_1_8_1 abs_sin_periodic continuous_abs_sin_complex summable_fourierC_abs_sin x
  simp only [fourierA_abs_sin, fourierB_abs_sin, zero_mul, add_zero] at h
  -- the real series `∑ₙ a_{n+1} cos((n + 1)x)`
  set F : ℕ → ℝ := fun n => 2 / π * ((1 + (-1) ^ (n + 1)) / (1 - ((n + 1 : ℕ) : ℝ) ^ 2)) *
    Real.cos ((n + 1 : ℕ) * x)
  have hF : HasSum F (|Real.sin x| - 2 / π) := by
    rw [← Complex.hasSum_ofReal]
    convert h using 1
    · funext n; simp only [F]; push_cast; ring
    · push_cast; ring
  -- only the odd `n` contribute
  have hodd : HasSum (F ∘ fun k => 2 * k + 1) (|Real.sin x| - 2 / π) := by
    refine (Function.Injective.hasSum_iff (fun a b h => by simpa using h) fun n hn => ?_).mpr hF
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [F]
      rw [show j + j + 1 = 2 * j + 1 by ring, pow_succ, pow_mul]
      simp
    · exact absurd ⟨j, rfl⟩ hn
  have hT := hasSum_inv_four_sq_sub_one.mul_left (4 / π)
  convert hT.add hodd using 1
  · funext k
    simp only [F, Function.comp]
    have hpos : 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by
      have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith
    have hpow : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
    rw [hpow]
    push_cast
    have hc : Real.cos ((2 * (k : ℝ) + 1 + 1) * x) = 1 - 2 * Real.sin (((k : ℝ) + 1) * x) ^ 2 := by
      rw [show (2 * (k : ℝ) + 1 + 1) * x = 2 * (((k : ℝ) + 1) * x) by ring, Real.cos_two_mul,
        Real.cos_sq']
      ring
    rw [hc]
    have h1 : 1 - (2 * (k : ℝ) + 1 + 1) ^ 2 = -(4 * ((k : ℝ) + 1) ^ 2 - 1) := by ring
    rw [h1]
    field_simp
    ring
  · ring

/-! ### `∫₀^{π/2} sin²(Mu)/sin u du = H′_M` -/

/-- `H′_M = ∑_{j=0}^{M−1} 1/(2j + 1)`. -/
noncomputable def hprime (M : ℕ) : ℝ := ∑ j ∈ range M, 1 / (2 * (j : ℝ) + 1)

theorem sin_sq_sub_sin_sq (a b : ℝ) :
    Real.sin a ^ 2 - Real.sin b ^ 2 = Real.sin (a + b) * Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  linear_combination (-Real.sin a ^ 2) * hb + Real.sin b ^ 2 * ha

/-- `sin²(Mu) = sin u ∑_{j<M} sin((2j + 1)u)`. -/
theorem sin_sq_nat_mul (M : ℕ) (u : ℝ) :
    Real.sin (M * u) ^ 2 = Real.sin u * ∑ j ∈ range M, Real.sin ((2 * (j : ℝ) + 1) * u) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, mul_add, ← ih]
    have := sin_sq_sub_sin_sq (((M + 1 : ℕ) : ℝ) * u) ((M : ℝ) * u)
    push_cast at this ⊢
    rw [show ((M : ℝ) + 1) * u + M * u = (2 * M + 1) * u by ring,
      show ((M : ℝ) + 1) * u - M * u = u by ring] at this
    linear_combination this

theorem cos_odd_mul_pi_div_two (j : ℕ) : Real.cos ((2 * (j : ℝ) + 1) * (π / 2)) = 0 := by
  rw [show (2 * (j : ℝ) + 1) * (π / 2) = j * π + π / 2 by ring, Real.cos_add_pi_div_two,
    Real.sin_nat_mul_pi, neg_zero]

/-- `∫₀^{π/2} sin²(Mu)/sin u du = H′_M`. -/
theorem integral_sin_sq_div_sin (M : ℕ) :
    ∫ u in (0 : ℝ)..π / 2, Real.sin (M * u) ^ 2 / Real.sin u = hprime M := by
  have e : EqOn (fun u => Real.sin (M * u) ^ 2 / Real.sin u)
      (fun u => ∑ j ∈ range M, Real.sin ((2 * (j : ℝ) + 1) * u)) (uIcc 0 (π / 2)) :=
      fun u hu => by
    rw [Set.uIcc_of_le (by positivity)] at hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · subst h0; simp
    · have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [hu.2, pi_pos])
      simp only
      rw [sin_sq_nat_mul, mul_div_cancel_left₀ _ hs.ne']
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_finsetSum
    fun (j : ℕ) _ => (by fun_prop : Continuous fun u : ℝ =>
      Real.sin ((2 * (j : ℝ) + 1) * u)).intervalIntegrable _ _, hprime]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_sin_mul_zero, cos_odd_mul_pi_div_two, sub_zero]

/-! ### Szegő's series -/

/-- `Lₙ = (2/π) ∫₀^{π/2} |sin((2n + 1)u)|/sin u du`. -/
theorem lebesgueConst_eq_half (n : ℕ) :
    lebesgueConst n = 2 / π *
      ∫ u in (0 : ℝ)..π / 2, |Real.sin (((2 * n + 1 : ℕ) : ℝ) * u)| / Real.sin u := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun t => |Real.sin ((n + 1 / 2) * t)| / Real.sin (t / 2)) (two_ne_zero (α := ℝ))
    (a := 0) (b := π / 2)
  rw [mul_zero, show (2 : ℝ) * (π / 2) = π by ring] at h
  have e : ∫ u in (0 : ℝ)..π / 2, |Real.sin (((2 * n + 1 : ℕ) : ℝ) * u)| / Real.sin u =
      ∫ x in (0 : ℝ)..π / 2, |Real.sin ((n + 1 / 2) * (2 * x))| / Real.sin (2 * x / 2) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast
    rw [show ((n : ℝ) + 1 / 2) * (2 * u) = (2 * n + 1) * u by ring,
      show 2 * u / 2 = u by ring]
  rw [lebesgueConst, e, h, smul_eq_mul]
  field_simp

/-- **Szegő's series**: `Lₙ = (16/π²) ∑_{k ≥ 1} H′_{k(2n+1)}/(4k² − 1)`. -/
theorem dlmf_3_11_ii_szego (n : ℕ) :
    HasSum (fun k : ℕ => 16 / π ^ 2 * hprime ((k + 1) * (2 * n + 1)) /
      (4 * ((k : ℝ) + 1) ^ 2 - 1)) (lebesgueConst n) := by
  set N : ℕ := 2 * n + 1
  set F : ℕ → ℝ → ℝ := fun k u =>
    8 / π * Real.sin ((((k + 1) * N : ℕ) : ℝ) * u) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1) /
      Real.sin u
  set f : ℝ → ℝ := fun u => |Real.sin ((N : ℝ) * u)| / Real.sin u
  have hpos : ∀ k : ℕ, 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := fun k => by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hlim : ∀ u, HasSum (fun k => F k u) (f u) := fun u => by
    have := (hasSum_abs_sin ((N : ℝ) * u)).div_const (Real.sin u)
    convert this using 2 with k
    simp only [F]
    push_cast
    ring_nf
  have htsum : (fun t => ∑' k, F k t) = f := funext fun t => (hlim t).tsum_eq
  have hFnn : ∀ k, ∀ t ∈ uIoc 0 (π / 2), 0 ≤ F k t := fun k t ht => by
    rw [Set.uIoc_of_le (by positivity)] at ht
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    have := hpos k
    simp only [F]
    positivity
  have hfint : IntervalIntegrable f volume 0 (π / 2) := by
    refine intervalIntegrable_of_abs_le (by positivity)
      ((by fun_prop : Continuous fun u : ℝ => |Real.sin ((N : ℝ) * u)|).measurable.div
        Real.continuous_sin.measurable) N fun t ht => ?_
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
    simp only [f]
    rw [abs_div, abs_abs, abs_of_pos hs, div_le_iff₀ hs]
    have := abs_sin_nat_mul_le N t
    rwa [abs_of_pos hs] at this
  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := π / 2) (f := f) (F := F) F
    (fun k => ((by fun_prop : Continuous fun u : ℝ => 8 / π *
      Real.sin ((((k + 1) * N : ℕ) : ℝ) * u) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 - 1)).measurable.div
        Real.continuous_sin.measurable).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn k t ht)])
    (Eventually.of_forall fun t _ => (hlim t).summable)
    (by rw [htsum]; exact hfint)
    (Eventually.of_forall fun t _ => hlim t)
  have hint : ∀ k, ∫ u in (0 : ℝ)..π / 2, F k u =
      8 / π / (4 * ((k : ℝ) + 1) ^ 2 - 1) * hprime ((k + 1) * N) := fun k => by
    rw [← integral_sin_sq_div_sin, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [F]
    ring
  simp only [hint] at hDC
  rw [lebesgueConst_eq_half]
  convert hDC.mul_left (2 / π) using 1
  funext k
  have := hpos k
  field_simp
  ring

/-- `H′` is monotone. -/
theorem hprime_mono {M M' : ℕ} (h : M ≤ M') : hprime M ≤ hprime M' :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h) fun _ _ _ => by positivity

theorem hprime_strictMono : StrictMono hprime := fun M M' h => by
  calc hprime M < hprime M + 1 / (2 * (M : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
    _ = hprime (M + 1) := by rw [hprime, hprime, sum_range_succ]
    _ ≤ hprime M' := hprime_mono h

/-- **DLMF §3.11(ii)**: "`Lₙ` is a monotonically increasing function of `n`" (strictly). -/
theorem dlmf_3_11_ii_lebesgue_strictMono : StrictMono lebesgueConst := fun n n' h => by
  have hpos : ∀ k : ℕ, 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := fun k => by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hc : 0 < 16 / π ^ 2 := by positivity
  refine hasSum_lt (i := 0) (fun k => ?_) ?_ (dlmf_3_11_ii_szego n) (dlmf_3_11_ii_szego n')
  · have := hprime_mono (M := (k + 1) * (2 * n + 1)) (M' := (k + 1) * (2 * n' + 1))
      (Nat.mul_le_mul_left _ (by omega))
    have := hpos k
    gcongr
  · have := hprime_strictMono (show (0 + 1) * (2 * n + 1) < (0 + 1) * (2 * n' + 1) by omega)
    have := hpos 0
    gcongr

end Azurite.DLMF
