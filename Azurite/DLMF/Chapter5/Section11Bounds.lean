/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Psi
import Azurite.DLMF.Chapter5.Section11Gstar
import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF §5.11(ii): error bounds for Stirling's series

Formalization of <https://dlmf.nist.gov/5.11#ii>: "If the sums in the expansions (5.11.1) and
(5.11.2) are terminated at `k = n − 1` and `z` is real and positive, then the remainder terms are
bounded in magnitude by the first neglected terms and have the same sign. If `z` is complex, then
the remainder terms are bounded in magnitude by `sec^{2n}(½ ph z)` for (5.11.1), and
`sec^{2n+1}(½ ph z)` for (5.11.2), times the first neglected terms."

With `D(t) = B̃_{2n}(t) − B_{2n}` the remainders are (`stirlingSeriesRem_eq`, `psiRem_eq`)
`−(1/2n) ∫₀^∞ D(t)/(z + t)^{2n} dt` and `∫₀^∞ D(t)/(z + t)^{2n+1} dt`. By the Fourier series of
the Bernoulli polynomials, `(−1)ⁿ D ≥ 0` (`bernoulliFun_sub_sign`), so for `z > 0` each remainder
has the sign of its first neglected term; the remainders after `n − 1` and `n` terms have opposite
signs and differ by that term, which gives the bound (`dlmf_5_11_ii_real`,
`dlmf_5_11_ii_psi_real`). For complex `z`, `|z + t| ≥ (|z| + t) cos(½ ph z)` reduces the bound to
the real one at `|z|` (`dlmf_5_11_ii_complex`, `dlmf_5_11_ii_psi_complex`).

5.11.10 defines the remainder `R_K(z)` of 5.11.3 (`stirlingR`, `dlmf_5_11_10`). The bound 5.11.11
(Boyd 1994) is in `Section11BoydBound.lean` (`sec` branch) and `Section11BoydMain.lean`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The sign of `B_{2n}(x) − B_{2n}` -/

theorem neg_one_pow_mul_bernoulli_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ) := by
  have h := hasSum_zeta_nat (k := n) (by omega)
  have hpos : 0 < ∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n) := by
    refine lt_of_lt_of_le ?_ (h.summable.sum_le_tsum (Finset.range 2) fun k _ => by positivity)
    simp [Finset.sum_range_succ, zero_pow (by omega : 2 * n ≠ 0)]
  rw [h.tsum_eq] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) / (2 * n)! := by positivity
  have : (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ) * ((2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) /
      (2 * n)!) > 0 := by
    have e : (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) * (bernoulli (2 * n) : ℝ) /
        (2 * n)! = (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ) * ((2 : ℝ) ^ (2 * n - 1) *
          π ^ (2 * n) / (2 * n)!) := by ring
    linarith [e ▸ hpos]
  exact pos_of_mul_pos_left this h2.le

/-- `(−1)ⁿ (B_{2n}(x) − B_{2n}) ≥ 0` on `[0, 1]`. -/
theorem bernoulliFun_sub_sign {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ (-1 : ℝ) ^ n * (bernoulliFun (2 * n) x - bernoulli (2 * n)) := by
  have hx' := hasSum_one_div_nat_pow_mul_cos (k := n) (by omega) hx
  have h0 := hasSum_one_div_nat_pow_mul_cos (k := n) (by omega) (left_mem_Icc.mpr zero_le_one)
  have hd := hx'.sub h0
  have hle : ∑' k : ℕ, (1 / (k : ℝ) ^ (2 * n) * Real.cos (2 * π * k * x) -
      1 / (k : ℝ) ^ (2 * n) * Real.cos (2 * π * k * 0)) ≤ 0 :=
    tsum_nonpos fun k => by
      rw [mul_zero, Real.cos_zero, mul_one, ← mul_sub_one]
      have hc := Real.cos_le_one (2 * π * k * x)
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  rw [hd.tsum_eq] at hle
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval x =
      bernoulliFun (2 * n) x := rfl
  have hb0 : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval 0 =
      bernoulli (2 * n) := bernoulliFun_eval_zero _
  rw [hb, hb0, ← mul_sub] at hle
  have hc : 0 < (2 * π) ^ (2 * n) / 2 / (2 * n)! := by positivity
  have : (-1 : ℝ) ^ (n + 1) * (bernoulliFun (2 * n) x - bernoulli (2 * n)) ≤ 0 := by
    have e : (-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)! *
        (bernoulliFun (2 * n) x - bernoulli (2 * n)) = (2 * π) ^ (2 * n) / 2 / (2 * n)! *
          ((-1 : ℝ) ^ (n + 1) * (bernoulliFun (2 * n) x - bernoulli (2 * n))) := by ring
    rw [e] at hle
    exact nonpos_of_mul_nonpos_right hle hc
  rw [pow_succ] at this
  linarith

/-! ### The remainders as integrals -/

/-- `∫₀^∞ dt/(z + t)^m = 1/((m − 1) z^{m−1})` on the slit plane, `m ≥ 2`. -/
theorem integral_inv_add_pow_complex {z : ℂ} (hz : z ∈ slitPlane) {m : ℕ} (hm : 2 ≤ m) :
    ∫ t in Ioi (0 : ℝ), (1 : ℂ) / (z + t) ^ m = 1 / (((m : ℂ) - 1) * z ^ (m - 1)) := by
  have hne : ∀ t : ℝ, 0 ≤ t → z + t ≠ 0 := fun t ht =>
    slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have hm1 : ((m : ℂ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    intro h; have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨hδ, hδπ, harg⟩ := slitPlane_sector hz
  have hint : IntegrableOn (fun t : ℝ => (1 : ℂ) / (z + t) ^ m) (Ioi 0) := by
    have := (integrableOn_div_add_pow (f := fun _ => 1) measurable_const (C := 1)
      (fun _ => by norm_num) (slitPlane_ne_zero hz) hδ hδπ harg hm).1
    simpa using this
  set F : ℝ → ℂ := fun t => -(1 / (((m : ℂ) - 1) * (z + t) ^ (m - 1))) with hF
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F ((1 : ℂ) / (z + t) ^ m) t := by
    intro t ht
    have ht0 := hne t (le_of_lt ht)
    have h1 : HasDerivAt (fun s : ℝ => z + (s : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_add z
    have h2 := ((h1.pow (m - 1)).const_mul ((m : ℂ) - 1)).inv
      (mul_ne_zero hm1 (pow_ne_zero _ ht0))
    have h3 := h2.neg
    convert h3 using 1
    · funext s; simp [hF]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      rw [show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
      simp only [Pi.pow_apply]
      push_cast
      have hk : (k : ℂ) + 1 ≠ 0 := by norm_cast
      rw [show (k : ℂ) + 2 - 1 = k + 1 by ring]
      field_simp
      ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hcob : Tendsto (fun t : ℝ => z + t) atTop (Bornology.cobounded ℂ) := by
      refine tendsto_norm_atTop_iff_cobounded.mp (tendsto_atTop_mono (fun t => ?_)
        (tendsto_atTop_add_const_right _ (-‖z‖) tendsto_id))
      have := norm_sub_norm_le ((t : ℂ)) (-z)
      simp only [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs] at this
      rw [add_comm] at this
      simp only [id]
      linarith [le_abs_self t]
    have hp : Tendsto (fun t : ℝ => (z + t) ^ (m - 1)) atTop (Bornology.cobounded ℂ) := by
      refine tendsto_norm_atTop_iff_cobounded.mp ?_
      simp only [norm_pow]
      exact (tendsto_pow_atTop (by omega)).comp (tendsto_norm_cobounded_atTop.comp hcob)
    have := ((tendsto_inv₀_cobounded.comp hp).const_mul (-(1 / ((m : ℂ) - 1))))
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp only [hF, Function.comp]
    field_simp
  have hc : ContinuousWithinAt F (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt ?_
    have h0 := hne 0 le_rfl
    exact (((continuous_const.add continuous_ofReal).pow (m - 1)).continuousAt.const_mul _
      |>.inv₀ (by simpa using mul_ne_zero hm1 (pow_ne_zero _ h0))).neg |>.congr
        (Eventually.of_forall fun s => by simp [hF, one_div])
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hderiv hint hlim]
  simp [hF]

/-- `D(t) = B̃_{2n}(t) − B_{2n}`. -/
noncomputable def bernD (n : ℕ) (t : ℝ) : ℝ := periodicBernoulli (2 * n) t - bernoulli (2 * n)

theorem bernD_sign {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : 0 ≤ (-1 : ℝ) ^ n * bernD n t :=
  bernoulliFun_sub_sign hn ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem measurable_bernD (n : ℕ) : Measurable (bernD n) :=
  (measurable_periodicBernoulli _).sub_const _

theorem bernD_bound (n : ℕ) : ∃ C, ∀ t, |bernD n t| ≤ C := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound (2 * n)
  exact ⟨C + |(bernoulli (2 * n) : ℝ)|, fun t =>
    (abs_sub _ _).trans (add_le_add (hC t) le_rfl)⟩

/-- The remainder of Stirling's series 5.11.1 after the terms `k = 1, …, n − 1`. -/
noncomputable def stirlingSeriesRem (n : ℕ) (z : ℂ) : ℂ :=
  stirlingJ z - ∑ s ∈ Finset.range (2 * n - 1), stirlingSeriesCoeff s * z ^ (-(s : ℤ))

/-- The first neglected term `B_{2n}/(2n(2n − 1) z^{2n−1})` of 5.11.1. -/
noncomputable def stirlingFirst (n : ℕ) (z : ℂ) : ℂ :=
  stirlingSeriesCoeff (2 * n - 1) * z ^ (-((2 * n - 1 : ℕ) : ℤ))

theorem stirlingFirst_eq {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    stirlingFirst n z = (bernoulli (2 * n) : ℂ) / (2 * n * (2 * n - 1) * z ^ (2 * n - 1)) := by
  rw [stirlingFirst, stirlingSeriesCoeff_odd hn, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
    div_div]

theorem integral_div_add_pow_split (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) {m : ℕ}
    (hm : 2 ≤ m) :
    ∫ t in Ioi (0 : ℝ), (bernD n t : ℂ) / (z + t) ^ m =
      (∫ t in Ioi (0 : ℝ), (periodicBernoulli (2 * n) t : ℂ) / (z + t) ^ m) -
        (bernoulli (2 * n) : ℂ) * (1 / (((m : ℂ) - 1) * z ^ (m - 1))) := by
  obtain ⟨hδ, hδπ, harg⟩ := slitPlane_sector hz
  obtain ⟨C, hC⟩ := periodicBernoulli_bound (2 * n)
  have h1 := (integrableOn_div_add_pow (measurable_periodicBernoulli (2 * n)) (C := C) hC
    (slitPlane_ne_zero hz) hδ hδπ harg hm).1
  have h2 := (integrableOn_div_add_pow (f := fun _ => (bernoulli (2 * n) : ℝ)) measurable_const
    (C := |(bernoulli (2 * n) : ℝ)|) (fun _ => le_rfl) (slitPlane_ne_zero hz) hδ hδπ harg hm).1
  rw [← integral_inv_add_pow_complex hz hm, ← integral_const_mul, ← integral_sub h1]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [bernD]
    push_cast
    ring
  · refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    push_cast; ring

/-- `R_n(z) = −(1/2n) ∫₀^∞ (B̃_{2n}(t) − B_{2n})/(z + t)^{2n} dt`. -/
theorem stirlingSeriesRem_eq {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingSeriesRem n z =
      -(1 / (2 * n : ℂ)) * ∫ t in Ioi (0 : ℝ), (bernD n t : ℂ) / (z + t) ^ (2 * n) := by
  have hz0 := slitPlane_ne_zero hz
  have h := stirlingJ_sub_sum hz (n := 2 * n - 1) (by omega)
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at h
  rw [stirlingSeriesRem, h, integral_div_add_pow_split n hz (by omega), stirlingSeriesCoeff_odd hn,
    stirlingK]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h2n : (2 * (n : ℂ) - 1) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [zpow_neg, zpow_natCast, Nat.cast_sub (by omega : 1 ≤ 2 * n)]
  push_cast
  field_simp
  ring

/-- The remainder of 5.11.2 (`ψ(z) − ln z + 1/(2z) + ∑_{k=1}^{n−1} B_{2k}/(2k z^{2k})`). -/
noncomputable def psiRem (n : ℕ) (z : ℂ) : ℂ :=
  digamma z - Complex.log z - ∑ s ∈ Finset.range (2 * n), psiCoeff s * z ^ (-(s : ℤ))

/-- The first neglected term `−B_{2n}/(2n z^{2n})` of 5.11.2. -/
noncomputable def psiFirst (n : ℕ) (z : ℂ) : ℂ := psiCoeff (2 * n) * z ^ (-((2 * n : ℕ) : ℤ))

theorem psiFirst_eq {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    psiFirst n z = -(bernoulli (2 * n) : ℂ) / (2 * n * z ^ (2 * n)) := by
  rw [psiFirst, psiCoeff_even hn, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_div]

/-- `ψ`-remainder `= ∫₀^∞ (B̃_{2n}(t) − B_{2n})/(z + t)^{2n+1} dt`. -/
theorem psiRem_eq {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    psiRem n z = ∫ t in Ioi (0 : ℝ), (bernD n t : ℂ) / (z + t) ^ (2 * n + 1) := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 2 := ⟨2 * n - 2, by omega⟩
  have hψ := digamma_eq_log_sub_add_deriv hz
  have hd := deriv_stirlingJ_eq hz m
  have hs := sum_psiCoeff z m
  rw [show m + 3 = 2 * n + 1 by omega, Finset.sum_range_succ] at hs
  rw [psiRem, integral_div_add_pow_split n hz (by omega), hψ, hd]
  have hL : stirlingL m z = ∫ t in Ioi (0 : ℝ), (periodicBernoulli (2 * n) t : ℂ) /
      (z + t) ^ (2 * n + 1) := by
    rw [stirlingL, hm, show m + 3 = m + 2 + 1 by omega]
  rw [hL, show 2 * n + 1 - 1 = 2 * n by omega, psiCoeff_even hn] at *
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [zpow_neg, zpow_natCast] at hs
  push_cast at hs ⊢
  linear_combination (-1 : ℂ) * hs

/-! ### Real `z`: same sign, bounded by the first neglected term -/

theorem ofReal_mem_slitPlane' {x : ℝ} (hx : 0 < x) : (x : ℂ) ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hx))

/-- `∫₀^∞ (−1)ⁿD(t)/(x + t)^m dt`, a nonnegative real number. -/
noncomputable def bernDIntegral (n m : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (-1 : ℝ) ^ n * bernD n t / (x + t) ^ m

theorem bernDIntegral_nonneg {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ bernDIntegral n m x :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    div_nonneg (bernD_sign hn t) (pow_nonneg (by linarith [mem_Ioi.mp ht]) _)

theorem integral_bernD_ofReal (n m : ℕ) (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), (bernD n t : ℂ) / ((x : ℂ) + t) ^ m =
      (((-1 : ℝ) ^ n * bernDIntegral n m x : ℝ) : ℂ) := by
  rw [bernDIntegral, ← integral_const_mul, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have h2 : ((-1 : ℝ) ^ n) * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  push_cast
  rw [show ((-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * (bernD n t : ℂ) / ((x : ℂ) + t) ^ m)) =
    ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * ((bernD n t : ℂ) / ((x : ℂ) + t) ^ m) by ring]
  rw [← mul_pow]; norm_num

theorem stirlingSeriesRem_ofReal {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    stirlingSeriesRem n x =
      (((-1 : ℝ) ^ (n + 1) / (2 * n) * bernDIntegral n (2 * n) x : ℝ) : ℂ) := by
  rw [stirlingSeriesRem_eq hn (ofReal_mem_slitPlane' hx), integral_bernD_ofReal n _ x]
  push_cast
  ring

theorem psiRem_ofReal {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    psiRem n x = (((-1 : ℝ) ^ n * bernDIntegral n (2 * n + 1) x : ℝ) : ℂ) := by
  rw [psiRem_eq hn (ofReal_mem_slitPlane' hx), integral_bernD_ofReal n _ x]

theorem stirlingSeriesRem_succ {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    stirlingSeriesRem n z = stirlingFirst n z + stirlingSeriesRem (n + 1) z := by
  rw [stirlingSeriesRem, stirlingSeriesRem, stirlingFirst,
    show 2 * (n + 1) - 1 = 2 * n - 1 + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ, show 2 * n - 1 + 1 = 2 * n by omega,
    stirlingSeriesCoeff_even hn]
  ring

theorem psiRem_succ {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    psiRem n z = psiFirst n z + psiRem (n + 1) z := by
  rw [psiRem, psiRem, psiFirst, show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ, psiCoeff_odd hn]
  ring

theorem stirlingFirst_ofReal {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    stirlingFirst n x = (((bernoulli (2 * n) : ℝ) / (2 * n * (2 * n - 1) * x ^ (2 * n - 1)) :
      ℝ) : ℂ) := by
  rw [stirlingFirst_eq hn]; push_cast; ring

theorem psiFirst_ofReal {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    psiFirst n x = ((-(bernoulli (2 * n) : ℝ) / (2 * n * x ^ (2 * n)) : ℝ) : ℂ) := by
  rw [psiFirst_eq hn]; push_cast; ring

/-- The alternating-remainder argument: if `r = τ + r'` with `εr ≥ 0`, `ετ ≥ 0`, `εr' ≤ 0` and
`ε = ±1`, then `|r| ≤ |τ|` and `rτ ≥ 0`. -/
theorem abs_le_of_alternating {r τ r' ε : ℝ} (hε : ε = 1 ∨ ε = -1) (h : r = τ + r')
    (hr : 0 ≤ ε * r) (hτ : 0 ≤ ε * τ) (hr' : ε * r' ≤ 0) : |r| ≤ |τ| ∧ 0 ≤ r * τ := by
  rcases hε with rfl | rfl
  · simp only [one_mul] at hr hτ hr'
    exact ⟨by rw [abs_of_nonneg hr, abs_of_nonneg hτ]; linarith, mul_nonneg hr hτ⟩
  · simp only [neg_one_mul, neg_nonneg, neg_nonpos] at hr hτ hr'
    exact ⟨by rw [abs_of_nonpos hr, abs_of_nonpos hτ]; linarith,
      mul_nonneg_of_nonpos_of_nonpos hr hτ⟩

theorem neg_one_pow_eq_or' (k : ℕ) : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := neg_one_pow_eq_or ℝ k

/-- **DLMF §5.11(ii)**, 5.11.1 for `z > 0`: the remainder after `k = n − 1` is real, has the sign
of the first neglected term `B_{2n}/(2n(2n − 1)z^{2n−1})` and is at most that term in
magnitude. -/
theorem dlmf_5_11_ii_real {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ r τ : ℝ, stirlingSeriesRem n x = r ∧ stirlingFirst n x = τ ∧ |r| ≤ |τ| ∧ 0 ≤ r * τ := by
  set ε : ℝ := (-1) ^ (n + 1)
  have hεε : ε * ε = 1 := by simp only [ε]; rw [← mul_pow]; norm_num
  refine ⟨_, _, stirlingSeriesRem_ofReal hn hx, stirlingFirst_ofReal hn x, ?_⟩
  have hrec := stirlingSeriesRem_succ hn (x : ℂ)
  rw [stirlingSeriesRem_ofReal hn hx, stirlingFirst_ofReal hn x,
    stirlingSeriesRem_ofReal (by omega) hx,
    ← ofReal_add, ofReal_inj] at hrec
  have hI := bernDIntegral_nonneg hn (2 * n) hx
  have hI' := bernDIntegral_nonneg (n := n + 1) (by omega) (2 * (n + 1)) hx
  have hB := neg_one_pow_mul_bernoulli_pos hn
  refine abs_le_of_alternating (ε := ε) (neg_one_pow_eq_or' _) hrec ?_ ?_ ?_
  · rw [show ε * ((-1 : ℝ) ^ (n + 1) / (2 * n) * bernDIntegral n (2 * n) x) =
      (ε * ε) / (2 * n) * bernDIntegral n (2 * n) x by ring, hεε]
    positivity
  · rw [show ε * ((bernoulli (2 * n) : ℝ) / (2 * n * (2 * n - 1) * x ^ (2 * n - 1))) =
      ((-1 : ℝ) ^ (n + 1) * bernoulli (2 * n)) / (2 * n * (2 * n - 1) * x ^ (2 * n - 1)) by
        simp only [ε]; ring]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < 2 * (n : ℝ) - 1 := by linarith
    positivity
  · rw [show ε * ((-1 : ℝ) ^ (n + 1 + 1) / (2 * (n + 1 : ℕ)) * bernDIntegral (n + 1)
        (2 * (n + 1)) x) = -((ε * ε) / (2 * (n + 1 : ℕ)) * bernDIntegral (n + 1) (2 * (n + 1)) x)
        by simp only [ε]; rw [pow_succ]; ring, hεε]
    have : 0 ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ)) * bernDIntegral (n + 1) (2 * (n + 1)) x := by
      positivity
    linarith

/-- **DLMF §5.11(ii)**, 5.11.2 for `z > 0`: same sign as, and at most, the first neglected term
`−B_{2n}/(2n z^{2n})`. -/
theorem dlmf_5_11_ii_psi_real {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ r τ : ℝ, psiRem n x = r ∧ psiFirst n x = τ ∧ |r| ≤ |τ| ∧ 0 ≤ r * τ := by
  set ε : ℝ := (-1) ^ n
  have hεε : ε * ε = 1 := by simp only [ε]; rw [← mul_pow]; norm_num
  refine ⟨_, _, psiRem_ofReal hn hx, psiFirst_ofReal hn x, ?_⟩
  have hrec := psiRem_succ hn (x : ℂ)
  rw [psiRem_ofReal hn hx, psiFirst_ofReal hn x, psiRem_ofReal (by omega) hx,
    ← ofReal_add, ofReal_inj] at hrec
  have hI := bernDIntegral_nonneg hn (2 * n + 1) hx
  have hI' := bernDIntegral_nonneg (n := n + 1) (by omega) (2 * (n + 1) + 1) hx
  have hB := neg_one_pow_mul_bernoulli_pos hn
  refine abs_le_of_alternating (ε := ε) (neg_one_pow_eq_or' _) hrec ?_ ?_ ?_
  · rw [show ε * ((-1 : ℝ) ^ n * bernDIntegral n (2 * n + 1) x) =
      (ε * ε) * bernDIntegral n (2 * n + 1) x by ring, hεε, one_mul]
    exact hI
  · rw [show ε * (-(bernoulli (2 * n) : ℝ) / (2 * n * x ^ (2 * n))) =
      ((-1 : ℝ) ^ (n + 1) * bernoulli (2 * n)) / (2 * n * x ^ (2 * n)) by
        simp only [ε]; rw [pow_succ]; ring]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  · rw [show ε * ((-1 : ℝ) ^ (n + 1) * bernDIntegral (n + 1) (2 * (n + 1) + 1) x) =
      -((ε * ε) * bernDIntegral (n + 1) (2 * (n + 1) + 1) x) by simp only [ε]; rw [pow_succ]; ring,
      hεε]
    linarith

/-! ### Complex `z`: the factor `sec^m(½ ph z)` -/

theorem cos_half_arg_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < Real.cos (arg z / 2) := by
  obtain ⟨h1, -, -⟩ := slitPlane_sector hz
  have := abs_lt.mp (show |arg z| < π by linarith)
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- `|∫₀^∞ D(t)/(z + t)^m dt| ≤ sec^m(½ ph z) ∫₀^∞ (−1)ⁿD(t)/(|z| + t)^m dt`. -/
theorem norm_integral_bernD_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) {m : ℕ}
    (hm : 2 ≤ m) :
    ‖∫ t in Ioi (0 : ℝ), (bernD n t : ℂ) / (z + t) ^ m‖ ≤
      (Real.cos (arg z / 2))⁻¹ ^ m * bernDIntegral n m ‖z‖ := by
  have hz0 := slitPlane_ne_zero hz
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set c := Real.cos (arg z / 2) with hcdef
  have hc := cos_half_arg_pos hz
  obtain ⟨hδ, hδπ, harg⟩ := slitPlane_sector hz
  have hge : ∀ t : ℝ, 0 ≤ t → c * (‖z‖ + t) ≤ ‖z + t‖ := fun t ht => by
    have h := norm_add_ofReal_ge hδ.le hδπ harg ht
    rwa [show (π - |arg z|) / 2 = π / 2 - |arg z| / 2 by ring, Real.sin_pi_div_two_sub,
      show |arg z| / 2 = |arg z / 2| by rw [abs_div, abs_two], Real.cos_abs] at h
  obtain ⟨C, hC⟩ := bernD_bound n
  have hint : IntegrableOn (fun t : ℝ => (-1 : ℝ) ^ n * bernD n t / (‖z‖ + t) ^ m) (Ioi 0) := by
    have h := (integrableOn_div_add_pow (f := fun t => (-1 : ℝ) ^ n * bernD n t)
      (measurable_const.mul (measurable_bernD n)) (C := C) (fun t => by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hC t)
      (z := (‖z‖ : ℂ)) (by exact_mod_cast hr.ne') (δ := π) Real.pi_pos le_rfl
      (by rw [Complex.arg_ofReal_of_nonneg hr.le]; simp) hm).1
    refine (h.re).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only
    rw [← ofReal_add, ← ofReal_pow, ← ofReal_div]
    exact RCLike.ofReal_re _
  rw [bernDIntegral, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ?_ (hint.const_mul _)
    measurableSet_Ioi fun t ht => ?_)
  · have h := (integrableOn_div_add_pow (measurable_bernD n) (C := C) hC hz0 hδ hδπ harg hm).1
    exact h.norm
  · have ht0 : 0 ≤ t := le_of_lt (mem_Ioi.mp ht)
    have hD := bernD_sign hn t
    have habs : |bernD n t| = (-1 : ℝ) ^ n * bernD n t := by
      rw [← abs_of_nonneg hD, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hzt := hge t ht0
    have hpos : 0 < c * (‖z‖ + t) := by positivity
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, habs,
      show c⁻¹ ^ m * ((-1 : ℝ) ^ n * bernD n t / (‖z‖ + t) ^ m) =
        (-1 : ℝ) ^ n * bernD n t / (c * (‖z‖ + t)) ^ m by
          rw [mul_pow, inv_pow]; field_simp]
    exact div_le_div_of_nonneg_left hD (pow_pos hpos m) (pow_le_pow_left₀ hpos.le hzt m)

theorem norm_stirlingFirst {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    ‖stirlingFirst n z‖ =
      |(bernoulli (2 * n) : ℝ)| / (2 * n * (2 * n - 1) * ‖z‖ ^ (2 * n - 1)) := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [stirlingFirst_eq hn, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_ratCast,
    show (2 * (n : ℂ) - 1) = ((2 * n - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Complex.norm_natCast, Real.norm_of_nonneg (by linarith)]
  norm_num

theorem norm_psiFirst {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    ‖psiFirst n z‖ = |(bernoulli (2 * n) : ℝ)| / (2 * n * ‖z‖ ^ (2 * n)) := by
  rw [psiFirst_eq hn, norm_div, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_ratCast,
    Complex.norm_natCast]
  norm_num

/-- **DLMF §5.11(ii)**, 5.11.1 for complex `z` (`|ph z| < π`): the remainder after `k = n − 1`
is at most `sec^{2n}(½ ph z)` times the first neglected term in magnitude. -/
theorem dlmf_5_11_ii_complex {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingSeriesRem n z‖ ≤ (Real.cos (arg z / 2))⁻¹ ^ (2 * n) * ‖stirlingFirst n z‖ := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hc := cos_half_arg_pos hz
  obtain ⟨r', τ, h1, h2, h3, -⟩ := dlmf_5_11_ii_real hn hr
  rw [stirlingSeriesRem_ofReal hn hr, ofReal_inj] at h1
  rw [stirlingFirst_ofReal hn, ofReal_inj] at h2
  have hI := bernDIntegral_nonneg hn (2 * n) hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : |r'| = bernDIntegral n (2 * n) ‖z‖ / (2 * n) := by
    rw [← h1, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity),
      abs_of_nonneg hI]; ring
  have hτ : |τ| = ‖stirlingFirst n z‖ := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < 2 * (n : ℝ) - 1 := by linarith
    have hden : 0 < 2 * (n : ℝ) * (2 * n - 1) * ‖z‖ ^ (2 * n - 1) := by positivity
    rw [← h2, norm_stirlingFirst hn, abs_div, abs_of_pos hden]
  rw [habs, hτ] at h3
  rw [stirlingSeriesRem_eq hn hz, norm_mul, norm_neg, norm_div, norm_one,
    show ‖(2 * (n : ℂ))‖ = 2 * n by
    rw [show (2 * (n : ℂ)) = ((2 * n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]]
  have hb := norm_integral_bernD_le hn hz (m := 2 * n) (by omega)
  calc 1 / (2 * n) * ‖∫ t in Ioi (0 : ℝ), (bernD n t : ℂ) / (z + t) ^ (2 * n)‖
      ≤ 1 / (2 * n) * ((Real.cos (arg z / 2))⁻¹ ^ (2 * n) * bernDIntegral n (2 * n) ‖z‖) := by
        gcongr
    _ = (Real.cos (arg z / 2))⁻¹ ^ (2 * n) * (bernDIntegral n (2 * n) ‖z‖ / (2 * n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (pow_nonneg (inv_nonneg.mpr hc.le) _)

/-- **DLMF §5.11(ii)**, 5.11.2 for complex `z` (`|ph z| < π`): the remainder after `k = n − 1`
is at most `sec^{2n+1}(½ ph z)` times the first neglected term in magnitude. -/
theorem dlmf_5_11_ii_psi_complex {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖psiRem n z‖ ≤ (Real.cos (arg z / 2))⁻¹ ^ (2 * n + 1) * ‖psiFirst n z‖ := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  obtain ⟨r', τ, h1, h2, h3, -⟩ := dlmf_5_11_ii_psi_real hn hr
  rw [psiRem_ofReal hn hr, ofReal_inj] at h1
  rw [psiFirst_ofReal hn, ofReal_inj] at h2
  have hI := bernDIntegral_nonneg hn (2 * n + 1) hr
  have habs : |r'| = bernDIntegral n (2 * n + 1) ‖z‖ := by
    rw [← h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hI]
  have hτ : |τ| = ‖psiFirst n z‖ := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : 0 < 2 * (n : ℝ) * ‖z‖ ^ (2 * n) := by positivity
    rw [← h2, norm_psiFirst hn, abs_div, abs_neg, abs_of_pos hden]
  rw [habs, hτ] at h3
  rw [psiRem_eq hn hz]
  refine (norm_integral_bernD_le hn hz (by omega)).trans ?_
  exact mul_le_mul_of_nonneg_left h3 (pow_nonneg (inv_nonneg.mpr (cos_half_arg_pos hz).le) _)

/-! ### 5.11.10 -/

/-- `R_K(z) = Γ*(z) − ∑_{k<K} gₖ/zᵏ`, the remainder of 5.11.3. -/
noncomputable def stirlingR (K : ℕ) (z : ℂ) : ℂ :=
  scaledGamma z - ∑ k ∈ Finset.range K, (BZ.stirlingCoeff k : ℂ) / z ^ k

/-- **DLMF 5.11.10**: `Γ(z) = e^{−z} z^z (2π/z)^{1/2} (∑_{k=0}^{K−1} gₖ/zᵏ + R_K(z))` on the slit
plane. -/
theorem dlmf_5_11_10 (K : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    Gamma z = cexp (-z) * z ^ z * (2 * π / z) ^ (1 / 2 : ℂ) *
      (∑ k ∈ Finset.range K, (BZ.stirlingCoeff k : ℂ) / z ^ k + stirlingR K z) := by
  rw [stirlingR, add_sub_cancel, dlmf_5_11_3_eq hz]

end Azurite.DLMF
