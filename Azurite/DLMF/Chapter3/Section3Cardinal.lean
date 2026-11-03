/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.PSeries

/-!
# DLMF §3.3(vi): the cardinal function

* 3.3.44: `sincS` (Mathlib's `Real.sinc`, value `1` at the removable singularity `x = kh`),
  `dlmf_3_3_44` (DLMF's formula for `x ≠ kh`), `sincS_node` (`S(k, h)(jh) = δ_{j,k}`),
  `abs_sincS_le` (`|S(k, h)(x)| ≤ (2|x|/h + 3)/(1 + |k|)`).
* 3.3.43: `cardinalFn` (the series as a `tsum`), `cardinal_node` (`C(f, h)(jh) = f(jh)` for every
  `f`), `cardinal_summable` (absolute convergence at every `x` when
  `∑ |f(kh)|/(1 + |k|) < ∞`).
* Erratum: DLMF defines `C(f, h)` for every bounded `f`, but the series need not converge. For the
  bounded `cardinalCounter` (`f(kh) = (−1)^k` for `k ≥ 0`, `0` for `k < 0`) the terms at
  `x = h/2` are `2/(π(1 − 2k))` (`cardinalCounter_term`): the series is not summable
  (`cardinal_not_summable`) and its symmetric partial sums tend to `−∞`
  (`cardinal_partial_sums_atBot`).

The pointers to Hermite, trigonometric, spline, rational, Chebyshev and bivariate interpolation
are references only.
-/

open Real Filter Topology Finset

namespace Azurite.DLMF

/-! ### The Sinc function 3.3.44 -/

/-- **DLMF 3.3.44**: the Sinc function `S(k, h)(x) = sin(π(x − kh)/h)/(π(x − kh)/h)`, with the
removable singularity at `x = kh` filled in (value `1`, via Mathlib's `Real.sinc`). -/
noncomputable def sincS (h : ℝ) (k : ℤ) (x : ℝ) : ℝ := sinc (π * (x - k * h) / h)

/-- **DLMF 3.3.44** for `x ≠ kh`. -/
theorem dlmf_3_3_44 {h : ℝ} (hh : h ≠ 0) (k : ℤ) {x : ℝ} (hx : x ≠ k * h) :
    sincS h k x = sin (π * (x - k * h) / h) / (π * (x - k * h) / h) :=
  sinc_of_ne_zero (div_ne_zero (mul_ne_zero pi_ne_zero (sub_ne_zero.mpr hx)) hh)

/-- `S(k, h)(jh) = δ_{j,k}`. -/
theorem sincS_node {h : ℝ} (hh : h ≠ 0) (k j : ℤ) :
    sincS h k (j * h) = if j = k then 1 else 0 := by
  rw [sincS, show π * (j * h - k * h) / h = ((j - k : ℤ) : ℝ) * π by push_cast; field_simp]
  split_ifs with hjk
  · rw [hjk, sub_self, Int.cast_zero, zero_mul, sinc_zero]
  · rw [sinc_of_ne_zero (mul_ne_zero (by exact_mod_cast sub_ne_zero.mpr hjk) pi_ne_zero),
      sin_int_mul_pi, zero_div]

/-- `|S(k, h)(x)| ≤ (2|x|/h + 3)/(1 + |k|)`. -/
theorem abs_sincS_le {h : ℝ} (hh : 0 < h) (k : ℤ) (x : ℝ) :
    |sincS h k x| ≤ (2 * |x| / h + 3) / (1 + |(k : ℝ)|) := by
  have hK : 0 < 1 + |(k : ℝ)| := by positivity
  have ha : 0 ≤ |x| / h := by positivity
  rw [le_div_iff₀ hK, show 2 * |x| / h = 2 * (|x| / h) by ring]
  by_cases hk : |(k : ℝ)| < 2 * (|x| / h) + 2
  · have := abs_sinc_le_one (π * (x - k * h) / h)
    rw [sincS]
    nlinarith [abs_nonneg (sinc (π * (x - k * h) / h))]
  · push Not at hk
    set y := π * (x - k * h) / h
    have hy : y = π * (x / h - k) := by simp only [y]; field_simp
    have hxh : |x / h| = |x| / h := by rw [abs_div, abs_of_pos hh]
    have h1 : |(k : ℝ)| - |x| / h ≤ |x / h - k| := by
      rw [← hxh, abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    have hyabs : π * ((1 + |(k : ℝ)|) / 2) ≤ |y| := by
      rw [hy, abs_mul, abs_of_pos pi_pos]
      exact mul_le_mul_of_nonneg_left (by linarith) pi_pos.le
    have hy0 : 0 < |y| := lt_of_lt_of_le (by positivity) hyabs
    have hs : |sinc y| ≤ 1 / |y| := by
      rw [sinc_of_ne_zero (abs_pos.mp hy0), abs_div, div_le_div_iff_of_pos_right hy0]
      exact abs_sin_le_one y
    rw [sincS]
    calc |sinc y| * (1 + |(k : ℝ)|) ≤ 1 / |y| * (1 + |(k : ℝ)|) :=
          mul_le_mul_of_nonneg_right hs hK.le
      _ ≤ 1 / (π * ((1 + |(k : ℝ)|) / 2)) * (1 + |(k : ℝ)|) :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) hyabs) hK.le
      _ = 2 / π := by field_simp
      _ ≤ 2 * (|x| / h) + 3 := by
          have := two_le_pi
          rw [div_le_iff₀ pi_pos]; nlinarith

/-! ### The cardinal function 3.3.43 -/

/-- **DLMF 3.3.43**: the cardinal function `C(f, h)(x) = ∑_{k=−∞}^{∞} f(kh) S(k, h)(x)` (as a
`tsum`; see `cardinal_summable` for convergence and `cardinal_not_summable` for the erratum). -/
noncomputable def cardinalFn (f : ℝ → ℝ) (h x : ℝ) : ℝ := ∑' k : ℤ, f (k * h) * sincS h k x

/-- The cardinal function interpolates: `C(f, h)(jh) = f(jh)` (the series has one nonzero term). -/
theorem cardinal_node (f : ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (j : ℤ) :
    cardinalFn f h (j * h) = f (j * h) := by
  rw [cardinalFn, tsum_eq_single j fun k hk => by simp [sincS_node hh, Ne.symm hk]]
  simp [sincS_node hh]

/-- The series 3.3.43 converges absolutely at every `x` when
`∑_k |f(kh)|/(1 + |k|) < ∞` (e.g. `f(x) = O(|x|^{−ε})`). -/
theorem cardinal_summable (f : ℝ → ℝ) {h : ℝ} (hh : 0 < h)
    (hf : Summable fun k : ℤ => |f (k * h)| / (1 + |(k : ℝ)|)) (x : ℝ) :
    Summable fun k : ℤ => f (k * h) * sincS h k x := by
  refine Summable.of_norm_bounded ((hf.mul_left (2 * |x| / h + 3))) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |f (k * h)| * |sincS h k x| ≤ |f (k * h)| * ((2 * |x| / h + 3) / (1 + |(k : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (abs_sincS_le hh k x) (abs_nonneg _)
    _ = (2 * |x| / h + 3) * (|f (k * h)| / (1 + |(k : ℝ)|)) := by ring

/-! ### Erratum: boundedness of `f` does not suffice -/

/-- The bounded function `f(x) = cos(πx/h)` for `x ≥ 0`, `0` for `x < 0` (`f(kh) = (−1)^k` for
`k ≥ 0`). -/
noncomputable def cardinalCounter (h x : ℝ) : ℝ := if 0 ≤ x then cos (π * x / h) else 0

theorem cardinalCounter_bounded (h x : ℝ) : |cardinalCounter h x| ≤ 1 := by
  unfold cardinalCounter; split_ifs
  · exact abs_cos_le_one _
  · simp

/-- The terms of 3.3.43 for `cardinalCounter` at `x = h/2`: `2/(π(1 − 2k))` for `k ≥ 0`. -/
theorem cardinalCounter_term {h : ℝ} (hh : 0 < h) (k : ℤ) :
    cardinalCounter h (k * h) * sincS h k (h / 2) =
      if 0 ≤ k then 2 / (π * (1 - 2 * k)) else 0 := by
  unfold cardinalCounter
  by_cases hk : 0 ≤ k
  · have hkh : (0 : ℝ) ≤ k * h := mul_nonneg (by exact_mod_cast hk) hh.le
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have h12 : (1 : ℝ) - 2 * n ≠ 0 := by
      intro h0
      have : (2 * n : ℝ) = 1 := by linarith
      have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast this
      omega
    simp only [hkh, hk, ↓reduceIte]
    rw [sincS,
      show π * ((n : ℤ) * h) / h = (n : ℝ) * π by push_cast; field_simp,
      show π * (h / 2 - ((n : ℤ) : ℝ) * h) / h = π / 2 - (n : ℝ) * π by push_cast; field_simp,
      sinc_of_ne_zero (by
        rw [show π / 2 - (n : ℝ) * π = π * (1 - 2 * n) / 2 by ring]
        exact div_ne_zero (mul_ne_zero pi_ne_zero h12) two_ne_zero),
      sin_pi_div_two_sub, cos_nat_mul_pi]
    push_cast
    rw [show π / 2 - (n : ℝ) * π = π * (1 - 2 * n) / 2 by ring]
    have hp : π * (1 - 2 * (n : ℝ)) ≠ 0 := mul_ne_zero pi_ne_zero h12
    field_simp
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  · have hkh : ¬ (0 : ℝ) ≤ k * h := by
      push Not; exact mul_neg_of_neg_of_pos (by exact_mod_cast (not_le.mp hk)) hh
    simp only [hkh, hk, ↓reduceIte, zero_mul]

/-- **Erratum to 3.3.43**: for the bounded function `cardinalCounter`, the series 3.3.43 at
`x = h/2` is not summable. -/
theorem cardinal_not_summable {h : ℝ} (hh : 0 < h) :
    ¬ Summable fun k : ℤ => cardinalCounter h (k * h) * sincS h k (h / 2) := by
  intro hs
  have hn := hs.comp_injective (Nat.cast_injective (R := ℤ))
  simp only [Function.comp_def, cardinalCounter_term hh, Nat.cast_nonneg, ↓reduceIte] at hn
  have hn' := ((summable_nat_add_iff 1).mpr hn).neg.mul_left π
  apply Real.not_summable_one_div_natCast
  refine (summable_nat_add_iff 1).mp (Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) hn')
  push_cast
  have hp := pi_pos
  rw [show π * -(2 / (π * (1 - 2 * ((n : ℝ) + 1)))) = 2 / (2 * n + 1) by
    have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    rw [show (1 : ℝ) - 2 * ((n : ℝ) + 1) = -(2 * n + 1) by ring]
    field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Erratum to 3.3.43**, in the sense of symmetric partial sums: `∑_{k=−N}^{N}` of the series
at `x = h/2` tends to `−∞`. -/
theorem cardinal_partial_sums_atBot {h : ℝ} (hh : 0 < h) :
    Tendsto (fun N : ℕ => ∑ k ∈ Icc (-(N : ℤ)) N,
      cardinalCounter h (k * h) * sincS h k (h / 2)) atTop atBot := by
  simp only [cardinalCounter_term hh]
  set S := fun N : ℕ => ∑ k ∈ Icc (-(N : ℤ)) N, (if 0 ≤ k then 2 / (π * (1 - 2 * k)) else 0 : ℝ)
  have hp := pi_pos
  have hstep : ∀ N : ℕ, S (N + 1) = S N + 2 / (π * (1 - 2 * ((N : ℝ) + 1))) := fun N => by
    have hI : Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Icc (-(N : ℤ)) N)) := by
      ext m; simp only [mem_Icc, mem_insert]; push_cast; omega
    simp only [S]
    rw [hI, sum_insert (by simp; omega), sum_insert (by simp)]
    simp only [show ¬ (0 : ℤ) ≤ -((N : ℤ) + 1) by omega, show (0 : ℤ) ≤ (N : ℤ) + 1 by omega,
      ↓reduceIte]
    push_cast; ring
  have hbound : ∀ N : ℕ, S N ≤ 2 / π - (∑ i ∈ range N, (1 / ((i : ℝ) + 1))) / π := by
    intro N
    induction N with
    | zero =>
      simp [S]
    | succ N ih =>
      rw [hstep, sum_range_succ]
      have : 2 / (π * (1 - 2 * ((N : ℝ) + 1))) ≤ -(1 / ((N : ℝ) + 1)) / π := by
        rw [show (1 : ℝ) - 2 * ((N : ℝ) + 1) = -(2 * N + 1) by ring, mul_neg, div_neg,
          neg_div, neg_le_neg_iff, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc S N + 2 / (π * (1 - 2 * ((N : ℝ) + 1)))
          ≤ 2 / π - (∑ i ∈ range N, (1 / ((i : ℝ) + 1))) / π + -(1 / ((N : ℝ) + 1)) / π :=
            add_le_add ih this
        _ = _ := by ring
  refine tendsto_atBot_mono hbound ?_
  have hH := (Real.tendsto_sum_range_one_div_nat_succ_atTop.atTop_div_const pi_pos)
  simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left _ (2 / π)
    (tendsto_neg_atTop_atBot.comp hH)

end Azurite.DLMF
