/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section19
import Azurite.DLMF.Chapter4.Section15
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# DLMF §4.19: the logarithmic series 4.19.7–4.19.9

With `u = (z/π)²`, `ln(sin z/z) = ∑ₖ ln(1 − u/k²)` (`logSinSum`). Expanding each logarithm and
summing over `k` by `ζ(2n)` gives 4.19.7 (`logSinSum_hasSum`). That this is the *principal*
logarithm comes from two facts: its exponential is Euler's product for `sin z/z`
(`exp_logSinSum`), and its imaginary part is below `π` in absolute value
(`abs_im_logSinSum_lt`, using `|arg(1 − u)| < π/2` for the first factor and
`|ln(1 + w)| ≤ (3/2)|w|` for the others).

* 4.19.7 (`|z| < π`): `dlmf_4_19_7`.
* 4.19.8 (`|z| < π/2`): `dlmf_4_19_8`. Here `cos z = (sin 2z/2z)/(sin z/z)`, and the branch is
  fixed by `|arg cos z| < π/2` (an integer multiple of `2πi` below `2π` in size is `0`).
* 4.19.9 (`|z| < π/2`): `dlmf_4_19_9`, as `ln(sin z/z) − ln cos z`.

The general term with index `n ≥ 1` is written with `n = m + 1`.
-/

open Set Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

/-- Row and column sums of an absolutely convergent double series. -/
theorem hasSum_rows_cols {f : ℕ → ℕ → ℂ} {g h : ℕ → ℂ}
    (hs : Summable fun p : ℕ × ℕ => ‖f p.1 p.2‖) (hg : ∀ n, HasSum (f n) (g n))
    (hh : ∀ m, HasSum (fun n => f n m) (h m)) :
    HasSum g (∑' p : ℕ × ℕ, f p.1 p.2) ∧ HasSum h (∑' p : ℕ × ℕ, f p.1 p.2) := by
  have hF : Summable fun p : ℕ × ℕ => f p.1 p.2 := hs.of_norm
  refine ⟨hF.hasSum.prod_fiberwise fun n => hg n, ?_⟩
  have h2 : HasSum ((fun p : ℕ × ℕ => f p.1 p.2) ∘ Equiv.prodComm ℕ ℕ)
      (∑' p : ℕ × ℕ, f p.1 p.2) := (Equiv.hasSum_iff _).mpr hF.hasSum
  exact h2.prod_fiberwise fun m => hh m

/-- The value `ζ(2m) = (−1)^{m+1} 2^{2m−1} π^{2m} B_{2m}/(2m)!`. -/
noncomputable def zetaEvenVal (m : ℕ) : ℝ :=
  (-1) ^ (m + 1) * 2 ^ (2 * m - 1) * π ^ (2 * m) * bernoulli (2 * m) / (2 * m)!

/-- `∑ₖ ln(1 − u/k²)` (`k ≥ 1`). -/
noncomputable def logSinSum (u : ℂ) : ℂ := ∑' k : ℕ, log (1 - u / ((k : ℂ) + 1) ^ 2)

theorem norm_div_succ_sq (u : ℂ) (k : ℕ) :
    ‖u / ((k : ℂ) + 1) ^ 2‖ = ‖u‖ / ((k : ℝ) + 1) ^ 2 := by
  rw [norm_div, norm_pow, show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  push_cast; ring

theorem norm_natCast_add_one (k : ℕ) : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
  rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

theorem one_le_succ_sq (k : ℕ) : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
  nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- The two expansions of `logSinSum u`, `|u| < 1`: over `k`, and as `−∑ ζ(2n) uⁿ/n`. -/
theorem logSinSum_hasSum {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun k : ℕ => log (1 - u / ((k : ℂ) + 1) ^ 2)) (logSinSum u) ∧
      HasSum (fun m : ℕ => -((zetaEvenVal (m + 1) : ℂ) * u ^ (m + 1) / ((m : ℂ) + 1)))
        (logSinSum u) := by
  have hv : ∀ k : ℕ, ‖-(u / ((k : ℂ) + 1) ^ 2)‖ < 1 := fun k => by
    rw [norm_neg, norm_div_succ_sq]
    exact (div_le_self (norm_nonneg _) (one_le_succ_sq k)).trans_lt hu
  set f : ℕ → ℕ → ℂ := fun k n => -((u / ((k : ℂ) + 1) ^ 2) ^ n / n) with hf
  have hg : ∀ k, HasSum (f k) (log (1 - u / ((k : ℂ) + 1) ^ 2)) := fun k => by
    have h := hasSum_taylorSeries_log (hv k)
    rw [← sub_eq_add_neg] at h
    convert h using 1
    funext n
    simp only [hf]
    rw [neg_pow]
    have : ((-1 : ℂ)) ^ (n + 1) * (-1) ^ n = -1 := by
      rw [← pow_add, show n + 1 + n = 2 * n + 1 by ring, pow_succ, pow_mul, neg_one_sq, one_pow,
        one_mul]
    linear_combination (-(u / ((k : ℂ) + 1) ^ 2) ^ n / n) * this
  set col : ℕ → ℂ := fun n => if n = 0 then 0 else -(((zetaEvenVal n : ℂ)) * u ^ n / n)
    with hcol
  have hh : ∀ n, HasSum (fun k => f k n) (col n) := by
    intro n
    rcases n with _ | m
    · simp [hf, hcol]
    · have := (hasSum_zeta_succ (k := m + 1) (by omega)).mul_left (-(u ^ (m + 1) / (m + 1 : ℕ)))
      convert this using 1
      · funext k
        simp only [hf]
        rw [div_pow, ← pow_mul, show 2 * (m + 1) = 2 * (m + 1) by rfl]
        field_simp
      · simp only [hcol, zetaEvenVal]
        rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero m))]
        push_cast
        ring
  have hs : Summable fun p : ℕ × ℕ => ‖f p.1 p.2‖ := by
    have hA : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have hB : Summable fun n : ℕ => ‖u‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hu
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity))
    rcases p with ⟨k, n⟩
    simp only [hf, norm_neg, norm_div, norm_pow, norm_natCast_add_one, Complex.norm_natCast]
    rcases n with _ | m
    · simp; positivity
    · have h1 := one_le_succ_sq k
      have hk : ((k : ℝ) + 1) ^ 2 ≤ (((k : ℝ) + 1) ^ 2) ^ (m + 1) :=
        le_self_pow₀ h1 (by omega)
      rw [div_pow]
      calc ‖u‖ ^ (m + 1) / (((k : ℝ) + 1) ^ 2) ^ (m + 1) / ((m + 1 : ℕ) : ℝ)
          ≤ ‖u‖ ^ (m + 1) / (((k : ℝ) + 1) ^ 2) ^ (m + 1) :=
            div_le_self (by positivity) (by norm_cast; omega)
        _ ≤ ‖u‖ ^ (m + 1) / ((k : ℝ) + 1) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hk
        _ = 1 / ((k : ℝ) + 1) ^ 2 * ‖u‖ ^ (m + 1) := by ring
  obtain ⟨hrow, hcl⟩ := hasSum_rows_cols hs hg hh
  have hL : logSinSum u = ∑' p : ℕ × ℕ, f p.1 p.2 := hrow.tsum_eq
  refine ⟨hL ▸ hrow, ?_⟩
  rw [hL]
  have := (hasSum_nat_add_iff' 1).mpr hcl
  simp only [Finset.range_one, Finset.sum_singleton, hcol, ite_true, sub_zero] at this
  convert this using 1
  funext m
  simp only [ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero m))]
  push_cast
  ring

/-- `|Im ∑ₖ ln(1 − u/k²)| < π` for `|u| < 1`. -/
theorem abs_im_logSinSum_lt {u : ℂ} (hu : ‖u‖ < 1) : |(logSinSum u).im| < π := by
  obtain ⟨ht, -⟩ := logSinSum_hasSum hu
  set t : ℕ → ℂ := fun k => log (1 - u / ((k : ℂ) + 1) ^ 2) with htdef
  have him := Complex.imCLM.hasSum ht
  have hz2 : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  set c : ℕ → ℝ := fun k => 3 / 2 * ‖u‖ * (1 / ((k : ℝ) + 1) ^ 2) with hc
  have hcs : HasSum c (3 / 2 * ‖u‖ * (π ^ 2 / 6)) := hz2.mul_left _
  have hb := hcs.add (hasSum_ite_eq 0 (|(t 0).im| - c 0))
  have hbound : ∀ k, ‖Complex.imCLM (t k)‖ ≤
      c k + (if k = 0 then |(t 0).im| - c 0 else 0) := by
    intro k
    rw [Complex.imCLM_apply, Real.norm_eq_abs]
    rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, ite_false, add_zero, hc]
      refine (abs_im_le_norm _).trans ?_
      have hw : ‖-(u / (((k + 1 : ℕ) : ℂ) + 1) ^ 2)‖ ≤ 1 / 2 := by
        rw [norm_neg, norm_div_succ_sq]
        have : (4 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
          push_cast; nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg u]
      have h := norm_log_one_add_half_le_self hw
      rw [← sub_eq_add_neg, norm_neg, norm_div_succ_sq] at h
      simp only [htdef]
      calc ‖log (1 - u / (((k + 1 : ℕ) : ℂ) + 1) ^ 2)‖
          ≤ 3 / 2 * (‖u‖ / (((k + 1 : ℕ) : ℝ) + 1) ^ 2) := h
        _ = 3 / 2 * ‖u‖ * (1 / (((k + 1 : ℕ) : ℝ) + 1) ^ 2) := by ring
  have hle := him.norm_le_of_bounded hb hbound
  rw [Complex.imCLM_apply, Real.norm_eq_abs] at hle
  have h0 : |(t 0).im| < π / 2 := by
    simp only [htdef, Nat.cast_zero, zero_add, one_pow, div_one, log_im]
    refine abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
    have := re_le_norm u
    simp; linarith
  have hc0 : c 0 = 3 / 2 * ‖u‖ := by simp [hc]
  rw [hc0] at hle
  have hpi1 := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have hnu := norm_nonneg u
  have hq : 0 ≤ π ^ 2 / 6 - 1 := by nlinarith
  calc |(logSinSum u).im| ≤ 3 / 2 * ‖u‖ * (π ^ 2 / 6) + (|(t 0).im| - 3 / 2 * ‖u‖) := hle
    _ = |(t 0).im| + 3 / 2 * ‖u‖ * (π ^ 2 / 6 - 1) := by ring
    _ < π / 2 + 3 / 2 * 1 * (π ^ 2 / 6 - 1) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.le
          (by norm_num : (0 : ℝ) ≤ 3 / 2)) hq
        linarith
    _ ≤ π := by nlinarith

/-- `|Im ∑ₖ ln(1 − u/k²)| < π/2` for `|u| < 1/4`. -/
theorem abs_im_logSinSum_lt_half {u : ℂ} (hu : ‖u‖ < 1 / 4) : |(logSinSum u).im| < π / 2 := by
  obtain ⟨ht, -⟩ := logSinSum_hasSum (hu.trans (by norm_num))
  have him := Complex.imCLM.hasSum ht
  have hz2 : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hcs := hz2.mul_left (3 / 2 * ‖u‖)
  have hbound : ∀ k : ℕ, ‖Complex.imCLM (log (1 - u / ((k : ℂ) + 1) ^ 2))‖ ≤
      3 / 2 * ‖u‖ * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    rw [Complex.imCLM_apply, Real.norm_eq_abs]
    refine (abs_im_le_norm _).trans ?_
    have hw : ‖-(u / ((k : ℂ) + 1) ^ 2)‖ ≤ 1 / 2 := by
      rw [norm_neg, norm_div_succ_sq]
      exact (div_le_self (norm_nonneg _) (one_le_succ_sq k)).trans (by linarith)
    have h := norm_log_one_add_half_le_self hw
    rw [← sub_eq_add_neg, norm_neg, norm_div_succ_sq] at h
    calc _ ≤ 3 / 2 * (‖u‖ / ((k : ℝ) + 1) ^ 2) := h
      _ = _ := by ring
  have hle := him.norm_le_of_bounded hcs hbound
  rw [Complex.imCLM_apply, Real.norm_eq_abs] at hle
  have hpi2 := Real.pi_lt_d2
  have hpi1 := Real.pi_gt_three
  calc |(logSinSum u).im| ≤ 3 / 2 * ‖u‖ * (π ^ 2 / 6) := hle
    _ < 3 / 2 * (1 / 4) * (π ^ 2 / 6) := by
        have : 0 < π ^ 2 / 6 := by positivity
        nlinarith
    _ ≤ π / 2 := by nlinarith

/-- Euler's product: `exp(∑ₖ ln(1 − u/k²)) = sin z/z` for `u = (z/π)²`, `0 < |z| < π`. -/
theorem exp_logSinSum {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) :
    exp (logSinSum ((z / π) ^ 2)) = sin z / z := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨x, hxdef⟩ : ∃ x : ℂ, x = z / π := ⟨_, rfl⟩
  have hxn : ‖x‖ < 1 := by
    rw [hxdef, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      div_lt_one Real.pi_pos]
    exact h1
  have hx0 : x ≠ 0 := by rw [hxdef]; exact div_ne_zero h0 hπ
  have hu : ‖x ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg x]
  rw [← hxdef]
  obtain ⟨ht, -⟩ := logSinSum_hasSum hu
  have hP := ht.cexp
  have hP' : HasProd (fun k : ℕ => 1 + sineTerm x k) (exp (logSinSum (x ^ 2))) := by
    convert hP using 1
    funext k
    simp only [Function.comp, sineTerm]
    have hne : 1 - x ^ 2 / ((k : ℂ) + 1) ^ 2 ≠ 0 := by
      intro h
      have : ‖x ^ 2 / ((k : ℂ) + 1) ^ 2‖ = 1 := by
        rw [show x ^ 2 / ((k : ℂ) + 1) ^ 2 = 1 by linear_combination -h, norm_one]
      rw [norm_div_succ_sq] at this
      have := (div_le_self (norm_nonneg _) (one_le_succ_sq k)).trans_lt hu
      linarith
    rw [exp_log hne]
    ring
  have hE := (multipliable_sineTerm x).hasProd
  rw [euler_sineTerm_tprod (mem_integerComplement_of_norm_lt_one hx0 hxn)] at hE
  rw [hP'.unique hE, hxdef]
  field_simp

/-- `ln(sin z/z) = ∑ₖ ln(1 − (z/π)²/k²)`, `|z| < π`. -/
theorem log_sin_div_eq {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) :
    log (sin z / z) = logSinSum ((z / π) ^ 2) := by
  have hu : ‖(z / π) ^ 2‖ < 1 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have : ‖z‖ / π < 1 := (div_lt_one Real.pi_pos).mpr h1
    nlinarith [div_nonneg (norm_nonneg z) Real.pi_pos.le]
  have h := abs_im_logSinSum_lt hu
  rw [← exp_logSinSum h0 h1, log_exp (by linarith [(abs_lt.mp h).1]) (abs_lt.mp h).2.le]

/-- The coefficient of `z^{2n}` in 4.19.7: `(−1)ⁿ 2^{2n−1} B_{2n}/(n (2n)!)`. -/
def logSinCoeff (n : ℕ) : ℚ := (-1) ^ n * 2 ^ (2 * n - 1) * bernoulli (2 * n) / (n * (2 * n)!)

/-- The coefficient of `z^{2n}` in 4.19.8: `(−1)ⁿ 2^{2n−1} (2^{2n} − 1) B_{2n}/(n (2n)!)`. -/
def logCosCoeff (n : ℕ) : ℚ :=
  (-1) ^ n * 2 ^ (2 * n - 1) * (2 ^ (2 * n) - 1) * bernoulli (2 * n) / (n * (2 * n)!)

/-- The coefficient of `z^{2n}` in 4.19.9: `(−1)^{n−1} 2^{2n} (2^{2n−1} − 1) B_{2n}/(n (2n)!)`. -/
def logTanCoeff (n : ℕ) : ℚ :=
  (-1) ^ (n - 1) * 2 ^ (2 * n) * (2 ^ (2 * n - 1) - 1) * bernoulli (2 * n) / (n * (2 * n)!)

/-- **DLMF 4.19.7**: `ln(sin z/z) = ∑_{n≥1} ((−1)ⁿ 2^{2n−1} B_{2n}/(n (2n)!)) z^{2n}`, `|z| < π`
(principal logarithm; at `z = 0` both sides are `0`). -/
theorem dlmf_4_19_7 {z : ℂ} (h1 : ‖z‖ < π) :
    HasSum (fun m : ℕ => (logSinCoeff (m + 1) : ℂ) * z ^ (2 * (m + 1))) (log (sin z / z)) := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hu : ‖(z / π) ^ 2‖ < 1 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have : ‖z‖ / π < 1 := (div_lt_one Real.pi_pos).mpr h1
    nlinarith [div_nonneg (norm_nonneg z) Real.pi_pos.le]
  rw [log_sin_div_eq h0 h1]
  convert (logSinSum_hasSum hu).2 using 1
  funext m
  simp only [logSinCoeff, zetaEvenVal]
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, ← pow_mul, div_pow]
  push_cast
  have hπm : (π : ℂ) ^ (2 * (m + 1)) ≠ 0 := pow_ne_zero _ hπ
  have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp
  ring

theorem re_cos_pos_of_norm_lt {z : ℂ} (h : ‖z‖ < π / 2) : 0 < (cos z).re := by
  rw [re_cos]
  apply mul_pos _ (Real.cosh_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have := abs_lt.mp ((abs_re_le_norm z).trans_lt h)
  constructor <;> linarith [this.1, this.2]

theorem norm_div_pi_sq_lt {z : ℂ} {c : ℝ} (h : ‖z‖ < c * π) :
    ‖(z / π) ^ 2‖ < c ^ 2 := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have : ‖z‖ / π < c := (div_lt_iff₀ Real.pi_pos).mpr h
  have h0 : 0 ≤ ‖z‖ / π := div_nonneg (norm_nonneg z) Real.pi_pos.le
  nlinarith

/-- **DLMF 4.19.8**: `ln cos z = ∑_{n≥1} ((−1)ⁿ 2^{2n−1}(2^{2n} − 1) B_{2n}/(n (2n)!)) z^{2n}`,
`|z| < π/2`. -/
theorem dlmf_4_19_8 {z : ℂ} (h1 : ‖z‖ < π / 2) :
    HasSum (fun m : ℕ => (logCosCoeff (m + 1) : ℂ) * z ^ (2 * (m + 1))) (log (cos z)) := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  have hpi := Real.pi_pos
  have h2 : ‖2 * z‖ < π := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have h20 : 2 * z ≠ 0 := mul_ne_zero two_ne_zero h0
  have hz1 : ‖z‖ < π := by linarith
  -- the logarithm of the quotient
  have hs : sin z ≠ 0 := sin_ne_zero_of_norm_lt_pi h0 hz1
  have hc : cos z ≠ 0 := cos_ne_zero_of_norm_lt_pi_div_two h1
  have hq1 : sin (2 * z) / (2 * z) ≠ 0 := by
    rw [sin_two_mul]; exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hs) hc) h20
  have hq2 : sin z / z ≠ 0 := div_ne_zero hs h0
  set D := log (sin (2 * z) / (2 * z)) - log (sin z / z) with hD
  have hexp : exp D = cos z := by
    rw [hD, exp_sub, exp_log hq1, exp_log hq2, sin_two_mul]
    field_simp
  have hlog : log (cos z) = D := by
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp (show exp (log (cos z)) = exp D by
      rw [exp_log hc, hexp])
    have hIm := congrArg im hn
    have h2π : (2 * (π : ℂ)).re = 2 * π := by simp
    simp only [log_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      mul_one, intCast_re, intCast_im, add_zero, h2π] at hIm
    have ha : |arg (cos z)| < π / 2 :=
      abs_arg_lt_pi_div_two_iff.mpr (Or.inl (re_cos_pos_of_norm_lt h1))
    have hb : |(log (sin (2 * z) / (2 * z))).im| < π := by
      rw [log_sin_div_eq h20 h2]
      exact abs_im_logSinSum_lt (by
        have := norm_div_pi_sq_lt (z := 2 * z) (c := 1) (by rw [one_mul]; exact h2)
        simpa using this)
    have hc' : |(log (sin z / z)).im| < π / 2 := by
      rw [log_sin_div_eq h0 hz1]
      exact abs_im_logSinSum_lt_half (by
        have := norm_div_pi_sq_lt (z := z) (c := 1 / 2) (by linarith)
        norm_num at this ⊢; linarith)
    have hDim : D.im = (log (sin (2 * z) / (2 * z))).im - (log (sin z / z)).im := by
      rw [hD, sub_im]
    have hn0 : n = 0 := by
      have hk : |(n : ℝ)| * (2 * π) < 2 * π := by
        have e : (n : ℝ) * (2 * π) = arg (cos z) - D.im := by linarith
        rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 * π), ← abs_mul, e, abs_of_pos
          (by positivity : (0 : ℝ) < 2 * π)]
        rw [hDim]
        calc |arg (cos z) - ((log (sin (2 * z) / (2 * z))).im - (log (sin z / z)).im)|
            ≤ |arg (cos z)| + |(log (sin (2 * z) / (2 * z))).im| + |(log (sin z / z)).im| := by
              have := abs_sub (arg (cos z)) ((log (sin (2 * z) / (2 * z))).im -
                (log (sin z / z)).im)
              have := abs_sub ((log (sin (2 * z) / (2 * z))).im) ((log (sin z / z)).im)
              linarith
          _ < 2 * π := by linarith
      have : |(n : ℝ)| < 1 := by
        by_contra hh; push Not at hh; nlinarith
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast this)
    rw [hn, hn0]; simp
  rw [hlog, hD]
  convert (dlmf_4_19_7 h2).sub (dlmf_4_19_7 hz1) using 1
  funext m
  simp only [logCosCoeff, logSinCoeff]
  rw [mul_pow]
  push_cast
  rw [show (2 : ℂ) ^ (2 * (m + 1)) = 2 ^ (2 * (m + 1)) by rfl]
  ring

/-- **DLMF 4.19.9**:
`ln(tan z/z) = ∑_{n≥1} ((−1)^{n−1} 2^{2n}(2^{2n−1} − 1) B_{2n}/(n (2n)!)) z^{2n}`,
`|z| < π/2`. -/
theorem dlmf_4_19_9 {z : ℂ} (h1 : ‖z‖ < π / 2) :
    HasSum (fun m : ℕ => (logTanCoeff (m + 1) : ℂ) * z ^ (2 * (m + 1))) (log (tan z / z)) := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  have hpi := Real.pi_pos
  have hz1 : ‖z‖ < π := by linarith
  have hs : sin z ≠ 0 := sin_ne_zero_of_norm_lt_pi h0 hz1
  have hc : cos z ≠ 0 := cos_ne_zero_of_norm_lt_pi_div_two h1
  have hq2 : sin z / z ≠ 0 := div_ne_zero hs h0
  have hlog : log (tan z / z) = log (sin z / z) - log (cos z) := by
    have hexp : exp (log (sin z / z) - log (cos z)) = tan z / z := by
      rw [exp_sub, exp_log hq2, exp_log hc, tan_eq_sin_div_cos]
      field_simp
    have ha : |arg (cos z)| < π / 2 :=
      abs_arg_lt_pi_div_two_iff.mpr (Or.inl (re_cos_pos_of_norm_lt h1))
    have hc' : |(log (sin z / z)).im| < π / 2 := by
      rw [log_sin_div_eq h0 hz1]
      exact abs_im_logSinSum_lt_half (by
        have := norm_div_pi_sq_lt (z := z) (c := 1 / 2) (by linarith)
        norm_num at this ⊢; linarith)
    have him : (log (sin z / z) - log (cos z)).im = (log (sin z / z)).im - arg (cos z) := by
      simp only [sub_im, log_im]
    rw [← hexp, log_exp] <;> rw [him] <;>
      linarith [(abs_lt.mp ha).1, (abs_lt.mp ha).2, (abs_lt.mp hc').1, (abs_lt.mp hc').2]
  rw [hlog]
  convert (dlmf_4_19_7 hz1).sub (dlmf_4_19_8 h1) using 1
  funext m
  simp only [logTanCoeff, logSinCoeff, logCosCoeff]
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show m + 1 - 1 = m by omega]
  push_cast
  rw [show (2 : ℂ) ^ (2 * (m + 1)) = 2 * 2 ^ (2 * m + 1) by ring, pow_succ (-1 : ℂ) m]
  ring

end Azurite.DLMF
