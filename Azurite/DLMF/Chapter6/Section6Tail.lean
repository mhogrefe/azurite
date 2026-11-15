/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section6

/-!
# DLMF §6.6: explicit truncation bounds for the power series

Remainder bounds for the power series 6.6.1, 6.6.2, 6.6.4, 6.6.5, 6.6.6 after `n` terms, for use
by certified evaluation (§6.18(i)).

## Main results

* Generic: `norm_tail_le_of_ratio` (`‖t_{k+1}‖ ≤ r‖t_k‖` for `k ≥ n` ⇒ tail `≤ ‖tₙ‖/(1 − r)`),
  `alternating_tail` (`aₖ` decreasing for `k ≥ n` ⇒ the remainder of `∑ (−1)^k aₖ` after `n`
  terms has the sign `(−1)ⁿ` and modulus `≤ aₙ`).
* Complex arguments (ratio form, any `0 ≤ r < 1`): `norm_ein_sub_partial_le` (6.6.4,
  `|z| ≤ r(n + 2)`), `norm_expIntE₁_sub_partial_le` (6.6.2), `norm_Si_sub_partial_le` (6.6.5,
  `|z|² ≤ r(2n + 2)(2n + 3)`), `norm_Ci_sub_partial_le` (6.6.6, `|z|² ≤ r(2n + 3)(2n + 4)`).
* Real arguments (sharper): `ein_real_tail`, `expIntE₁R_tail` (alternating, `x ≤ n + 2`: remainder
  `≤` first neglected term, same sign), `Ei_tail` (positive terms: `0 ≤` remainder
  `≤ tₙ/(1 − r)` for `x ≤ r(n + 2)`), `SiR_tail` (`x² ≤ (2n + 2)(2n + 3)`), `CiR_tail`
  (`x² ≤ (2n + 3)(2n + 4)`).
* Term ratios: `norm_einTerm_succ_le` (`|z|/(k + 2)`), `norm_siTerm_succ_le`
  (`|z|²/((2k + 2)(2k + 3))`), `norm_ciTerm_succ_le` (`|z|²/((2k + 3)(2k + 4))`).

6.6.3 (`e^{−z} ∑ zⁿψ(n+1)/n!`) is not given a tail bound: it offers no advantage over 6.6.2 for
computation (the same cancellation against `ln z`).
-/

open Complex Filter Topology Set
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Generic tail bounds -/

/-- Ratio test with an explicit tail: if `‖t_{k+1}‖ ≤ r ‖t_k‖` for `k ≥ n`, `0 ≤ r < 1`, then
`‖S − ∑_{k<n} t_k‖ ≤ ‖t_n‖/(1 − r)`. -/
theorem norm_tail_le_of_ratio {t : ℕ → ℂ} {S : ℂ} (hS : HasSum t S) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hratio : ∀ k, n ≤ k → ‖t (k + 1)‖ ≤ r * ‖t k‖) :
    ‖S - ∑ k ∈ Finset.range n, t k‖ ≤ ‖t n‖ / (1 - r) := by
  have htail := (hasSum_nat_add_iff' n).2 hS
  have hb : ∀ k : ℕ, ‖t (k + n)‖ ≤ ‖t n‖ * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show k + 1 + n = (k + n) + 1 by ring, pow_succ]
      calc ‖t (k + n + 1)‖ ≤ r * ‖t (k + n)‖ := hratio _ (Nat.le_add_left n k)
        _ ≤ r * (‖t n‖ * r ^ k) := by gcongr
        _ = ‖t n‖ * (r ^ k * r) := by ring
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ‖t n‖
  rw [← div_eq_mul_inv] at hg
  exact htail.norm_le_of_bounded hg hb

/-- Alternating series with an explicit tail: if `aₖ` decreases for `k ≥ n`, the remainder
of `∑ (−1)^k aₖ` after `n` terms has the sign `(−1)ⁿ` and modulus at most `aₙ`. -/
theorem alternating_tail {a : ℕ → ℝ} {S : ℝ} (hS : HasSum (fun k => (-1) ^ k * a k) S) (n : ℕ)
    (hdec : ∀ k, n ≤ k → a (k + 1) ≤ a k) :
    0 ≤ (-1) ^ n * (S - ∑ k ∈ Finset.range n, (-1) ^ k * a k) ∧
      |S - ∑ k ∈ Finset.range n, (-1) ^ k * a k| ≤ a n := by
  set T := S - ∑ k ∈ Finset.range n, (-1) ^ k * a k
  have htail := (hasSum_nat_add_iff' n).2 hS
  set b : ℕ → ℝ := fun k => a (k + n)
  have hU : HasSum (fun k => (-1) ^ k * b k) ((-1) ^ n * T) := by
    have := htail.mul_left ((-1) ^ n)
    refine this.congr_fun fun k => ?_
    simp only [b]
    have h : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [pow_add]
    linear_combination (-(-1 : ℝ) ^ k * a (k + n)) * h
  have hanti : Antitone b := antitone_nat_of_succ_le fun k => by
    simp only [b]; rw [show k + 1 + n = (k + n) + 1 by ring]; exact hdec _ (Nat.le_add_left n k)
  have hlo := hanti.alternating_series_le_tendsto hU.tendsto_sum_nat 0
  have hhi := hanti.tendsto_le_alternating_series hU.tendsto_sum_nat 0
  simp only [mul_zero, Finset.range_zero, Finset.sum_empty, zero_add, Finset.range_one,
    Finset.sum_singleton, pow_zero, one_mul] at hlo hhi
  have hb0 : b 0 = a n := by simp [b]
  rw [hb0] at hhi
  refine ⟨hlo, ?_⟩
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have habs : |T| = |(-1) ^ n * T| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs, abs_of_nonneg hlo]
  exact hhi

/-! ### `Ein`, `E₁`, `Ei` (6.6.1, 6.6.2, 6.6.4) -/

/-- The `k`-th term `(−1)^k z^{k+1}/((k+1)!(k+1))` of 6.6.4. -/
noncomputable def einTerm (z : ℂ) (k : ℕ) : ℂ := (-1) ^ k * z ^ (k + 1) / (((k + 1)! : ℂ) * (k + 1))

theorem norm_einTerm (z : ℂ) (k : ℕ) :
    ‖einTerm z k‖ = ‖z‖ ^ (k + 1) / ((k + 1)! * (k + 1)) := by
  rw [einTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    norm_mul, Complex.norm_natCast, show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  push_cast; ring

theorem norm_einTerm_succ_le (z : ℂ) (k : ℕ) :
    ‖einTerm z (k + 1)‖ ≤ ‖z‖ / (k + 2) * ‖einTerm z k‖ := by
  rw [norm_einTerm, norm_einTerm, Nat.factorial_succ]
  push_cast
  have hk : (0 : ℝ) < (k + 1)! := by exact_mod_cast Nat.factorial_pos _
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have hz := norm_nonneg z
  have : ‖z‖ ^ (k + 1 + 1) = ‖z‖ * ‖z‖ ^ (k + 1) := by ring
  rw [this]
  have hp : 0 ≤ ‖z‖ * ‖z‖ ^ (k + 1) * (k + 1)! := by positivity
  nlinarith [mul_nonneg hp (by positivity : (0 : ℝ) ≤ (k + 1 : ℝ))]

/-- **6.6.4 with an explicit tail**: if `|z| ≤ r(n + 2)`, `0 ≤ r < 1`, the remainder of the power
series of `Ein(z)` after `n` terms is at most `|tₙ|/(1 − r)`. -/
theorem norm_ein_sub_partial_le (z : ℂ) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖z‖ ≤ r * (n + 2)) :
    ‖ein z - ∑ k ∈ Finset.range n, einTerm z k‖ ≤ ‖einTerm z n‖ / (1 - r) := by
  refine norm_tail_le_of_ratio (dlmf_6_6_4 z) n hr0 hr1 fun k hk => ?_
  refine (norm_einTerm_succ_le z k).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [div_le_iff₀ (by positivity)]
  have : (n : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- **6.6.2 with an explicit tail**: `E₁(z) = −γ − ln z + ∑_{k<n} tₖ + R`, `|R| ≤ |tₙ|/(1 − r)`
for `|z| ≤ r(n + 2)`. -/
theorem norm_expIntE₁_sub_partial_le {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hzr : ‖z‖ ≤ r * (n + 2)) :
    ‖expIntE₁ z - (-γ - log z + ∑ k ∈ Finset.range n, einTerm z k)‖ ≤
      ‖einTerm z n‖ / (1 - r) := by
  rw [dlmf_6_2_4 hz, show ein z - log z - γ - (-γ - log z + ∑ k ∈ Finset.range n, einTerm z k) =
    ein z - ∑ k ∈ Finset.range n, einTerm z k by ring]
  exact norm_ein_sub_partial_le z n hr0 hr1 hzr

/-- The real `k`-th term `x^{k+1}/((k+1)!(k+1))` of 6.6.1. -/
noncomputable def eiTerm (x : ℝ) (k : ℕ) : ℝ := x ^ (k + 1) / ((k + 1)! * (k + 1))

theorem eiTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ eiTerm x k := by
  unfold eiTerm; positivity

theorem eiTerm_succ_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    eiTerm x (k + 1) ≤ x / (k + 2) * eiTerm x k := by
  have h := norm_einTerm_succ_le (x : ℂ) k
  rw [norm_einTerm, norm_einTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at h
  simp only [eiTerm]
  push_cast at h ⊢
  exact h

/-- **6.6.4 for real `x > 0`, alternating form**: if `x ≤ n + 2`, the remainder of the series of
`Ein(x)` after `n` terms has the sign `(−1)ⁿ` of the first neglected term and modulus at most
`x^{n+1}/((n+1)!(n+1))`. -/
theorem ein_real_tail {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hxn : x ≤ n + 2) :
    0 ≤ (-1) ^ n * ((ein x).re - ∑ k ∈ Finset.range n, (-1) ^ k * eiTerm x k) ∧
      |(ein x).re - ∑ k ∈ Finset.range n, (-1) ^ k * eiTerm x k| ≤ eiTerm x n := by
  have hS : HasSum (fun k => (-1) ^ k * eiTerm x k) (ein x).re := by
    have := (Complex.hasSum_re (dlmf_6_6_4 x))
    refine this.congr_fun fun k => ?_
    simp only [eiTerm]
    rw [show ((-1 : ℂ) ^ k * (x : ℂ) ^ (k + 1) / (((k + 1)! : ℂ) * (k + 1))) =
      (((-1 : ℝ) ^ k * (x ^ (k + 1) / ((k + 1)! * (k + 1))) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
  refine alternating_tail hS n fun k hk => ?_
  refine (eiTerm_succ_le hx k).trans ?_
  have : (n : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : x / (k + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact mul_le_of_le_one_left (eiTerm_nonneg hx k) h1

/-- **6.6.2 for real `x > 0`, alternating form**: `E₁(x) = −γ − ln x − ∑_{k<n} (−1)^k
x^{k+1}/((k+1)!(k+1)) + R` with the same bound and sign properties of `R` (`x ≤ n + 2`). -/
theorem expIntE₁R_tail {x : ℝ} (hx : 0 < x) (n : ℕ) (hxn : x ≤ n + 2) :
    0 ≤ (-1) ^ n * (expIntE₁R x - (-γ - Real.log x +
        ∑ k ∈ Finset.range n, (-1) ^ k * eiTerm x k)) ∧
      |expIntE₁R x - (-γ - Real.log x + ∑ k ∈ Finset.range n, (-1) ^ k * eiTerm x k)| ≤
        eiTerm x n := by
  have he : expIntE₁R x = (ein x).re - Real.log x - γ := by
    rw [expIntE₁R, ein_ofReal, ofReal_re]
  obtain ⟨h1, h2⟩ := ein_real_tail hx.le n hxn
  rw [he]
  refine ⟨by convert h1 using 2; ring, by convert h2 using 2; ring⟩

/-- **6.6.1 with an explicit tail** (positive terms): for `0 < x ≤ r(n + 2)`, `0 ≤ r < 1`,
`0 ≤ Ei(x) − γ − ln x − ∑_{k<n} x^{k+1}/((k+1)!(k+1)) ≤ x^{n+1}/((n+1)!(n+1)(1 − r))`. -/
theorem Ei_tail {x : ℝ} (hx : 0 < x) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : x ≤ r * (n + 2)) :
    0 ≤ Ei x - γ - Real.log x - ∑ k ∈ Finset.range n, eiTerm x k ∧
      Ei x - γ - Real.log x - ∑ k ∈ Finset.range n, eiTerm x k ≤ eiTerm x n / (1 - r) := by
  have hS : HasSum (eiTerm x) (Ei x - γ - Real.log x) := by
    refine (dlmf_6_6_1 hx).congr_fun fun k => ?_
    simp only [eiTerm]
  have htail := (hasSum_nat_add_iff' n).2 hS
  refine ⟨htail.nonneg fun k => eiTerm_nonneg hx.le _, ?_⟩
  have hc := norm_tail_le_of_ratio (Complex.hasSum_ofReal.2 hS) n hr0 hr1 fun k hk => by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (eiTerm_nonneg hx.le _), abs_of_nonneg (eiTerm_nonneg hx.le _)]
    refine (eiTerm_succ_le hx.le k).trans (mul_le_mul_of_nonneg_right ?_ (eiTerm_nonneg hx.le _))
    rw [div_le_iff₀ (by positivity)]
    have : (n : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [← ofReal_sum, ← ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (eiTerm_nonneg hx.le _)] at hc
  exact (le_abs_self _).trans hc

/-! ### `Si`, `Ci` (6.6.5, 6.6.6) -/

/-- The `k`-th term `(−1)^k z^{2k+1}/((2k+1)!(2k+1))` of 6.6.5. -/
noncomputable def siTerm (z : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k * z ^ (2 * k + 1) / (((2 * k + 1)! : ℂ) * (2 * k + 1))

/-- The `k`-th term `(−1)^{k+1} z^{2k+2}/((2k+2)!(2k+2))` of 6.6.6. -/
noncomputable def ciTerm (z : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ (k + 1) * z ^ (2 * (k + 1)) / (((2 * (k + 1))! : ℂ) * (2 * (k + 1)))

theorem norm_siTerm (z : ℂ) (k : ℕ) :
    ‖siTerm z k‖ = ‖z‖ ^ (2 * k + 1) / ((2 * k + 1)! * (2 * k + 1)) := by
  rw [siTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    norm_mul, Complex.norm_natCast, show (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) by
      push_cast; ring, Complex.norm_natCast]
  push_cast; ring

theorem norm_ciTerm (z : ℂ) (k : ℕ) :
    ‖ciTerm z k‖ = ‖z‖ ^ (2 * k + 2) / ((2 * k + 2)! * (2 * k + 2)) := by
  rw [ciTerm, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_mul, Complex.norm_natCast, show (2 * ((k : ℂ) + 1)) = ((2 * k + 2 : ℕ) : ℂ) by
      push_cast; ring, Complex.norm_natCast, show 2 * (k + 1) = 2 * k + 2 by ring]
  push_cast; ring

theorem norm_siTerm_succ_le (z : ℂ) (k : ℕ) :
    ‖siTerm z (k + 1)‖ ≤ ‖z‖ ^ 2 / ((2 * k + 2) * (2 * k + 3)) * ‖siTerm z k‖ := by
  have hk : (0 : ℝ) < (2 * k + 1)! := by exact_mod_cast Nat.factorial_pos _
  have e : ‖siTerm z (k + 1)‖ = ‖z‖ ^ 2 * (2 * k + 1) / ((2 * k + 2) * (2 * k + 3) * (2 * k + 3)) *
      ‖siTerm z k‖ := by
    rw [norm_siTerm, norm_siTerm, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := sq_nonneg ‖z‖
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith [mul_nonneg this hk0]

theorem norm_ciTerm_succ_le (z : ℂ) (k : ℕ) :
    ‖ciTerm z (k + 1)‖ ≤ ‖z‖ ^ 2 / ((2 * k + 3) * (2 * k + 4)) * ‖ciTerm z k‖ := by
  have hk : (0 : ℝ) < (2 * k + 2)! := by exact_mod_cast Nat.factorial_pos _
  have e : ‖ciTerm z (k + 1)‖ = ‖z‖ ^ 2 * (2 * k + 2) / ((2 * k + 3) * (2 * k + 4) * (2 * k + 4)) *
      ‖ciTerm z k‖ := by
    rw [norm_ciTerm, norm_ciTerm, show 2 * (k + 1) + 2 = 2 * k + 2 + 1 + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := sq_nonneg ‖z‖
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith [mul_nonneg this hk0]

/-- **6.6.5 with an explicit tail**: if `|z|² ≤ r(2n + 2)(2n + 3)`, `0 ≤ r < 1`, the remainder of
the series of `Si(z)` after `n` terms is at most `|sₙ|/(1 − r)`. -/
theorem norm_Si_sub_partial_le (z : ℂ) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖z‖ ^ 2 ≤ r * ((2 * n + 2) * (2 * n + 3))) :
    ‖Si z - ∑ k ∈ Finset.range n, siTerm z k‖ ≤ ‖siTerm z n‖ / (1 - r) := by
  refine norm_tail_le_of_ratio (dlmf_6_6_5 z) n hr0 hr1 fun k hk => ?_
  refine (norm_siTerm_succ_le z k).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [div_le_iff₀ (by positivity)]
  have : (n : ℝ) ≤ k := by exact_mod_cast hk
  have : ((2 * n + 2) * (2 * n + 3) : ℝ) ≤ (2 * k + 2) * (2 * k + 3) := by nlinarith
  nlinarith

/-- **6.6.6 with an explicit tail**: if `|z|² ≤ r(2n + 3)(2n + 4)`, `0 ≤ r < 1`, the remainder
of the series of `Ci(z) − γ − ln z` after `n` terms is at most `|cₙ|/(1 − r)`. -/
theorem norm_Ci_sub_partial_le {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hzr : ‖z‖ ^ 2 ≤ r * ((2 * n + 3) * (2 * n + 4))) :
    ‖Ci z - (γ + log z + ∑ k ∈ Finset.range n, ciTerm z k)‖ ≤ ‖ciTerm z n‖ / (1 - r) := by
  have h := norm_tail_le_of_ratio (dlmf_6_6_6 hz) n hr0 hr1 fun k hk => by
    refine (norm_ciTerm_succ_le z k).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [div_le_iff₀ (by positivity)]
    have : (n : ℝ) ≤ k := by exact_mod_cast hk
    have : ((2 * n + 3) * (2 * n + 4) : ℝ) ≤ (2 * k + 3) * (2 * k + 4) := by nlinarith
    nlinarith
  rw [show Ci z - (γ + log z + ∑ k ∈ Finset.range n, ciTerm z k) =
    Ci z - γ - log z - ∑ k ∈ Finset.range n, ciTerm z k by ring]
  exact h

/-- **6.6.5 for real `x`, alternating form**: if `x² ≤ (2n + 2)(2n + 3)`, the remainder of the
series of `Si(x)` after `n` terms has the sign `(−1)ⁿ` and modulus at most
`|x|^{2n+1}/((2n+1)!(2n+1))`. -/
theorem SiR_tail {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hxn : x ^ 2 ≤ (2 * n + 2) * (2 * n + 3)) :
    0 ≤ (-1) ^ n * (SiR x - ∑ k ∈ Finset.range n, (-1) ^ k *
        (x ^ (2 * k + 1) / ((2 * k + 1)! * (2 * k + 1)))) ∧
      |SiR x - ∑ k ∈ Finset.range n, (-1) ^ k * (x ^ (2 * k + 1) / ((2 * k + 1)! * (2 * k + 1)))|
        ≤ x ^ (2 * n + 1) / ((2 * n + 1)! * (2 * n + 1)) := by
  set a : ℕ → ℝ := fun k => x ^ (2 * k + 1) / ((2 * k + 1)! * (2 * k + 1))
  have hS : HasSum (fun k => (-1) ^ k * a k) (SiR x) := by
    have := Complex.hasSum_re (dlmf_6_6_5 x)
    rw [dlmf_6_3_F2_Si_real, ofReal_re] at this
    refine this.congr_fun fun k => ?_
    simp only [a]
    rw [show ((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k + 1) / (((2 * k + 1)! : ℂ) * (2 * k + 1))) =
      (((-1 : ℝ) ^ k * (x ^ (2 * k + 1) / ((2 * k + 1)! * (2 * k + 1))) : ℝ) : ℂ) by
        push_cast; ring, ofReal_re]
  have ha : ∀ k, a k = ‖siTerm (x : ℂ) k‖ := fun k => by
    rw [norm_siTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  refine alternating_tail hS n fun k hk => ?_
  rw [ha, ha]
  refine (norm_siTerm_succ_le _ k).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_le_one (by positivity)]
  have : (n : ℝ) ≤ k := by exact_mod_cast hk
  have : ((2 * n + 2) * (2 * n + 3) : ℝ) ≤ (2 * k + 2) * (2 * k + 3) := by nlinarith
  linarith

/-- **6.6.6 for real `x > 0`, alternating form**: if `x² ≤ (2n + 3)(2n + 4)`, the remainder of
the series of `Ci(x) − γ − ln x` after `n` terms has the sign `(−1)^{n+1}` and modulus at most
`x^{2n+2}/((2n+2)!(2n+2))`. -/
theorem CiR_tail {x : ℝ} (hx : 0 < x) (n : ℕ) (hxn : x ^ 2 ≤ (2 * n + 3) * (2 * n + 4)) :
    0 ≤ (-1) ^ (n + 1) * (CiR x - (γ + Real.log x + ∑ k ∈ Finset.range n, (-1) ^ (k + 1) *
        (x ^ (2 * k + 2) / ((2 * k + 2)! * (2 * k + 2))))) ∧
      |CiR x - (γ + Real.log x + ∑ k ∈ Finset.range n, (-1) ^ (k + 1) *
        (x ^ (2 * k + 2) / ((2 * k + 2)! * (2 * k + 2))))| ≤
        x ^ (2 * n + 2) / ((2 * n + 2)! * (2 * n + 2)) := by
  set a : ℕ → ℝ := fun k => x ^ (2 * k + 2) / ((2 * k + 2)! * (2 * k + 2))
  have hS : HasSum (fun k => (-1) ^ k * a k) (-(CiR x - γ - Real.log x)) := by
    have := (Complex.hasSum_re (dlmf_6_6_6 (ofReal_mem_slitPlane.2 hx))).neg
    rw [dlmf_6_3_F2_Ci_real hx, ← ofReal_log hx.le] at this
    simp only [sub_re, ofReal_re] at this
    refine this.congr_fun fun k => ?_
    simp only [a]
    rw [show ((-1 : ℂ) ^ (k + 1) * (x : ℂ) ^ (2 * (k + 1)) /
        (((2 * (k + 1))! : ℂ) * (2 * (k + 1)))) =
      (((-1 : ℝ) ^ (k + 1) * (x ^ (2 * k + 2) / ((2 * k + 2)! * (2 * k + 2))) : ℝ) : ℂ) by
        push_cast; ring_nf, ofReal_re, pow_succ]
    ring
  have ha : ∀ k, a k = ‖ciTerm (x : ℂ) k‖ := fun k => by
    rw [norm_ciTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  obtain ⟨h1, h2⟩ := alternating_tail hS n fun k hk => by
      rw [ha, ha]
      refine (norm_ciTerm_succ_le _ k).trans ?_
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_le_one (by positivity)]
      have : (n : ℝ) ≤ k := by exact_mod_cast hk
      have : ((2 * n + 3) * (2 * n + 4) : ℝ) ≤ (2 * k + 3) * (2 * k + 4) := by nlinarith
      linarith
  have e : CiR x - (γ + Real.log x + ∑ k ∈ Finset.range n, (-1) ^ (k + 1) * a k) =
      -(-(CiR x - γ - Real.log x) - ∑ k ∈ Finset.range n, (-1) ^ k * a k) := by
    rw [neg_sub, Finset.sum_congr rfl fun k _ => show (-1 : ℝ) ^ (k + 1) * a k =
      -((-1) ^ k * a k) by ring, Finset.sum_neg_distrib]
    ring
  refine ⟨?_, ?_⟩
  · rw [e, pow_succ]; linarith
  · rw [e, abs_neg]; exact h2

end Azurite.DLMF
