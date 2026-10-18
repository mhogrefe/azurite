/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ContourIntegration
import Azurite.BrentZimmermann.Chapter4.DoublingTripling
import Azurite.BrentZimmermann.Chapter4.FormalPowerSeries
import Azurite.BrentZimmermann.Chapter4.GuardDigits
import Azurite.BrentZimmermann.Chapter4.RectangularSplitting
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Size
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Brent–Zimmermann Chapter 4: exercises

Formal content of the exercises; the prose answers are in the "Exercises" part of the Chapter 4
ledger in `docs/azfloat_plan.md`.

## Exercise 4.1

For a formal power series `A` with `a₀ = 1`, `ln A` can be computed with error `O(xⁿ)` in time
`O(M(n))` (hint: `(ln A)′ = A′/A`); the analogous question for `n`-bit numbers (`x = 1/2`).

* `logSeries A := ∫ A′ A⁻¹` (the formal integral of §4.2.4) with `constantCoeff_logSeries`,
  `derivative_logSeries` (`(ln A)′ = A′/A`) and the characterization `logSeries_unique`;
  `logSeries_one`, `logSeries_exp` (`ln exp = X`), `logSeries_mul` (`ln(AB) = ln A + ln B`).
* "Error `O(xⁿ)`": `X_pow_dvd_logSeries_sub` — `A ≡ B (mod X^(n+1))` ⇒
  `ln A ≡ ln B (mod X^(n+1))`, so `ln A mod xⁿ` is determined by `A mod xⁿ` and the algorithm
  `A′`, `1/A mod xⁿ` (Newton), one product, one termwise integration is exact modulo `xⁿ`.
* The cost: `sum_cost_le` — under the smoothness `M(2m) ≥ 2M(m)`, the Newton doubling costs
  `∑_{k<L} M(2^k) ≤ M(2^L)`, so the whole computation is `O(M(n))`.

## Exercise 4.2 (Schönhage, Schost)

`1/s(x) mod xⁿ` by an odd–even scheme: `s(x)s(−x)` is even, `= t(x²)`, so
`1/s = s(−x) · (1/t)(x²)` and `1/t` is needed only modulo `x^⌈n/2⌉` — a recursion halving the
size.  `coeff_odd_mul_rescale_neg_one` (odd coefficients of `s(x)s(−x)` vanish), `oddEvenT`,
`mul_rescale_neg_one_eq_expand` (`s(x)s(−x) = t(x²)`), `inv_eq_rescale_mul_expand_inv`
(`1/s = s(−x)(1/t)(x²)`), `X_pow_dvd_inv_sub_oddEven` (an approximation of `1/t` modulo `x^m` gives
`1/s` modulo `x^(2m)`), and the recurrence `cost_recurrence_le` (`T(n) ≤ T(n/2) + cM(n)` ⇒
`T(n) ≤ T(1) + 2cM(n)` for smooth `M`).

## Exercise 4.3

`g(h(x)) = x`, `y_j = h(x_j)`: the iteration
`x_{j+1} = x_j + ∑_{m=1}^{k−1} (y − y_j)^m g^{(m)}(y_j)/m!` is of order `k` and converges to
`x = g(y)` under suitable conditions (generalizing (4.16)).
`taylorInverseStep`; `taylorInverseStep_sub` (Lagrange remainder: `g(y) − x_{j+1} = g^{(k)}(ξ)(y −
y_j)^k/k!`), `abs_sub_taylorInverseStep_le` (`≤ M|y − y_j|^k/k!`), `taylorInverseStep_order`
(with `h` Lipschitz, `|x − x_{j+1}| ≤ (M L^k/k!) |x − x_j|^k`), and the generic convergence
`iterate_le_of_order` (`e_{j+1} ≤ C e_j^k`, `C r^(k−1) ≤ 1/2`, `e₀ ≤ r` ⇒ `e_j ≤ r/2^j`).

## Exercise 4.4

A Horner-like *forward* evaluation of `∑ a_j x^j` that decides dynamically where to stop
(`|a_j|` decreasing, `|x| < 1/2`; hint `y = 1/x`).  `forwardHorner a y j = ∑_{i≤j} a_i y^(j−i)`
(`T_{j+1} = T_j y + a_{j+1}`, `forwardHorner_succ`, `forwardHorner_eq_sum`), the partial sum
`∑_{i≤j} a_i x^i = x^j T_j` (`sum_eq_pow_mul_forwardHorner`), the tail bound
`abs_tsum_sub_sum_le_two_mul` (`|∑_{i>j} a_i x^i| ≤ 2|a_{j+1}||x|^(j+1)`) and
`abs_tsum_sub_sum_le_term` (`≤ |a_j x^j|`, the last term added), and the stopping criterion
`stop_criterion_iff` (`|a_j| ≤ ε|y|^j ↔ |a_j x^j| ≤ ε`) with `abs_tsum_sub_forwardHorner_le`.

## Exercise 4.5

`n` bits of `exp x`, `x` of order `2^j`, by `k` doublings and the naive series: the best reduced
argument `x/2^k`.  `exp_series_terms_of_small` (`|r| ≤ 2^(−m)` ⇒ `d` terms with `md ≥ n + 2` give
`2^(−n)`), the cost `d + k ≈ n/(k − j) + k` and its minimum `doubling_cost_ge` (`≥ 2√n` at
`k − j = √n`, `doubling_cost_sqrt`): the reduced argument should be about `2^(−√n)`.

## Exercise 4.6

Given `ln` to `n` bits in time `T(n)` with `n ≪ M(n) = o(T(n))`, compute `exp x` to `n` bits in
time `∼ T(n)`.  The order-`k` iteration of Exercise 4.3 with `g = exp`, `h = ln` collapses to
`z_{j+1} = z_j ∑_{m<k} (x − ln z_j)^m/m!` (`expViaLogStep`, `expViaLogStep_eq_taylorInverseStep`),
one `ln` and `O(k)` products per step; the relative error satisfies
`ρ_{j+1} ≤ (3·2^(k−1)/k!) ρ_j^k` (`expViaLogStep_relative_error`, with the Lipschitz bound
`abs_log_sub_log_le`); the precisions `n, n/k, n/k², …` cost `∑ T(n/k^i) ≤ T(n)·k/(k−1)`
(`geometric_cost_le`), so with `k → ∞` slowly the total is `T(n)(1 + o(1))`.

## Exercise 4.7

`exp x = exp(x/2^k)^(2^k)` loses about `k` bits: a relative error `ε` in `exp(x/2^k)` becomes
`(1+ε)^(2^k) − 1`, and `2^k ε ≤ (1+ε)^(2^k) − 1 ≤ 2·2^k ε` (`two_pow_mul_le_one_add_pow_sub_one`,
`one_add_pow_sub_one_le_two_mul`), i.e. between `k` and `k + 1` bits are lost
(`logb_one_add_pow_sub_one_ge`); the rounding errors of the squarings themselves are covered
by §4.3.1's `abs_squareSeq_sub_exp_le`.

## Exercise 4.8

With `expm1 x = exp x − 1` and `expm1(2x) = expm1 x (2 + expm1 x)` (§4.3.3's `expm1_two_mul`), the
loss disappears: a relative error `ε` becomes `ε(1 + δ)` with `|δ| ≤ expm1 x` per step
(`abs_expm1_relError_step_le`, sharpening §4.3.3's `2|ε| + ε²`), so after `k` doublings from
`r = x/2^k` the amplification is `∏_{i<k}(1 + expm1(r 2^i)) ≤ exp(x eˣ)` — bounded, not `2^k`
(`expm1DoublingSeq`, `expm1DoublingSeq_exact`, `expm1DoublingSeq_relError`,
`prod_one_add_le_exp_sum`, `sum_expm1_two_pow_le`).

## Exercise 4.9

`log1p x = ln(1 + x)` satisfies `log1p x = 2 log1p (x/(1 + √(1+x)))` for `x > −1`
(`log1p_reduction`); the reduced argument is `√(1+x) − 1` in cancellation-free form
(`div_one_add_sqrt_eq`), lies in `[0, x/2]` for `x ≥ 0` (`sqrt_sub_one_le_half`), and the
reduction does not amplify relative errors (`reduced_relError_le`), whereas forming `y − 1` from
a rounded `y ≈ 1` loses `−log₂(y − 1)` bits (`relError_sub_one`).

## Exercise 4.10

With `u = expm1 |x| ≥ 0`, `sinh |x| = u(2 + u)/(2(1 + u)) = (u + u/(1 + u))/2` and
`sinh x = ±sinh |x|` (`sinh_eq_sinhExpm1`, `sinhExpm1_eq`, `sinh_eq_sign_mul_sinh_abs`): one
`expm1`, one division, and a few additions of nonnegative terms, so no cancellation, in contrast
to (4.20)'s two `expm1` evaluations. The formula is well conditioned in `u`
(`sinhExpm1_relError_le`: relative errors are not amplified) and `cosh` comes for free
(`cosh_eq_expm1`).

## Exercise 4.11

`exp x = sinh x + √(1 + sinh² x)` (`exp_eq_sinh_add_sqrt`), with `sinh x = ∑ x^(2k+1)/(2k+1)!`
(`hasSum_sinh_series`, `hasSum_sinh_series'` in powers of `x²`): half the terms of the `exp`
series, one square root. For `x < 0` the sum cancels; use `exp x = 1/(sinh |x| + √(1 + sinh² |x|))`
(`exp_eq_inv_sinh_abs_add_sqrt`, and `sqrt_sub_eq_inv` for the cancelling difference). The map
`s ↦ s + √(1 + s²)` is well conditioned for `s ≥ 0` (`sinh_add_sqrt_relError_le`). Same idea for
other even/odd pairs: `cos x = √(1 − sin² x)` on `[−π/2, π/2]` (Mathlib's
`Real.cos_eq_sqrt_one_sub_sin_sq`), `exp x = (1 + tanh(x/2))/(1 − tanh(x/2))` (`exp_eq_tanh_half`).

## Exercise 4.12

A counting monad `Counted` records general non-scalar products (`nsMul`) and squarings (`nsSq`);
scalar products and additions are free. The two variants of §4.4.3 are written in it
(`powersC`, `hornerC`, `binPowC`, `classicalEvalC`, `modularEvalC`), proven to compute `polyEval`
(`classicalEvalC_val`, `modularEvalC_val`), and their costs are *derived*: classical uses
`⌈k/2⌉ − 1` products and `⌊k/2⌋` squarings for the powers plus `j − 1` Horner products, `j + k − 2`
in all (`classicalEvalC_mul`, `classicalEvalC_sq`, `classicalEvalC_total`); modular uses
`⌊log₂ j⌋` squarings and `popcount j − 1` products for `y = x^j`, `⌈(k−1)/2⌉ − 1` products and
`⌊(k−1)/2⌋` squarings for its powers, and `j − 1` Horner products, `j + k − 3 + ℓ(j)` in all with
`ℓ(j) = ⌊log₂ j⌋ + popcount j − 1 ≤ j − 1` (`modularEvalC_total`, `binPowC_total_le`,
`modularEvalC_total_le`); examples `12 = 3·4`: `5` and `6`.

## Exercise 4.13

When `a_{i+1}/a_i = r_i` are small rationals, evaluate each inner polynomial of the classical
splitting by Horner's rule *in the ratio direction* with the stored powers as the coefficients,
`P_ℓ(x)/a_{kℓ} = x⁰ + r_{kℓ}(x¹ + r_{kℓ+1}(x² + ⋯ + r_{kℓ+k−2} x^{k−1}))` (`ratioHorner`,
`ratioHorner_eq`, `innerPoly_eq_ratioHorner`): every scalar multiplier is a single ratio of
`O(log d)` bits instead of a coefficient of `O(d log d)` bits. The outer Horner in `y = x^k` then
carries the block ratios `a_{k(ℓ+1)}/a_{kℓ} = ∏_{i<k} r_{kℓ+i}` (`scaledHornerC`). The whole
scheme (`ratioEvalC`) computes `polyEval` whenever `a_{i+1} = r_i a_i` (`coeff_eq_prod_ratio`,
`ratioEvalC_val`) at exactly the non-scalar cost of the classical splitting (`ratioEvalC_mul`,
`ratioEvalC_sq`).

## Exercise 4.14

`c(d)` is the number of machine words of a scalar multiplier (`wordsOf`): with the ratios of
Exercise 4.13 every multiplier is an integer `≤ d` (`ratio_multiplier_size`), so
`c(d) = ⌈size(d)/w⌉` (`ratioScalarWords`), equal to `1` for `d < 2^w` (`ratioScalarWords_eq_one`),
i.e. `O(1)` in practice and `O(log d)` in bit terms. With the raw coefficients `1/i!` instead,
`c(d) = ⌈size(d!)/w⌉` (`naiveScalarWords`) and `size(d!) = Θ(d log d)` (`size_factorial_gt`,
`size_factorial_le`), which is what Exercise 4.13 avoids.
-/

namespace Azurite

namespace BZ

open PowerSeries

section Exercise41

variable {K : Type*} [Field K]

theorem integral_zero : integral (0 : K⟦X⟧) = 0 := by
  ext n
  cases n with
  | zero => simp [coeff_integral_zero]
  | succ n => simp [coeff_integral_succ]

theorem integral_add (F G : K⟦X⟧) : integral (F + G) = integral F + integral G := by
  ext n
  cases n with
  | zero => rw [coeff_integral_zero, map_add, coeff_integral_zero, coeff_integral_zero, add_zero]
  | succ n => simp only [map_add, coeff_integral_succ]; ring

theorem integral_sub (F G : K⟦X⟧) : integral (F - G) = integral F - integral G := by
  ext n
  cases n with
  | zero => rw [coeff_integral_zero, map_sub, coeff_integral_zero, coeff_integral_zero, sub_zero]
  | succ n => simp only [map_sub, coeff_integral_succ]; ring

/-- Exercise 4.1: the formal logarithm `ln A := ∫ A′/A` (for `A` with `a₀ ≠ 0`). -/
noncomputable def logSeries (A : K⟦X⟧) : K⟦X⟧ := integral (d⁄dX A * A⁻¹)

theorem constantCoeff_logSeries (A : K⟦X⟧) : constantCoeff (logSeries A) = 0 :=
  constantCoeff_integral _

/-- `(ln A)′ = A′/A`. -/
theorem derivative_logSeries [CharZero K] (A : K⟦X⟧) : d⁄dX (logSeries A) = d⁄dX A * A⁻¹ :=
  derivative_integral _

/-- `ln A` is the unique series with zero constant term and derivative `A′/A`. -/
theorem logSeries_unique [CharZero K] {A L : K⟦X⟧} (h0 : constantCoeff L = 0)
    (hL : d⁄dX L = d⁄dX A * A⁻¹) : L = logSeries A := by
  rw [logSeries, ← hL, integral_derivative, h0, map_zero, sub_zero]

theorem logSeries_one : logSeries (1 : K⟦X⟧) = 0 := by
  rw [logSeries, Derivation.map_one_eq_zero, zero_mul, integral_zero]

/-- `ln (exp x) = x`. -/
theorem logSeries_exp : logSeries (exp ℚ) = X := by
  rw [logSeries, PowerSeries.derivative_exp ℚ,
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_exp]; exact one_ne_zero)]
  ext n
  cases n with
  | zero => simp [coeff_integral_zero]
  | succ n =>
    rw [coeff_integral_succ, coeff_one, coeff_X]
    by_cases hn : n = 0
    · subst hn
      norm_num
    · simp [hn]

/-- `ln(AB) = ln A + ln B` for `A, B` with nonzero constant coefficients. -/
theorem logSeries_mul {A B : K⟦X⟧} (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    logSeries (A * B) = logSeries A + logSeries B := by
  have hAB : constantCoeff (A * B) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hA hB
  have hA0 : A ≠ 0 := fun h => hA (by rw [h, map_zero])
  have hB0 : B ≠ 0 := fun h => hB (by rw [h, map_zero])
  have hinvA := PowerSeries.mul_inv_cancel A hA
  have hinvB := PowerSeries.mul_inv_cancel B hB
  have hinvAB := PowerSeries.mul_inv_cancel (A * B) hAB
  have key : d⁄dX (A * B) * (A * B)⁻¹ = d⁄dX A * A⁻¹ + d⁄dX B * B⁻¹ := by
    apply mul_right_cancel₀ (mul_ne_zero hA0 hB0)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination (A * d⁄dX B + B * d⁄dX A) * hinvAB - (d⁄dX A * B) * hinvA
      - (d⁄dX B * A) * hinvB
  rw [logSeries, key, integral_add]
  rfl

/-- Integration raises the order of vanishing by one. -/
theorem X_pow_dvd_integral {n : ℕ} {F : K⟦X⟧} (h : X ^ n ∣ F) : X ^ (n + 1) ∣ integral F := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  cases m with
  | zero => exact coeff_integral_zero F
  | succ m => rw [coeff_integral_succ, h m (by omega), zero_div]

/-- "Error `O(xⁿ)`": `ln A mod x^(n+1)` depends only on `A mod x^(n+1)`. -/
theorem X_pow_dvd_logSeries_sub {A B : K⟦X⟧} (hA : constantCoeff A ≠ 0)
    (hB : constantCoeff B ≠ 0) {n : ℕ} (h : X ^ (n + 1) ∣ A - B) :
    X ^ (n + 1) ∣ logSeries A - logSeries B := by
  obtain ⟨R, hR⟩ := h
  have hAB : A = B + X ^ (n + 1) * R := by rw [← hR]; ring
  have hinvA := PowerSeries.mul_inv_cancel A hA
  have hinvB := PowerSeries.mul_inv_cancel B hB
  have key : d⁄dX A * A⁻¹ - d⁄dX B * B⁻¹ = (d⁄dX A * B - A * d⁄dX B) * (A⁻¹ * B⁻¹) := by
    linear_combination (-(d⁄dX A * A⁻¹)) * hinvB + (d⁄dX B * B⁻¹) * hinvA
  have hdA : d⁄dX A = d⁄dX B + (((n + 1 : ℕ) : K⟦X⟧) * X ^ n * R + X ^ (n + 1) * d⁄dX R) := by
    rw [hAB, map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, mul_one]
    push_cast
    ring
  have hnum : X ^ n ∣ d⁄dX A * B - A * d⁄dX B :=
    ⟨((n + 1 : ℕ) : K⟦X⟧) * R * B + X * d⁄dX R * B - X * R * d⁄dX B, by rw [hdA, hAB]; ring⟩
  rw [logSeries, logSeries, ← integral_sub, key]
  exact X_pow_dvd_integral (hnum.mul_right _)

/-- The Newton doubling cost: if `M(2m) ≥ 2M(m)` (the "reasonable smoothness condition"), the
precisions `1, 2, 4, …, 2^(L−1)` together cost at most `M(2^L)`. -/
theorem sum_cost_le (M : ℕ → ℝ) (hM0 : ∀ m, 0 ≤ M m) (hM : ∀ m, 2 * M m ≤ M (2 * m)) (L : ℕ) :
    ∑ k ∈ Finset.range L, M (2 ^ k) ≤ M (2 ^ L) := by
  induction L with
  | zero => simpa using hM0 1
  | succ L ih =>
    rw [Finset.sum_range_succ, pow_succ, mul_comm]
    linarith [hM (2 ^ L)]

end Exercise41

section Exercise42

variable {K : Type*} [Field K] [CharZero K]

/-- The odd coefficients of `s(x) s(−x)` vanish. -/
theorem coeff_odd_mul_rescale_neg_one (s : K⟦X⟧) (j : ℕ) :
    coeff (2 * j + 1) (s * rescale (-1) s) = 0 := by
  rw [coeff_mul]
  set f : ℕ × ℕ → K := fun p => coeff p.1 s * coeff p.2 (rescale (-1) s) with hf
  have hswap : ∀ p ∈ Finset.antidiagonal (2 * j + 1), f p.swap = -f p := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    simp only [hf, Prod.fst_swap, Prod.snd_swap, coeff_rescale]
    have hodd : (-1 : K) ^ p.1 = -(-1) ^ p.2 := by
      rcases Nat.even_or_odd p.1 with h | h
      · have h2 : Odd p.2 := by
          rcases h with ⟨a, ha⟩
          exact ⟨j - a, by omega⟩
        rw [h.neg_one_pow, h2.neg_one_pow, neg_neg]
      · have h2 : Even p.2 := by
          rcases h with ⟨a, ha⟩
          exact ⟨j - a, by omega⟩
        rw [h.neg_one_pow, h2.neg_one_pow]
    rw [hodd]
    ring
  have h := Finset.Nat.sum_antidiagonal_swap (n := 2 * j + 1) (f := f)
  rw [Finset.sum_congr rfl hswap, Finset.sum_neg_distrib] at h
  have h2 : (2 : K) * ∑ p ∈ Finset.antidiagonal (2 * j + 1), f p = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- `t` with `t(x²) = s(x) s(−x)`. -/
noncomputable def oddEvenT (s : K⟦X⟧) : K⟦X⟧ := mk fun j => coeff (2 * j) (s * rescale (-1) s)

omit [CharZero K] in
theorem coeff_oddEvenT (s : K⟦X⟧) (j : ℕ) :
    coeff j (oddEvenT s) = coeff (2 * j) (s * rescale (-1) s) :=
  coeff_mk _ _

omit [CharZero K] in
theorem constantCoeff_rescale' (a : K) (f : K⟦X⟧) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

/-- `s(x) s(−x) = t(x²)`. -/
theorem mul_rescale_neg_one_eq_expand (s : K⟦X⟧) :
    s * rescale (-1) s = expand 2 two_ne_zero (oddEvenT s) := by
  ext n
  rw [coeff_expand]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [coeff_oddEvenT, Nat.mul_div_cancel_left j two_pos]
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
    exact coeff_odd_mul_rescale_neg_one s j

omit [CharZero K] in
theorem constantCoeff_oddEvenT (s : K⟦X⟧) : constantCoeff (oddEvenT s) = constantCoeff s ^ 2 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_oddEvenT, mul_zero, coeff_zero_eq_constantCoeff,
    map_mul, constantCoeff_rescale', sq]

/-- The odd–even reciprocal: `1/s = s(−x) · (1/t)(x²)`. -/
theorem inv_eq_rescale_mul_expand_inv {s : K⟦X⟧} (hs : constantCoeff s ≠ 0) :
    s⁻¹ = rescale (-1) s * expand 2 two_ne_zero (oddEvenT s)⁻¹ := by
  have ht : constantCoeff (oddEvenT s) ≠ 0 := by rw [constantCoeff_oddEvenT]; exact pow_ne_zero 2 hs
  have hW : s * (rescale (-1) s * expand 2 two_ne_zero (oddEvenT s)⁻¹) = 1 := by
    rw [← mul_assoc, mul_rescale_neg_one_eq_expand, ← map_mul, PowerSeries.mul_inv_cancel _ ht,
      map_one]
  calc s⁻¹ = s⁻¹ * (s * (rescale (-1) s * expand 2 two_ne_zero (oddEvenT s)⁻¹)) := by
        rw [hW, mul_one]
    _ = _ := by rw [← mul_assoc, PowerSeries.inv_mul_cancel s hs, one_mul]

/-- Precision doubling: an approximation of `1/t` modulo `x^m` yields `1/s` modulo `x^(2m)`. -/
theorem X_pow_dvd_inv_sub_oddEven {s u : K⟦X⟧} (hs : constantCoeff s ≠ 0) {m : ℕ}
    (hu : X ^ m ∣ (oddEvenT s)⁻¹ - u) :
    X ^ (2 * m) ∣ s⁻¹ - rescale (-1) s * expand 2 two_ne_zero u := by
  rw [inv_eq_rescale_mul_expand_inv hs, ← mul_sub, ← map_sub]
  have h := map_dvd (expand 2 two_ne_zero) hu
  rw [map_pow, expand_X, ← pow_mul] at h
  exact h.mul_left _

/-- The cost recurrence of a halving scheme: if `T(2^(k+1)) ≤ T(2^k) + c M(2^(k+1))` and
`M(2^(k+1)) ≥ 2 M(2^k)` (smoothness), then `T(2^L) ≤ T(1) + 2c M(2^L)`. -/
theorem cost_recurrence_le (T M : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) (hM0 : ∀ m, 0 ≤ M m)
    (hM : ∀ k, 2 * M (2 ^ k) ≤ M (2 ^ (k + 1)))
    (hT : ∀ k, T (2 ^ (k + 1)) ≤ T (2 ^ k) + c * M (2 ^ (k + 1))) (L : ℕ) :
    T (2 ^ L) ≤ T 1 + 2 * c * M (2 ^ L) := by
  induction L with
  | zero => simp only [pow_zero]; nlinarith [hM0 1]
  | succ L ih =>
    have := hT L
    have := hM L
    nlinarith

end Exercise42

section Exercise43

open Set

/-- Exercise 4.3: the order-`k` step `x_j ↦ x_j + ∑_{m=1}^{k−1} (y − h x_j)^m g^{(m)}(h x_j)/m!`. -/
noncomputable def taylorInverseStep (g h : ℝ → ℝ) (y : ℝ) (k : ℕ) (xj : ℝ) : ℝ :=
  xj + ∑ m ∈ Finset.Ico 1 k, (y - h xj) ^ m * iteratedDeriv m g (h xj) / m.factorial

/-- The step is the degree-`(k−1)` Taylor polynomial of `g` at `y_j`, evaluated at `y`
(`g(y_j) = x_j` supplies the constant term). -/
theorem taylorInverseStep_eq_taylor {g h : ℝ → ℝ} {y xj : ℝ} {k : ℕ} (hg : ContDiff ℝ k g)
    (hgh : g (h xj) = xj) (hk : 1 ≤ k) (hne : h xj ≠ y) :
    taylorInverseStep g h y k xj = taylorWithinEval g (k - 1) (uIcc (h xj) y) (h xj) y := by
  rw [taylor_within_apply, Nat.sub_add_cancel hk, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hk]
  have hu : UniqueDiffOn ℝ (uIcc (h xj) y) := uniqueDiffOn_uIcc hne
  have hmem : h xj ∈ uIcc (h xj) y := left_mem_uIcc
  have hw : ∀ m ∈ Finset.Ico 1 k,
      iteratedDerivWithin m g (uIcc (h xj) y) (h xj) = iteratedDeriv m g (h xj) := fun m hm =>
    iteratedDerivWithin_eq_iteratedDeriv hu (hg.contDiffAt.of_le (by
      have := (Finset.mem_Ico.mp hm).2; exact_mod_cast this.le)) hmem
  rw [iteratedDerivWithin_eq_iteratedDeriv hu (hg.contDiffAt.of_le (by simp)) hmem,
    iteratedDeriv_zero, hgh]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one, one_smul]
  unfold taylorInverseStep
  rw [add_right_inj]
  exact Finset.sum_congr rfl fun m hm => by rw [hw m hm, smul_eq_mul]; ring

/-- The Lagrange remainder: `g(y) − x_{j+1} = g^{(k)}(ξ) (y − y_j)^k / k!` for some `ξ` strictly
between `y_j` and `y`. -/
theorem taylorInverseStep_sub {g h : ℝ → ℝ} {y xj : ℝ} {k : ℕ} (hg : ContDiff ℝ k g)
    (hgh : g (h xj) = xj) (hk : 1 ≤ k) (hne : h xj ≠ y) :
    ∃ ξ ∈ uIoo (h xj) y,
      g y - taylorInverseStep g h y k xj = iteratedDeriv k g ξ * (y - h xj) ^ k / k.factorial := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hg' : ContDiffOn ℝ (n + 1) g (uIcc (h xj) y) := hg.contDiffOn
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hg'
  refine ⟨ξ, hξ, ?_⟩
  rw [taylorInverseStep_eq_taylor hg hgh hk hne, Nat.add_sub_cancel]
  exact h

/-- `|g(y) − x_{j+1}| ≤ M |y − y_j|^k / k!` when `|g^{(k)}| ≤ M` between `y_j` and `y`. -/
theorem abs_sub_taylorInverseStep_le {g h : ℝ → ℝ} {y xj M : ℝ} {k : ℕ} (hg : ContDiff ℝ k g)
    (hgh : g (h xj) = xj) (hk : 1 ≤ k)
    (hM : ∀ ξ ∈ uIcc (h xj) y, |iteratedDeriv k g ξ| ≤ M) :
    |g y - taylorInverseStep g h y k xj| ≤ M * |y - h xj| ^ k / k.factorial := by
  rcases eq_or_ne (h xj) y with heq | hne
  · have hstep : taylorInverseStep g h y k xj = xj := by
      unfold taylorInverseStep
      rw [← heq, sub_self]
      rw [Finset.sum_eq_zero fun m hm => by
        rw [zero_pow (by have := (Finset.mem_Ico.mp hm).1; omega)]; ring]
      ring
    rw [hstep, ← heq, hgh, sub_self, abs_zero, sub_self, abs_zero, zero_pow (by omega), mul_zero,
      zero_div]
  · obtain ⟨ξ, hξ, hrem⟩ := taylorInverseStep_sub hg hgh hk hne
    rw [hrem, abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < k.factorial)]
    have hξ' : ξ ∈ uIcc (h xj) y := uIoo_subset_uIcc_self hξ
    gcongr
    exact hM ξ hξ'

/-- Order `k`: with `x = g(y)`, `y = h(x)`, and `h` Lipschitz with constant `L` between `x` and
`x_j`, `|x − x_{j+1}| ≤ (M L^k / k!) |x − x_j|^k`. -/
theorem taylorInverseStep_order {g h : ℝ → ℝ} {x xj M L : ℝ} {k : ℕ} (hg : ContDiff ℝ k g)
    (hgx : g (h x) = x) (hgh : g (h xj) = xj) (hk : 1 ≤ k)
    (hLip : |h x - h xj| ≤ L * |x - xj|)
    (hM : ∀ ξ ∈ uIcc (h xj) (h x), |iteratedDeriv k g ξ| ≤ M) :
    |x - taylorInverseStep g h (h x) k xj| ≤ M * L ^ k / k.factorial * |x - xj| ^ k := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (h xj) left_mem_uIcc)
  have h1 := abs_sub_taylorInverseStep_le hg hgh hk hM
  rw [hgx] at h1
  refine h1.trans ?_
  have h2 : |h x - h xj| ^ k ≤ (L * |x - xj|) ^ k := pow_le_pow_left₀ (abs_nonneg _) hLip k
  rw [mul_pow] at h2
  calc M * |h x - h xj| ^ k / k.factorial ≤ M * (L ^ k * |x - xj| ^ k) / k.factorial := by
        gcongr
    _ = M * L ^ k / k.factorial * |x - xj| ^ k := by ring

/-- Convergence of a `k`-th order iteration: if `e_{j+1} ≤ C e_j^k` whenever `e_j ≤ r`, with
`C r^(k−1) ≤ 1/2` and `e₀ ≤ r`, then `e_j ≤ r / 2^j`. -/
theorem iterate_le_of_order {e : ℕ → ℝ} {C r : ℝ} {k : ℕ} (hk : 1 ≤ k) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (he0 : ∀ j, 0 ≤ e j) (hstep : ∀ j, e j ≤ r → e (j + 1) ≤ C * e j ^ k)
    (hCr : C * r ^ (k - 1) ≤ 1 / 2) (h0 : e 0 ≤ r) (j : ℕ) : e j ≤ r / 2 ^ j := by
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hr' : e j ≤ r := ih.trans (by
      rw [div_le_iff₀ (by positivity)]
      exact le_mul_of_one_le_right hr (one_le_pow₀ (by norm_num)))
    have h1 := hstep j hr'
    have h2 : e j ^ k = e j ^ (k - 1) * e j := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    have h3 : e j ^ (k - 1) ≤ r ^ (k - 1) := pow_le_pow_left₀ (he0 j) hr' _
    calc e (j + 1) ≤ C * (e j ^ (k - 1) * e j) := by rw [← h2]; exact h1
      _ ≤ C * (r ^ (k - 1) * e j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (he0 j)) hC
      _ = (C * r ^ (k - 1)) * e j := by ring
      _ ≤ 1 / 2 * (r / 2 ^ j) := mul_le_mul hCr ih (he0 j) (by norm_num)
      _ = r / 2 ^ (j + 1) := by rw [pow_succ]; ring

end Exercise43

section Exercise44

open Finset

variable {K : Type*} [Field K]

/-- Exercise 4.4: `T_j = ∑_{i≤j} a_i y^(j−i)`, Horner in `y = 1/x` run forward:
`T₀ = a₀`, `T_{j+1} = T_j y + a_{j+1}`. -/
def forwardHorner (a : ℕ → K) (y : K) : ℕ → K
  | 0 => a 0
  | j + 1 => forwardHorner a y j * y + a (j + 1)

theorem forwardHorner_zero (a : ℕ → K) (y : K) : forwardHorner a y 0 = a 0 := rfl

theorem forwardHorner_succ (a : ℕ → K) (y : K) (j : ℕ) :
    forwardHorner a y (j + 1) = forwardHorner a y j * y + a (j + 1) := rfl

theorem forwardHorner_eq_sum (a : ℕ → K) (y : K) (j : ℕ) :
    forwardHorner a y j = ∑ i ∈ range (j + 1), a i * y ^ (j - i) := by
  induction j with
  | zero => simp [forwardHorner_zero]
  | succ j ih =>
    rw [forwardHorner_succ, ih, sum_range_succ _ (j + 1), Nat.sub_self, pow_zero, mul_one,
      sum_mul]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [mul_assoc, ← pow_succ, show j + 1 - i = j - i + 1 by omega]

/-- The partial sum of the series is `x^j T_j` with `y = 1/x`. -/
theorem sum_eq_pow_mul_forwardHorner (a : ℕ → K) {x : K} (hx : x ≠ 0) (j : ℕ) :
    ∑ i ∈ range (j + 1), a i * x ^ i = x ^ j * forwardHorner a x⁻¹ j := by
  rw [forwardHorner_eq_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [inv_pow, show x ^ j = x ^ i * x ^ (j - i) by rw [← pow_add, Nat.add_sub_cancel' this]]
  have h := mul_inv_cancel₀ (pow_ne_zero (j - i) hx)
  linear_combination (-(a i * x ^ i)) * h

/-- The series converges absolutely for `|x| < 1` and bounded coefficients. -/
theorem summable_abs_term {a : ℕ → ℝ} {x : ℝ} (hx : |x| < 1) (ha : Antitone fun i => |a i|) :
    Summable fun i => |a i * x ^ i| :=
  ((summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left |a 0|).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun i => by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (ha (Nat.zero_le i)) (by positivity)

/-- The tail after `j` terms: `|∑_{i>j} a_i x^i| ≤ 2|a_{j+1}||x|^(j+1)` for decreasing `|a_i|` and
`|x| < 1/2`. -/
theorem abs_tsum_sub_sum_le_two_mul {a : ℕ → ℝ} {x : ℝ} (hx : |x| < 1 / 2)
    (ha : Antitone fun i => |a i|) (j : ℕ) :
    |∑' i, a i * x ^ i - ∑ i ∈ range (j + 1), a i * x ^ i| ≤ 2 * |a (j + 1)| * |x| ^ (j + 1) := by
  have hx1 : |x| < 1 := by linarith
  have hs := (summable_abs_term hx1 ha).of_abs
  rw [← Summable.sum_add_tsum_nat_add' (f := fun i => a i * x ^ i) (k := j + 1)
    ((summable_nat_add_iff (f := fun i => a i * x ^ i) (j + 1)).mpr hs), add_sub_cancel_left]
  have hgeo : Summable fun i : ℕ => |a (j + 1)| * |x| ^ (j + 1) * |x| ^ i :=
    (summable_geometric_of_lt_one (abs_nonneg x) hx1).mul_left _
  have hbound : ∀ i : ℕ, |a (i + (j + 1)) * x ^ (i + (j + 1))|
      ≤ |a (j + 1)| * |x| ^ (j + 1) * |x| ^ i := by
    intro i
    rw [abs_mul, abs_pow, pow_add, mul_comm (|x| ^ i)]
    have h1 : |a (i + (j + 1))| ≤ |a (j + 1)| := ha (by omega)
    have h2 : 0 ≤ |x| ^ (j + 1) * |x| ^ i := by positivity
    calc |a (i + (j + 1))| * (|x| ^ (j + 1) * |x| ^ i) ≤ |a (j + 1)| * (|x| ^ (j + 1) * |x| ^ i) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  have hnorm : Summable fun i : ℕ => |a (i + (j + 1)) * x ^ (i + (j + 1))| :=
    hgeo.of_nonneg_of_le (fun _ => abs_nonneg _) hbound
  calc |∑' i : ℕ, a (i + (j + 1)) * x ^ (i + (j + 1))|
      ≤ ∑' i : ℕ, |a (i + (j + 1)) * x ^ (i + (j + 1))| := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hnorm)
    _ ≤ ∑' i : ℕ, |a (j + 1)| * |x| ^ (j + 1) * |x| ^ i := hnorm.tsum_le_tsum hbound hgeo
    _ = |a (j + 1)| * |x| ^ (j + 1) * (1 - |x|)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg x) hx1]
    _ ≤ |a (j + 1)| * |x| ^ (j + 1) * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
    _ = 2 * |a (j + 1)| * |x| ^ (j + 1) := by ring

/-- The tail is at most the last term added: `|∑_{i>j} a_i x^i| ≤ |a_j x^j|`. -/
theorem abs_tsum_sub_sum_le_term {a : ℕ → ℝ} {x : ℝ} (hx : |x| < 1 / 2)
    (ha : Antitone fun i => |a i|) (j : ℕ) :
    |∑' i, a i * x ^ i - ∑ i ∈ range (j + 1), a i * x ^ i| ≤ |a j * x ^ j| := by
  refine (abs_tsum_sub_sum_le_two_mul hx ha j).trans ?_
  rw [abs_mul, abs_pow, pow_succ]
  have h1 : |a (j + 1)| ≤ |a j| := ha (Nat.le_succ j)
  have h2 : 0 ≤ |x| ^ j := by positivity
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg x)) h2
  have h4 := mul_le_mul_of_nonneg_left hx.le (mul_nonneg (abs_nonneg (a j)) h2)
  nlinarith [h3, h4]

/-- The dynamic test in terms of `y = 1/x`: `|a_j| ≤ ε |y|^j` means `|a_j x^j| ≤ ε`. -/
theorem stop_criterion_iff {a : ℕ → ℝ} {x ε : ℝ} (hx : x ≠ 0) (j : ℕ) :
    |a j| ≤ ε * |x⁻¹| ^ j ↔ |a j * x ^ j| ≤ ε := by
  have hpos : 0 < |x| ^ j := by positivity
  rw [abs_inv, inv_pow, abs_mul, abs_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]

/-- Stopping when `|a_j x^j| ≤ ε` returns `x^j T_j` within `ε` of the series. -/
theorem abs_tsum_sub_forwardHorner_le {a : ℕ → ℝ} {x ε : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1 / 2)
    (ha : Antitone fun i => |a i|) {j : ℕ} (hstop : |a j * x ^ j| ≤ ε) :
    |∑' i, a i * x ^ i - x ^ j * forwardHorner a x⁻¹ j| ≤ ε := by
  rw [← sum_eq_pow_mul_forwardHorner a hx0]
  exact (abs_tsum_sub_sum_le_term hx ha j).trans hstop

end Exercise44

section Exercise45

open Finset

/-- With `|r| ≤ 2^(−m)`, `d` terms of the exponential series with `m·d ≥ n + 2` give
`exp r` to within `2^(−n)`. -/
theorem exp_series_terms_of_small {r : ℝ} {m d n : ℕ} (hr : |r| ≤ (1 / 2) ^ m)
    (hd : n + 2 ≤ m * d) :
    |Real.exp r - ∑ i ∈ range d, r ^ i / i.factorial| ≤ (1 / 2) ^ n := by
  have h := abs_exp_sub_sum_le r d
  have hr1 : |r| ≤ 1 := hr.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hexp : Real.exp |r| ≤ 3 := (Real.exp_le_exp.mpr hr1).trans Real.exp_one_lt_three.le
  have hfact : (1 : ℝ) ≤ d.factorial := by exact_mod_cast d.factorial_pos
  have hpow : |r| ^ d ≤ (1 / 2) ^ (n + 2) := by
    calc |r| ^ d ≤ ((1 / 2 : ℝ) ^ m) ^ d := pow_le_pow_left₀ (abs_nonneg r) hr d
      _ = (1 / 2) ^ (m * d) := by rw [← pow_mul]
      _ ≤ (1 / 2) ^ (n + 2) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
  refine h.trans ?_
  calc |r| ^ d / d.factorial * Real.exp |r| ≤ (1 / 2) ^ (n + 2) / 1 * 3 := by
        gcongr
    _ = (1 / 2) ^ n * (3 / 4) := by ring
    _ ≤ (1 / 2) ^ n := by
        have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
        linarith

/-- The cost model: `k` doublings plus `d ≈ n/(k − j)` series terms, each one multiplication;
`n/m + m ≥ 2√n` for `m = k − j > 0`. -/
theorem doubling_cost_ge {n m : ℝ} (hn : 0 ≤ n) (hm : 0 < m) : 2 * Real.sqrt n ≤ n / m + m := by
  have := two_sqrt_le_add_div hn hm
  linarith

/-- Equality at `m = √n`: the optimal reduction is to `x/2^k ≈ 2^(−√n)`. -/
theorem doubling_cost_sqrt (n : ℝ) : n / Real.sqrt n + Real.sqrt n = 2 * Real.sqrt n := by
  rw [Real.div_sqrt, two_mul]

end Exercise45

section Exercise46

open Finset Set

theorem iteratedDeriv_exp (m : ℕ) : iteratedDeriv m Real.exp = Real.exp := by
  induction m with
  | zero => exact iteratedDeriv_zero
  | succ m ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

/-- Exercise 4.6: the order-`k` step for `exp x` from `ln`: `z ↦ z ∑_{m<k} (x − ln z)^m/m!`. -/
noncomputable def expViaLogStep (k : ℕ) (x z : ℝ) : ℝ :=
  z * ∑ m ∈ range k, (x - Real.log z) ^ m / m.factorial

/-- It is Exercise 4.3's iteration with `g = exp`, `h = ln` (for `z > 0`). -/
theorem expViaLogStep_eq_taylorInverseStep {k : ℕ} (hk : 1 ≤ k) {x z : ℝ} (hz : 0 < z) :
    expViaLogStep k x z = taylorInverseStep Real.exp Real.log x k z := by
  unfold expViaLogStep taylorInverseStep
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hk, mul_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [iteratedDeriv_exp, Real.exp_log hz]
  ring

/-- `|ln a − ln b| ≤ |a − b| / min a b` for `a, b > 0`. -/
theorem abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  wlog hab : a ≤ b generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    rwa [abs_sub_comm b a, min_comm b a, abs_sub_comm (Real.log b)] at this
  rw [min_eq_left hab, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab),
    abs_sub_comm (Real.log a), abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log ha hab)),
    ← Real.log_div hb.ne' ha.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [div_sub_one ha.ne'] at this
  exact this

/-- The relative error of one step: with `ρ = |exp x − z| / exp x ≤ 1/2`,
`|exp x − z'| / exp x ≤ (3·2^(k−1)/k!) ρ^k`. -/
theorem expViaLogStep_relative_error {k : ℕ} (hk : 1 ≤ k) {x z : ℝ}
    (hz : |Real.exp x - z| ≤ Real.exp x / 2) :
    |Real.exp x - expViaLogStep k x z| / Real.exp x
      ≤ 3 * 2 ^ (k - 1) / k.factorial * (|Real.exp x - z| / Real.exp x) ^ k := by
  have hex : 0 < Real.exp x := Real.exp_pos x
  have hz0 : Real.exp x / 2 ≤ z := by linarith [(abs_le.mp hz).2]
  have hz2 : z ≤ 3 / 2 * Real.exp x := by linarith [(abs_le.mp hz).1]
  have hzpos : 0 < z := by linarith
  rw [expViaLogStep_eq_taylorInverseStep hk hzpos]
  -- the hypotheses of `taylorInverseStep_order` with `g = exp`, `h = log`, target `exp x`
  have hL : |Real.log (Real.exp x) - Real.log z| ≤ (2 / Real.exp x) * |Real.exp x - z| := by
    refine (abs_log_sub_log_le hex hzpos).trans ?_
    rw [div_eq_mul_inv, mul_comm]
    gcongr
    rw [inv_le_comm₀ (lt_min hex hzpos) (by positivity), inv_div, le_min_iff]
    constructor <;> linarith
  have hM : ∀ ξ ∈ uIcc (Real.log z) (Real.log (Real.exp x)),
      |iteratedDeriv k Real.exp ξ| ≤ 3 / 2 * Real.exp x := by
    intro ξ hξ
    rw [iteratedDeriv_exp, abs_of_pos (Real.exp_pos ξ)]
    have h1 : Real.exp (Real.log z) ≤ 3 / 2 * Real.exp x := by rw [Real.exp_log hzpos]; exact hz2
    have h2 : Real.exp (Real.log (Real.exp x)) ≤ 3 / 2 * Real.exp x := by
      rw [Real.exp_log hex]; linarith
    rcases mem_uIcc.mp hξ with ⟨-, h⟩ | ⟨-, h⟩
    · exact (Real.exp_le_exp.mpr h).trans h2
    · exact (Real.exp_le_exp.mpr h).trans h1
  have h := taylorInverseStep_order (g := Real.exp) (h := Real.log) (x := Real.exp x) (xj := z)
    (M := 3 / 2 * Real.exp x) (L := 2 / Real.exp x) (Real.contDiff_exp.of_le le_top)
    (Real.exp_log hex) (Real.exp_log hzpos) hk hL hM
  rw [Real.log_exp] at h
  rw [div_le_iff₀ hex]
  refine h.trans (le_of_eq ?_)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, div_pow, div_pow]
  field_simp
  ring

/-- Precision doubling by a factor `k`: with `k·T(m/k) ≤ T(m)` (smoothness), the costs at
precisions `n, n/k, n/k², …` sum to at most `T(n) · k/(k−1)`. -/
theorem geometric_cost_le (T : ℝ → ℝ) {k : ℝ} (hk : 1 < k) (hT0 : ∀ m, 0 ≤ T m)
    (hT : ∀ m, k * T (m / k) ≤ T m) (n : ℝ) (L : ℕ) :
    ∑ i ∈ range L, T (n / k ^ i) ≤ T n * (k / (k - 1)) := by
  have hk0 : 0 < k := by linarith
  have hterm : ∀ i : ℕ, T (n / k ^ i) ≤ T n * (1 / k) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h := hT (n / k ^ i)
      rw [div_div, ← pow_succ] at h
      calc T (n / k ^ (i + 1)) ≤ T (n / k ^ i) / k := by
            rw [le_div_iff₀ hk0]; linarith
        _ ≤ T n * (1 / k) ^ i / k := by gcongr
        _ = T n * (1 / k) ^ (i + 1) := by rw [pow_succ]; ring
  have hgeo : ∑ i ∈ range L, (1 / k) ^ i ≤ k / (k - 1) := by
    have hr : (1 / k : ℝ) < 1 := by rw [div_lt_one hk0]; exact hk
    have hr0 : (0 : ℝ) ≤ 1 / k := by positivity
    calc ∑ i ∈ range L, (1 / k) ^ i ≤ ∑' i : ℕ, (1 / k) ^ i :=
          (summable_geometric_of_lt_one hr0 hr).sum_le_tsum _ fun i _ => by positivity
      _ = (1 - 1 / k)⁻¹ := tsum_geometric_of_lt_one hr0 hr
      _ = k / (k - 1) := by field_simp
  calc ∑ i ∈ range L, T (n / k ^ i) ≤ ∑ i ∈ range L, T n * (1 / k) ^ i :=
        sum_le_sum fun i _ => hterm i
    _ = T n * ∑ i ∈ range L, (1 / k) ^ i := by rw [mul_sum]
    _ ≤ T n * (k / (k - 1)) := by gcongr; exact hT0 n

end Exercise46

section Exercise47

/-- Bernoulli: a relative error `ε ≥ 0` is amplified at least `2^k`-fold by `k` squarings. -/
theorem two_pow_mul_le_one_add_pow_sub_one {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    2 ^ k * ε ≤ (1 + ε) ^ 2 ^ k - 1 := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ ε by linarith) (2 ^ k)
  push_cast at h
  linarith

/-- … and at most `2·2^k`-fold while `2^k ε ≤ 1`. -/
theorem one_add_pow_sub_one_le_two_mul {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} (hk : 2 ^ k * ε ≤ 1) :
    (1 + ε) ^ 2 ^ k - 1 ≤ 2 * (2 ^ k * ε) := by
  have h1 : (1 + ε) ^ 2 ^ k ≤ Real.exp (2 ^ k * ε) := by
    rw [show (2 ^ k * ε : ℝ) = ((2 ^ k : ℕ) : ℝ) * ε by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ε]) _
  have h2 := exp_sub_one_le_two_mul (by positivity : (0 : ℝ) ≤ 2 ^ k * ε) hk
  linarith

/-- In bits: if `exp(x/2^k)` carries a relative error `ε`, the result carries at least
`2^k ε`, so `log₂(1/error) ≤ log₂(1/ε) − k`: `k` bits are lost. -/
theorem logb_one_add_pow_sub_one_ge {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    (k : ℝ) + Real.logb 2 ε ≤ Real.logb 2 ((1 + ε) ^ 2 ^ k - 1) := by
  have h := two_pow_mul_le_one_add_pow_sub_one hε.le k
  have hpos : (0 : ℝ) < 2 ^ k * ε := by positivity
  calc (k : ℝ) + Real.logb 2 ε = Real.logb 2 (2 ^ k * ε) := by
        rw [Real.logb_mul (by positivity) hε.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two,
          mul_one]
    _ ≤ Real.logb 2 ((1 + ε) ^ 2 ^ k - 1) := Real.logb_le_logb_of_le one_lt_two hpos h

end Exercise47

section Exercise48

open Finset

/-- The sharp one-step bound: for `x ≥ 0` and `|ε| ≤ 1`, the relative error after one `expm1`
doubling is at most `|ε|(1 + expm1 x)` (compare `abs_expm1_two_mul_relError_le`). -/
theorem abs_expm1_relError_step_le {x ε : ℝ} (hx : 0 ≤ x) (hε : |ε| ≤ 1) :
    |ε * (2 * (expm1 x + 1) + expm1 x * ε) / (expm1 x + 2)| ≤ |ε| * (1 + expm1 x) := by
  have he : 0 ≤ expm1 x := by unfold expm1; linarith [Real.one_le_exp_iff.mpr hx]
  have h2 := expm1_add_two_pos x
  rw [abs_div, abs_of_pos h2, div_le_iff₀ h2, abs_mul]
  have hb : |2 * (expm1 x + 1) + expm1 x * ε| ≤ 2 + 3 * expm1 x := by
    calc |2 * (expm1 x + 1) + expm1 x * ε| ≤ |2 * (expm1 x + 1)| + |expm1 x * ε| := abs_add_le _ _
      _ = 2 * (expm1 x + 1) + expm1 x * |ε| := by
          rw [abs_of_pos (by linarith), abs_mul, abs_of_nonneg he]
      _ ≤ 2 + 3 * expm1 x := by nlinarith
  calc |ε| * |2 * (expm1 x + 1) + expm1 x * ε| ≤ |ε| * (2 + 3 * expm1 x) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ ≤ |ε| * (1 + expm1 x) * (expm1 x + 2) := by nlinarith [abs_nonneg ε, sq_nonneg (expm1 x)]

/-- The exact doubling chain started from a (possibly perturbed) value `t`:
`s₀ = t`, `s_{i+1} = s_i (s_i + 2)`. -/
def expm1DoublingSeq (t : ℝ) : ℕ → ℝ
  | 0 => t
  | i + 1 => expm1DoublingSeq t i * (expm1DoublingSeq t i + 2)

/-- Started exactly, the chain computes `expm1 (r 2^k)`. -/
theorem expm1DoublingSeq_exact (r : ℝ) (k : ℕ) :
    expm1DoublingSeq (expm1 r) k = expm1 (r * 2 ^ k) := by
  induction k with
  | zero => simp [expm1DoublingSeq]
  | succ k ih =>
    rw [expm1DoublingSeq, ih, pow_succ, ← mul_assoc, mul_comm (r * 2 ^ k) 2, expm1_two_mul]

/-- `∏ (1 + a_i) ≤ exp (∑ a_i)` for `a_i ≥ 0`. -/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  exact prod_le_prod₀ (fun i hi => by linarith [ha i hi]) fun i _ => by
    linarith [Real.add_one_le_exp (a i)]

/-- `∑_{i<k} expm1 (r 2^i) ≤ r 2^k exp(r 2^k)` for `r ≥ 0` (so `≤ x eˣ` with `x = r 2^k`). -/
theorem sum_expm1_two_pow_le {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ∑ i ∈ range k, expm1 (r * 2 ^ i) ≤ r * 2 ^ k * Real.exp (r * 2 ^ k) := by
  have hterm : ∀ i ∈ range k, expm1 (r * 2 ^ i) ≤ r * 2 ^ i * Real.exp (r * 2 ^ k) := by
    intro i hi
    refine (expm1_le_mul_exp _).trans ?_
    have hi' : (2 : ℝ) ^ i ≤ 2 ^ k :=
      pow_le_pow_right₀ (by norm_num) (mem_range.mp hi).le
    gcongr
  calc ∑ i ∈ range k, expm1 (r * 2 ^ i) ≤ ∑ i ∈ range k, r * 2 ^ i * Real.exp (r * 2 ^ k) :=
        sum_le_sum hterm
    _ = r * Real.exp (r * 2 ^ k) * ∑ i ∈ range k, (2 : ℝ) ^ i := by
        rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ = r * Real.exp (r * 2 ^ k) * (2 ^ k - 1) := by
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; ring
    _ ≤ r * 2 ^ k * Real.exp (r * 2 ^ k) := by nlinarith [Real.exp_pos (r * 2 ^ k)]

/-- Exercise 4.8: starting the `expm1` doubling chain from `expm1 r (1 + ε)`, the relative error
after `k` steps is at most `|ε| ∏_{i<k} (1 + expm1(r 2^i))`, provided this bound is `≤ 1`. -/
theorem expm1DoublingSeq_relError {r ε : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (hbound : |ε| * ∏ i ∈ range k, (1 + expm1 (r * 2 ^ i)) ≤ 1) :
    ∃ ε' : ℝ, expm1DoublingSeq (expm1 r * (1 + ε)) k = expm1 (r * 2 ^ k) * (1 + ε')
      ∧ |ε'| ≤ |ε| * ∏ i ∈ range k, (1 + expm1 (r * 2 ^ i)) := by
  have hpos : ∀ j, 1 ≤ ∏ i ∈ range j, (1 + expm1 (r * 2 ^ i)) := fun j =>
    one_le_prod₀ fun i _ => by
      have : 0 ≤ expm1 (r * 2 ^ i) := by
        unfold expm1; linarith [Real.one_le_exp_iff.mpr (by positivity : (0 : ℝ) ≤ r * 2 ^ i)]
      linarith
  have hmono : ∀ j ≤ k, ∏ i ∈ range j, (1 + expm1 (r * 2 ^ i))
      ≤ ∏ i ∈ range k, (1 + expm1 (r * 2 ^ i)) := fun j hj =>
    prod_le_prod_of_subset_of_one_le₀ (range_subset_range.mpr hj)
      (fun i _ => by
        have : 0 ≤ expm1 (r * 2 ^ i) := by
          unfold expm1; linarith [Real.one_le_exp_iff.mpr (by positivity : (0 : ℝ) ≤ r * 2 ^ i)]
        linarith)
      fun i _ _ => by
        have : 0 ≤ expm1 (r * 2 ^ i) := by
          unfold expm1; linarith [Real.one_le_exp_iff.mpr (by positivity : (0 : ℝ) ≤ r * 2 ^ i)]
        linarith
  -- induction with the invariant `|ε_j| ≤ |ε| ∏_{i<j}`
  suffices h : ∀ j ≤ k, ∃ ε' : ℝ, expm1DoublingSeq (expm1 r * (1 + ε)) j
      = expm1 (r * 2 ^ j) * (1 + ε') ∧ |ε'| ≤ |ε| * ∏ i ∈ range j, (1 + expm1 (r * 2 ^ i)) from
    h k le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨ε, by simp [expm1DoublingSeq], by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨ε', heq, hle⟩ := ih (by omega)
    have hε'1 : |ε'| ≤ 1 := hle.trans ((mul_le_mul_of_nonneg_left (hmono j (by omega))
      (abs_nonneg ε)).trans hbound)
    have hx : 0 ≤ r * 2 ^ j := by positivity
    refine ⟨ε' * (2 * (expm1 (r * 2 ^ j) + 1) + expm1 (r * 2 ^ j) * ε') / (expm1 (r * 2 ^ j) + 2),
      ?_, ?_⟩
    · rw [expm1DoublingSeq, heq, expm1_two_mul_perturbed]
      congr 2
      ring
    · refine (abs_expm1_relError_step_le hx hε'1).trans ?_
      rw [prod_range_succ, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hle (by
        linarith [Real.one_le_exp_iff.mpr hx, show expm1 (r * 2 ^ j) = Real.exp (r * 2 ^ j) - 1
          from rfl])

end Exercise48

section Exercise49

/-- `log1p x = ln(1 + x)`. -/
noncomputable def log1p (x : ℝ) : ℝ := Real.log (1 + x)

/-- The reduced argument in cancellation-free form: `x/(1 + √(1+x)) = √(1+x) − 1`. -/
theorem div_one_add_sqrt_eq {x : ℝ} (hx : -1 < x) :
    x / (1 + Real.sqrt (1 + x)) = Real.sqrt (1 + x) - 1 := by
  have h1 : 0 ≤ 1 + x := by linarith
  have hs2 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1
  rw [div_eq_iff (by positivity)]
  linear_combination -hs2

/-- Exercise 4.9: `log1p x = 2 log1p (x/(1 + √(1+x)))` for `x > −1`. -/
theorem log1p_reduction {x : ℝ} (hx : -1 < x) :
    log1p x = 2 * log1p (x / (1 + Real.sqrt (1 + x))) := by
  rw [div_one_add_sqrt_eq hx]
  unfold log1p
  have h1 : 0 < 1 + x := by linarith
  rw [show (1 : ℝ) + (Real.sqrt (1 + x) - 1) = Real.sqrt (1 + x) by ring]
  calc Real.log (1 + x) = Real.log (Real.sqrt (1 + x) ^ 2) := by rw [Real.sq_sqrt h1.le]
    _ = 2 * Real.log (Real.sqrt (1 + x)) := by rw [Real.log_pow]; norm_num

/-- The reduced argument is at most half the original (for `x ≥ 0`). -/
theorem sqrt_sub_one_le_half {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (1 + x) - 1 ≤ x / 2 := by
  have : Real.sqrt (1 + x) ≤ 1 + x / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  linarith

theorem one_le_sqrt_one_add {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Real.sqrt (1 + x) := by
  rw [Real.le_sqrt zero_le_one (by positivity)]
  linarith

/-- The reduction does not amplify relative errors: for `0 < x ≤ y`,
`(r(y) − r(x))/r(x) ≤ (y − x)/x` with `r(x) = √(1+x) − 1`. -/
theorem reduced_relError_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ((Real.sqrt (1 + y) - 1) - (Real.sqrt (1 + x) - 1)) / (Real.sqrt (1 + x) - 1)
      ≤ (y - x) / x := by
  set A := Real.sqrt (1 + y) with hA
  set B := Real.sqrt (1 + x) with hB
  have hA2 : A ^ 2 = 1 + y := Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hB1 : 1 < B := by
    rw [hB, Real.lt_sqrt zero_le_one]
    linarith
  have hAB : B ≤ A := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_div_iff₀ (by linarith) hx]
  -- `(A − B) x ≤ (y − x)(B − 1)`, with `x = B² − 1 = (B−1)(B+1)` and `y − x = (A−B)(A+B)`
  have hx' : x = (B - 1) * (B + 1) := by linear_combination -hB2
  have hyx : y - x = (A - B) * (A + B) := by linear_combination hB2 - hA2
  rw [hyx, hx']
  have h0 : 0 ≤ (A - B) * (B - 1) * (A - 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hB1.le))
      (sub_nonneg.mpr (hB1.le.trans hAB))
  nlinarith [h0]

/-- Forming `y − 1` from a rounded `y(1 + ε)` turns the relative error `ε` into `ε·y/(y − 1)`:
for `y = 1 + x` with small `x`, a loss of `−log₂ x` bits. -/
theorem relError_sub_one {y ε : ℝ} (hy : y ≠ 1) :
    ((y * (1 + ε) - 1) - (y - 1)) / (y - 1) = ε * (y / (y - 1)) := by
  have : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  field_simp
  ring

end Exercise49

section Exercise410

/-- `sinh |x|` as a function of `u = expm1 |x|`: `u(2 + u)/(2(1 + u))`. -/
noncomputable def sinhExpm1 (u : ℝ) : ℝ := u * (2 + u) / (2 * (1 + u))

/-- `sinh x = u(2 + u)/(2(1 + u))` with `u = expm1 x`; valid for every `x`. -/
theorem sinh_eq_sinhExpm1 (x : ℝ) : Real.sinh x = sinhExpm1 (expm1 x) := by
  unfold sinhExpm1 expm1
  have he : 0 < Real.exp x := Real.exp_pos x
  rw [Real.sinh_eq, Real.exp_neg, show (1 : ℝ) + (Real.exp x - 1) = Real.exp x by ring]
  field_simp
  ring

/-- The cancellation-free arrangement: `(u + u/(1 + u))/2`. -/
theorem sinhExpm1_eq {u : ℝ} (hu : 0 ≤ u) : sinhExpm1 u = (u + u / (1 + u)) / 2 := by
  unfold sinhExpm1
  have : (1 : ℝ) + u ≠ 0 := by positivity
  field_simp
  ring

theorem sinhExpm1_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ sinhExpm1 u := by
  unfold sinhExpm1; positivity

/-- Exercise 4.10: `sinh x = ±sinh |x|`, and `sinh |x| = sinhExpm1 (expm1 |x|)` with
`expm1 |x| ≥ 0`. -/
theorem sinh_eq_sign_mul_sinh_abs (x : ℝ) :
    Real.sinh x = (if 0 ≤ x then 1 else -1) * sinhExpm1 (expm1 |x|) := by
  rw [← sinh_eq_sinhExpm1]
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · rw [abs_of_neg (not_le.mp h), Real.sinh_neg]; ring

theorem expm1_abs_nonneg (x : ℝ) : 0 ≤ expm1 |x| := by
  unfold expm1; linarith [Real.one_le_exp_iff.mpr (abs_nonneg x)]

/-- `cosh x = 1 + u²/(2(1 + u))` with `u = expm1 x`. -/
theorem cosh_eq_expm1 (x : ℝ) : Real.cosh x = 1 + expm1 x ^ 2 / (2 * (1 + expm1 x)) := by
  unfold expm1
  have he : 0 < Real.exp x := Real.exp_pos x
  rw [Real.cosh_eq, Real.exp_neg, show (1 : ℝ) + (Real.exp x - 1) = Real.exp x by ring]
  field_simp
  ring

/-- Monotonicity in the form `u · sinhExpm1 v ≤ v · sinhExpm1 u` for `0 ≤ u ≤ v`: the relative
growth of the formula is at most that of its argument. -/
theorem mul_sinhExpm1_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u * sinhExpm1 v ≤ v * sinhExpm1 u := by
  unfold sinhExpm1
  have hv : 0 ≤ v := hu.trans huv
  rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hu (sub_nonneg.mpr huv), mul_nonneg (mul_nonneg hu hu) (sub_nonneg.mpr huv),
    mul_nonneg (mul_nonneg hu (hu.trans huv)) (sub_nonneg.mpr huv)]

theorem sinhExpm1_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : sinhExpm1 u ≤ sinhExpm1 v := by
  rw [sinhExpm1_eq hu, sinhExpm1_eq (hu.trans huv)]
  have h1 : u / (1 + u) ≤ v / (1 + v) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  linarith

/-- The `sinh` formula is well conditioned in `u`: for `0 < u ≤ v`,
`0 ≤ (sinhExpm1 v − sinhExpm1 u)/sinhExpm1 u ≤ (v − u)/u`. -/
theorem sinhExpm1_relError_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    0 ≤ (sinhExpm1 v - sinhExpm1 u) / sinhExpm1 u ∧
      (sinhExpm1 v - sinhExpm1 u) / sinhExpm1 u ≤ (v - u) / u := by
  have hf : 0 < sinhExpm1 u := by unfold sinhExpm1; positivity
  refine ⟨div_nonneg (sub_nonneg.mpr (sinhExpm1_mono hu.le huv)) hf.le, ?_⟩
  rw [div_le_div_iff₀ hf hu]
  nlinarith [mul_sinhExpm1_le hu.le huv]

end Exercise410

section Exercise411

/-- White's formula: `exp x = sinh x + √(1 + sinh² x)`. -/
theorem exp_eq_sinh_add_sqrt (x : ℝ) :
    Real.exp x = Real.sinh x + Real.sqrt (1 + Real.sinh x ^ 2) := by
  rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos x).le, Real.sinh_add_cosh]

/-- The odd part of the exponential series: `sinh x = ∑ x^(2k+1)/(2k+1)!`. -/
theorem hasSum_sinh_series (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) (Real.sinh x) := by
  have h : HasSum (fun n : ℕ => (x ^ n / (n.factorial : ℝ) - (-x) ^ n / (n.factorial : ℝ)) / 2)
      (Real.sinh x) := by
    rw [Real.sinh_eq]
    exact ((hasSum_exp_series x).sub (hasSum_exp_series (-x))).div_const 2
  have hg : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by
    simp only at hab; omega
  rw [← hg.hasSum_iff] at h
  · convert h using 1
    ext k
    simp only [Function.comp]
    rw [Odd.neg_pow ⟨k, rfl⟩]
    ring
  · intro n hn
    obtain ⟨m, hm⟩ : Even n := by
      rcases Nat.even_or_odd n with h | ⟨k, hk⟩
      · exact h
      · exact absurd ⟨k, hk.symm⟩ hn
    rw [Even.neg_pow ⟨m, hm⟩]
    ring

/-- The same series organised in powers of `x²`: `sinh x = x ∑ (x²)^k/(2k+1)!`. -/
theorem hasSum_sinh_series' (x : ℝ) :
    HasSum (fun k : ℕ => x * (x ^ 2) ^ k / ((2 * k + 1).factorial : ℝ)) (Real.sinh x) := by
  convert hasSum_sinh_series x using 1
  ext k
  rw [pow_succ x (2 * k), pow_mul]
  ring

/-- The cancelling difference for negative arguments: `√(1 + s²) − s = 1/(s + √(1 + s²))`. -/
theorem sqrt_sub_eq_inv (s : ℝ) :
    Real.sqrt (1 + s ^ 2) - s = 1 / (s + Real.sqrt (1 + s ^ 2)) := by
  have hs2 : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < s + Real.sqrt (1 + s ^ 2) := by
    have : |s| < Real.sqrt (1 + s ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg s), sq_abs]; linarith
    linarith [neg_abs_le s]
  rw [eq_div_iff hpos.ne']
  linear_combination hs2

/-- The stable form for every sign: `exp x = 1/(sinh |x| + √(1 + sinh² |x|))` for `x ≤ 0`. -/
theorem exp_eq_inv_sinh_abs_add_sqrt {x : ℝ} (hx : x ≤ 0) :
    Real.exp x = 1 / (Real.sinh |x| + Real.sqrt (1 + Real.sinh |x| ^ 2)) := by
  rw [abs_of_nonpos hx, Real.sinh_neg, ← sqrt_sub_eq_inv, neg_sq, sub_neg_eq_add,
    exp_eq_sinh_add_sqrt]
  ring

/-- `s ↦ s + √(1 + s²)` does not amplify relative errors for `s ≥ 0`: for `0 < s ≤ t`,
`(f t − f s)/f s ≤ (t − s)/s`. -/
theorem sinh_add_sqrt_relError_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ((t + Real.sqrt (1 + t ^ 2)) - (s + Real.sqrt (1 + s ^ 2))) / (s + Real.sqrt (1 + s ^ 2))
      ≤ (t - s) / s := by
  have hS : 0 < s + Real.sqrt (1 + s ^ 2) := by positivity
  rw [div_le_div_iff₀ hS hs]
  -- reduces to `s √(1 + t²) ≤ t √(1 + s²)`, i.e. `s²(1 + t²) ≤ t²(1 + s²)`
  have key : s * Real.sqrt (1 + t ^ 2) ≤ t * Real.sqrt (1 + s ^ 2) := by
    rw [← Real.sqrt_sq hs.le, ← Real.sqrt_sq (hs.le.trans hst), ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le, Real.sqrt_sq (hs.le.trans hst)]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hst)]
  nlinarith [key]

/-- Another even/odd pair: `exp x = (1 + tanh(x/2))/(1 − tanh(x/2))`. -/
theorem exp_eq_tanh_half (x : ℝ) :
    Real.exp x = (1 + Real.tanh (x / 2)) / (1 - Real.tanh (x / 2)) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : 0 < Real.cosh (x / 2) := Real.cosh_pos _
  have h1 : (1 : ℝ) - Real.sinh (x / 2) / Real.cosh (x / 2) ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq hc.ne']
    exact fun h => by linarith [Real.sinh_lt_cosh (x / 2)]
  rw [eq_div_iff h1]
  have hce : Real.cosh (x / 2) + Real.sinh (x / 2) = Real.exp (x / 2) := Real.cosh_add_sinh _
  have h2 : (Real.cosh (x / 2) + Real.sinh (x / 2)) * (Real.cosh (x / 2) - Real.sinh (x / 2))
      = 1 := by linear_combination Real.cosh_sq' (x / 2)
  have hx : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; ring_nf
  field_simp
  rw [hx, ← hce]
  linear_combination (Real.cosh (x / 2) + Real.sinh (x / 2)) * h2

end Exercise411

section Exercise412

universe u

/-- A value together with the numbers of general non-scalar products and of squarings spent
computing it. Scalar products and additions are free. -/
structure Counted (α : Type u) where
  /-- The computed value. -/
  val : α
  /-- General non-scalar products. -/
  mul : ℕ
  /-- Squarings. -/
  sq : ℕ

namespace Counted

variable {α β : Type u}

/-- Sequencing adds up the costs. -/
protected def bind (m : Counted α) (f : α → Counted β) : Counted β :=
  ⟨(f m.val).val, m.mul + (f m.val).mul, m.sq + (f m.val).sq⟩

instance : Monad Counted where
  pure a := ⟨a, 0, 0⟩
  bind := Counted.bind

@[simp] theorem val_pure (a : α) : (pure a : Counted α).val = a := rfl
@[simp] theorem mul_pure (a : α) : (pure a : Counted α).mul = 0 := rfl
@[simp] theorem sq_pure (a : α) : (pure a : Counted α).sq = 0 := rfl
@[simp] theorem val_bind (m : Counted α) (f : α → Counted β) : (m >>= f).val = (f m.val).val := rfl
@[simp] theorem mul_bind (m : Counted α) (f : α → Counted β) :
    (m >>= f).mul = m.mul + (f m.val).mul := rfl
@[simp] theorem sq_bind (m : Counted α) (f : α → Counted β) :
    (m >>= f).sq = m.sq + (f m.val).sq := rfl

/-- A general non-scalar product. -/
def nsMul [Mul α] (a b : α) : Counted α := ⟨a * b, 1, 0⟩

/-- A squaring. -/
def nsSq [Monoid α] (a : α) : Counted α := ⟨a ^ 2, 0, 1⟩

@[simp] theorem val_nsMul [Mul α] (a b : α) : (nsMul a b).val = a * b := rfl
@[simp] theorem mul_nsMul [Mul α] (a b : α) : (nsMul a b).mul = 1 := rfl
@[simp] theorem sq_nsMul [Mul α] (a b : α) : (nsMul a b).sq = 0 := rfl
@[simp] theorem val_nsSq [Monoid α] (a : α) : (nsSq a).val = a ^ 2 := rfl
@[simp] theorem mul_nsSq [Monoid α] (a : α) : (nsSq a).mul = 0 := rfl
@[simp] theorem sq_nsSq [Monoid α] (a : α) : (nsSq a).sq = 1 := rfl

end Counted

open Counted Finset

variable {α : Type*} [CommSemiring α]

/-- The table `[x^0, x^1, …, x^k]`: even powers by squaring, odd ones by one product with `x`. -/
def powersC (x : α) : ℕ → Counted (List α)
  | 0 => pure [1]
  | 1 => pure [1, x]
  | m + 2 => do
    let L ← powersC x (m + 1)
    let p ← if (m + 2) % 2 = 0 then nsSq (L.getD ((m + 2) / 2) 0) else nsMul (L.getD (m + 1) 0) x
    pure (L ++ [p])

theorem powersC_length (x : α) (k : ℕ) : (powersC x k).val.length = k + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      simp only [powersC, val_bind]
      split_ifs <;> simp [List.length_append, ih (m + 1) (by omega)]

theorem powersC_getD (x : α) (k : ℕ) : ∀ i ≤ k, (powersC x k).val.getD i 0 = x ^ i := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro i hi; obtain rfl : i = 0 := (by omega); simp [powersC]
    | 1 =>
      intro i hi
      interval_cases i <;> simp [powersC]
    | m + 2 =>
      intro i hi
      have hlen := powersC_length x (m + 1)
      simp only [powersC, val_bind, val_pure, apply_ite Counted.val, val_nsSq, val_nsMul]
      rcases Nat.lt_or_ge i (m + 2) with h | h
      · split_ifs <;>
          (rw [List.getD_append _ _ _ _ (by omega)]; exact ih (m + 1) (by omega) i (by omega))
      · obtain rfl : i = m + 2 := (by omega)
        split_ifs with he
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [ih (m + 1) (by omega) _ (by omega), ← pow_mul]
          congr 1; omega
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [ih (m + 1) (by omega) _ (by omega), ← pow_succ]

theorem powersC_sq (x : α) (k : ℕ) : (powersC x k).sq = k / 2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      simp only [powersC, sq_bind, sq_pure, apply_ite Counted.sq, sq_nsSq, sq_nsMul,
        ih (m + 1) (by omega)]
      split_ifs with he <;> omega

theorem powersC_mul (x : α) (k : ℕ) : (powersC x k).mul = (k + 1) / 2 - 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      simp only [powersC, mul_bind, mul_pure, apply_ite Counted.mul, mul_nsSq, mul_nsMul,
        ih (m + 1) (by omega)]
      split_ifs with he <;> omega

/-- Horner's rule on `n + 1` coefficients: `c_0 + y(c_1 + y(… + y c_n))`, `n` products. -/
def hornerC (c : ℕ → α) (y : α) : ℕ → Counted α
  | 0 => pure (c 0)
  | n + 1 => do
    let r ← hornerC (fun i => c (i + 1)) y n
    let p ← nsMul y r
    pure (c 0 + p)

theorem hornerC_val (c : ℕ → α) (y : α) (n : ℕ) :
    (hornerC c y n).val = ∑ i ∈ range (n + 1), c i * y ^ i := by
  induction n generalizing c with
  | zero => simp [hornerC]
  | succ n ih =>
    simp only [hornerC, val_bind, val_nsMul, val_pure, ih]
    rw [sum_range_succ' (fun i => c i * y ^ i) (n + 1), pow_zero, mul_one, mul_sum, add_comm (c 0)]
    congr 1
    exact sum_congr rfl fun i _ => by ring

theorem hornerC_mul (c : ℕ → α) (y : α) (n : ℕ) : (hornerC c y n).mul = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [hornerC, ih]

theorem hornerC_sq (c : ℕ → α) (y : α) (n : ℕ) : (hornerC c y n).sq = 0 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [hornerC, ih]

/-- Binary powering `x^j`: a squaring per bit after the leading one, a product per further
one-bit. -/
def binPowC (x : α) : ℕ → Counted α
  | 0 => pure 1
  | 1 => pure x
  | j + 2 => do
    let h ← binPowC x ((j + 2) / 2)
    let s ← nsSq h
    if (j + 2) % 2 = 1 then nsMul s x else pure s
  decreasing_by omega

theorem binPowC_val (x : α) (j : ℕ) : (binPowC x j).val = x ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp [binPowC]
    | 1 => simp [binPowC]
    | j + 2 =>
      rw [binPowC]
      simp only [val_bind, val_nsSq, ih ((j + 2) / 2) (by omega)]
      split_ifs with he
      · simp only [val_nsMul]
        rw [← pow_mul, ← pow_succ]
        congr 1; omega
      · simp only [val_pure]
        rw [← pow_mul]
        congr 1; omega

theorem binPowC_sq (x : α) (j : ℕ) : (binPowC x j).sq = Nat.log 2 j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp [binPowC]
    | 1 => simp [binPowC]
    | j + 2 =>
      rw [binPowC]
      have h1 : 0 < Nat.log 2 (j + 2) := Nat.log_pos (by norm_num) (by omega)
      have h2 := Nat.log_div_base 2 (j + 2)
      simp only [sq_bind, sq_nsSq, ih ((j + 2) / 2) (by omega)]
      split_ifs <;> simp only [sq_nsMul, sq_pure] <;> omega

/-- The products of binary powering: one fewer than the number of one-bits of `j`. -/
theorem binPowC_mul (x : α) {j : ℕ} (hj : 0 < j) :
    (binPowC x j).mul + 1 = (Nat.digits 2 j).sum := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => omega
    | 1 => simp [binPowC]
    | j + 2 =>
      rw [binPowC, Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
      have := ih ((j + 2) / 2) (by omega) (by omega)
      simp only [mul_bind, mul_nsSq]
      split_ifs with he <;> simp only [mul_nsMul, mul_pure] <;> omega

/-- The classical splitting in the counting monad: the table `x^0, …, x^k`, the inner polynomials
by scalar products against it, and Horner in `y = x^k` over the `j` inner values. -/
def classicalEvalC (a : ℕ → α) (j k : ℕ) (x : α) : Counted α := do
  let T ← powersC x k
  hornerC (fun ℓ => ∑ m ∈ range k, a (k * ℓ + m) * T.getD m 0) (T.getD k 0) (j - 1)

theorem classicalEvalC_val (a : ℕ → α) {j : ℕ} (hj : 0 < j) (k : ℕ) (x : α) :
    (classicalEvalC a j k x).val = polyEval a (j * k) x := by
  simp only [classicalEvalC, val_bind, hornerC_val, powersC_getD x k k le_rfl]
  rw [polyEval_split, show j - 1 + 1 = j by omega]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [mul_comm, innerPoly]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  rw [powersC_getD x k m (by simpa using (mem_range.mp hm).le)]

theorem classicalEvalC_mul (a : ℕ → α) (j k : ℕ) (x : α) :
    (classicalEvalC a j k x).mul = ((k + 1) / 2 - 1) + (j - 1) := by
  simp [classicalEvalC, hornerC_mul, powersC_mul]

theorem classicalEvalC_sq (a : ℕ → α) (j k : ℕ) (x : α) :
    (classicalEvalC a j k x).sq = k / 2 := by
  simp [classicalEvalC, hornerC_sq, powersC_sq]

/-- Classical splitting: `j + k − 2` non-scalar products in all (`j, k ≥ 1`). -/
theorem classicalEvalC_total (a : ℕ → α) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) (x : α) :
    (classicalEvalC a j k x).mul + (classicalEvalC a j k x).sq = j + k - 2 := by
  rw [classicalEvalC_mul, classicalEvalC_sq]; omega

/-- The modular splitting in the counting monad: `y = x^j` by binary powering, the table
`y^0, …, y^(k−1)`, the row sums by scalar products, and Horner in `x` over the `j` rows. -/
def modularEvalC (a : ℕ → α) (j k : ℕ) (x : α) : Counted α := do
  let y ← binPowC x j
  let T ← powersC y (k - 1)
  hornerC (fun ℓ => ∑ m ∈ range k, a (j * m + ℓ) * T.getD m 0) x (j - 1)

theorem modularEvalC_val (a : ℕ → α) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) (x : α) :
    (modularEvalC a j k x).val = polyEval a (j * k) x := by
  simp only [modularEvalC, val_bind, hornerC_val, binPowC_val]
  rw [polyEval_modular_split, show j - 1 + 1 = j by omega]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [mul_comm, modularPoly]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  rw [powersC_getD _ (k - 1) m (by have := mem_range.mp hm; omega)]

theorem modularEvalC_sq (a : ℕ → α) (j k : ℕ) (x : α) :
    (modularEvalC a j k x).sq = Nat.log 2 j + (k - 1) / 2 := by
  simp [modularEvalC, hornerC_sq, powersC_sq, binPowC_sq]

theorem modularEvalC_mul (a : ℕ → α) {j : ℕ} (hj : 0 < j) (k : ℕ) (x : α) :
    (modularEvalC a j k x).mul + 1 = (Nat.digits 2 j).sum + (k / 2 - 1) + (j - 1) := by
  simp only [modularEvalC, mul_bind, hornerC_mul, powersC_mul]
  have := binPowC_mul x hj
  omega

/-- Modular splitting: `j + k − 3 + ℓ(j)` non-scalar products in all (`j ≥ 1`, `k ≥ 2`), where
`ℓ(j) = ⌊log₂ j⌋ + popcount(j) − 1` is the length of the binary addition chain for `x^j`. -/
theorem modularEvalC_total (a : ℕ → α) {j k : ℕ} (hj : 0 < j) (hk : 2 ≤ k) (x : α) :
    (modularEvalC a j k x).mul + (modularEvalC a j k x).sq
      = (Nat.log 2 j + (Nat.digits 2 j).sum - 1) + (k - 2) + (j - 1) := by
  have h1 := modularEvalC_mul a hj k x
  have h2 := modularEvalC_sq a j k x
  have h3 := binPowC_mul x hj
  omega

/-- The binary addition chain never beats repeated multiplication's `j − 1` by a negative
amount: `⌊log₂ j⌋ + popcount(j) ≤ j`. -/
theorem log_add_digits_sum_le (j : ℕ) : Nat.log 2 j + (Nat.digits 2 j).sum ≤ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp
    | 1 => simp
    | j + 2 =>
      have h1 : 0 < Nat.log 2 (j + 2) := Nat.log_pos (by norm_num) (by omega)
      have h2 := Nat.log_div_base 2 (j + 2)
      rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
      have := ih ((j + 2) / 2) (by omega)
      omega

theorem binPowC_total_le (x : α) {j : ℕ} (hj : 0 < j) :
    (binPowC x j).mul + (binPowC x j).sq ≤ j - 1 := by
  have h1 := binPowC_mul x hj
  have h2 := binPowC_sq x j
  have h3 := log_add_digits_sum_le j
  omega

/-- The derived modular count is at most the `(j − 1) + (k − 2) + (j − 1)` of
`modularNonscalar` (which powers `x^j` naively), and exceeds the classical count by
`ℓ(j) − 1 ≤ 2⌊log₂ j⌋ − 1 = O(log d)`: "almost the same". -/
theorem modularEvalC_total_le (a : ℕ → α) {j k : ℕ} (hj : 0 < j) (hk : 2 ≤ k) (x : α) :
    (modularEvalC a j k x).mul + (modularEvalC a j k x).sq ≤ modularNonscalar j k := by
  rw [modularEvalC_total a hj hk, modularNonscalar]
  have := log_add_digits_sum_le j
  omega

/-- `popcount(j) ≤ ⌊log₂ j⌋ + 1`, so `ℓ(j) ≤ 2⌊log₂ j⌋`. -/
theorem digits_sum_le_log_add_one {j : ℕ} (hj : 0 < j) :
    (Nat.digits 2 j).sum ≤ Nat.log 2 j + 1 := by
  have hlen : (Nat.digits 2 j).length = Nat.log 2 j + 1 :=
    Nat.length_digits 2 j (by norm_num) hj.ne'
  calc (Nat.digits 2 j).sum ≤ (Nat.digits 2 j).length • 1 :=
        List.sum_le_length_nsmul _ _ fun d hd =>
          Nat.lt_succ_iff.mp (Nat.digits_lt_base (by norm_num) hd)
    _ = Nat.log 2 j + 1 := by rw [hlen, smul_eq_mul, mul_one]

/-- The example `d = 12 = 3 · 4`: classical `5` (one product `x³`, two squarings `x², x⁴`, two
Horner products), modular `6` (`x³`: one squaring and one product; `y², y³`: one squaring and one
product; two Horner products). -/
theorem splitting_example (a : ℕ → α) (x : α) :
    (classicalEvalC a 3 4 x).mul = 3 ∧ (classicalEvalC a 3 4 x).sq = 2 ∧
      (modularEvalC a 3 4 x).mul = 4 ∧ (modularEvalC a 3 4 x).sq = 2 := by
  have hlog : Nat.log 2 3 = 1 := by
    rw [Nat.log_eq_iff (by norm_num)]; norm_num
  have hdig : (Nat.digits 2 3).sum = 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [classicalEvalC_mul]
  · rw [classicalEvalC_sq]
  · have := modularEvalC_mul a (by norm_num : 0 < 3) 4 x; omega
  · rw [modularEvalC_sq, hlog]

end Exercise412

section Exercise413

open Counted Finset

variable {α : Type*} [CommSemiring α]

/-- Horner's rule in the ratio direction: `ratioHorner r pw k = pw 0 + r 0 (pw 1 + r 1 (⋯ + r_{k−2}
pw_{k−1}))`, so that with `pw m = x^m` and `r i = a_{i+1}/a_i` it is `∑_{m<k} a_m x^m / a_0` using
only the small multipliers `r i`. -/
def ratioHorner (r pw : ℕ → α) : ℕ → α
  | 0 => 0
  | k + 1 => pw 0 + r 0 * ratioHorner (fun i => r (i + 1)) (fun i => pw (i + 1)) k

theorem ratioHorner_eq (r pw : ℕ → α) (k : ℕ) :
    ratioHorner r pw k = ∑ m ∈ range k, pw m * ∏ i ∈ range m, r i := by
  induction k generalizing r pw with
  | zero => simp [ratioHorner]
  | succ k ih =>
    rw [ratioHorner, ih, sum_range_succ', prod_range_zero, mul_one, add_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [prod_range_succ']
    ring

/-- Coefficients with ratios `r`: `a_i = a_0 ∏_{i'<i} r_{i'}`. -/
theorem coeff_eq_prod_ratio {a r : ℕ → α} (ha : ∀ i, a (i + 1) = r i * a i) (i : ℕ) :
    a i = a 0 * ∏ i' ∈ range i, r i' := by
  induction i with
  | zero => simp
  | succ i ih => rw [ha, ih, prod_range_succ]; ring

theorem coeff_shift_eq_prod_ratio {a r : ℕ → α} (ha : ∀ i, a (i + 1) = r i * a i) (n m : ℕ) :
    a (n + m) = a n * ∏ i ∈ range m, r (n + i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, ha, ih, prod_range_succ]; ring

/-- The inner polynomial of the classical splitting via the ratio Horner rule. -/
theorem innerPoly_eq_ratioHorner {a r : ℕ → α} (ha : ∀ i, a (i + 1) = r i * a i) (k ℓ : ℕ)
    (x : α) :
    innerPoly a k ℓ x = a (k * ℓ) * ratioHorner (fun i => r (k * ℓ + i)) (fun m => x ^ m) k := by
  rw [ratioHorner_eq, innerPoly, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_shift_eq_prod_ratio ha]; ring

/-- Horner in `y` with a block ratio `R ℓ` applied at each step:
`c 0 + R 0 · y (c 1 + R 1 · y (⋯))`; `n` non-scalar products for `n + 1` blocks. -/
def scaledHornerC (c R : ℕ → α) (y : α) : ℕ → Counted α
  | 0 => pure (c 0)
  | n + 1 => do
    let w ← scaledHornerC (fun i => c (i + 1)) (fun i => R (i + 1)) y n
    let p ← nsMul y w
    pure (c 0 + R 0 * p)

theorem scaledHornerC_val (c R : ℕ → α) (y : α) (n : ℕ) :
    (scaledHornerC c R y n).val = ∑ ℓ ∈ range (n + 1), c ℓ * y ^ ℓ * ∏ i ∈ range ℓ, R i := by
  induction n generalizing c R with
  | zero => simp [scaledHornerC]
  | succ n ih =>
    simp only [scaledHornerC, val_bind, val_nsMul, val_pure, ih]
    rw [sum_range_succ' (fun ℓ => c ℓ * y ^ ℓ * ∏ i ∈ range ℓ, R i) (n + 1), pow_zero, mul_one,
      prod_range_zero, mul_one, mul_sum, mul_sum, add_comm (c 0)]
    congr 1
    refine sum_congr rfl fun ℓ _ => ?_
    rw [prod_range_succ']
    ring

theorem scaledHornerC_mul (c R : ℕ → α) (y : α) (n : ℕ) : (scaledHornerC c R y n).mul = n := by
  induction n generalizing c R with
  | zero => rfl
  | succ n ih => simp [scaledHornerC, ih]

theorem scaledHornerC_sq (c R : ℕ → α) (y : α) (n : ℕ) : (scaledHornerC c R y n).sq = 0 := by
  induction n generalizing c R with
  | zero => rfl
  | succ n ih => simp [scaledHornerC, ih]

/-- Exercise 4.13: classical splitting driven by the ratios `r`. The powers `x⁰, …, x^k` are
computed as before; each inner value `U_ℓ = P_ℓ(x)/a_{kℓ}` is the ratio Horner rule over the stored
powers with the single ratios `r_{kℓ+i}` as multipliers; the outer Horner in `y = x^k` multiplies by
the block ratios `a_{k(ℓ+1)}/a_{kℓ} = ∏_{i<k} r_{kℓ+i}`, and the result is scaled by `a_0`. -/
def ratioEvalC (r : ℕ → α) (a0 : α) (j k : ℕ) (x : α) : Counted α := do
  let T ← powersC x k
  let w ← scaledHornerC (fun ℓ => ratioHorner (fun i => r (k * ℓ + i)) (fun m => T.getD m 0) k)
    (fun ℓ => ∏ i ∈ range k, r (k * ℓ + i)) (T.getD k 0) (j - 1)
  pure (a0 * w)

theorem prod_range_mul_eq (f : ℕ → α) (k ℓ : ℕ) :
    ∏ i ∈ range ℓ, ∏ i' ∈ range k, f (k * i + i') = ∏ i' ∈ range (k * ℓ), f i' := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [prod_range_succ, ih, Nat.mul_succ, prod_range_add]

theorem ratioEvalC_val {a r : ℕ → α} (ha : ∀ i, a (i + 1) = r i * a i) {j : ℕ} (hj : 0 < j)
    (k : ℕ) (x : α) : (ratioEvalC r (a 0) j k x).val = polyEval a (j * k) x := by
  simp only [ratioEvalC, val_bind, val_pure, scaledHornerC_val, powersC_getD x k k le_rfl]
  rw [polyEval_split, show j - 1 + 1 = j by omega, mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  have hU : ratioHorner (fun i => r (k * ℓ + i)) (fun m => (powersC x k).val.getD m 0) k
      = ratioHorner (fun i => r (k * ℓ + i)) (fun m => x ^ m) k := by
    rw [ratioHorner_eq, ratioHorner_eq]
    exact sum_congr rfl fun m hm => by
      rw [powersC_getD x k m (by have := mem_range.mp hm; omega)]
  rw [hU, innerPoly_eq_ratioHorner ha, coeff_eq_prod_ratio ha (k * ℓ), prod_range_mul_eq]
  ring

/-- The ratio-driven scheme has exactly the non-scalar cost of the classical splitting. -/
theorem ratioEvalC_mul (r : ℕ → α) (a0 : α) (j k : ℕ) (x : α) :
    (ratioEvalC r a0 j k x).mul = (classicalEvalC (fun _ => a0) j k x).mul := by
  simp [ratioEvalC, scaledHornerC_mul, powersC_mul, classicalEvalC_mul]

theorem ratioEvalC_sq (r : ℕ → α) (a0 : α) (j k : ℕ) (x : α) :
    (ratioEvalC r a0 j k x).sq = (classicalEvalC (fun _ => a0) j k x).sq := by
  simp [ratioEvalC, scaledHornerC_sq, powersC_sq, classicalEvalC_sq]

end Exercise413

section Exercise414

/-- Machine words needed for `b` bits with word size `w`: `⌈b/w⌉`. -/
def wordsOf (w b : ℕ) : ℕ := (b + w - 1) / w

theorem wordsOf_eq_one {w b : ℕ} (hw : 0 < w) (hb : 0 < b) (h : b ≤ w) : wordsOf w b = 1 := by
  unfold wordsOf
  refine le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hw).mpr (by omega))) ?_
  rw [Nat.le_div_iff_mul_le hw]
  omega

/-- `c(d)` for the ratio-driven splitting: the word length of the largest multiplier, an integer
`≤ d`. A scalar product of an `n`-bit number then costs `c(d) · n/w` word products. -/
def ratioScalarWords (w d : ℕ) : ℕ := wordsOf w (Nat.size d)

/-- `c(d)` with the raw coefficients `1/i!` of the exponential series. -/
def naiveScalarWords (w d : ℕ) : ℕ := wordsOf w (Nat.size (Nat.factorial d))

/-- The multipliers of the exponential series' ratios `1/(i + 1)`, `i < d`, fit in `size d`
bits. -/
theorem ratio_multiplier_size {i d : ℕ} (hi : i < d) : Nat.size (i + 1) ≤ Nat.size d :=
  Nat.size_le_size hi

/-- Exercise 4.14: with ratios, `c(d) = 1` word as long as `d < 2^w` (so for every `d` that
fits a machine word, e.g. `d < 2^64`); in bit terms `c(d) = size d = O(log d)`. -/
theorem ratioScalarWords_eq_one {w d : ℕ} (hw : 0 < w) (hd : 0 < d) (h : d < 2 ^ w) :
    ratioScalarWords w d = 1 :=
  wordsOf_eq_one hw (Nat.size_pos.mpr hd) (Nat.size_le.mpr h)

/-- Without ratios the coefficient `1/d!` has more than `(d/2) · log₂(d/2 + 1)` bits. -/
theorem size_factorial_gt (d : ℕ) :
    d / 2 * Nat.log 2 (d / 2 + 1) < Nat.size (Nat.factorial d) := by
  rw [Nat.lt_size, pow_mul']
  have h1 : 2 ^ Nat.log 2 (d / 2 + 1) ≤ d / 2 + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : (d / 2 + 1) ^ (d / 2) ≤ (d + 1 - d / 2) ^ (d / 2) :=
    Nat.pow_le_pow_left (by omega) _
  have h3 : (d + 1 - d / 2) ^ (d / 2) ≤ d.descFactorial (d / 2) :=
    Nat.pow_sub_le_descFactorial d (d / 2)
  have h4 : d.descFactorial (d / 2) ≤ Nat.factorial d := by
    rw [← Nat.factorial_mul_descFactorial (show d / 2 ≤ d by omega)]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  calc (2 ^ Nat.log 2 (d / 2 + 1)) ^ (d / 2) ≤ (d / 2 + 1) ^ (d / 2) := Nat.pow_le_pow_left h1 _
    _ ≤ Nat.factorial d := h2.trans (h3.trans h4)

/-- …and at most `d · (log₂ d + 1)` bits: `size(d!) = Θ(d log d)`. -/
theorem size_factorial_le {d : ℕ} (hd : 0 < d) :
    Nat.size (Nat.factorial d) ≤ d * (Nat.log 2 d + 1) := by
  rw [Nat.size_le, pow_mul']
  calc Nat.factorial d ≤ d ^ d := Nat.factorial_le_pow d
    _ < (2 ^ (Nat.log 2 d + 1)) ^ d :=
        Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) d) hd.ne'

end Exercise414

end BZ

end Azurite
