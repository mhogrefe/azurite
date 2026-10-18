/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AGMLogBound
import Azurite.BrentZimmermann.Chapter4.AsymptoticExpansion
import Azurite.BrentZimmermann.Chapter4.BernoulliRecurrence
import Azurite.BrentZimmermann.Chapter4.ContinuedFractionEval
import Azurite.BrentZimmermann.Chapter4.ContourIntegration
import Azurite.BrentZimmermann.Chapter4.DoublingTripling
import Azurite.BrentZimmermann.Chapter4.ErrorFunctionSeries
import Azurite.BrentZimmermann.Chapter4.FormalPowerSeries
import Azurite.BrentZimmermann.Chapter4.GuardDigits
import Azurite.BrentZimmermann.Chapter4.RectangularSplitting
import Azurite.BrentZimmermann.Chapter4.SecondAGMLog
import Azurite.BrentZimmermann.Chapter4.StirlingLogGamma
import Azurite.BrentZimmermann.Chapter4.TangentAlgorithm
import Azurite.BrentZimmermann.Chapter4.TangentNumbers
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Nat.Size
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

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

## Exercise 4.15

The remainder (4.28) of the expansion (4.27) of `E₁` was proven in `AsymptoticExpansion.lean`
exactly along the hint: `expTail_succ` is the integration by parts
`I_k(x) = e^(−x)/x^(k+1) − (k+1) I_{k+1}(x)`, `asymptoticRemainder_succ` turns it into
`R_k = t_k + R_{k+1}`, and `exp_mul_expIntegral_eq` is the induction on `k`. Added here: the
text's indexing `∑_{j=1}^k (j−1)! (−1)^(j−1)/x^j` (`exp_mul_expIntegral_eq_text`) and the strict
bound `|R_k(x)| < k!/x^(k+1)` of (4.28) (`expTail_lt`, `abs_asymptoticRemainder_lt`), from the
positivity of `I_{k+1}`.

## Exercise 4.16

`Ein z = ∑_{j≥1} (−1)^(j−1) z^j/(j! j)` (`Ein`, `EinTerm`) converges for every `z`
(`summable_EinTerm`, dominated by the exponential series) and is differentiable everywhere with
`Ein' z = (1 − e^(−z))/z`, `Ein' 0 = 1` (`hasDerivAt_Ein`, `EinDeriv`, `hasSum_EinDerivTerm`), so it
is entire; it is real on the real axis (`EinR`, `Ein_ofReal`) and `EinR x = ∫_0^x (1 − e^(−t))/t dt`
for `x ≥ 0` (`EinR_eq_integral`). Then `E₁(z) = −γ − Log z + Ein z` (`E1Ein`, `hasDerivAt_E1Ein`:
derivative `−e^(−z)/z` off the branch cut) and `Ei(x) = γ + ln|x| − Ein(−x)` (`EiEin`,
`hasDerivAt_EiEin`: derivative `e^x/x` for `x ≠ 0`) need no principal-value integral.

## Exercise 4.17

`1/x − 1/x² < e^x E₁(x) < 1/x` for `x > 0` (`exp_mul_expIntegral_bounds`): (4.27) with `k = 1`
gives `e^x E₁(x) = 1/x + R₁(x)` where `R₁ < 0` (sign `(−1)^1`) and `|R₁| < 1/x²` (Exercise 4.15).

## Exercise 4.18

Exponential generating functions as formal power series over a `ℚ`-algebra (`egf`): the binomial
transform `A_n = ∑_{j≤n} C(n,j) a_j` (`binomialTransform`) has `S(z) = e^z s(z)`
(`egf_binomialTransform`), by comparing coefficients with `C(n,j)/n! = 1/(j! (n−j)!)`; conversely
`s(z) = e^(−z) S(z)` (`egf_eq_exp_neg_mul`), i.e. `a_n = ∑_{j≤n} (−1)^(n−j) C(n,j) A_j`.

## Exercise 4.19

`Ein` is the exponential generating function of `a_j = (−1)^(j−1)/j`, whose binomial transform is
`H_n = ∑_{j=1}^n C(n,j) (−1)^(j−1)/j` (`sum_choose_alt_div_eq_harmonic`, by induction with
`∑_{l≤m} C(m,l)(−1)^l/(l+1) = 1/(m+1)`, `sum_choose_alt_div_succ`), so by Exercise 4.18
`e^z Ein(z) = ∑_{j≥1} H_j z^j/j!` as formal series (`exp_mul_egf_ein`) and, by the Cauchy product
of the two absolutely convergent series, as functions on `ℂ` (`hasSum_exp_mul_Ein`); the new
series has positive terms for `z > 0`, so no cancellation.

## Exercise 4.20

(4.23) from (4.22): with `t = x²`, `erf(x)/x` is `(2/√π)` times the e.g.f. of `(−1)^j/(2j+1)`,
whose binomial transform is `∑_{j≤n} C(n,j)(−1)^j/(2j+1) = 2^n n!/(2n+1)‼` (`altOddSum`, the
integral `∫_0^1 u^(s−1)(1−u²)^n du` in closed form `altOddSum_eq`, via the recurrence
`altOddSum_succ`; `prod_odd_eq_doubleFactorial`). Formally `exp · egf a = egf (2^n n!/(2n+1)‼)`
(`exp_mul_egf_erf`); analytically the Cauchy product of (4.22) with `e^(x²)` gives
`e^(x²) erf x = (2/√π) ∑ 2^n x^(2n+1)/(2n+1)‼` (`sum_antidiagonal_erf_exp`,
`erf_eq_exp_mul_erfExpSum'`), which is (4.23).

## Exercise 4.21

`Γ(x)` for `x ≥ 1/2` by the shifted Stirling series: `Γ(x) = e^(L + R)/P` with
`L = stirlingApprox m (x + δ)`, `R` its remainder and `P = ∏_{i<δ} (x + i)`
(`Gamma_eq_exp_stirling_div`); dropping `R` with `|R| ≤ ε ≤ 1` costs relative error `≤ 2ε`
(`Gamma_stirling_relError`), rounding the `δ` factors of `P` to relative `η` costs
`≤ e^(δη) − 1` (`abs_prod_one_add_sub_one_le`), and a term of (4.38) at `x'` can only be below
`2^(−n)` if `2πx' + ln(2π²x') ≥ n ln 2` (`shift_necessary`), so `δ ≈ n ln 2/(2π)`.

## Exercise 4.22

`1/Γ(z)` on `ℂ`: the shift holds for every `z`, poles included,
`1/Γ(z) = (∏_{i<δ} (z + i)) / Γ(z + δ)` (`inv_Gamma_eq_prod_mul_inv_Gamma_add`), and for `Re z`
small the reflection formula `1/Γ(z) = Γ(1 − z) sin(πz)/π` (`inv_Gamma_eq_Gamma_one_sub_mul_sin`)
moves the Stirling evaluation to the right half plane; an error `ε ≤ 1` in the logarithm costs
relative error `≤ 2ε` (`inv_Gamma_approx_relError`) and `δ` rounded complex factors cost
`≤ e^(δη) − 1` (`norm_prod_one_add_sub_one_le`). The warning: `|Γ(iy)|² = π/(y sinh(πy))`
(`norm_Gamma_I_mul_sq`), at most `4π e^(−πy)/y` (`norm_Gamma_I_mul_sq_le`), and
`|Γ(1/2 + iy)|² = π/cosh(πy)` (`norm_Gamma_half_add_I_mul_sq`): `|Γ|` is exponentially small in
`|Im z|`, which the logarithmic form handles without loss.

## Exercise 4.23

The convergent Stirling series (4.88): unsigned Stirling numbers of the first kind by the
three-term recurrence (`stirling1`, generating function `sum_stirling1_mul_pow`, `sum_stirling1`
`= n!`), the coefficients `c_k` (`stirlingC`, `stirlingC_one = 1/12`, lower bound
`stirlingC_ge`: `c_k ≥ k!/(4k(k+2))`) and the terms `c_k/((N+1)⋯(N+k))` (`convergentTerm`,
positive). Why it is no improvement: for `1 ≤ K ≤ N` the `K`-th term is at least
`e^(−2N)/(4K(K+2))` (`convergentTerm_ge`), which exceeds the floor `e^(−2πN)` that the divergent
series reaches at the same argument with `⌈πN⌉` terms (`convergentTerm_gt_stirling_floor`): the
convergent series needs far more terms (and far larger coefficients) for the same accuracy.

## Exercise 4.25

The backward recurrence (4.43) was proven in `ContinuedFractionEval.lean` (`backR`,
`backR_pred`, `backR_div`, `approximant_eq_backR`), by the invariant
`R_j/R_{j−1} = 1/b_j+ a_{j+1}/b_{j+1}+ ⋯ a_k/b_k`. Added here: the text's statement with `b₀ = 0`,
`a₁/b₁+ ⋯ a_k/b_k = a₁ R₁/R₀` (`finiteFrac_eq_backR`), the recurrence's first two steps
`R_{k−2} = b_{k−1} b_k + a_k` (`backR_sub_two`), and the sanity check `k = 2`
(`finiteFrac_two_eq`).

## Exercise 4.26

The forward recurrence (4.44), proven along the hint: with the perturbed fraction
`y_k(x) = a₁/b₁+ ⋯ a_k/(b_k + x)` (`tailFracX`, which peels from the back:
`y_{k+1}(x) = y_k(a_{k+1}/(b_{k+1} + x))`, `tailFracX_succ`), induction on `k` gives
`b₀ + y_k(x) = (P_k + P_{k−1} x)/(Q_k + Q_{k−1} x)` for Mathlib's continuants `P = nums`, `Q = dens`
(`tailFracX_eq_nums_dens`), and `x = 0` is (4.44): `f_k = P_k/Q_k` (`approximant_eq_nums_div_dens`),
an independent proof of `approximant_eq_convs`.

## Exercise 4.27

The matrix form of (4.44): with `M_j = [[b_j, 1], [a_j, 0]]` (`cfStep`) and the ordered product
`M_1 M_2 ⋯ M_k` (`cfProd`, built from the segment products `cfProdRange`),
`M_1 ⋯ M_k = [[Q_k, Q_{k−1}], [P_k, P_{k−1}]]` for `k ≥ 1` when `b₀ = 0` (`cfProd_eq`), and for
`k = 0` with `P_{−1} = 1`, `Q_{−1} = 0` (`cfProd_zero`); so `f_k` is the ratio of the first-column
entries (`approximant_eq_cfProd`). The segments compose,
`∏_{i<j≤i+m+n} = (∏_{i<j≤i+m})(∏_{i+m<j≤i+m+n})` (`cfProdRange_add`), which is the parallel (or
binary-splitting) evaluation of the remark.

## Exercise 4.28

`det [[Q_k, Q_{k−1}], [P_k, P_{k−1}]] = (−1)^k a_1 ⋯ a_k`: each `M_j` has determinant `−a_j`
(`det_cfStep`), determinants multiply (`det_cfProdRange`, `det_cfProd`), and Exercise 4.27
identifies the product (`det_continuants`, the determinant formula behind (4.45)–(4.46)).

## Exercise 4.29

The identity (4.46), `D₁ = a₁/b₁`, `D_j = −a_j Q_{j−2} D_{j−1}/Q_j`, was proven in
`ContinuedFractionEval.lean` (`diff_one`, `diff_succ`, from `D_j = Δ_j/(Q_j Q_{j−1})` and
`Δ_{j} = −a_j Δ_{j−1}`). Added here: the closed form `D_k = (−1)^{k−1} a_1 ⋯ a_k/(Q_k Q_{k−1})`
(`diff_eq_prod_div`, from Exercise 4.28) and (4.46) rederived from it by taking the ratio of
consecutive closed forms (`diff_succ'`).

## Exercise 4.30

Theorem 4.1 was proven in `ContinuedFractionEval.lean` (`approximant_even_strictMono`,
`approximant_odd_strictAnti`, `approximant_even_lt`, `lt_approximant_odd`,
`abs_sub_midpoint_lt`); here it is packaged as one statement (`theorem_4_1`), together with the
bracket between consecutive approximants it rests on (`approximant_between_consecutive`).

## Exercise 4.31

The continued fraction (4.40) for `erfc`: its coefficients are positive (`erfcCF_pos`), so Theorem
4.1 applies; `a₁⋯a_{k+1} = k!/2^k` (`erfcCF_prod_num`), `Q_k ≥ x^k` (`erfcCF_dens_ge`), hence the
`(k+1)`-th step `|D_{k+1}| ≤ k!/(2^k x^(2k+1))` (`erfcCF_abs_diff_le`), which is at most the `k`-th
term of the asymptotic series (4.37) (`factorial_sq_mul_two_pow_le_factorial`,
`erfcCF_abs_diff_le_erfcTermMag`): the fraction converges at least as fast as (4.37) wherever
the latter is usable, and keeps converging where (4.37) stalls (`abs_diff_succ_lt`) — the region
just below the asymptotic threshold `x ≈ √(n ln 2/2)` where Algorithm Erf has to fall back to the
`Ω(x²)`-term series.

## Exercise 4.32

Binary splitting for continued fractions with bounded integer coefficients: the entries of a
product of `n` step matrices with `|a_j|, |b_j| ≤ B` are at most `(2B)^n` (`cfStep_entry_le`,
`cfProdRange_entry_le`), i.e. `O(n log B)` bits, so the product tree of Exercise 4.27 has, at each
of its `⌈lg k⌉` levels, `2^ℓ` products of `O(k/2^ℓ)`-bit matrices; in the quasi-linear model each
level costs `≤ 8 M(ck)` (`splitting_levels_cost_le`), giving `O(M(k) log k)` in all, plus one
division `P_k/Q_k`.

## Exercise 4.33

Normalizing Miller's algorithm by (4.54) `J₀ + 2∑ J_{2ν} = 1` or by (4.89) `J₀² + 2∑ J_ν² = 1`:
a linear normalization sum with terms carrying relative errors `≤ ε` has absolute error
`≤ ε ∑|t_ν|`, amplification `κ₁ = ∑|t_ν|/|∑ t_ν|` (`abs_sum_perturbed_sub_le`); a sum of squares
of nonnegative terms has relative error `≤ 2ε + ε²` with no amplification
(`abs_sum_sq_perturbed_sub_le`); and by Cauchy–Schwarz `∑|t_ν| ≤ √(N ∑ t_ν²)`
(`sum_abs_le_sqrt_card_mul_sum_sq`), so given (4.89) the amplification of (4.54) is at most
`√N ≈ √x`, a loss of `≤ ½ log₂ x` bits.

## Exercise 4.34

The model recurrence `f_{ν−1} + f_{ν+1} = 2K f_ν` (`IsConstRecSol`): `λ^ν` solves it iff
`λ² − 2Kλ + 1 = 0` (`isConstRecSol_pow`), solutions form a vector space and are determined by two
initial values (`IsConstRecSol.eq_of_init`), so for distinct roots `λ ≠ μ` every solution is
`A λ^ν + B μ^ν` with `A = (f₁ − μ f₀)/(λ − μ)`, `B = (λ f₀ − f₁)/(λ − μ)`
(`IsConstRecSol.exists_eq_comb`). The roots: for `K > 1` they are real, `K ± √(K² − 1)`, with
`λμ = 1`, `λ > 1 > μ > 0` (`roots_of_one_lt`); for `0 < K < 1` they are `K ± i√(1 − K²)`,
complex conjugates on the unit circle (`roots_of_lt_one`).

## Exercise 4.35

Error propagation in the Bernoulli recurrences. The forward recurrence (4.59) solves
`C ∗ T = R` with `T_m = 1/(2m+1)!` (the series `sinh x/x`), so a perturbation `ρ` of the right
sides propagates as `e = ρ ∗ κ` where `κ` is the inverse of `T`: the coefficients of `x/sinh x`,
`κ_k = (2 − 4^k) C_k` (`bernoulliKernel`, `kernel_mul_sinh`: `(2S(x) − S(2x))(e^x − e^(−x)) = 2x`,
`kernel_conv_eq`, `error_propagation`). Since `|C_k| ≍ (2π)^(−2k)` (`abs_scaledBernoulli_ge`,
`abs_scaledBernoulli_le`) while `|κ_k| ≍ π^(−2k)`, an initial relative error is amplified by
`≥ (4^k − 2)·6/π²` (`kernel_amplification_ge`): (a) `4^k 2^(−n)`. The stable recurrence (4.60)
is the same convolution for `D_k = 4^k C_k ≍ π^(−2k)`, and `|κ_m| ≤ |D_m|`
(`abs_bernoulliKernel_le`), so each step's error reaches `D_k` with amplification `≤ π⁴/18`
(`kernel_amplification_le`): `k` steps of `k` roundings each give (b) `O(k² 2^(−n))`.

## Exercise 4.36

(4.57) from (4.56): `x/(e^x − 1) + x/2` is an even function (`div_exp_sub_one_add_half_even`), so
in `∑ B_k x^k/k! + x/2` the odd coefficients vanish, `B_1 = −1/2` and `B_{2j+1} = 0`
(`bernoulli_odd_eq_zero'`), leaving `∑ C_k x^(2k)` with `C_k = B_{2k}/(2k)!`
(`scaledBernoulliPowerSeries_eq`, re-exporting the §4.7.2 coefficient lemmas); its closed form
`(x/2)/tanh(x/2)` is `div_exp_sub_one_add_half`. (4.62) in the text's indexing,
`T_j = (−1)^(j−1) 2^(2j) (2^(2j) − 1) B_{2j}/(2j)` for `j ≥ 1` (`tangentNumber_eq_bernoulli'`),
follows from `tan x = tanh(ix)/i` and `tanh(x/2) = 2S(x)/x − …` as in `TangentNumbers.lean`
(`tangentNumber_eq_bernoulli`).

## Exercise 4.37

Sizes: `|T_k| = 2(4^k − 1)(2k−1)! ζ(2k)/π^(2k)` (`abs_tangentNumber_eq`), so
`(4/π²)^k (2k−1)! ≤ |T_k| ≤ (π²/3)(2k−1)!` (`abs_tangentNumber_bounds`) and, with Stirling
(`log_factorial_bounds`), `2k ln k − 4k − ln(2k) ≤ ln|T_k| ≤ 2k ln k + 3`
(`log_abs_tangentNumber_bounds`): (a) `lg|T_k| ∼ 2k lg k`. (b) `den B_{2k} ∣ 4^k(4^k − 1)` gives
`ln den ≤ 4k ln 2` (`log_bernoulli_den_le`), and `|B_{2k}| = |num|/den` with
`|B_{2k}| = 2(2k)! ζ(2k)/(2π)^(2k)` gives `2k ln k − 8k ≤ ln|num| + ln den ≤ 2k ln k + 6k + 3`
(`log_bernoulli_num_den_bounds`): the rational `B_{2k}` also needs `∼ 2k lg k` bits, almost all
of them in the numerator.

## Exercise 4.38

Correctness of Algorithm TangentNumbers from (4.63): one update `T_j ← (j−k) T_{j−1} + (j−k+2) T_j`
on a row holding `T_{j−1} = p_{j+k−3, j−k}` (already updated in this pass) and
`T_j = p_{j+k−3, j−k+2}` (not yet) produces `p_{j+k−2, j−k+1}`, which is exactly (4.63) at
`n = j+k−2` (`tangentStep_eq_coeff`); the loop
invariant that pass `k` turns the row `p_{·+k−3, ·−k+2}` into `p_{·+k−2, ·−k+1}` and leaves `T_k =
p_{2k−1,0}` behind was proven in `TangentAlgorithm.lean` (`tangentPass_spec`, `tangentOuter_spec`),
giving `tangentNumbersModel_eq`, packaged here as `algorithm_tangentNumbers_correct`.

## Exercise 4.39

Cost of Algorithm TangentNumbers: every intermediate entry is a coefficient `p_{n,i}` with
`n ≤ 2m − 3`, and `p_{n,i} ≤ P_n(1) ≤ 2^n (n+1)!` (`coeff_tanDerivPoly_le_eval_one`,
`eval_one_tanDerivPoly_le`, from `P_{n+1}(1) = 2 P_n'(1) ≤ 2(n+1) P_n(1)`), so each entry has at
most `2m(lg(2m) + 2) = O(m log m)` bits (`size_coeff_tanDerivPoly_le`); the `≈ m²/2` updates, each
`O(log T)` by assumption, cost at most `m² · 2m(lg(2m) + 2) = O(m³ log m)` bits in all
(`tangentAlgorithmBits`, `tangentAlgorithmBits_le`). By Exercise 4.37 the output alone has
`Θ(m² log m)` bits, so the bound is tight up to the factor `m` of passes.

## Exercise 4.40

Algorithm SecantNumbers: with `Dⁿ sec x = Q_n(tan x) sec x`, `Q_0 = 1`,
`Q_{n+1} = X Q_n + (1 + X²) Q_n'` (`secDerivPoly`, `iteratedDeriv_sec`), the coefficients satisfy
`q_{n+1,j+1} = (j+1) q_{n,j} + (j+2) q_{n,j+2}`, `q_{n+1,0} = q_{n,1}`, `q_{n,n} = n!`
(`coeff_secDerivPoly_succ`, `_succ_zero`, `_top`), and `S_k = D^(2k) sec 0 = q_{2k,0}`
(`secantNumber`, `iteratedDeriv_sec_zero`; `S = 1, 1, 5, 61, …`). The in-place algorithm
(`secantInit`, `secantStep`, `secantPass`, `secantOuter`, `secantNumbersModel`) keeps the
invariant "before pass `k`: `S_0, …, S_{k−1}` finished, position `j ≥ k` holds `q_{j+k−1, j−k+1}`"
(`secantPass_spec`, `secantOuter_spec`), so it returns `S_0, …, S_m` (`secantNumbersModel_eq`).

## Exercise 4.41

Harvey's reciprocal method: `∑ B_k x^k/k! = (∑ x^k/(k+1)!)⁻¹` (`recipSeries`,
`bernoulliPowerSeries_mul_recipSeries`), the Newton step for a power-series reciprocal doubles
the number of correct coefficients (`newton_reciprocal_step`: `1 − E·R(2 − ER) = (1 − ER)²`), the
scaled coefficients `(B_k/k!) · k! · den B_k = num B_k` are integers of `O(k log k)` bits
(`scaled_coeff_eq_num`, Exercise 4.37), and `M(n² lg n) ≤ 3 n² (lg n)²` in the quasi-linear model
(`quasiLinearCost_sq_log_le`): the `n + 1` Bernoulli numbers cost `O(n² (log n)^(2+ε))`.

## Exercise 4.42

Algorithm SeriesExponential (`seriesExp`: `b_0 = 1`, `k b_k = ∑_{j=1}^k j a_j b_{k−j}`) solves
`B' = A' B`, `B(0) = 1` (`derivative_mk_seriesExp`), hence `log B = A` in the sense of Exercise
4.1 (`logSeries_mk_seriesExp`): (a). (b) With `a_{2k−1} = B_{2k}/(2k(2k−1))`, `a_{2k} = 0`
(`stirlingLogCoeff`, the coefficients of (4.38) in `1/z`: `stirlingTerm_eq_stirlingLogCoeff`),
`seriesExp` gives the Stirling coefficients `b = 1, 1/12, 1/288, −139/51840, …`
(`stirlingCoeff`, `stirlingCoeff_one/two/three`) of `n! ∼ (n/e)^n √(2πn) ∑ b_k/n^k`. (c) is prose.

## Exercise 4.43

Second-order AGM logarithm: from (4.69) `|K − (π/2)(1 + k²/4)| ≤ A k⁴` and (4.70)
`|K' − ((2/π) ln(4/k) K − k²/4)| ≤ B k⁴`, pure algebra gives
`|ln(4/k) − ((1 − k²/4) K' + k²/4)| ≤ k⁴ ((1/16 + 2A/π) ln(4/k) + 1/16 + B)`
(`second_order_deduction`), and with the proven (4.69) constant `A = 3π/16` for `k² ≤ 1/2`,
`k⁴ ((7/16) ln(4/k) + 1/16 + B)` (`second_order_expansion`; `B` is the still-unproven second-order
constant of (4.70), numerically `21/128`). With `k = 4/x` this is `agmLog2 x := (1 − 4/x²) agmLog x
+ 4/x²` and `|agmLog2 x − ln x| ≤ (4/x)⁴ (c₁ ln x + c₂)` (`abs_agmLog2_sub_log_le`), so `x⁴ ≥
(c₁ ln x + c₂) 256 · 2^n`, i.e. `x ≳ 2^(n/4)`, gives `n` bits (`agmLog2_precision`).

## Exercise 4.44

`π` and `ln 2` from (4.71): `(π/2)/AGM(1,k) ≈ ln(4/k)` turned around gives
`π ≈ 2 ln(4/k) AGM(1,k)` with error `≤ (k²/2)(2 − ln k)` (`abs_two_mul_log_mul_AGM_sub_pi`); at
`4/k = e^j` the logarithm is known exactly, so `π ≈ 2j AGM(1, 4e^(−j))` with error
`≤ 8 e^(−2j)(j + 2 − ln 4)` (`abs_pi_approx_exp`), and then `ln 2 ≈ (π/2)/(m AGM(1, 2^(2−m)))`
(`abs_log_two_approx`), with an approximate `π` propagating linearly (`abs_log_two_approx_of_pi`,
using `AGM(1,k) ≥ (π/2)/(ln(4/k) + (k²/4)(2 − ln k))`, `pi_div_two_div_le_AGM`).

## Exercise 4.45

Computing `2θ₂θ₃` and `θ₂² + θ₃²` with two non-scalar products: (A) `u = (θ₂+θ₃)²`, `v = θ₂θ₃`,
outputs `2v`, `u − 2v` (`methodA_eq`); (B) `u`, `w = (θ₂−θ₃)²`, outputs `(u ± w)/2` (`methodB_eq`).
Relative errors `ε` in the products give `|Δ(u − 2v)| ≤ 3ε(θ₂² + θ₃²)` for (A)
(`methodA_relError_le`), but `|Δ((u − w)/2)|` up to `ε(θ₂² + θ₃²)`, i.e. a relative error
`ε(θ₂² + θ₃²)/(2θ₂θ₃) ≥ ε θ₃/(2θ₂)` for (B) (`methodB_amplification`), and since
`θ₂(q) ≤ 2q^(1/4)/(1 − q)` (`theta2_le_two_rpow_div`) while `θ₃ ≥ 1`, this loses about
`¼ lg(1/q)` bits for small `q`: (A) is preferable.

## Exercise 4.46

Improving Table 4.1's complex column in the transform-count model: a complex product or squaring
costs exactly twice its real counterpart (`fftCost_complex_mul_eq_two_mul`,
`fftCost_complex_sq_eq_two_mul`), so running the *real* Newton iterations for reciprocal
(`13/9`), division (`5/3`) and square root (`4/3`) over `ℂ` costs `26/9`, `10/3`, `8/3` instead of
the table's `31/9`, `43/9`, `16/3` obtained by reducing to real operations through `|z|²`
(`complex_reciprocal_improved`, `complex_division_improved`, `complex_sqrt_improved`), the AGM
iteration drops from `20/3` to `4` and `ln z` via the AGM from `(40/3) lg n` to `8 lg n`
(`complex_agm_iteration_improved`, `complex_log_improved`); the table's `|z|²`-based counts are
re-derived (`complex_reciprocal_via_norm`, `complex_sqrt_via_norm`).

## Exercise 4.47

(4.80), `∑_{k=1}^{⌈lg n⌉} 2^k M(2^(−k) n lg n) = O((lg n)^α M(n))`: for `M(m) = m^c`, `1 < c ≤ 2`,
the level costs form a geometric series with ratio `2^(1−c) < 1`
(`two_pow_mul_div_rpow`, `binary_splitting_cost_pow`: `∑_{k=1}^{L} 2^k (N/2^k)^c ≤ N^c ·
2^(1−c)/(1 − 2^(1−c))`), and with `N = n lg n`, `(n lg n)^c = (lg n)^c M(n)`
(`binary_splitting_cost_pow_eq`), so `α = c ≤ 2` (`rpow_logb_le_sq`); the quasi-linear case
`α = 2` is `binary_splitting_cost` in `BinarySplitting.lean`.

## Exercise 4.48

Yes: `exp(x²) + x/(1 − x²)` is holonomic (`IsHolonomicOn`, a linear ODE with polynomial
coefficients and nonzero leading coefficient, here on `{x | x² ≠ 1}`).  Both summands are
(`exp_sq_ode`, `ratPart_ode`), holonomic functions are closed under addition, and the explicit
annihilator is the second-order operator `(1−x²)(1−x²+2x⁴) D² − 2x(2+x²+3x⁴−2x⁶) D +
2(2x⁶+3x⁴+4x²−1)` (`salvyFun_ode`, `salvyFun_isHolonomicOn`), obtained by eliminating `f`
and `g` from `f'' = (2+4x²) f` and `x(1−x²) g' = (1+x²) g`.  Its Taylor coefficients `1/m!`
(even index `2m`) and `1` (odd index) are interleaved and not hypergeometric, which is the
point of the exercise.

## Exercise 4.49

Theorem 4.2's `O(M(n) log³ n)` comes from charging every one of the `⌈lg n⌉ + 1` bit-burst
steps the full binary-splitting cost `O(M(n) log² n)` of (4.80).  Step `i` evaluates about
`n/2^i` terms whose recurrence coefficients have `2^i + O(lg n)` bits, so its product tree has
root size `S_i = n + n lg n/2^i` (`burstStepSize`), not `n lg n`, and costs at most
`(lg n + 1) · M(S_i)` (`binary_splitting_levels_le`).  Since `M(a + b) ≤ 4(M(a) + M(b))`
(`quasiLinearCost_add_le`) and `M(m/2^i) ≤ M(m)/2^i` (`quasiLinearCost_div_two_pow_le`), the
sizes `n lg n/2^i` contribute a geometric series: `∑_i M(S_i) ≤ (4(L+1) + 16 lg n) M(n)`
(`sum_quasiLinearCost_burstStepSize_le`, using `M(n lg n) ≤ 2 lg n · M(n)`,
`quasiLinearCost_natCast_mul_logb_le`), and the whole algorithm costs at most `56 (lg n)² M(n)`
(`bit_burst_cost`), i.e. `O(M(n) log² n)` (van der Hoeven; Mezzarobba).

## Exercise 4.50

Partial fractions for `w = e^(2πi/k)`: `1/(z^k − 1) = (1/k) ∑_{m<k} w^m/(z − w^m)`
(`sum_primitiveRoot_div_eq`, via `z^k − 1 = (z − w^m) ∑_i z^i w^(m(k−1−i))` and orthogonality
`sum_zpow_primitiveRoot`).  Hence for `f` holomorphic on `|z| ≤ R`, `R > 1`, and `j < k`, the
discrete sum (4.84) `S_{j,k} = (1/k) ∑_{m<k} f(w^m) w^(−jm)` (`aliasSumFun`; `aliasSum` of
`ContourIntegration.lean` is the special case of a series) is the contour integral
`(2πi)⁻¹ ∮_{|z|=R} z^(k−j−1)/(z^k − 1) f(z) dz` (`aliasSumFun_eq_circleIntegral`: each partial
fraction contributes a Cauchy integral `(2πi)⁻¹ ∮ z^(k−j−1) f(z)/(z − w^m) dz = w^(m(k−j−1))
f(w^m)`).  Subtracting (4.83) for `a_j` (`cauchyCoeff`, with `hasSum_cauchyCoeff` identifying
it with the Taylor coefficient) gives `S_{j,k} − a_j = (2πi)⁻¹ ∮ f(z)/(z^(j+1)(z^k − 1)) dz`
(`aliasSumFun_sub_cauchyCoeff`), and expanding `1/(z^k − 1) = ∑_{l≥1} z^(−lk)` on `|z| = R`
(dominated convergence, `hasSum_circleIntegral_div_pow`) yields (4.85)
`S_{j,k} − a_j = ∑_{l≥1} a_{j+lk}` (`aliasSumFun_sub_cauchyCoeff_eq_tsum`): aliasing.

## Exercise 4.51

For `f(z) = z/(e^z − 1) + z/2`, which is even with real coefficients: conjugation
`f(conj z) = conj f(z)` pairs the sample `w^m` with `w^(k−m)`, so every sample value is one of
`f(w^r)`, `r ≤ k/2`, or its conjugate (`sample_reduce_conj`, about `k/2` evaluations for odd
`k`); for even `k`, evenness `w^(m + k/2) = −w^m` (`exp_two_pi_div_pow_half`) folds further to
`r ≤ k/4` (`sample_reduce_even`, about `k/4` evaluations).  For odd `k`, the aliased
coefficients `a_{2j+lk}` with `l` odd have odd index and vanish, so `S_{2j,k} = S_{2j,2k}`
(`bernoulli_aliasSum_odd`) and the error (4.87) improves from `O((2π)^(−k))` to `O((2π)^(−2k))`
(`norm_bernoulli_aliasSum_sub_le_odd`).
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

section Exercise415

open Finset

/-- (4.27) in the text's indexing: `e^x E₁(x) = ∑_{j=1}^k (j−1)! (−1)^(j−1)/x^j + R_k(x)`. -/
theorem exp_mul_expIntegral_eq_text {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.exp x * expIntegral x
      = ∑ j ∈ Icc 1 k, ((j - 1).factorial : ℝ) * (-1) ^ (j - 1) / x ^ j
        + asymptoticRemainder k x := by
  rw [exp_mul_expIntegral_eq hx k, ← Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
    sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [asymptoticTerm, add_comm 1 j, Nat.add_sub_cancel]

/-- The strict form of `expTail_le`: `I_k(x) < e^(−x)/x^(k+1)`, since `I_{k+1}(x) > 0`. -/
theorem expTail_lt {x : ℝ} (hx : 0 < x) (k : ℕ) : expTail k x < Real.exp (-x) / x ^ (k + 1) := by
  rw [expTail_succ hx k]
  have := expTail_pos hx (k + 1)
  have hk : (0 : ℝ) < k + 1 := by positivity
  nlinarith

/-- (4.28), strict: `|R_k(x)| < k!/x^(k+1)`. -/
theorem abs_asymptoticRemainder_lt {x : ℝ} (hx : 0 < x) (k : ℕ) :
    |asymptoticRemainder k x| < k.factorial / x ^ (k + 1) := by
  unfold asymptoticRemainder
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_pos (Real.exp_pos x), abs_of_nonneg (expTail_nonneg hx k),
    abs_of_pos (by positivity : (0 : ℝ) < k.factorial)]
  calc (k.factorial : ℝ) * Real.exp x * expTail k x
      < k.factorial * Real.exp x * (Real.exp (-x) / x ^ (k + 1)) := by
        gcongr; exact expTail_lt hx k
    _ = k.factorial / x ^ (k + 1) := by
        have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
        rw [mul_assoc, ← mul_div_assoc, this, mul_one_div]

end Exercise415

section Exercise416

open Complex Finset

/-- Term `n` of `Ein`: `(−1)^n z^(n+1)/((n+1)! (n+1))` (the text's `j = n + 1`). -/
noncomputable def EinTerm (n : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ n * z ^ (n + 1) / (((n + 1).factorial * (n + 1) : ℕ) : ℂ)

/-- The entire function `Ein z = ∫_0^z (1 − e^(−t))/t dt = ∑_{j≥1} (−1)^(j−1) z^j/(j! j)`. -/
noncomputable def Ein (z : ℂ) : ℂ := ∑' n, EinTerm n z

theorem norm_EinTerm_le (n : ℕ) (z : ℂ) :
    ‖EinTerm n z‖ ≤ ‖z‖ ^ (n + 1) / (n + 1).factorial := by
  unfold EinTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    Complex.norm_natCast]
  push_cast
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact le_mul_of_one_le_right (by positivity) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])

theorem summable_EinTerm (z : ℂ) : Summable fun n => EinTerm n z := by
  refine Summable.of_norm_bounded (g := fun n => ‖z‖ ^ (n + 1) / (n + 1).factorial) ?_
    fun n => norm_EinTerm_le n z
  exact (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖z‖)

theorem EinTerm_zero (n : ℕ) : EinTerm n 0 = 0 := by simp [EinTerm]

theorem Ein_zero : Ein 0 = 0 := by simp [Ein, EinTerm_zero]

/-- The termwise derivative `(−1)^n z^n/(n+1)!`. -/
noncomputable def EinDerivTerm (n : ℕ) (z : ℂ) : ℂ := (-1) ^ n * z ^ n / ((n + 1).factorial : ℂ)

theorem hasDerivAt_EinTerm (n : ℕ) (z : ℂ) : HasDerivAt (EinTerm n) (EinDerivTerm n z) z := by
  have h := (((hasDerivAt_pow (n + 1) z).const_mul ((-1 : ℂ) ^ n)).div_const
    (((n + 1).factorial * (n + 1) : ℕ) : ℂ))
  refine h.congr_deriv ?_
  unfold EinDerivTerm
  rw [Nat.add_sub_cancel]
  push_cast
  have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

theorem norm_EinDerivTerm_le {R : ℝ} (n : ℕ) {y : ℂ} (hy : ‖y‖ ≤ R) :
    ‖EinDerivTerm n y‖ ≤ R ^ n / n.factorial := by
  unfold EinDerivTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    Complex.norm_natCast]
  have hR : 0 ≤ R := (norm_nonneg y).trans hy
  calc ‖y‖ ^ n / ((n + 1).factorial : ℝ) ≤ R ^ n / ((n + 1).factorial : ℝ) := by
        gcongr
    _ ≤ R ^ n / n.factorial := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast Nat.factorial_le (Nat.le_succ n)

/-- `Ein' z = (1 − e^(−z))/z`, with the removable value `1` at `0`. -/
noncomputable def EinDeriv (z : ℂ) : ℂ := if z = 0 then 1 else (1 - exp (-z)) / z

theorem hasSum_cexp_series (w : ℂ) : HasSum (fun n => w ^ n / (n.factorial : ℂ)) (exp w) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp w

theorem hasSum_EinDerivTerm (z : ℂ) : HasSum (fun n => EinDerivTerm n z) (EinDeriv z) := by
  unfold EinDeriv
  split_ifs with hz
  · subst hz
    have : (fun n => EinDerivTerm n 0) = fun n => if n = 0 then (1 : ℂ) else 0 := by
      ext n; cases n <;> simp [EinDerivTerm]
    rw [this]
    exact hasSum_ite_eq 0 1
  · have h1 := (hasSum_nat_add_iff' 1).mpr (hasSum_cexp_series (-z))
    rw [sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h1
    have h2 := h1.div_const (-z)
    convert h2 using 1
    · ext n
      unfold EinDerivTerm
      rw [pow_succ]
      have : (-z) ≠ 0 := neg_ne_zero.mpr hz
      field_simp
      ring
    · rw [div_neg, ← neg_div, neg_sub]

/-- `Ein` is differentiable everywhere, hence entire. -/
theorem hasDerivAt_Ein (z : ℂ) : HasDerivAt Ein (EinDeriv z) z := by
  rw [← (hasSum_EinDerivTerm z).tsum_eq]
  set R : ℝ := ‖z‖ + 1 with hR
  have hu : Summable fun n => R ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial R
  have hg' : ∀ n (y : ℂ), y ∈ Metric.ball (0 : ℂ) R →
      ‖EinDerivTerm n y‖ ≤ R ^ n / n.factorial := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact norm_EinDerivTerm_le n hy.le
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (by positivity)
  show HasDerivAt (fun w => ∑' n, EinTerm n w) (∑' n, EinDerivTerm n z) z
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected (fun n y _ => hasDerivAt_EinTerm n y) hg' h0
    (summable_EinTerm 0) hz

/-- `Ein` restricted to the real axis. -/
noncomputable def EinR (x : ℝ) : ℝ := (Ein x).re

theorem Ein_ofReal (x : ℝ) : Ein x = (EinR x : ℂ) := by
  have : Ein x = ((∑' n, ((-1) ^ n * x ^ (n + 1) / (((n + 1).factorial * (n + 1) : ℕ) : ℝ))
      : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    unfold Ein EinTerm
    congr 1; ext n; push_cast; ring
  rw [EinR, this, Complex.ofReal_re]

theorem EinR_zero : EinR 0 = 0 := by simp [EinR, Ein_zero]

/-- `EinR' x = (1 − e^(−x))/x`, `EinR' 0 = 1`. -/
noncomputable def EinDerivR (x : ℝ) : ℝ := if x = 0 then 1 else (1 - Real.exp (-x)) / x

theorem EinDeriv_ofReal (x : ℝ) : EinDeriv x = (EinDerivR x : ℂ) := by
  unfold EinDeriv EinDerivR
  simp only [Complex.ofReal_eq_zero]
  split_ifs <;> push_cast <;> simp

theorem hasDerivAt_EinR (x : ℝ) : HasDerivAt EinR (EinDerivR x) x := by
  have h := (hasDerivAt_Ein x).real_of_complex
  rwa [EinDeriv_ofReal, Complex.ofReal_re] at h

theorem hasDerivAt_EinR_of_ne {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt EinR ((1 - Real.exp (-x)) / x) x := by
  have h := hasDerivAt_EinR x
  simpa only [EinDerivR, hx, ↓reduceIte] using h

/-- The integrand `(1 − e^(−t))/t` is bounded by `1` on `(0, x]`. -/
theorem abs_one_sub_exp_neg_div_le {t : ℝ} (ht : 0 < t) : |(1 - Real.exp (-t)) / t| ≤ 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  rw [abs_div, abs_of_pos ht, abs_of_nonneg (by linarith), div_le_one ht]
  linarith

theorem intervalIntegrable_one_sub_exp_neg_div {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-t)) / t) MeasureTheory.volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_const.sub (Real.measurable_exp.comp measurable_neg)).div
      measurable_id).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact abs_one_sub_exp_neg_div_le ht.1

/-- `Ein x = ∫_0^x (1 − e^(−t))/t dt` for real `x ≥ 0`: both sides vanish at `0` and have the
same derivative on `(0, ∞)`; the integral from `0` is controlled by the bound `1` on the
integrand. -/
theorem EinR_eq_integral {x : ℝ} (hx : 0 ≤ x) :
    EinR x = ∫ t in (0 : ℝ)..x, (1 - Real.exp (-t)) / t := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [EinR_zero]
  set f : ℝ → ℝ := fun t => (1 - Real.exp (-t)) / t with hf
  have hint := intervalIntegrable_one_sub_exp_neg_div hx.le
  -- for `0 < a ≤ x`: `∫_a^x f = EinR x − EinR a`
  have hpart : ∀ a, 0 < a → a ≤ x → ∫ t in a..x, f t = EinR x - EinR a := by
    intro a ha hax
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
    · rw [Set.uIcc_of_le hax] at ht
      exact hasDerivAt_EinR_of_ne (by linarith [ht.1])
    · have hmem : a ∈ Set.uIcc 0 x := by rw [Set.uIcc_of_le hx.le]; exact ⟨ha.le, hax⟩
      exact hint.mono_set (Set.uIcc_subset_uIcc_right hmem)
  -- so `|∫_0^x f − EinR x| ≤ a + |EinR a|` for all such `a`
  have hbound : ∀ a, 0 < a → a ≤ x →
      |(∫ t in (0 : ℝ)..x, f t) - EinR x| ≤ a + |EinR a| := by
    intro a ha hax
    have hmem : a ∈ Set.uIcc 0 x := by rw [Set.uIcc_of_le hx.le]; exact ⟨ha.le, hax⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (Set.uIcc_subset_uIcc_left hmem))
      (hint.mono_set (Set.uIcc_subset_uIcc_right hmem))
    have hsmall : |∫ t in (0 : ℝ)..a, f t| ≤ a := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a) (C := 1)
        (f := f) fun t ht => by
          rw [Set.uIoc_of_le ha.le] at ht
          rw [Real.norm_eq_abs]
          exact abs_one_sub_exp_neg_div_le ht.1
      simpa [abs_of_pos ha] using this
    rw [← hsplit, hpart a ha hax]
    calc |(∫ t in (0 : ℝ)..a, f t) + (EinR x - EinR a) - EinR x|
        = |(∫ t in (0 : ℝ)..a, f t) - EinR a| := by ring_nf
      _ ≤ |∫ t in (0 : ℝ)..a, f t| + |EinR a| := abs_sub _ _
      _ ≤ a + |EinR a| := by linarith
  -- let `a → 0⁺`
  have hlim : Filter.Tendsto (fun a : ℝ => a + |EinR a|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto (fun a : ℝ => a + |EinR a|) (nhds 0) (nhds (0 + |EinR 0|)) :=
      Filter.tendsto_id.add ((hasDerivAt_EinR 0).continuousAt.tendsto.abs)
    rw [EinR_zero, abs_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hle : |(∫ t in (0 : ℝ)..x, f t) - EinR x| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hx] with a ha
    exact hbound a ha.1 ha.2.le
  have := abs_nonneg ((∫ t in (0 : ℝ)..x, f t) - EinR x)
  linarith [abs_eq_zero.mp (le_antisymm hle this) |> sub_eq_zero.mp]

/-- `E₁(z) = −γ − Log z + Ein z`: (4.26) as a definition, with no principal value. -/
noncomputable def E1Ein (z : ℂ) : ℂ := -(Real.eulerMascheroniConstant : ℂ) - log z + Ein z

/-- `E₁' z = −e^(−z)/z` away from the branch cut of `Log`. -/
theorem hasDerivAt_E1Ein {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt E1Ein (-exp (-z) / z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h := ((Complex.hasDerivAt_log hz).const_sub (-(Real.eulerMascheroniConstant : ℂ))).add
    (hasDerivAt_Ein z)
  refine h.congr_deriv ?_
  simp only [EinDeriv, hz0, ↓reduceIte]
  field_simp
  ring

/-- `Ei(x) = γ + ln|x| − Ein(−x)`: the real exponential integral without a principal value
(`Real.log` is `ln|x|` for negative `x`). -/
noncomputable def EiEin (x : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log x - EinR (-x)

/-- `Ei' x = e^x/x` for `x ≠ 0`. -/
theorem hasDerivAt_EiEin {x : ℝ} (hx : x ≠ 0) : HasDerivAt EiEin (Real.exp x / x) x := by
  have h1 := (Real.hasDerivAt_log hx).const_add Real.eulerMascheroniConstant
  have h2 : HasDerivAt (fun x : ℝ => EinR (-x)) ((1 - Real.exp (-(-x))) / (-x) * (-1)) x :=
    (hasDerivAt_EinR_of_ne (neg_ne_zero.mpr hx)).comp x (hasDerivAt_neg x)
  refine (h1.sub h2).congr_deriv ?_
  rw [neg_neg]
  field_simp
  ring

end Exercise416

section Exercise417

/-- Exercise 4.17: `1/x − 1/x² < e^x E₁(x) < 1/x` for `x > 0`. -/
theorem exp_mul_expIntegral_bounds {x : ℝ} (hx : 0 < x) :
    1 / x - 1 / x ^ 2 < Real.exp x * expIntegral x ∧ Real.exp x * expIntegral x < 1 / x := by
  have h := exp_mul_expIntegral_eq hx 1
  simp only [Finset.sum_range_one, asymptoticTerm, Nat.factorial_zero, Nat.cast_one, pow_zero,
    mul_one, zero_add, pow_one] at h
  have hsign := sign_asymptoticRemainder hx 1
  have habs := abs_asymptoticRemainder_lt hx 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at hsign habs
  rw [abs_lt] at habs
  constructor <;> linarith [habs.1, habs.2]

end Exercise417

section Exercise418

open Finset

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The exponential generating function `s(z) = ∑ a_j z^j/j!` as a formal power series. -/
noncomputable def egf (a : ℕ → A) : A⟦X⟧ :=
  PowerSeries.mk fun j => algebraMap ℚ A (1 / j.factorial) * a j

/-- The binomial transform `A_n = ∑_{j≤n} C(n, j) a_j`. -/
def binomialTransform (a : ℕ → A) (n : ℕ) : A := ∑ j ∈ range (n + 1), (n.choose j : A) * a j

theorem coeff_egf (a : ℕ → A) (n : ℕ) :
    PowerSeries.coeff n (egf a) = algebraMap ℚ A (1 / n.factorial) * a n := by
  simp [egf]

/-- `C(n,j)/n! = 1/j! · 1/(n−j)!` in any `ℚ`-algebra. -/
theorem algebraMap_inv_factorial_mul_choose {n j : ℕ} (hj : j ≤ n) :
    algebraMap ℚ A (1 / n.factorial) * (n.choose j : A)
      = algebraMap ℚ A (1 / j.factorial) * algebraMap ℚ A (1 / (n - j).factorial) := by
  rw [← map_natCast (algebraMap ℚ A), ← map_mul, ← map_mul]
  congr 1
  rw [Nat.cast_choose ℚ hj]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (j.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((n - j).factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- Exercise 4.18: `S(z) = e^z s(z)`. -/
theorem egf_binomialTransform (a : ℕ → A) : egf (binomialTransform a) = exp A * egf a := by
  rw [mul_comm]
  ext n
  rw [coeff_egf, PowerSeries.coeff_mul, binomialTransform, mul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i (egf a) *
      PowerSeries.coeff j (exp A))]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [coeff_egf, coeff_exp, ← mul_assoc, algebraMap_inv_factorial_mul_choose hjn]
  ring

/-- The inverse transform: `s(z) = e^(−z) S(z)`, i.e. `a_n = ∑_{j≤n} (−1)^(n−j) C(n,j) A_j`. -/
theorem egf_eq_exp_neg_mul (a : ℕ → A) :
    egf a = evalNegHom (exp A) * egf (binomialTransform a) := by
  rw [egf_binomialTransform, ← mul_assoc, mul_comm (evalNegHom (exp A)), exp_mul_exp_neg_eq_one,
    one_mul]

end Exercise418

section Exercise419

open Finset

/-- `C(m,l)/(l+1) = C(m+1,l+1)/(m+1)` for `l ≤ m`. -/
theorem choose_div_succ_eq {m l : ℕ} (hl : l ≤ m) :
    (m.choose l : ℚ) / (l + 1) = ((m + 1).choose (l + 1) : ℚ) / (m + 1) := by
  rw [Nat.cast_choose ℚ hl, Nat.cast_choose ℚ (by omega : l + 1 ≤ m + 1),
    show m + 1 - (l + 1) = m - l by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (l.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((m - l).factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- `∑_{l≤m} C(m,l) (−1)^l/(l+1) = 1/(m+1)`. -/
theorem sum_choose_alt_div_succ (m : ℕ) :
    ∑ l ∈ range (m + 1), (m.choose l : ℚ) * (-1) ^ l / (l + 1) = 1 / (m + 1) := by
  have h : ∀ l ∈ range (m + 1), (m.choose l : ℚ) * (-1) ^ l / (l + 1)
      = (((m + 1).choose (l + 1) : ℚ) * (-1) ^ l) / (m + 1) := by
    intro l hl
    rw [mul_div_right_comm, choose_div_succ_eq (Nat.lt_succ_iff.mp (mem_range.mp hl)),
      div_mul_eq_mul_div]
  rw [sum_congr rfl h, ← sum_div]
  congr 1
  -- `∑_{l≤m} C(m+1,l+1)(−1)^l = 1 − ∑_{j≤m+1} C(m+1,j)(−1)^j = 1`
  have halt := Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero m)
  have hcast : (∑ j ∈ range (m + 1 + 1), ((-1) ^ j * (m + 1).choose j : ℚ)) = 0 := by
    exact_mod_cast halt
  rw [sum_range_succ', pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one] at hcast
  have : ∑ l ∈ range (m + 1), ((m + 1).choose (l + 1) : ℚ) * (-1) ^ l
      = -∑ l ∈ range (m + 1), ((-1) ^ (l + 1) * (m + 1).choose (l + 1) : ℚ) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun l _ => by rw [pow_succ]; ring
  rw [this]
  linarith

/-- The binomial transform of `(−1)^(j−1)/j` is the harmonic number: in the shifted form,
`∑_{l<m} C(m,l+1) (−1)^l/(l+1) = H_m`. -/
theorem sum_choose_alt_div_eq_harmonic (m : ℕ) :
    ∑ l ∈ range m, (m.choose (l + 1) : ℚ) * (-1) ^ l / (l + 1) = harmonic m := by
  induction m with
  | zero => simp [harmonic_zero]
  | succ m ih =>
    rw [harmonic_succ, ← ih, ← one_div, Nat.cast_succ, ← sum_choose_alt_div_succ m]
    have hsplit : ∀ l ∈ range (m + 1), ((m + 1).choose (l + 1) : ℚ) * (-1) ^ l / (l + 1)
        = (m.choose (l + 1) : ℚ) * (-1) ^ l / (l + 1) + (m.choose l : ℚ) * (-1) ^ l / (l + 1) := by
      intro l _
      rw [Nat.choose_succ_succ, Nat.cast_add]
      ring
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_range_succ (fun l => (m.choose (l + 1) : ℚ)
      * (-1) ^ l / (l + 1)), Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_div, add_zero]

/-- The coefficients `a_j = (−1)^(j−1)/j` of `Ein`, with `a_0 = 0`. -/
noncomputable def einCoeff (j : ℕ) : ℚ := if j = 0 then 0 else (-1) ^ (j - 1) / j

theorem binomialTransform_einCoeff (n : ℕ) : binomialTransform einCoeff n = harmonic n := by
  rw [← sum_choose_alt_div_eq_harmonic, binomialTransform, sum_range_succ']
  simp only [einCoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
  exact sum_congr rfl fun l _ => by ring

/-- Exercise 4.19 as formal power series: `e^z Ein(z) = ∑ H_j z^j/j!`. -/
theorem exp_mul_egf_ein : exp ℚ * egf einCoeff = egf (fun n => harmonic n) := by
  rw [← egf_binomialTransform]
  congr 1
  ext n
  exact binomialTransform_einCoeff n

theorem harmonic_le_self (n : ℕ) : harmonic n ≤ n := by
  unfold harmonic
  calc ∑ i ∈ range n, ((i + 1 : ℕ) : ℚ)⁻¹ ≤ ∑ _i ∈ range n, (1 : ℚ) :=
        sum_le_sum fun i _ => inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos i)
    _ = n := by simp

/-- The Cauchy product term: `∑_{k+l=n} z^k/k! · EinTerm l z = H_{n+1} z^(n+1)/(n+1)!`. -/
theorem sum_antidiagonal_exp_EinTerm (z : ℂ) (n : ℕ) :
    ∑ kl ∈ antidiagonal n, z ^ kl.1 / (kl.1.factorial : ℂ) * EinTerm kl.2 z
      = (harmonic (n + 1) : ℂ) * z ^ (n + 1) / ((n + 1).factorial : ℂ) := by
  have hq := sum_choose_alt_div_eq_harmonic (n + 1)
  have hqc : ((∑ l ∈ range (n + 1), ((n + 1).choose (l + 1) : ℚ) * (-1) ^ l / (l + 1) : ℚ) : ℂ)
      = (harmonic (n + 1) : ℂ) := by rw [hq]
  push_cast at hqc
  rw [← hqc, ← sum_range_reflect, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => z ^ k / (k.factorial : ℂ) * EinTerm l z), sum_mul, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega]
  unfold EinTerm
  rw [Nat.cast_choose ℂ (by omega : n - k + 1 ≤ n + 1), show n + 1 - (n - k + 1) = k by omega,
    Nat.cast_mul]
  have hz : z ^ k * z ^ (n - k + 1) = z ^ (n + 1) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : ((n - k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h4 : ((n - k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n - k)
  have h5 : ((n - k : ℕ) : ℂ) + 1 = ((n - k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h5, ← hz]
  field_simp

/-- Exercise 4.19 as functions: `e^z Ein(z) = ∑_{j≥1} H_j z^j/j!` for every complex `z`. -/
theorem hasSum_exp_mul_Ein (z : ℂ) :
    HasSum (fun n => (harmonic n : ℂ) * z ^ n / (n.factorial : ℂ)) (Complex.exp z * Ein z) := by
  have hf : Summable fun n => ‖z ^ n / (n.factorial : ℂ)‖ := by
    simpa [norm_div, norm_pow, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖z‖
  have hg : Summable fun n => ‖EinTerm n z‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_EinTerm_le n z)
      ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖z‖))
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  rw [(hasSum_cexp_series z).tsum_eq] at hprod
  have h1 : HasSum
      (fun n => ∑ kl ∈ antidiagonal n, z ^ kl.1 / (kl.1.factorial : ℂ) * EinTerm kl.2 z)
      (Complex.exp z * Ein z) := by
    rw [Ein, hprod]; exact hsum.of_norm.hasSum
  simp_rw [sum_antidiagonal_exp_EinTerm] at h1
  rw [← hasSum_nat_add_iff' 1]
  simpa [harmonic_zero] using h1

end Exercise419

section Exercise420

open Finset

/-- `∑_{j≤n} C(n,j) (−1)^j/(2j+s)`, the integral `∫_0^1 u^(s−1) (1−u²)^n du`. -/
noncomputable def altOddSum (n : ℕ) (s : ℚ) : ℚ :=
  ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (-1) ^ j / (2 * j + s)

theorem altOddSum_zero (s : ℚ) : altOddSum 0 s = 1 / s := by simp [altOddSum]

/-- The recurrence `altOddSum (n+1) s = altOddSum n s − altOddSum n (s+2)` (Pascal's rule). -/
theorem altOddSum_succ (n : ℕ) (s : ℚ) :
    altOddSum (n + 1) s = altOddSum n s - altOddSum n (s + 2) := by
  unfold altOddSum
  have h1 : ∀ j ∈ range (n + 1), ((n + 1).choose (j + 1) : ℚ) * (-1) ^ (j + 1)
      / (2 * ((j + 1 : ℕ) : ℚ) + s)
      = (n.choose (j + 1) : ℚ) * (-1) ^ (j + 1) / (2 * ((j + 1 : ℕ) : ℚ) + s)
        - (n.choose j : ℚ) * (-1) ^ j / (2 * j + (s + 2)) := by
    intro j _
    rw [Nat.choose_succ_succ, Nat.cast_add]
    push_cast
    ring
  rw [sum_range_succ' (fun j => ((n + 1).choose j : ℚ) * (-1) ^ j / (2 * j + s)),
    sum_congr rfl h1, sum_sub_distrib,
    sum_range_succ (fun j => (n.choose (j + 1) : ℚ) * (-1) ^ (j + 1) / (2 * ((j + 1 : ℕ) : ℚ) + s)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_div, add_zero,
    sum_range_succ' (fun j => (n.choose j : ℚ) * (-1) ^ j / (2 * j + s))]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Nat.cast_zero, mul_zero,
    zero_add]
  ring

/-- Closed form: `altOddSum n s = 2^n n! / ∏_{i≤n} (s + 2i)` for `s > 0`. -/
theorem altOddSum_eq (n : ℕ) {s : ℚ} (hs : 0 < s) :
    altOddSum n s = 2 ^ n * n.factorial / ∏ i ∈ range (n + 1), (s + 2 * i) := by
  induction n generalizing s with
  | zero => simp [altOddSum_zero]
  | succ n ih =>
    rw [altOddSum_succ, ih hs, ih (by linarith)]
    have hP : 0 < ∏ i ∈ range (n + 1), (s + 2 * (i : ℚ)) :=
      prod_pos fun i _ => by positivity
    have hP2 : ∏ i ∈ range (n + 1), (s + 2 + 2 * (i : ℚ))
        = (∏ i ∈ range (n + 1 + 1), (s + 2 * i)) / s := by
      rw [prod_range_succ' (fun i => (s + 2 * (i : ℚ))) (n + 1)]
      rw [Nat.cast_zero, mul_zero, add_zero, mul_div_assoc, div_self hs.ne', mul_one]
      exact prod_congr rfl fun i _ => by push_cast; ring
    have hP1 : ∏ i ∈ range (n + 1 + 1), (s + 2 * (i : ℚ))
        = (∏ i ∈ range (n + 1), (s + 2 * (i : ℚ))) * (s + 2 * ((n + 1 : ℕ) : ℚ)) :=
      prod_range_succ _ _
    rw [hP2, hP1, Nat.factorial_succ]
    have hq : (s + 2 * ((n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- `∏_{i≤n} (1 + 2i) = (2n+1)‼`. -/
theorem prod_odd_eq_doubleFactorial (n : ℕ) :
    ∏ i ∈ range (n + 1), ((1 : ℚ) + 2 * i) = ((2 * n + 1).doubleFactorial : ℚ) := by
  induction n with
  | zero => simp [Nat.doubleFactorial]
  | succ n ih =>
    rw [prod_range_succ, ih, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring,
      Nat.doubleFactorial_add_two]
    push_cast
    ring

/-- `∑_{j≤n} C(n,j)(−1)^j/(2j+1) = 2^n n!/(2n+1)‼`. -/
theorem altOddSum_one (n : ℕ) :
    altOddSum n 1 = 2 ^ n * n.factorial / ((2 * n + 1).doubleFactorial : ℚ) := by
  rw [altOddSum_eq n one_pos, prod_odd_eq_doubleFactorial]

/-- The formal statement: `e^t · ∑ (−1)^j t^j/(j!(2j+1)) = ∑ 2^n t^n/(2n+1)‼`. -/
theorem exp_mul_egf_erf :
    exp ℚ * egf (fun j : ℕ => ((-1 : ℚ) ^ j / (2 * j + 1)))
      = egf (fun n : ℕ => (2 : ℚ) ^ n * n.factorial / ((2 * n + 1).doubleFactorial : ℚ)) := by
  rw [← egf_binomialTransform]
  congr 1
  ext n
  rw [← altOddSum_one, binomialTransform, altOddSum]
  exact sum_congr rfl fun j _ => by ring

/-- The Cauchy product coefficient: `∑_{j+k=n} (−1)^j x^(2j+1)/(j!(2j+1)) · (x²)^k/k!
= c_n x^(2n+1)` with `c_n = 2^n/(2n+1)‼`. -/
theorem sum_antidiagonal_erf_exp (x : ℝ) (n : ℕ) :
    ∑ kl ∈ antidiagonal n, ((-1) ^ kl.1 * x ^ (2 * kl.1 + 1) / (kl.1.factorial * (2 * kl.1 + 1)))
      * ((x ^ 2) ^ kl.2 / (kl.2.factorial : ℝ))
      = erfExpCoeff n * x ^ (2 * n + 1) := by
  have hq : ((altOddSum n 1 : ℚ) : ℝ)
      = 2 ^ n * n.factorial / ((2 * n + 1).doubleFactorial : ℝ) := by
    rw [altOddSum_one]; push_cast; rfl
  have hq' : ((altOddSum n 1 : ℚ) : ℝ)
      = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (-1) ^ j / (2 * j + 1) := by
    rw [altOddSum]; push_cast; rfl
  have hc : erfExpCoeff n * x ^ (2 * n + 1)
      = ((altOddSum n 1 : ℚ) : ℝ) * x ^ (2 * n + 1) / n.factorial := by
    rw [hq, erfExpCoeff]
    have := Nat.doubleFactorial_pos (2 * n + 1)
    have h0 : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hc, hq', sum_mul, sum_div, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => ((-1) ^ j * x ^ (2 * j + 1) / (j.factorial * (2 * j + 1)))
      * ((x ^ 2) ^ k / (k.factorial : ℝ)))]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [Nat.cast_choose ℝ hjn]
  have hx : (x ^ 2) ^ (n - j) * x ^ (2 * j + 1) = x ^ (2 * n + 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n - j).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  rw [← hx]
  field_simp

/-- Exercise 4.20: (4.23) derived from (4.22) by the Cauchy product with `e^(x²)`
(no differential equation, unlike `erf_eq_exp_mul_erfExpSum`). -/
theorem erf_eq_exp_mul_erfExpSum' (x : ℝ) :
    erf x = 2 / Real.sqrt Real.pi * Real.exp (-x ^ 2) * erfExpSum x := by
  set c : ℝ := 2 / Real.sqrt Real.pi with hc
  have hcpos : 0 < c := by have := Real.sqrt_pos.mpr Real.pi_pos; positivity
  -- (4.22) without the constant
  have hf : HasSum (fun j : ℕ => (-1) ^ j * x ^ (2 * j + 1) / (j.factorial * (2 * j + 1)))
      (erf x / c) := by
    have h := (hasSum_erf_series x).div_const c
    convert h using 1
    funext j
    rw [show (2 : ℝ) / Real.sqrt Real.pi = c from hc.symm, mul_div_cancel_left₀ _ hcpos.ne']
  have hg : HasSum (fun k : ℕ => (x ^ 2) ^ k / (k.factorial : ℝ)) (Real.exp (x ^ 2)) :=
    hasSum_exp_series (x ^ 2)
  have hfn : Summable fun j : ℕ => ‖(-1) ^ j * x ^ (2 * j + 1) / (j.factorial * (2 * j + 1))‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((Real.summable_pow_div_factorial (x ^ 2)).mul_left |x|)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < j.factorial * (2 * j + 1)), pow_succ, pow_mul,
      abs_mul, abs_pow, abs_of_nonneg (sq_nonneg x), mul_comm ((x ^ 2) ^ j) |x|, mul_div_assoc]
    have h1 : (x ^ 2) ^ j / (j.factorial * (2 * j + 1)) ≤ (x ^ 2) ^ j / j.factorial :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (le_mul_of_one_le_right (by positivity) (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]))
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
  have hgn : Summable fun k : ℕ => ‖(x ^ 2) ^ k / (k.factorial : ℝ)‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using
      Real.summable_pow_div_factorial (x ^ 2)
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at hprod
  simp_rw [sum_antidiagonal_erf_exp] at hprod
  have hsum : erfExpSum x = erf x / c * Real.exp (x ^ 2) := by
    rw [erfExpSum]; exact hprod.symm
  rw [hsum, Real.exp_neg]
  field_simp

end Exercise420

section Exercise421

open Finset

/-- The exact identity behind the algorithm: `Γ(x) = e^(L + R) / ∏_{i<δ} (x + i)` with
`L = stirlingApprox m (x + δ)` and `R = stirlingRem m (x + δ)`. -/
theorem Gamma_eq_exp_stirling_div {x : ℝ} (hx : 0 < x) (m δ : ℕ) :
    Real.Gamma x = Real.exp (stirlingApprox m (x + δ) + stirlingRem m (x + δ))
      / ∏ i ∈ range δ, (x + i) := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hpos : ∀ i ∈ range δ, (0 : ℝ) < x + i := fun i _ => by positivity
  have hP : 0 < ∏ i ∈ range δ, (x + (i : ℝ)) := prod_pos hpos
  have h := log_Gamma_eq_log_Gamma_add_sub hx δ
  rw [log_Gamma_eq_stirlingApprox_add m (x + δ),
    ← Real.log_prod (fun i hi => (hpos i hi).ne')] at h
  rw [eq_div_iff hP.ne']
  conv_lhs => rw [← Real.exp_log hG, ← Real.exp_log hP, ← Real.exp_add]
  rw [h]
  congr 1
  ring

/-- Dropping the remainder `R` with `|R| ≤ ε ≤ 1` changes `Γ(x)` by a relative error `≤ 2ε`. -/
theorem Gamma_stirling_relError {x : ℝ} (hx : 0 < x) (m δ : ℕ) {ε : ℝ}
    (hR : |stirlingRem m (x + δ)| ≤ ε) (hε : ε ≤ 1) :
    |Real.exp (stirlingApprox m (x + δ)) / (∏ i ∈ range δ, (x + i)) - Real.Gamma x|
      ≤ 2 * ε * Real.Gamma x := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hP : 0 < ∏ i ∈ range δ, (x + (i : ℝ)) := prod_pos fun i _ => by positivity
  have hid := Gamma_eq_exp_stirling_div hx m δ
  set L := stirlingApprox m (x + δ)
  set R := stirlingRem m (x + δ)
  set P := ∏ i ∈ range δ, (x + (i : ℝ))
  have h1 : Real.exp L / P = Real.Gamma x * Real.exp (-R) := by
    rw [hid, Real.exp_add, div_mul_eq_mul_div, mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
  have h2 := Real.abs_exp_sub_one_le (x := -R) (by rw [abs_neg]; exact hR.trans hε)
  rw [abs_neg] at h2
  rw [h1, show Real.Gamma x * Real.exp (-R) - Real.Gamma x
      = Real.Gamma x * (Real.exp (-R) - 1) by ring, abs_mul, abs_of_pos hG]
  calc Real.Gamma x * |Real.exp (-R) - 1| ≤ Real.Gamma x * (2 * |R|) := by gcongr
    _ ≤ Real.Gamma x * (2 * ε) := by gcongr
    _ = 2 * ε * Real.Gamma x := by ring

/-- Rounding `δ` factors to relative precision `η ≤ 1` perturbs their product by a relative
error at most `e^(δη) − 1`. -/
theorem abs_prod_one_add_sub_one_le {δ : ℕ} {e : ℕ → ℝ} {η : ℝ} (hη : η ≤ 1)
    (he : ∀ i ∈ range δ, |e i| ≤ η) :
    |∏ i ∈ range δ, (1 + e i) - 1| ≤ Real.exp (δ * η) - 1 := by
  rcases Nat.eq_zero_or_pos δ with hδ | hδ
  · subst hδ; simp
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (he 0 (mem_range.mpr hδ))
  have hlo : ∀ i ∈ range δ, -η ≤ e i := fun i hi => (abs_le.mp (he i hi)).1
  have hhi : ∀ i ∈ range δ, e i ≤ η := fun i hi => (abs_le.mp (he i hi)).2
  have hup : ∏ i ∈ range δ, (1 + e i) ≤ Real.exp (δ * η) := by
    calc ∏ i ∈ range δ, (1 + e i) ≤ ∏ _i ∈ range δ, Real.exp η :=
          prod_le_prod₀ (fun i hi => by linarith [hlo i hi])
            fun i hi => by linarith [hhi i hi, Real.add_one_le_exp η]
      _ = Real.exp (δ * η) := by rw [prod_const, card_range, ← Real.exp_nat_mul]
  have hdown : 1 - δ * η ≤ ∏ i ∈ range δ, (1 + e i) := by
    calc (1 : ℝ) - δ * η = 1 + δ * (-η) := by ring
      _ ≤ (1 + -η) ^ δ := one_add_mul_le_pow (by linarith) δ
      _ = ∏ _i ∈ range δ, (1 + -η) := by rw [prod_const, card_range]
      _ ≤ ∏ i ∈ range δ, (1 + e i) :=
          prod_le_prod₀ (fun i _ => by linarith) fun i hi => by linarith [hlo i hi]
  have hexp : (δ : ℝ) * η ≤ Real.exp (δ * η) - 1 := by linarith [Real.add_one_le_exp (δ * η)]
  rw [abs_le]
  constructor <;> linarith

/-- Necessity of the shift: a term of (4.38) at `x'` can be `≤ 2^(−n)` only if
`n ln 2 ≤ 2πx' + ln(2π² x')`, i.e. `x' ≳ n ln 2/(2π)`; so `δ ≈ n ln 2/(2π) ≈ 0.11 n`. -/
theorem shift_necessary {k : ℕ} (hk : 1 ≤ k) {x' : ℝ} (hx : 0 < x') {n : ℕ}
    (h : |stirlingTerm k x'| ≤ (1 / 2) ^ n) :
    n * Real.log 2 ≤ 2 * Real.pi * x' + Real.log (2 * Real.pi ^ 2 * x') := by
  have h1 := abs_stirlingTerm_ge hk hx
  have h2 : Real.exp (-(2 * Real.pi * x')) / (2 * Real.pi ^ 2 * x') ≤ (1 / 2) ^ n := h1.trans h
  rw [div_le_iff₀ (by positivity)] at h2
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp, Real.log_mul (by positivity) (by positivity), one_div, Real.log_pow,
    Real.log_inv] at h3
  linarith

end Exercise421

section Exercise422

open Finset

/-- The shift for the entire function `1/Γ`, valid for every `z` (at a pole both sides vanish):
`1/Γ(z) = (∏_{i<δ} (z + i)) / Γ(z + δ)`. -/
theorem inv_Gamma_eq_prod_mul_inv_Gamma_add (z : ℂ) (δ : ℕ) :
    (Complex.Gamma z)⁻¹ = (∏ i ∈ range δ, (z + i)) * (Complex.Gamma (z + δ))⁻¹ := by
  induction δ with
  | zero => simp
  | succ δ ih =>
    have hz : z + ((δ + 1 : ℕ) : ℂ) = z + δ + 1 := by push_cast; ring
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + δ), prod_range_succ, hz]
    ring

/-- The reflection formula as a formula for `1/Γ`, for `z` not an integer (`sin(πz) ≠ 0`):
`1/Γ(z) = Γ(1 − z) sin(πz)/π`. -/
theorem inv_Gamma_eq_Gamma_one_sub_mul_sin {z : ℂ} (hz : Complex.sin (Real.pi * z) ≠ 0) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gamma z ≠ 0 := by
    intro h0
    rw [h0, zero_mul, eq_comm, div_eq_zero_iff] at h
    exact h.elim hpi hz
  have h' : Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) = Real.pi := by
    rw [h, div_mul_cancel₀ _ hz]
  rw [eq_div_iff hpi, inv_mul_eq_div, div_eq_iff hG]
  linear_combination (-1 : ℂ) * h'

/-- An error `ε ≤ 1` in the logarithm `L` of `Γ(z')` gives a relative error at most `2ε` in
`1/Γ(z) = P e^(−L)`. -/
theorem inv_Gamma_approx_relError (P L L' : ℂ) {ε : ℝ} (hL : ‖L' - L‖ ≤ ε) (hε : ε ≤ 1) :
    ‖P * Complex.exp (-L') - P * Complex.exp (-L)‖ ≤ 2 * ε * ‖P * Complex.exp (-L)‖ := by
  have h1 : P * Complex.exp (-L') - P * Complex.exp (-L)
      = P * Complex.exp (-L) * (Complex.exp (L - L') - 1) := by
    rw [mul_assoc, mul_sub, mul_one, ← Complex.exp_add]; ring_nf
  have h2 := Complex.norm_exp_sub_one_le (x := L - L') (by rw [norm_sub_rev]; exact hL.trans hε)
  rw [norm_sub_rev L L'] at h2
  rw [h1, norm_mul]
  calc ‖P * Complex.exp (-L)‖ * ‖Complex.exp (L - L') - 1‖
      ≤ ‖P * Complex.exp (-L)‖ * (2 * ‖L' - L‖) := by gcongr
    _ ≤ ‖P * Complex.exp (-L)‖ * (2 * ε) := by gcongr
    _ = 2 * ε * ‖P * Complex.exp (-L)‖ := by ring

/-- `‖∏ (1 + e_i) − 1‖ ≤ ∏ (1 + ‖e_i‖) − 1`. -/
theorem norm_prod_one_add_sub_one_le_prod (e : ℕ → ℂ) (δ : ℕ) :
    ‖∏ i ∈ range δ, (1 + e i) - 1‖ ≤ ∏ i ∈ range δ, (1 + ‖e i‖) - 1 := by
  induction δ with
  | zero => simp
  | succ δ ih =>
    rw [prod_range_succ, prod_range_succ]
    have hid : (∏ i ∈ range δ, (1 + e i)) * (1 + e δ) - 1
        = ((∏ i ∈ range δ, (1 + e i)) - 1) * (1 + e δ) + e δ := by ring
    rw [hid]
    calc ‖((∏ i ∈ range δ, (1 + e i)) - 1) * (1 + e δ) + e δ‖
        ≤ ‖(∏ i ∈ range δ, (1 + e i)) - 1‖ * ‖1 + e δ‖ + ‖e δ‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ((∏ i ∈ range δ, (1 + ‖e i‖)) - 1) * (1 + ‖e δ‖) + ‖e δ‖ := by
          have h1e : ‖1 + e δ‖ ≤ 1 + ‖e δ‖ := by simpa using norm_add_le (1 : ℂ) (e δ)
          exact add_le_add_right
            (mul_le_mul ih h1e (norm_nonneg _) ((norm_nonneg _).trans ih)) ‖e δ‖ |>.trans_eq
            rfl |> fun h => by simpa only [add_comm] using h
      _ = (∏ i ∈ range δ, (1 + ‖e i‖)) * (1 + ‖e δ‖) - 1 := by ring

/-- Rounding `δ` complex factors to relative precision `η` perturbs their product by a relative
error at most `e^(δη) − 1`. -/
theorem norm_prod_one_add_sub_one_le {δ : ℕ} {e : ℕ → ℂ} {η : ℝ}
    (he : ∀ i ∈ range δ, ‖e i‖ ≤ η) :
    ‖∏ i ∈ range δ, (1 + e i) - 1‖ ≤ Real.exp (δ * η) - 1 := by
  refine (norm_prod_one_add_sub_one_le_prod e δ).trans ?_
  have : ∏ i ∈ range δ, (1 + ‖e i‖) ≤ Real.exp (δ * η) := by
    calc ∏ i ∈ range δ, (1 + ‖e i‖) ≤ ∏ _i ∈ range δ, Real.exp η :=
          prod_le_prod₀ (fun i _ => by positivity)
            fun i hi => by linarith [he i hi, Real.add_one_le_exp η]
      _ = Real.exp (δ * η) := by rw [prod_const, card_range, ← Real.exp_nat_mul]
  linarith

/-- `Γ(iy) Γ(−iy) = π/(y sinh(πy))` for real `y ≠ 0`. -/
theorem Gamma_I_mul_mul_Gamma_neg {y : ℝ} (hy : y ≠ 0) :
    Complex.Gamma (y * Complex.I) * Complex.Gamma (-(y * Complex.I))
      = Real.pi / (y * Real.sinh (Real.pi * y)) := by
  have hyI : (-(y * Complex.I) : ℂ) ≠ 0 := by
    rw [neg_ne_zero]; exact mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
  have h1 := Complex.Gamma_add_one _ hyI
  have h2 := Complex.Gamma_mul_Gamma_one_sub (y * Complex.I)
  have hs : Complex.sin (Real.pi * (y * Complex.I)) = Real.sinh (Real.pi * y) * Complex.I := by
    rw [← mul_assoc, Complex.sin_mul_I]; push_cast; rfl
  rw [hs] at h2
  have h3 : (1 : ℂ) - y * Complex.I = -(y * Complex.I) + 1 := by ring
  rw [h3, h1] at h2
  have hsinhR : Real.sinh (Real.pi * y) ≠ 0 := fun h =>
    mul_ne_zero Real.pi_ne_zero hy (Real.sinh_injective (by rw [h, Real.sinh_zero]))
  have hsinh : (Real.sinh (Real.pi * y) : ℂ) ≠ 0 := by exact_mod_cast hsinhR
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have h4 : Complex.Gamma (y * Complex.I) * Complex.Gamma (-(y * Complex.I)) * (-(y * Complex.I))
      = Real.pi / (Real.sinh (Real.pi * y) * Complex.I) := by
    rw [← h2]; ring
  rw [← mul_div_cancel_right₀ (Complex.Gamma (y * Complex.I) * Complex.Gamma (-(y * Complex.I)))
    hyI, h4, div_div]
  congr 1
  linear_combination (-((Real.sinh (Real.pi * y) : ℂ) * y)) * Complex.I_sq

/-- `|Γ(iy)|² = π/(y sinh(πy))` for real `y ≠ 0`: `|Γ(iy)|` is exponentially small in `|y|`. -/
theorem norm_Gamma_I_mul_sq {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (y * Complex.I)‖ ^ 2 = Real.pi / (y * Real.sinh (Real.pi * y)) := by
  have hconj : (starRingEnd ℂ) (Complex.Gamma (y * Complex.I))
      = Complex.Gamma (-(y * Complex.I)) := by
    rw [← Complex.Gamma_conj]; congr 1; simp
  have h := Gamma_I_mul_mul_Gamma_neg hy
  rw [← hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- For `πy ≥ 1`: `|Γ(iy)|² ≤ 4π e^(−πy)/y`, the `≈ e^(−π|y|)` of the text. -/
theorem norm_Gamma_I_mul_sq_le {y : ℝ} (hy : 1 ≤ Real.pi * y) :
    ‖Complex.Gamma (y * Complex.I)‖ ^ 2 ≤ 4 * Real.pi * Real.exp (-(Real.pi * y)) / y := by
  have hy0 : 0 < y := by nlinarith [Real.pi_pos]
  rw [norm_Gamma_I_mul_sq hy0.ne']
  have hsinh : Real.exp (Real.pi * y) / 4 ≤ Real.sinh (Real.pi * y) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(Real.pi * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 2 ≤ Real.exp (Real.pi * y) := by
      have := Real.add_one_le_exp (Real.pi * y); linarith
    linarith
  have hE : 0 < Real.exp (Real.pi * y) := Real.exp_pos _
  have hsp : 0 < Real.sinh (Real.pi * y) := by
    rw [← Real.sinh_zero]; exact (Real.sinh_lt_sinh).mpr (by positivity)
  rw [Real.exp_neg, div_le_div_iff₀ (mul_pos hy0 hsp) hy0]
  calc Real.pi * y
      = 4 * Real.pi * (Real.exp (Real.pi * y))⁻¹ * (y * (Real.exp (Real.pi * y) / 4)) := by
        field_simp
    _ ≤ 4 * Real.pi * (Real.exp (Real.pi * y))⁻¹ * (y * Real.sinh (Real.pi * y)) := by gcongr

/-- `|Γ(1/2 + iy)|² = π/cosh(πy)`. -/
theorem norm_Gamma_half_add_I_mul_sq (y : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + y * Complex.I)‖ ^ 2
      = Real.pi / Real.cosh (Real.pi * y) := by
  have hconj : (starRingEnd ℂ) (Complex.Gamma (((1 / 2 : ℝ) : ℂ) + y * Complex.I))
      = Complex.Gamma (1 - (((1 / 2 : ℝ) : ℂ) + y * Complex.I)) := by
    rw [← Complex.Gamma_conj]; congr 1; apply Complex.ext <;> simp; norm_num
  have h := Complex.Gamma_mul_Gamma_one_sub (((1 / 2 : ℝ) : ℂ) + y * Complex.I)
  have hs : Complex.sin (Real.pi * (((1 / 2 : ℝ) : ℂ) + y * Complex.I))
      = Real.cosh (Real.pi * y) := by
    rw [show (Real.pi : ℂ) * (((1 / 2 : ℝ) : ℂ) + y * Complex.I)
        = (Real.pi * y) * Complex.I + Real.pi / 2 by push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I]
    push_cast; rfl
  rw [hs, ← hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

end Exercise422

section Exercise423

open Finset

/-- Unsigned Stirling numbers of the first kind `|s(n, j)|`, by the three-term recurrence
`|s(n+1, j+1)| = |s(n, j)| + n |s(n, j+1)|`; `∑_j |s(n,j)| x^j = x(x+1)⋯(x+n−1)`. -/
def stirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => n * stirling1 n 0
  | n + 1, j + 1 => stirling1 n j + n * stirling1 n (j + 1)

theorem stirling1_eq_zero_of_lt : ∀ {n j : ℕ}, n < j → stirling1 n j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j + 1, h => by
    rw [stirling1, stirling1_eq_zero_of_lt (by omega : n < j),
      stirling1_eq_zero_of_lt (by omega : n < j + 1)]
    simp

theorem stirling1_zero_right : ∀ {n : ℕ}, 1 ≤ n → stirling1 n 0 = 0
  | 0, h => absurd h (by norm_num)
  | 1, _ => rfl
  | n + 2, _ => by rw [stirling1, stirling1_zero_right (by omega : 1 ≤ n + 1), mul_zero]

/-- The generating function: `∑_{j≤n} |s(n,j)| x^j = ∏_{i<n} (x + i)`. -/
theorem sum_stirling1_mul_pow {R : Type*} [CommSemiring R] (n : ℕ) (x : R) :
    ∑ j ∈ range (n + 1), (stirling1 n j : R) * x ^ j = ∏ i ∈ range n, (x + i) := by
  induction n with
  | zero => simp [stirling1]
  | succ n ih =>
    rw [prod_range_succ, ← ih, sum_range_succ' (fun j => (stirling1 (n + 1) j : R) * x ^ j)]
    simp only [stirling1, Nat.cast_add, Nat.cast_mul, pow_zero, mul_one, add_mul,
      sum_add_distrib]
    -- the shifted part: `∑_{j≤n} n |s(n,j+1)| x^(j+1) + n |s(n,0)| = n ∑_{j≤n} |s(n,j)| x^j`
    have hshift : ∑ j ∈ range (n + 1), (n : R) * stirling1 n (j + 1) * x ^ (j + 1)
        + (n : R) * stirling1 n 0 = (n : R) * ∑ j ∈ range (n + 1), (stirling1 n j : R) * x ^ j := by
      have h2 : ∑ j ∈ range (n + 1 + 1), (stirling1 n j : R) * x ^ j
          = ∑ j ∈ range (n + 1), (stirling1 n j : R) * x ^ j := by
        rw [sum_range_succ, stirling1_eq_zero_of_lt (Nat.lt_succ_self n)]; simp
      rw [← h2, sum_range_succ' (fun j => (stirling1 n j : R) * x ^ j), mul_add, mul_sum]
      simp only [pow_zero, mul_one]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    rw [add_assoc, hshift, mul_add, sum_mul]
    congr 1
    · exact sum_congr rfl fun j _ => by ring
    · ring

theorem prod_one_add_range_eq_factorial (n : ℕ) : ∏ i ∈ range n, (1 + i) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, Nat.factorial_succ]; ring

/-- `∑_j |s(n,j)| = n!`. -/
theorem sum_stirling1 (n : ℕ) : ∑ j ∈ range (n + 1), stirling1 n j = n.factorial := by
  have h := sum_stirling1_mul_pow n (1 : ℕ)
  simp only [one_pow, mul_one, Nat.cast_id] at h
  rw [h, prod_one_add_range_eq_factorial]

/-- The coefficients of (4.88): `c_k = (1/(2k)) ∑_{j=1}^k j |s(k,j)| / ((j+1)(j+2))` (the `j = 0`
term vanishes, so the sum may run from `0`). -/
def stirlingC (k : ℕ) : ℚ :=
  1 / (2 * k) * ∑ j ∈ range (k + 1), (j : ℚ) * stirling1 k j / ((j + 1) * (j + 2))

/-- `c_1 = 1/12`, matching the first term `B_2/2 = 1/12` of (4.38). -/
theorem stirlingC_one : stirlingC 1 = 1 / 12 := by
  simp [stirlingC, stirling1, sum_range_succ]
  norm_num

/-- `c_k ≥ k!/(4k(k+2))`: the coefficients grow factorially, like the Bernoulli numbers. -/
theorem stirlingC_ge {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℚ) / (4 * k * (k + 2)) ≤ stirlingC k := by
  have hterm : ∀ j ∈ range (k + 1),
      (stirling1 k j : ℚ) / (2 * (k + 2)) ≤ (j : ℚ) * stirling1 k j / ((j + 1) * (j + 2)) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [stirling1_zero_right hk]; simp
    · have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast hj0
      have hjk' : (j : ℚ) ≤ k := by exact_mod_cast hjk
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hs : (0 : ℚ) ≤ stirling1 k j := by positivity
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hj1), mul_nonneg hs (sub_nonneg.mpr hjk'),
        mul_nonneg (mul_nonneg hs (sub_nonneg.mpr hj1)) (sub_nonneg.mpr hjk')]
  have hsum : ∑ j ∈ range (k + 1), (stirling1 k j : ℚ) / (2 * (k + 2))
      = (k.factorial : ℚ) / (2 * (k + 2)) := by
    rw [← sum_div, ← Nat.cast_sum, sum_stirling1]
  calc (k.factorial : ℚ) / (4 * k * (k + 2))
      = 1 / (2 * k) * ((k.factorial : ℚ) / (2 * (k + 2))) := by
        have : (k : ℚ) ≠ 0 := by positivity
        field_simp
        norm_num
    _ ≤ stirlingC k := by
        unfold stirlingC
        rw [← hsum]
        exact mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)

/-- The `k`-th term of (4.88) at the integer argument `N`: `c_k / ((N+1)(N+2)⋯(N+k))`. -/
noncomputable def convergentTerm (k N : ℕ) : ℝ :=
  (stirlingC k : ℝ) / ∏ i ∈ range k, ((N : ℝ) + i + 1)

theorem convergentTerm_pos {k : ℕ} (hk : 1 ≤ k) (N : ℕ) : 0 < convergentTerm k N := by
  unfold convergentTerm
  have h := stirlingC_ge hk
  have hc : (0 : ℚ) < stirlingC k := lt_of_lt_of_le (by positivity) h
  have : (0 : ℝ) < (stirlingC k : ℝ) := by exact_mod_cast hc
  positivity

/-- `(K/(2eN))^K ≥ e^(−2N)` for every `K ≥ 1`: `K ln(2eN/K) ≤ 2N`, since `1 + ln u ≤ u`. -/
theorem pow_div_ge_exp_neg {K : ℕ} (hK : 1 ≤ K) {N : ℝ} (hN : 0 < N) :
    Real.exp (-(2 * N)) ≤ ((K : ℝ) / (2 * Real.exp 1 * N)) ^ K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hu : 0 < 2 * N / K := by positivity
  have hlog : Real.log (2 * N / K) ≤ 2 * N / K - 1 := Real.log_le_sub_one_of_pos hu
  have hbase : (K : ℝ) / (2 * Real.exp 1 * N) = Real.exp (-(1 + Real.log (2 * N / K))) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hu]
    field_simp
  rw [hbase, ← Real.exp_nat_mul, Real.exp_le_exp]
  have h1 : (K : ℝ) * (1 + Real.log (2 * N / K)) ≤ K * (2 * N / K) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0.le
  have h2 : (K : ℝ) * (2 * N / K) = 2 * N := by field_simp
  linarith

/-- For `1 ≤ K ≤ N` the `K`-th term of (4.88) at `N` is at least `e^(−2N)/(4K(K+2))`. -/
theorem convergentTerm_ge {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    Real.exp (-(2 * N)) / (4 * K * (K + 2)) ≤ convergentTerm K N := by
  unfold convergentTerm
  have hN : (0 : ℝ) < N := by exact_mod_cast (hK.trans hKN)
  have hA : (0 : ℝ) < 4 * K * (K + 2) := by positivity
  have hB : (0 : ℝ) < (2 * N) ^ K := by positivity
  have hP : ∏ i ∈ range K, ((N : ℝ) + i + 1) ≤ (2 * N) ^ K := by
    calc ∏ i ∈ range K, ((N : ℝ) + i + 1) ≤ ∏ _i ∈ range K, (2 * (N : ℝ)) :=
          prod_le_prod₀ (fun i _ => by positivity) fun i hi => by
            have h1 : (i : ℝ) + 1 ≤ K := by exact_mod_cast mem_range.mp hi
            have h2 : (K : ℝ) ≤ N := by exact_mod_cast hKN
            linarith
      _ = (2 * N) ^ K := by rw [prod_const, card_range]
  have hPpos : 0 < ∏ i ∈ range K, ((N : ℝ) + i + 1) := prod_pos fun i _ => by positivity
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hc : (K.factorial : ℝ) / (4 * K * (K + 2)) ≤ (stirlingC K : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (stirlingC_ge hK)
    push_cast at h
    exact h
  have hc0 : (0 : ℝ) ≤ (stirlingC K : ℝ) := le_trans (by positivity) hc
  have hfac : ((K : ℝ) / Real.exp 1) ^ K ≤ K.factorial := by
    have h := Stirling.le_factorial_stirling K
    have hs : 1 ≤ Real.sqrt (2 * Real.pi * K) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith [Real.pi_gt_three]
    nlinarith [pow_pos (div_pos hK0 (Real.exp_pos 1)) K]
  have hpow := pow_div_ge_exp_neg hK hN
  have hsplit : ((K : ℝ) / (2 * Real.exp 1 * N)) ^ K
      = ((K : ℝ) / Real.exp 1) ^ K / (2 * N) ^ K := by
    rw [← div_pow, div_div]; ring_nf
  calc Real.exp (-(2 * N)) / (4 * K * (K + 2))
      ≤ ((K : ℝ) / (2 * Real.exp 1 * N)) ^ K / (4 * K * (K + 2)) :=
        div_le_div_of_nonneg_right hpow hA.le
    _ = ((K : ℝ) / Real.exp 1) ^ K / (4 * K * (K + 2)) / (2 * N) ^ K := by
        rw [hsplit, div_right_comm]
    _ ≤ (K.factorial : ℝ) / (4 * K * (K + 2)) / (2 * N) ^ K := by gcongr
    _ ≤ (stirlingC K : ℝ) / (2 * N) ^ K := by gcongr
    _ ≤ (stirlingC K : ℝ) / ∏ i ∈ range K, ((N : ℝ) + i + 1) :=
        div_le_div_of_nonneg_left hc0 hPpos hP

/-- Exercise 4.23: with `K ≤ N` terms the convergent series at `N` cannot reach the floor
`e^(−2πN)` that the divergent series (4.38) reaches at the same argument with `⌈πN⌉` terms. -/
theorem convergentTerm_gt_stirling_floor {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    Real.exp (-(2 * Real.pi * N)) < convergentTerm K N := by
  refine lt_of_lt_of_le ?_ (convergentTerm_ge hK hKN)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hK.trans hKN
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hA : (4 : ℝ) * K * (K + 2) ≤ 4 * N * (N + 2) := by
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hquad : 1 + 2 * (N : ℝ) + 2 * N ^ 2 ≤ Real.exp (2 * N) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 2 * (N : ℝ)) (by positivity)
    nlinarith
  have hexp4 : 4 * (N : ℝ) * (N + 2) < Real.exp (4 * N) := by
    have h : Real.exp (4 * N) = Real.exp (2 * N) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h]
    nlinarith [hquad, hN]
  have hpi : Real.exp (4 * N) ≤ Real.exp ((2 * Real.pi - 2) * N) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three]
  rw [lt_div_iff₀ (by positivity)]
  calc Real.exp (-(2 * Real.pi * N)) * (4 * K * (K + 2))
      ≤ Real.exp (-(2 * Real.pi * N)) * (4 * N * (N + 2)) := by gcongr
    _ < Real.exp (-(2 * Real.pi * N)) * Real.exp ((2 * Real.pi - 2) * N) :=
        mul_lt_mul_of_pos_left (hexp4.trans_le hpi) (Real.exp_pos _)
    _ = Real.exp (-(2 * N)) := by rw [← Real.exp_add]; congr 1; ring

end Exercise423

section Exercise425

/-- (4.43) in the text's form: for `b₀ = 0` and positive `a_j, b_j`,
`a₁/b₁+ a₂/b₂+ ⋯ a_k/b_k = a₁ R₁ / R₀`. -/
theorem finiteFrac_eq_backR {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (hb0 : b 0 = 0)
    {k : ℕ} (hk : 1 ≤ k) : approximant a b k = a 1 * backR a b k 1 / backR a b k 0 := by
  rw [approximant_eq_backR hpos hk, hb0, zero_add]

/-- The first genuine step of the recurrence:
`R_{k−2} = b_{k−1} R_{k−1} + a_k R_k = b_{k−1} b_k + a_k`. -/
theorem backR_sub_two (a b : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    backR a b k (k - 2) = b (k - 1) * b k + a k := by
  rw [backR_of_lt a b (by omega), show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = k by omega,
    backR_pred_self a b (by omega), backR_self, mul_one]

/-- Sanity check at `k = 2`: `a₁/(b₁ + a₂/b₂) = a₁ b₂/(b₁ b₂ + a₂) = a₁ R₁/R₀`. -/
theorem finiteFrac_two_eq {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (hb0 : b 0 = 0) :
    approximant a b 2 = a 1 * b 2 / (b 1 * b 2 + a 2) := by
  have h := backR_sub_two a b (k := 2) le_rfl
  rw [finiteFrac_eq_backR hpos hb0 (by norm_num), backR_pred_self a b (by norm_num)]
  simp only [Nat.sub_self] at h
  rw [h]

end Exercise425

section Exercise426

/-- The tail with terminal value `x`: `a_j/b_j+ ⋯ a_k/(b_k + x)`, and `x` itself if `j > k`. -/
noncomputable def tailFracX (a b : ℕ → ℝ) (k : ℕ) (x : ℝ) (j : ℕ) : ℝ :=
  if k < j then x else a j / (b j + tailFracX a b k x (j + 1))
termination_by k + 1 - j

theorem tailFracX_of_lt (a b : ℕ → ℝ) (k : ℕ) (x : ℝ) {j : ℕ} (h : k < j) :
    tailFracX a b k x j = x := by
  rw [tailFracX, ite_eq_left h]

theorem tailFracX_of_le (a b : ℕ → ℝ) (k : ℕ) (x : ℝ) {j : ℕ} (h : j ≤ k) :
    tailFracX a b k x j = a j / (b j + tailFracX a b k x (j + 1)) := by
  rw [tailFracX, ite_eq_right (not_lt.mpr h)]

/-- `x = 0` recovers the plain tail. -/
theorem tailFracX_zero (a b : ℕ → ℝ) (k j : ℕ) : tailFracX a b k 0 j = tailFrac a b k j := by
  by_cases h : k < j
  · rw [tailFracX_of_lt _ _ _ _ h, tailFrac_of_lt _ _ h]
  · rw [tailFracX_of_le _ _ _ _ (not_lt.mp h), tailFrac_of_le _ _ (not_lt.mp h),
      tailFracX_zero a b k (j + 1)]
termination_by k + 1 - j

/-- Peeling from the back: `y_{k+1}(x) = y_k(a_{k+1}/(b_{k+1} + x))`, at every start index
`j ≤ k + 1`. -/
theorem tailFracX_succ (a b : ℕ → ℝ) (k : ℕ) (x : ℝ) {j : ℕ} (hj : j ≤ k + 1) :
    tailFracX a b (k + 1) x j = tailFracX a b k (a (k + 1) / (b (k + 1) + x)) j := by
  rcases eq_or_lt_of_le hj with rfl | hlt
  · rw [tailFracX_of_le _ _ _ _ le_rfl, tailFracX_of_lt _ _ _ _ (Nat.lt_succ_self _),
      tailFracX_of_lt _ _ _ _ (Nat.lt_succ_self _)]
  · rw [tailFracX_of_le a b (k + 1) x (j := j) (by omega),
      tailFracX_of_le a b k (a (k + 1) / (b (k + 1) + x)) (j := j) (by omega),
      tailFracX_succ a b k x (j := j + 1) (by omega)]
termination_by k + 1 - j

theorem tailFracX_nonneg {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) {j : ℕ} (hj : 1 ≤ j) : 0 ≤ tailFracX a b k x j := by
  by_cases h : k < j
  · rw [tailFracX_of_lt _ _ _ _ h]; exact hx
  · rw [tailFracX_of_le _ _ _ _ (not_lt.mp h)]
    have hT := tailFracX_nonneg hpos k hx (j := j + 1) (by omega)
    obtain ⟨ha, hb⟩ := hpos j hj
    positivity
termination_by k + 1 - j

/-- The hint: `b₀ + y_{k+1}(x) = (P_{k+1} + P_k x)/(Q_{k+1} + Q_k x)` for `x ≥ 0`, by induction
on `k`, where `P = nums`, `Q = dens` are the continuants of (4.44). -/
theorem tailFracX_eq_nums_dens {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    b 0 + tailFracX a b (k + 1) x 1
      = ((contFrac a b).nums (k + 1) + (contFrac a b).nums k * x)
        / ((contFrac a b).dens (k + 1) + (contFrac a b).dens k * x) := by
  induction k generalizing x with
  | zero =>
    rw [tailFracX_of_le _ _ _ _ le_rfl, tailFracX_of_lt _ _ _ _ (by norm_num), nums_one, nums_zero,
      dens_one, dens_zero]
    have hb1 := (hpos 1 le_rfl).2
    have : 0 < b 1 + x := by linarith
    field_simp
    ring
  | succ k ih =>
    obtain ⟨ha, hb⟩ := hpos (k + 2) (by omega)
    have hd : 0 < b (k + 2) + x := by linarith
    have hx' : 0 ≤ a (k + 2) / (b (k + 2) + x) := by positivity
    rw [tailFracX_succ a b (k + 1) x (by omega), ih hx', nums_recurrence', dens_recurrence']
    have hQ1 := dens_pos hpos (k + 1)
    have hQ0 := dens_pos hpos k
    have hden1 : 0 < (contFrac a b).dens (k + 1) + (contFrac a b).dens k
        * (a (k + 2) / (b (k + 2) + x)) := by positivity
    have hden2 : 0 < b (k + 2) * (contFrac a b).dens (k + 1) + a (k + 2) * (contFrac a b).dens k
        + (contFrac a b).dens (k + 1) * x := by positivity
    rw [div_eq_div_iff hden1.ne' hden2.ne']
    field_simp
    ring

/-- (4.44): `f_k = P_k / Q_k`, the forward recurrence, from the hint at `x = 0`. -/
theorem approximant_eq_nums_div_dens {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j)
    (k : ℕ) : approximant a b k = (contFrac a b).nums k / (contFrac a b).dens k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [approximant_zero, nums_zero, dens_zero, div_one]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [approximant_eq_tailFrac, ← tailFracX_zero, tailFracX_eq_nums_dens hpos m le_rfl]
    simp

end Exercise426

section Exercise427

/-- The step matrix `M_j = [[b_j, 1], [a_j, 0]]` of the forward recurrence. -/
noncomputable def cfStep (a b : ℕ → ℝ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![b j, 1; a j, 0]

/-- The ordered product `M_{i+1} M_{i+2} ⋯ M_{i+n}` of `n` consecutive step matrices. -/
noncomputable def cfProdRange (a b : ℕ → ℝ) (i : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => 1
  | n + 1 => cfProdRange a b i n * cfStep a b (i + n + 1)

/-- `M_1 M_2 ⋯ M_k`. -/
noncomputable def cfProd (a b : ℕ → ℝ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := cfProdRange a b 0 k

/-- Segments compose: the product over `(i, i+m+n]` is the product over `(i, i+m]` times the
product over `(i+m, i+m+n]` — the basis of a parallel or binary-splitting evaluation. -/
theorem cfProdRange_add (a b : ℕ → ℝ) (i m n : ℕ) :
    cfProdRange a b i (m + n) = cfProdRange a b i m * cfProdRange a b (i + m) n := by
  induction n with
  | zero => simp [cfProdRange]
  | succ n ih =>
    rw [show m + (n + 1) = m + n + 1 by ring, cfProdRange, ih, cfProdRange, mul_assoc,
      show i + m + n + 1 = i + (m + n) + 1 by ring]

/-- `k = 0`: the empty product is the identity, `[[Q₀, Q_{−1}], [P₀, P_{−1}]]` with the
convention `P_{−1} = 1`, `Q_{−1} = 0` (and `P₀ = b₀ = 0`, `Q₀ = 1`). -/
theorem cfProd_zero (a b : ℕ → ℝ) (hb0 : b 0 = 0) :
    cfProd a b 0 = !![(contFrac a b).dens 0, 0; (contFrac a b).nums 0, 1] := by
  rw [cfProd, cfProdRange, dens_zero, nums_zero, hb0]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Exercise 4.27: `M_1 ⋯ M_k = [[Q_k, Q_{k−1}], [P_k, P_{k−1}]]` for `k ≥ 1` (with `b₀ = 0`). -/
theorem cfProd_eq (a b : ℕ → ℝ) (hb0 : b 0 = 0) (k : ℕ) :
    cfProd a b (k + 1) = !![(contFrac a b).dens (k + 1), (contFrac a b).dens k;
      (contFrac a b).nums (k + 1), (contFrac a b).nums k] := by
  induction k with
  | zero =>
    rw [cfProd, cfProdRange, cfProdRange, one_mul, cfStep, dens_one, dens_zero, nums_one,
      nums_zero, hb0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [cfProd, cfProdRange, ← cfProd, ih, cfStep, nums_recurrence', dens_recurrence']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `f_k` is the ratio of the first-column entries of the product. -/
theorem approximant_eq_cfProd {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j)
    (hb0 : b 0 = 0) (k : ℕ) :
    approximant a b (k + 1) = cfProd a b (k + 1) 1 0 / cfProd a b (k + 1) 0 0 := by
  rw [approximant_eq_nums_div_dens hpos, cfProd_eq a b hb0 k]
  simp

end Exercise427

section Exercise428

open Finset

theorem det_cfStep (a b : ℕ → ℝ) (j : ℕ) : (cfStep a b j).det = -a j := by
  rw [cfStep, Matrix.det_fin_two_of]; ring

theorem det_cfProdRange (a b : ℕ → ℝ) (i n : ℕ) :
    (cfProdRange a b i n).det = ∏ j ∈ range n, (-a (i + j + 1)) := by
  induction n with
  | zero => simp [cfProdRange]
  | succ n ih => rw [cfProdRange, Matrix.det_mul, ih, det_cfStep, prod_range_succ]

/-- `det (M_1 ⋯ M_k) = (−1)^k a_1 a_2 ⋯ a_k`. -/
theorem det_cfProd (a b : ℕ → ℝ) (k : ℕ) :
    (cfProd a b k).det = (-1) ^ k * ∏ j ∈ range k, a (j + 1) := by
  rw [cfProd, det_cfProdRange, prod_neg, card_range]
  simp

/-- Exercise 4.28: `Q_k P_{k−1} − P_k Q_{k−1} = (−1)^k a_1 ⋯ a_k` for `k ≥ 1` (with `b₀ = 0`). -/
theorem det_continuants (a b : ℕ → ℝ) (hb0 : b 0 = 0) (k : ℕ) :
    (contFrac a b).dens (k + 1) * (contFrac a b).nums k
      - (contFrac a b).dens k * (contFrac a b).nums (k + 1)
      = (-1) ^ (k + 1) * ∏ j ∈ range (k + 1), a (j + 1) := by
  have h := det_cfProd a b (k + 1)
  rw [cfProd_eq a b hb0 k, Matrix.det_fin_two_of] at h
  exact h

end Exercise428

section Exercise429

open Finset

/-- The closed form of (4.45): `D_{k+1} = (−1)^k a_1 ⋯ a_{k+1} / (Q_{k+1} Q_k)` (positive
coefficients, `b₀ = 0`). -/
theorem diff_eq_prod_div {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (hb0 : b 0 = 0)
    (k : ℕ) :
    diff a b (k + 1) = (-1) ^ k * (∏ j ∈ range (k + 1), a (j + 1))
      / ((contFrac a b).dens (k + 1) * (contFrac a b).dens k) := by
  rw [diff_eq_det_div hpos k]
  congr 1
  have h := det_continuants a b hb0 k
  rw [pow_succ] at h
  linear_combination -h

/-- (4.46) rederived from the closed form: `D_{k+2}/D_{k+1} = −a_{k+2} Q_k / Q_{k+2}`. -/
theorem diff_succ' {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (hb0 : b 0 = 0)
    (k : ℕ) :
    diff a b (k + 2)
      = -a (k + 2) * (contFrac a b).dens k * diff a b (k + 1) / (contFrac a b).dens (k + 2) := by
  rw [diff_eq_prod_div hpos hb0 (k + 1), diff_eq_prod_div hpos hb0 k, prod_range_succ _ (k + 1),
    pow_succ]
  have h0 := dens_pos hpos k
  have h1 := dens_pos hpos (k + 1)
  have h2 := dens_pos hpos (k + 2)
  field_simp

end Exercise429

section Exercise430

/-- The value lies strictly between any two consecutive approximants. -/
theorem approximant_between_consecutive {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j)
    {f : ℝ} (hf : HasContFracValue a b f) (m : ℕ) :
    min (approximant a b m) (approximant a b (m + 1)) < f ∧
      f < max (approximant a b m) (approximant a b (m + 1)) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h1 := approximant_even_lt hpos hf k
    have h2 := lt_approximant_odd hpos hf k
    rw [show m = 2 * k by omega, show 2 * k + 1 = 2 * k + 1 from rfl]
    exact ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_right _ _)⟩
  · have h1 := approximant_even_lt hpos hf (k + 1)
    have h2 := lt_approximant_odd hpos hf k
    rw [show m = 2 * k + 1 by omega, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    exact ⟨lt_of_le_of_lt (min_le_right _ _) h1, lt_of_lt_of_le h2 (le_max_left _ _)⟩

/-- Theorem 4.1 (Exercise 4.30): for positive `a_j, b_j`, the even approximants increase
strictly, the odd ones decrease strictly, the value `f` lies strictly between every even and
every odd approximant, and the midpoint of two consecutive approximants is within half their
distance of `f`. -/
theorem theorem_4_1 {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {f : ℝ}
    (hf : HasContFracValue a b f) :
    StrictMono (fun k => approximant a b (2 * k)) ∧
      StrictAnti (fun k => approximant a b (2 * k + 1)) ∧
      (∀ k, approximant a b (2 * k) < f) ∧
      (∀ k, f < approximant a b (2 * k + 1)) ∧
      ∀ m, 1 ≤ m → |f - (approximant a b (m - 1) + approximant a b m) / 2|
        < |approximant a b m - approximant a b (m - 1)| / 2 :=
  ⟨approximant_even_strictMono hpos, approximant_odd_strictAnti hpos,
    approximant_even_lt hpos hf, lt_approximant_odd hpos hf,
    fun _ hm => abs_sub_midpoint_lt hpos hf hm⟩

end Exercise430

section Exercise431

open Finset

/-- The coefficients of (4.40) are positive for `x > 0`. -/
theorem erfcCF_pos {x : ℝ} (hx : 0 < x) : ∀ j, 1 ≤ j → 0 < erfcCFNum j ∧ 0 < erfcCFDen x j := by
  intro j hj
  refine ⟨?_, ?_⟩
  · unfold erfcCFNum
    split_ifs with h
    · exact one_pos
    · have : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
      linarith
  · unfold erfcCFDen
    rw [ite_eq_right (by omega)]
    exact hx

theorem erfcCFDen_zero (x : ℝ) : erfcCFDen x 0 = 0 := by simp [erfcCFDen]

/-- `a₁ a₂ ⋯ a_{k+1} = 1 · (1/2) · (2/2) ⋯ (k/2) = k!/2^k`. -/
theorem erfcCF_prod_num (k : ℕ) :
    ∏ j ∈ range (k + 1), erfcCFNum (j + 1) = (k.factorial : ℝ) / 2 ^ k := by
  induction k with
  | zero => simp [erfcCFNum]
  | succ k ih =>
    rw [prod_range_succ, ih, erfcCFNum, ite_eq_right (by omega), Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `Q_j ≥ x^j`: each step multiplies by at least `x`. -/
theorem erfcCF_dens_ge {x : ℝ} (hx : 0 < x) (j : ℕ) :
    x ^ j ≤ (contFrac erfcCFNum (erfcCFDen x)).dens j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => rw [dens_zero, pow_zero]
    | 1 => rw [dens_one, erfcCFDen, ite_eq_right one_ne_zero, pow_one]
    | j + 2 =>
      rw [dens_recurrence', erfcCFDen, ite_eq_right (by omega)]
      have h1 := ih (j + 1) (by omega)
      have h0 := dens_pos (erfcCF_pos hx) j
      have ha := (erfcCF_pos hx (j + 2) (by omega)).1
      calc x ^ (j + 2) = x * x ^ (j + 1) := by ring
        _ ≤ x * (contFrac erfcCFNum (erfcCFDen x)).dens (j + 1) := by gcongr
        _ ≤ _ := by nlinarith

/-- The step `|D_{k+1}| = |f_{k+1} − f_k| ≤ k!/(2^k x^(2k+1))` of the normalized fraction (4.40). -/
theorem erfcCF_abs_diff_le {x : ℝ} (hx : 0 < x) (k : ℕ) :
    |diff erfcCFNum (erfcCFDen x) (k + 1)| ≤ k.factorial / (2 ^ k * x ^ (2 * k + 1)) := by
  rw [diff_eq_prod_div (erfcCF_pos hx) (erfcCFDen_zero x) k, erfcCF_prod_num, abs_div, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0:ℝ) < k.factorial / 2 ^ k),
    abs_of_pos (mul_pos (dens_pos (erfcCF_pos hx) (k + 1)) (dens_pos (erfcCF_pos hx) k))]
  have h1 := erfcCF_dens_ge hx (k + 1)
  have h0 := erfcCF_dens_ge hx k
  have hprod : x ^ (2 * k + 1) ≤ (contFrac erfcCFNum (erfcCFDen x)).dens (k + 1)
      * (contFrac erfcCFNum (erfcCFDen x)).dens k := by
    calc x ^ (2 * k + 1) = x ^ (k + 1) * x ^ k := by ring
      _ ≤ _ := mul_le_mul h1 h0 (by positivity) (by linarith [pow_pos hx (k + 1)])
  rw [div_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hprod (by positivity))

/-- `(k!)² 2^k ≤ (2k)!`, i.e. `k!/2^k ≤ (2k)!/(k! 4^k)`: the fraction's step is below the
asymptotic series' term coefficient. -/
theorem factorial_sq_mul_two_pow_le_factorial (k : ℕ) :
    k.factorial ^ 2 * 2 ^ k ≤ (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    have h2 : (2 * (k + 1)).factorial = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [h1, h2, pow_succ]
    calc ((k + 1) * k.factorial) ^ 2 * (2 ^ k * 2)
        = (k + 1) * (k + 1) * 2 * (k.factorial ^ 2 * 2 ^ k) := by ring
      _ ≤ (k + 1) * (2 * k + 1) * 2 * (2 * k).factorial :=
          Nat.mul_le_mul (Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left (k + 1) (by omega))) ih
      _ = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by ring

/-- The `(k+1)`-th step of (4.40) is at most the `k`-th term of the asymptotic series (4.37),
both normalized by the common prefactor `e^(−x²)/√π`. -/
theorem erfcCF_abs_diff_le_erfcTermMag {x : ℝ} (hx : 0 < x) (k : ℕ) :
    |diff erfcCFNum (erfcCFDen x) (k + 1)| ≤ erfcTermMag k x / x := by
  refine (erfcCF_abs_diff_le hx k).trans ?_
  unfold erfcTermMag erfcCoeff
  have h := factorial_sq_mul_two_pow_le_factorial k
  have hc : (k.factorial : ℝ) ^ 2 * 2 ^ k ≤ (2 * k).factorial := by exact_mod_cast h
  rw [div_div, div_div, pow_succ, pow_mul, ← mul_assoc]
  have hk0 : (0 : ℝ) < k.factorial := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [this]
  have hX : 0 < (x ^ 2) ^ k * x := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  calc _ = (k.factorial ^ 2 * 2 ^ k) * (2 ^ k * ((x ^ 2) ^ k * x)) := by ring
    _ ≤ ((2 * k).factorial : ℝ) * (2 ^ k * ((x ^ 2) ^ k * x)) := by gcongr
    _ = _ := by ring

end Exercise431

section Exercise432

open Finset

/-- The entries of a step matrix are bounded by `B ≥ 1` when `|a_j|, |b_j| ≤ B`. -/
theorem cfStep_entry_le {a b : ℕ → ℝ} {B : ℝ} (hB : 1 ≤ B) {j : ℕ} (ha : |a j| ≤ B)
    (hb : |b j| ≤ B) (r s : Fin 2) : |cfStep a b j r s| ≤ B := by
  fin_cases r <;> fin_cases s <;> simp [cfStep] <;> linarith

/-- The entries of a product of `n` step matrices are bounded by `(2B)^n`: they have
`O(n log B)` bits. -/
theorem cfProdRange_entry_le {a b : ℕ → ℝ} {B : ℝ} (hB : 1 ≤ B) (i : ℕ)
    (ha : ∀ j, |a j| ≤ B) (hb : ∀ j, |b j| ≤ B) (n : ℕ) (r s : Fin 2) :
    |cfProdRange a b i n r s| ≤ (2 * B) ^ n := by
  induction n generalizing r s with
  | zero => fin_cases r <;> fin_cases s <;> simp [cfProdRange]
  | succ n ih =>
    rw [cfProdRange, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
    have h0 := cfStep_entry_le hB (ha (i + n + 1)) (hb (i + n + 1)) 0 s
    have h1 := cfStep_entry_le hB (ha (i + n + 1)) (hb (i + n + 1)) 1 s
    have hP0 := ih r 0
    have hP1 := ih r 1
    have hpow : (0 : ℝ) ≤ (2 * B) ^ n := by positivity
    calc |cfProdRange a b i n r 0 * cfStep a b (i + n + 1) 0 s
          + cfProdRange a b i n r 1 * cfStep a b (i + n + 1) 1 s|
        ≤ |cfProdRange a b i n r 0| * |cfStep a b (i + n + 1) 0 s|
          + |cfProdRange a b i n r 1| * |cfStep a b (i + n + 1) 1 s| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (2 * B) ^ n * B + (2 * B) ^ n * B := by
          gcongr
      _ = (2 * B) ^ n * (2 * B) := by ring

/-- The product tree: level `ℓ` of the splitting forms `2^ℓ` products of matrices whose entries
have `m/2^ℓ` bits (`m = O(k log B)` at the root); in the quasi-linear model `M(x) = x lg x` each
level costs at most `8 M(m)` (eight multiplications per `2×2` product), so `L` levels cost at most
`8 L M(m)`. -/
theorem splitting_levels_cost_le {m : ℝ} (hm : 1 ≤ m) (L : ℕ) :
    ∑ ℓ ∈ range L, 2 ^ ℓ * (8 * quasiLinearCost (m / 2 ^ ℓ)) ≤ L * (8 * quasiLinearCost m) := by
  have hterm : ∀ ℓ ∈ range L,
      2 ^ ℓ * (8 * quasiLinearCost (m / 2 ^ ℓ)) ≤ 8 * quasiLinearCost m := by
    intro ℓ _
    have := two_pow_mul_quasiLinearCost_div_le hm ℓ
    linarith
  calc _ ≤ ∑ _ℓ ∈ range L, 8 * quasiLinearCost m := sum_le_sum hterm
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

end Exercise432

section Exercise433

open Finset

/-- A linear normalization sum whose terms carry relative errors `|e_i| ≤ ε` is off by at most
`ε ∑|t_i|`: the error is amplified by `κ₁ = ∑|t_i| / |∑ t_i|` relative to the sum. -/
theorem abs_sum_perturbed_sub_le {ι : Type*} (s : Finset ι) (t e : ι → ℝ) {ε : ℝ}
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |∑ i ∈ s, t i * (1 + e i) - ∑ i ∈ s, t i| ≤ ε * ∑ i ∈ s, |t i| := by
  rw [← sum_sub_distrib]
  calc |∑ i ∈ s, (t i * (1 + e i) - t i)| ≤ ∑ i ∈ s, |t i * (1 + e i) - t i| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |t i| * |e i| := sum_congr rfl fun i _ => by
        rw [show t i * (1 + e i) - t i = t i * e i by ring, abs_mul]
    _ ≤ ∑ i ∈ s, |t i| * ε :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (he i hi) (abs_nonneg _)
    _ = ε * ∑ i ∈ s, |t i| := by rw [← sum_mul, mul_comm]

/-- A sum of squares of nonnegative terms with relative errors `|e_i| ≤ ε` has relative error at
most `2ε + ε²`: no amplification. -/
theorem abs_sum_sq_perturbed_sub_le {ι : Type*} (s : Finset ι) (t e : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) {ε : ℝ} (he : ∀ i ∈ s, |e i| ≤ ε) :
    |∑ i ∈ s, t i * (1 + e i) ^ 2 - ∑ i ∈ s, t i| ≤ (2 * ε + ε ^ 2) * ∑ i ∈ s, t i := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  have hε : 0 ≤ ε := (abs_nonneg _).trans (he i₀ hi₀)
  rw [← sum_sub_distrib]
  calc |∑ i ∈ s, (t i * (1 + e i) ^ 2 - t i)| ≤ ∑ i ∈ s, |t i * (1 + e i) ^ 2 - t i| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, t i * (2 * ε + ε ^ 2) := by
        refine sum_le_sum fun i hi => ?_
        rw [show t i * (1 + e i) ^ 2 - t i = t i * (e i * (2 + e i)) by ring, abs_mul,
          abs_of_nonneg (ht i hi), abs_mul]
        have h1 := he i hi
        have h2 : |2 + e i| ≤ 2 + ε := (abs_add_le _ _).trans (by rw [abs_two]; linarith)
        have h3 : |e i| * |2 + e i| ≤ ε * (2 + ε) :=
          mul_le_mul h1 h2 (abs_nonneg _) hε
        nlinarith [ht i hi]
    _ = (2 * ε + ε ^ 2) * ∑ i ∈ s, t i := by rw [← sum_mul, mul_comm]

/-- Cauchy–Schwarz: `∑|t_i| ≤ √(N ∑ t_i²)` over `N` terms; so when `∑ t_i² ≤ 1` (as in (4.89))
the amplification of a linear normalization sum is at most `√N`. -/
theorem sum_abs_le_sqrt_card_mul_sum_sq {ι : Type*} (s : Finset ι) (t : ι → ℝ) :
    ∑ i ∈ s, |t i| ≤ Real.sqrt (s.card * ∑ i ∈ s, t i ^ 2) := by
  rw [Real.le_sqrt (sum_nonneg fun i _ => abs_nonneg _) (by positivity)]
  have h := sum_mul_sq_le_sq_mul_sq s (fun i => |t i|) fun _ => (1 : ℝ)
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, sq_abs] at h
  linarith

end Exercise433

section Exercise434

/-- The constant-coefficient model `f_ν + f_{ν+2} = 2K f_{ν+1}` of (4.53) near `ν ≈ Kx`. -/
def IsConstRecSol (K : ℂ) (f : ℕ → ℂ) : Prop := ∀ ν, f ν + f (ν + 2) = 2 * K * f (ν + 1)

/-- `λ^ν` is a solution iff `λ² − 2Kλ + 1 = 0`. -/
theorem isConstRecSol_pow {K lam : ℂ} (h : lam ^ 2 - 2 * K * lam + 1 = 0) :
    IsConstRecSol K (fun ν => lam ^ ν) := by
  intro ν
  simp only
  linear_combination lam ^ ν * h

theorem IsConstRecSol.add {K : ℂ} {f g : ℕ → ℂ} (hf : IsConstRecSol K f) (hg : IsConstRecSol K g) :
    IsConstRecSol K (fun ν => f ν + g ν) := by
  intro ν; simp only; linear_combination hf ν + hg ν

theorem IsConstRecSol.smul {K : ℂ} {f : ℕ → ℂ} (hf : IsConstRecSol K f) (c : ℂ) :
    IsConstRecSol K (fun ν => c * f ν) := by
  intro ν; simp only; linear_combination c * hf ν

/-- A solution is determined by its two initial values. -/
theorem IsConstRecSol.eq_of_init {K : ℂ} {f g : ℕ → ℂ} (hf : IsConstRecSol K f)
    (hg : IsConstRecSol K g) (h0 : f 0 = g 0) (h1 : f 1 = g 1) : ∀ ν, f ν = g ν := by
  intro ν
  induction ν using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more ν ih0 ih1 =>
    have hfν := hf ν
    have hgν := hg ν
    linear_combination hfν - hgν - ih0 + 2 * K * ih1

/-- Exercise 4.34: for distinct roots `λ ≠ μ` of `x² − 2Kx + 1`, every solution is
`A λ^ν + B μ^ν` with `A = (f₁ − μ f₀)/(λ − μ)`, `B = (λ f₀ − f₁)/(λ − μ)`. -/
theorem IsConstRecSol.exists_eq_comb {K lam mu : ℂ} (hl : lam ^ 2 - 2 * K * lam + 1 = 0)
    (hm : mu ^ 2 - 2 * K * mu + 1 = 0) (hne : lam ≠ mu) {f : ℕ → ℂ} (hf : IsConstRecSol K f) :
    ∃ A B : ℂ, ∀ ν, f ν = A * lam ^ ν + B * mu ^ ν := by
  have hd : lam - mu ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨(f 1 - mu * f 0) / (lam - mu), (lam * f 0 - f 1) / (lam - mu), ?_⟩
  have hg : IsConstRecSol K fun ν => (f 1 - mu * f 0) / (lam - mu) * lam ^ ν
      + (lam * f 0 - f 1) / (lam - mu) * mu ^ ν :=
    ((isConstRecSol_pow hl).smul _).add ((isConstRecSol_pow hm).smul _)
  exact hf.eq_of_init hg (by simp; field_simp; ring) (by simp; field_simp; ring)

/-- `K > 1`: two real roots `K ± √(K² − 1)`, with product `1` and `λ > 1 > μ > 0`. -/
theorem roots_of_one_lt {K : ℝ} (hK : 1 < K) :
    let s := Real.sqrt (K ^ 2 - 1)
    (K + s) ^ 2 - 2 * K * (K + s) + 1 = 0 ∧ (K - s) ^ 2 - 2 * K * (K - s) + 1 = 0 ∧
      (K + s) * (K - s) = 1 ∧ 1 < K + s ∧ 0 < K - s ∧ K - s < 1 := by
  intro s
  have hs2 : s ^ 2 = K ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hsK : s < K := by
    rw [show s = Real.sqrt (K ^ 2 - 1) from rfl, Real.sqrt_lt' (by linarith)]; linarith
  refine ⟨by linear_combination hs2, by linear_combination hs2, by linear_combination -hs2,
    by linarith, by linarith, ?_⟩
  nlinarith

/-- `0 < K < 1`: the roots `K ± i√(1 − K²)` are complex conjugates of modulus `1`. -/
theorem roots_of_lt_one {K : ℝ} (hK0 : 0 < K) (hK : K < 1) :
    let lam : ℂ := K + Real.sqrt (1 - K ^ 2) * Complex.I
    lam ^ 2 - 2 * (K : ℂ) * lam + 1 = 0 ∧
      (starRingEnd ℂ) lam ^ 2 - 2 * (K : ℂ) * (starRingEnd ℂ) lam + 1 = 0 ∧
      lam * (starRingEnd ℂ) lam = 1 ∧ ‖lam‖ = 1 ∧ lam ≠ (starRingEnd ℂ) lam := by
  intro lam
  have hs2 : Real.sqrt (1 - K ^ 2) ^ 2 = 1 - K ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs : 0 < Real.sqrt (1 - K ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hconj : (starRingEnd ℂ) lam = K - Real.sqrt (1 - K ^ 2) * Complex.I := by
    simp [lam, Complex.conj_ofReal]; ring
  set sC : ℂ := ((Real.sqrt (1 - K ^ 2) : ℝ) : ℂ) with hsC
  have hs2c : sC ^ 2 = 1 - (K : ℂ) ^ 2 := by rw [hsC]; exact_mod_cast hs2
  have hmul : lam * (starRingEnd ℂ) lam = 1 := by
    rw [hconj]; linear_combination hs2c - sC ^ 2 * Complex.I_sq
  refine ⟨?_, ?_, hmul, ?_, ?_⟩
  · linear_combination (-1 : ℂ) * hs2c + sC ^ 2 * Complex.I_sq
  · rw [hconj]
    linear_combination (-1 : ℂ) * hs2c + sC ^ 2 * Complex.I_sq
  · have h := congrArg Complex.re hmul
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    simp only [Complex.ofReal_re, Complex.one_re] at h
    have h' : ‖lam‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg lam]
  · rw [hconj]
    intro h
    have := congrArg Complex.im h
    simp [lam, hsC] at this
    linarith

end Exercise434

section Exercise435

open Finset PowerSeries

/-- The propagation kernel of the forward recurrence (4.59): `κ_k = (2 − 4^k) C_k`, the
coefficient of `x^(2k)` in `x/sinh x = 2S(x) − S(2x)`. -/
def bernoulliKernel (k : ℕ) : ℚ := (2 - 4 ^ k) * scaledBernoulli k

theorem exp_ne_zero' : (exp ℚ : ℚ⟦X⟧) ≠ 0 := fun h => by
  have := congrArg (coeff 0) h
  rw [coeff_exp, map_zero] at this
  simp at this

/-- `x/sinh x = 2S(x) − S(2x)`: `(2S − S(2x))(e^x − e^(−x)) = 2x` in `ℚ⟦X⟧`. -/
theorem kernel_mul_sinh :
    (2 * scaledBernoulliPowerSeries - rescale (2 : ℚ) scaledBernoulliPowerSeries)
      * (exp ℚ - evalNegHom (exp ℚ)) = 2 * X := by
  set S := scaledBernoulliPowerSeries
  set E := exp ℚ
  have h1 : S * (E - 1) = X + C (1 / 2 : ℚ) * X * (E - 1) :=
    scaledBernoulliPowerSeries_mul_exp_sub_one
  have hE2 : rescale (2 : ℚ) E = E * E := by
    have := exp_pow_eq_rescale_exp (A := ℚ) 2
    push_cast at this
    rw [← this, sq]
  have h2 : rescale (2 : ℚ) S * (E * E - 1)
      = C (2 : ℚ) * X + C (1 / 2 : ℚ) * (C (2 : ℚ) * X) * (E * E - 1) := by
    have := congrArg (rescale (2 : ℚ)) h1
    rwa [map_mul, map_sub, map_one, map_add, map_mul, map_mul, map_sub, map_one, rescale_X,
      rescale_C', hE2] at this
  have hEi : E * evalNegHom E = 1 := exp_mul_exp_neg_eq_one
  have hc2 : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := map_ofNat C 2
  apply mul_right_cancel₀ exp_ne_zero'
  linear_combination (2 * (E + 1)) * h1 - h2 - (X + C (1 / 2 : ℚ) * X * (E * E - 1)) * hc2
    - (2 * S - rescale (2 : ℚ) S) * hEi

theorem coeff_kernelSeries_even (j : ℕ) :
    coeff (2 * j) (2 * scaledBernoulliPowerSeries - rescale (2 : ℚ) scaledBernoulliPowerSeries)
      = bernoulliKernel j := by
  rw [map_sub, coeff_rescale, coeff_scaledBernoulliPowerSeries_even, bernoulliKernel,
    show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    coeff_scaledBernoulliPowerSeries_even, pow_mul]
  norm_num
  ring

theorem coeff_kernelSeries_odd (j : ℕ) :
    coeff (2 * j + 1) (2 * scaledBernoulliPowerSeries - rescale (2 : ℚ) scaledBernoulliPowerSeries)
      = 0 := by
  rw [map_sub, coeff_rescale, coeff_scaledBernoulliPowerSeries_odd,
    show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    coeff_scaledBernoulliPowerSeries_odd]
  ring

/-- The coefficient of `x^(2k+1)` in `φ ψ` for an even series `φ`. -/
theorem coeff_even_mul (φ ψ : ℚ⟦X⟧) (hodd : ∀ j, coeff (2 * j + 1) φ = 0) (k : ℕ) :
    coeff (2 * k + 1) (φ * ψ)
      = ∑ j ∈ range (k + 1), coeff (2 * j) φ * coeff (2 * k + 1 - 2 * j) ψ := by
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, sum_range_two_mul,
    show ∑ j ∈ range (k + 1), coeff (2 * j + 1) φ * coeff (2 * k + 1 - (2 * j + 1)) ψ = 0 from
      sum_eq_zero fun j _ => by rw [hodd, zero_mul], add_zero]

theorem coeff_sinhSeries (m : ℕ) :
    coeff (2 * m + 1) (exp ℚ - evalNegHom (exp ℚ)) = 2 / ((2 * m + 1).factorial : ℚ) := by
  rw [map_sub, coeff_exp, algebraMap_rat_rat, show evalNegHom (exp ℚ) = rescale (-1 : ℚ) (exp ℚ)
    from rfl, coeff_rescale, coeff_exp, algebraMap_rat_rat, Odd.neg_one_pow ⟨m, rfl⟩]
  ring

/-- The kernel inverts `T_m = 1/(2m+1)!` under convolution:
`∑_{j≤k} κ_j/(2(k−j)+1)! = [k = 0]`. -/
theorem kernel_conv_eq (k : ℕ) :
    ∑ j ∈ range (k + 1), bernoulliKernel j / ((2 * (k - j) + 1).factorial : ℚ)
      = if k = 0 then 1 else 0 := by
  have h := congrArg (coeff (2 * k + 1)) kernel_mul_sinh
  have hR : coeff (2 * k + 1) (2 * X : ℚ⟦X⟧) = if k = 0 then 2 else 0 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_X]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
  rw [coeff_even_mul _ _ coeff_kernelSeries_odd, hR] at h
  have h2 : ∑ j ∈ range (k + 1), coeff (2 * j)
        (2 * scaledBernoulliPowerSeries - rescale (2 : ℚ) scaledBernoulliPowerSeries)
        * coeff (2 * k + 1 - 2 * j) (exp ℚ - evalNegHom (exp ℚ))
      = 2 * ∑ j ∈ range (k + 1), bernoulliKernel j / ((2 * (k - j) + 1).factorial : ℚ) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have := mem_range.mp hj
    rw [coeff_kernelSeries_even, show 2 * k + 1 - 2 * j = 2 * (k - j) + 1 by omega,
      coeff_sinhSeries]
    ring
  rw [h2] at h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ite_eq_left rfl] at h ⊢; linarith
  · rw [ite_eq_right (by omega)] at h ⊢; linarith

/-- Error propagation through (4.59): if the computed `e_k` satisfy the perturbed recurrence
`e_k + ∑_{j<k} e_j/(2(k−j)+1)! = ρ_k`, then `e_k = ∑_{j≤k} ρ_j κ_{k−j}`. -/
theorem error_propagation (e ρ : ℕ → ℚ)
    (h : ∀ k, e k + ∑ j ∈ range k, e j / ((2 * (k - j) + 1).factorial : ℚ) = ρ k) (k : ℕ) :
    e k = ∑ j ∈ range (k + 1), ρ j * bernoulliKernel (k - j) := by
  have hET : mk e * mk (fun m => 1 / ((2 * m + 1).factorial : ℚ)) = mk ρ := by
    ext n
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
    simp only [coeff_mk, Nat.sub_self, mul_zero, zero_add, Nat.factorial_one, Nat.cast_one,
      div_one, mul_one]
    rw [← h n, add_comm]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  have hKT : mk bernoulliKernel * mk (fun m => 1 / ((2 * m + 1).factorial : ℚ)) = 1 := by
    ext n
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_one]
    simp only [coeff_mk]
    rw [← kernel_conv_eq n]
    exact sum_congr rfl fun j _ => by ring
  have hE : mk e = mk ρ * mk bernoulliKernel := by
    calc mk e = mk e * (mk bernoulliKernel * mk (fun m => 1 / ((2 * m + 1).factorial : ℚ))) := by
          rw [hKT, mul_one]
      _ = (mk e * mk (fun m => 1 / ((2 * m + 1).factorial : ℚ))) * mk bernoulliKernel := by ring
      _ = mk ρ * mk bernoulliKernel := by rw [hET]
  have := congrArg (coeff k) hE
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
  simpa only [coeff_mk, Nat.succ_eq_add_one] using this

/-- `|C_k| ≥ 2/(2π)^(2k)` for `k ≥ 1` (from `ζ(2k) ≥ 1`). -/
theorem abs_scaledBernoulli_ge {k : ℕ} (hk : 1 ≤ k) :
    2 / (2 * Real.pi) ^ (2 * k) ≤ |(scaledBernoulli k : ℝ)| := by
  rw [scaledBernoulli_eq_zeta hk, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_two, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ (2 * k)),
    abs_of_nonneg (by linarith [one_le_zetaReal_two_mul hk] : (0 : ℝ) ≤ zetaReal (2 * k))]
  have hζ := one_le_zetaReal_two_mul hk
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
  rw [div_le_div_iff_of_pos_right hp]
  linarith

theorem abs_bernoulliKernel_eq {k : ℕ} (hk : 1 ≤ k) :
    |(bernoulliKernel k : ℝ)| = (4 ^ k - 2) * |(scaledBernoulli k : ℝ)| := by
  have h4 : (4 : ℝ) ≤ 4 ^ k := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hk
  rw [bernoulliKernel]
  push_cast
  rw [abs_mul, abs_of_neg (by linarith), neg_sub]

/-- (a): the kernel amplifies a relative perturbation of `C_0` into `C_k` by at least
`(4^k − 2)·6/π²`, i.e. `≍ 4^k`. -/
theorem kernel_amplification_ge {k : ℕ} (hk : 1 ≤ k) :
    (4 ^ k - 2) * (6 / Real.pi ^ 2) * |(scaledBernoulli k : ℝ)| ≤ |(bernoulliKernel k : ℝ)| := by
  rw [abs_bernoulliKernel_eq hk]
  have h4 : (4 : ℝ) ≤ 4 ^ k := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hC := abs_scaledBernoulli_le hk
  have hC' := abs_scaledBernoulli_ge hk
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
  -- `(6/π²)|C_k| ≤ (6/π²)(π²/3)/(2π)^(2k) = 2/(2π)^(2k) ≤ |C_k|`
  have h6 : 6 / Real.pi ^ 2 * |(scaledBernoulli k : ℝ)| ≤ |(scaledBernoulli k : ℝ)| := by
    calc 6 / Real.pi ^ 2 * |(scaledBernoulli k : ℝ)|
        ≤ 6 / Real.pi ^ 2 * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * k)) := by gcongr
      _ = 2 / (2 * Real.pi) ^ (2 * k) := by field_simp; ring
      _ ≤ |(scaledBernoulli k : ℝ)| := hC'
  calc (4 ^ k - 2) * (6 / Real.pi ^ 2) * |(scaledBernoulli k : ℝ)|
      = (4 ^ k - 2) * (6 / Real.pi ^ 2 * |(scaledBernoulli k : ℝ)|) := by ring
    _ ≤ (4 ^ k - 2) * |(scaledBernoulli k : ℝ)| := mul_le_mul_of_nonneg_left h6 (by linarith)

/-- `|κ_m| ≤ 4^m |C_m| = |D_m|`, the size of the terms of the stable recurrence (4.60). -/
theorem abs_bernoulliKernel_le (m : ℕ) :
    |(bernoulliKernel m : ℝ)| ≤ 4 ^ m * |(scaledBernoulli m : ℝ)| := by
  rw [bernoulliKernel]
  push_cast
  rw [abs_mul]
  have h1 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
  have : |(2 : ℝ) - 4 ^ m| ≤ 4 ^ m := by
    rw [abs_le]; constructor <;> linarith
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-- (b): in the stable recurrence, a relative perturbation of `D_j = 4^j C_j` reaches `D_k`
through `κ_{k−j}` with amplification at most `π⁴/18 = O(1)` (`1 ≤ j < k`). -/
theorem kernel_amplification_le {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    |(bernoulliKernel (k - j) : ℝ)| * (4 ^ j * |(scaledBernoulli j : ℝ)|)
      ≤ Real.pi ^ 4 / 18 * (4 ^ k * |(scaledBernoulli k : ℝ)|) := by
  have hkj : 1 ≤ k - j := by omega
  have h1 := abs_bernoulliKernel_le (k - j)
  have hCkj := abs_scaledBernoulli_le hkj
  have hCj := abs_scaledBernoulli_le hj
  have hCk := abs_scaledBernoulli_ge (by omega : 1 ≤ k)
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
  have hsplit : (4 : ℝ) ^ (k - j) * 4 ^ j = 4 ^ k := by rw [← pow_add]; congr 1; omega
  have hsplit' : ((2 * Real.pi) ^ (2 * (k - j)) * (2 * Real.pi) ^ (2 * j) : ℝ)
      = (2 * Real.pi) ^ (2 * k) := by rw [← pow_add]; congr 1; omega
  calc |(bernoulliKernel (k - j) : ℝ)| * (4 ^ j * |(scaledBernoulli j : ℝ)|)
      ≤ (4 ^ (k - j) * |(scaledBernoulli (k - j) : ℝ)|) * (4 ^ j * |(scaledBernoulli j : ℝ)|) := by
        gcongr
    _ ≤ (4 ^ (k - j) * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * (k - j))))
        * (4 ^ j * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * j))) := by gcongr
    _ = Real.pi ^ 4 / 18 * (4 ^ k * (2 / (2 * Real.pi) ^ (2 * k))) := by
        rw [← hsplit, ← hsplit']
        field_simp
        ring
    _ ≤ Real.pi ^ 4 / 18 * (4 ^ k * |(scaledBernoulli k : ℝ)|) := by gcongr

end Exercise435

section Exercise436

open PowerSeries

/-- The function `x/(e^x − 1) + x/2` of (4.57) is even: this is why the odd Bernoulli numbers
beyond `B_1 = −1/2` vanish. -/
theorem div_exp_sub_one_add_half_even (x : ℝ) :
    (-x) / (Real.exp (-x) - 1) + (-x) / 2 = x / (Real.exp x - 1) + x / 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 : Real.exp x - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => hx (Real.exp_eq_one_iff x |>.mp h)
  have hE : 0 < Real.exp x := Real.exp_pos x
  have h3 : (1 : ℝ) - Real.exp x ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => hx (Real.exp_eq_one_iff x |>.mp h.symm)
  have hexp : (Real.exp x)⁻¹ - 1 = (1 - Real.exp x) / Real.exp x := by field_simp
  rw [Real.exp_neg, hexp]
  field_simp
  ring

/-- The odd Bernoulli numbers beyond `B_1` vanish (Mathlib's `bernoulli_eq_zero_of_odd`). -/
theorem bernoulli_odd_eq_zero' (j : ℕ) : bernoulli (2 * j + 3) = 0 :=
  bernoulli_eq_zero_of_odd ⟨j + 1, by ring⟩ (by omega)

/-- (4.57) as a formal power series: `x/(e^x − 1) + x/2 = ∑_k C_k x^(2k)`, i.e. the series has
coefficient `C_k = B_{2k}/(2k)!` at `x^(2k)` and `0` at `x^(2k+1)`. -/
theorem scaledBernoulliPowerSeries_eq :
    scaledBernoulliPowerSeries = bernoulliPowerSeries ℚ + C (1 / 2 : ℚ) * X ∧
      (∀ k, coeff (2 * k) scaledBernoulliPowerSeries = bernoulli (2 * k) / (2 * k).factorial) ∧
      ∀ k, coeff (2 * k + 1) scaledBernoulliPowerSeries = 0 :=
  ⟨rfl, fun k => coeff_scaledBernoulliPowerSeries_even k,
    fun k => coeff_scaledBernoulliPowerSeries_odd k⟩

/-- (4.62) in the text's indexing: `T_j = (−1)^(j−1) 2^(2j) (2^(2j) − 1) B_{2j} / (2j)` for
`j ≥ 1`. -/
theorem tangentNumber_eq_bernoulli' {j : ℕ} (hj : 1 ≤ j) :
    (tangentNumber j : ℚ)
      = (-1) ^ (j - 1) * 2 ^ (2 * j) * (2 ^ (2 * j) - 1) * bernoulli (2 * j) / (2 * j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [tangentNumber_eq_bernoulli k, Nat.add_sub_cancel,
    show (2 : ℚ) ^ (2 * (k + 1)) = 4 ^ (k + 1) by rw [pow_mul]; norm_num]
  push_cast
  ring

end Exercise436

section Exercise437

/-- `|B_{2k}| = 2 (2k)! ζ(2k) / (2π)^(2k)` for `k ≥ 1`. -/
theorem abs_bernoulli_two_mul_eq {k : ℕ} (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)|
      = 2 * (2 * k).factorial * zetaReal (2 * k) / (2 * Real.pi) ^ (2 * k) := by
  rw [bernoulli_two_mul_eq_zeta hk, abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_two,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * k).factorial),
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ (2 * k)),
    abs_of_nonneg (by linarith [one_le_zetaReal_two_mul hk] : (0 : ℝ) ≤ zetaReal (2 * k))]

/-- `|T_k| = 2 (4^k − 1) (2k−1)! ζ(2k) / π^(2k)` for `k ≥ 1`. -/
theorem abs_tangentNumber_eq {k : ℕ} (hk : 1 ≤ k) :
    |(tangentNumber k : ℝ)|
      = 2 * (4 ^ k - 1) * (2 * k - 1).factorial * zetaReal (2 * k) / Real.pi ^ (2 * k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hT : (tangentNumber (m + 1) : ℝ) = (-1) ^ m * 4 ^ (m + 1) * (4 ^ (m + 1) - 1)
      * (bernoulli (2 * (m + 1)) : ℝ) / (2 * (m + 1)) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (tangentNumber_eq_bernoulli m)
    push_cast at this
    exact this
  have h4 : (1 : ℝ) < 4 ^ (m + 1) := one_lt_pow₀ (by norm_num) (by omega)
  rw [hT, abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (m + 1)), abs_of_pos (by linarith),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((m : ℝ) + 1)), abs_bernoulli_two_mul_eq hk,
    show (2 * (m + 1)).factorial = (2 * (m + 1)) * (2 * m + 1).factorial by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ],
    show 2 * (m + 1) - 1 = 2 * m + 1 by omega, mul_pow,
    show (2 : ℝ) ^ (2 * (m + 1)) = 4 ^ (m + 1) by rw [pow_mul]; norm_num]
  push_cast
  have hπ : (0 : ℝ) < Real.pi ^ (2 * (m + 1)) := by positivity
  field_simp

/-- `(4/π²)^k (2k−1)! ≤ |T_k| ≤ (π²/3)(2k−1)!`. -/
theorem abs_tangentNumber_bounds {k : ℕ} (hk : 1 ≤ k) :
    (4 / Real.pi ^ 2) ^ k * (2 * k - 1).factorial ≤ |(tangentNumber k : ℝ)| ∧
      |(tangentNumber k : ℝ)| ≤ Real.pi ^ 2 / 3 * (2 * k - 1).factorial := by
  rw [abs_tangentNumber_eq hk]
  have hζ1 := one_le_zetaReal_two_mul hk
  have hζ2 := zetaReal_two_mul_le hk
  have hF : (0 : ℝ) < (2 * k - 1).factorial := by positivity
  have hπ : (0 : ℝ) < Real.pi ^ (2 * k) := by positivity
  have h4 : (4 : ℝ) ≤ 4 ^ k := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hπ2 : (4 : ℝ) ^ k ≤ Real.pi ^ (2 * k) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by nlinarith [Real.pi_gt_three]) k
  constructor
  · rw [div_pow, ← pow_mul, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hπ]
    nlinarith [mul_nonneg hF.le (sub_nonneg.mpr hζ1), mul_pos hF (by linarith : (0:ℝ) < 4 ^ k - 1)]
  · rw [div_le_iff₀ hπ]
    have hA : (0 : ℝ) ≤ 2 * (4 ^ k - 1) * (2 * k - 1).factorial := by
      have := hF.le; nlinarith
    have hB : (0 : ℝ) ≤ ((2 * k - 1).factorial : ℝ) * (Real.pi ^ 2 / 3) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hζ2 hA, mul_le_mul_of_nonneg_right hπ2 hB]

/-- Stirling: `m ln m − m ≤ ln m! ≤ m ln m − m + 1 + (ln m)/2` for `m ≥ 1`. -/
theorem log_factorial_bounds {m : ℕ} (hm : 1 ≤ m) :
    m * Real.log m - m ≤ Real.log m.factorial ∧
      Real.log m.factorial ≤ m * Real.log m - m + 1 + Real.log m / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hF : (0 : ℝ) < m.factorial := by positivity
  have hpow : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hlogpow : Real.log (((m : ℝ) / Real.exp 1) ^ m) = m * Real.log m - m := by
    rw [Real.log_pow, Real.log_div hm0.ne' (Real.exp_pos 1).ne', Real.log_exp]; ring
  constructor
  · have h := Stirling.le_factorial_stirling m
    have hs : 1 ≤ Real.sqrt (2 * Real.pi * m) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [Real.pi_gt_three]
    have h' : ((m : ℝ) / Real.exp 1) ^ m ≤ m.factorial := by nlinarith
    rw [← hlogpow]
    exact Real.log_le_log hpow h'
  · have h := factorial_le_stirling_upper hm
    calc Real.log m.factorial ≤ Real.log (Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m) :=
          Real.log_le_log hF h
      _ = m * Real.log m - m + 1 + Real.log m / 2 := by
          rw [Real.log_mul (by positivity) hpow.ne', Real.log_mul (Real.exp_pos 1).ne'
            (Real.sqrt_pos.mpr hm0).ne', Real.log_exp, Real.log_sqrt hm0.le, hlogpow]
          ring

/-- (a): `2k ln k − 4k − ln(2k) ≤ ln|T_k| ≤ 2k ln k + 3`, so the bit size of `T_k` is
`∼ 2k lg k`. -/
theorem log_abs_tangentNumber_bounds {k : ℕ} (hk : 1 ≤ k) :
    2 * k * Real.log k - 4 * k - Real.log (2 * k) ≤ Real.log |(tangentNumber k : ℝ)| ∧
      Real.log |(tangentNumber k : ℝ)| ≤ 2 * k * Real.log k + 3 := by
  obtain ⟨hlo, hhi⟩ := abs_tangentNumber_bounds hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hF : (0 : ℝ) < (2 * k - 1).factorial := by positivity
  have hT : 0 < |(tangentNumber k : ℝ)| := lt_of_lt_of_le (by positivity) hlo
  -- `(2k−1)! = (2k)!/(2k)`
  have hfac : ((2 * k - 1).factorial : ℝ) = (2 * k).factorial / (2 * k) := by
    have : (2 * k).factorial = 2 * k * (2 * k - 1).factorial := by
      rw [show 2 * k = 2 * k - 1 + 1 by omega, Nat.factorial_succ,
        show 2 * k - 1 + 1 = 2 * k by omega]
    rw [this]; push_cast; field_simp
  have h2k : 1 ≤ 2 * k := by omega
  obtain ⟨hs1, hs2⟩ := log_factorial_bounds h2k
  have hlogF : Real.log ((2 * k - 1).factorial : ℝ)
      = Real.log ((2 * k).factorial : ℝ) - Real.log (2 * k) := by
    rw [hfac, Real.log_div (by positivity) (by positivity)]
  have hlog2k : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log k :=
    Real.log_mul two_ne_zero hk0.ne'
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog2k0 : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have e1 : 2 * (k : ℝ) * Real.log (2 * k) = 2 * (k * Real.log 2) + 2 * (k * Real.log k) := by
    rw [hlog2k]; ring
  have e4 : 2 * (k : ℝ) * Real.log k = 2 * (k * Real.log k) := by ring
  have p1 : (k : ℝ) * Real.log 2 ≤ k * 1 := mul_le_mul_of_nonneg_left hlog2 hk0.le
  push_cast at hs1 hs2
  constructor
  · -- `ln|T| ≥ k ln(4/π²) + ln(2k−1)!`, `ln(4/π²) ≥ −2`
    have hlog4 : -2 ≤ Real.log (4 / Real.pi ^ 2) := by
      have h1 : Real.log (4 / Real.pi ^ 2) = Real.log 4 - 2 * Real.log Real.pi := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      have h2 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
      have h3 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
      linarith
    calc 2 * k * Real.log k - 4 * k - Real.log (2 * k)
        ≤ k * Real.log (4 / Real.pi ^ 2)
            + (Real.log ((2 * k).factorial : ℝ) - Real.log (2 * k)) := by
          nlinarith [hlog4, hs1, hlog2k, hlog2]
      _ = Real.log ((4 / Real.pi ^ 2) ^ k * (2 * k - 1).factorial) := by
          rw [Real.log_mul (by positivity) hF.ne', Real.log_pow, hlogF]
      _ ≤ Real.log |(tangentNumber k : ℝ)| := Real.log_le_log (by positivity) hlo
  · have hpi23 : Real.log (Real.pi ^ 2 / 3) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    calc Real.log |(tangentNumber k : ℝ)|
        ≤ Real.log (Real.pi ^ 2 / 3 * (2 * k - 1).factorial) := Real.log_le_log hT hhi
      _ = Real.log (Real.pi ^ 2 / 3) + (Real.log ((2 * k).factorial : ℝ) - Real.log (2 * k)) := by
          rw [Real.log_mul (by positivity) hF.ne', hlogF]
      _ ≤ 2 * k * Real.log k + 3 := by linarith [hpi23, hs2, e1, e4, p1, hlog2k0]

/-- (b), the denominator: `ln den B_{2k} ≤ 4k ln 2` (from `den ∣ 4^k (4^k − 1)`). -/
theorem log_bernoulli_den_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((bernoulli (2 * k)).den : ℝ) ≤ 4 * k * Real.log 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hdvd := bernoulli_den_dvd m
  have h4 : (1 : ℤ) < 4 ^ (m + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hle : ((bernoulli (2 * (m + 1))).den : ℤ) ≤ 4 ^ (m + 1) * (4 ^ (m + 1) - 1) :=
    Int.le_of_dvd (by nlinarith) hdvd
  have hle' : ((bernoulli (2 * (m + 1))).den : ℝ) ≤ 16 ^ (m + 1) := by
    have : ((bernoulli (2 * (m + 1))).den : ℝ) ≤ 4 ^ (m + 1) * (4 ^ (m + 1) - 1) := by
      exact_mod_cast hle
    have h16 : (16 : ℝ) ^ (m + 1) = 4 ^ (m + 1) * 4 ^ (m + 1) := by rw [← mul_pow]; norm_num
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) (m + 1)]
  have hden : (0 : ℝ) < (bernoulli (2 * (m + 1))).den := by exact_mod_cast Rat.den_pos _
  calc Real.log ((bernoulli (2 * (m + 1))).den : ℝ) ≤ Real.log (16 ^ (m + 1)) :=
        Real.log_le_log hden hle'
    _ = 4 * ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring

/-- (b): the exact rational `B_{2k} = num/den` has
`2k ln k − 8k ≤ ln|num| + ln den ≤ 2k ln k + 6k + 3`, so it also needs `∼ 2k lg k` bits (almost
all of them in the numerator, the denominator having only `O(k)` bits). -/
theorem log_bernoulli_num_den_bounds {k : ℕ} (hk : 1 ≤ k) :
    2 * k * Real.log k - 8 * k
        ≤ Real.log |((bernoulli (2 * k)).num : ℝ)| + Real.log ((bernoulli (2 * k)).den : ℝ) ∧
      Real.log |((bernoulli (2 * k)).num : ℝ)| + Real.log ((bernoulli (2 * k)).den : ℝ)
        ≤ 2 * k * Real.log k + 6 * k + 3 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hB := abs_bernoulli_two_mul_eq hk
  have hζ1 := one_le_zetaReal_two_mul hk
  have hζ2 := zetaReal_two_mul_le hk
  have hden : (0 : ℝ) < (bernoulli (2 * k)).den := by exact_mod_cast Rat.den_pos _
  have hBpos : 0 < |(bernoulli (2 * k) : ℝ)| := by rw [hB]; positivity
  -- `|B| = |num|/den`, so `ln|num| = ln|B| + ln den`
  have hnum : Real.log |((bernoulli (2 * k)).num : ℝ)|
      = Real.log |(bernoulli (2 * k) : ℝ)| + Real.log ((bernoulli (2 * k)).den : ℝ) := by
    have hcast : ((bernoulli (2 * k) : ℚ) : ℝ)
        = ((bernoulli (2 * k)).num : ℝ) / (bernoulli (2 * k)).den := Rat.cast_def _
    have hnum0 : ((bernoulli (2 * k)).num : ℝ) ≠ 0 := by
      intro h0; rw [hcast, h0, zero_div, abs_zero] at hBpos; exact lt_irrefl _ hBpos
    rw [hcast, abs_div, abs_of_pos hden, Real.log_div (abs_ne_zero.mpr hnum0) hden.ne']
    ring
  have hden0 : 0 ≤ Real.log ((bernoulli (2 * k)).den : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Rat.den_pos _)
  have hdenle := log_bernoulli_den_le hk
  have h2k : 1 ≤ 2 * k := by omega
  obtain ⟨hs1, hs2⟩ := log_factorial_bounds h2k
  push_cast at hs1 hs2
  have hlog2k : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log k :=
    Real.log_mul two_ne_zero hk0.ne'
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogpi : Real.log Real.pi ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_lt_four]
  have hlogpi0 : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlogB : Real.log |(bernoulli (2 * k) : ℝ)|
      = Real.log 2 + Real.log ((2 * k).factorial : ℝ) + Real.log (zetaReal (2 * k))
        - 2 * k * (Real.log 2 + Real.log Real.pi) := by
    rw [hB, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by linarith), Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul two_ne_zero Real.pi_pos.ne']
    push_cast; ring
  have hζlog0 : 0 ≤ Real.log (zetaReal (2 * k)) := Real.log_nonneg hζ1
  have hζlog : Real.log (zetaReal (2 * k)) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e1 : 2 * (k : ℝ) * Real.log (2 * k) = 2 * (k * Real.log 2) + 2 * (k * Real.log k) := by
    rw [hlog2k]; ring
  have e2 : 2 * (k : ℝ) * (Real.log 2 + Real.log Real.pi)
      = 2 * (k * Real.log 2) + 2 * (k * Real.log Real.pi) := by ring
  have e3 : 4 * (k : ℝ) * Real.log 2 = 4 * (k * Real.log 2) := by ring
  have e4 : 2 * (k : ℝ) * Real.log k = 2 * (k * Real.log k) := by ring
  have p1 : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hk0.le
  have p2 : 0 ≤ (k : ℝ) * Real.log Real.pi := mul_nonneg hk0.le hlogpi0.le
  have p3 : (k : ℝ) * Real.log Real.pi ≤ k * 3 := mul_le_mul_of_nonneg_left hlogpi hk0.le
  have p4 : 0 ≤ (k : ℝ) * Real.log 2 := mul_nonneg hk0.le hlog2'.le
  constructor
  · rw [hnum]
    linarith [hlogB, hs1, e1, e2, e4, p3, p4, hζlog0, hden0]
  · rw [hnum]
    have hlog2k' : Real.log (2 * (k : ℝ)) ≤ 2 * k - 1 := by
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * k)]
    linarith [hlogB, hs2, e1, e2, e3, e4, p1, p2, hζlog, hdenle, hlog2k', hlog2]

end Exercise437

section Exercise438

/-- One update of Algorithm TangentNumbers is one instance of (4.63): if the row holds
`a_{j−1} = p_{j+k−3, j−k}` (the entry just updated in this pass) and `a_j = p_{j+k−3, j−k+2}`
(not yet updated), `2 ≤ k ≤ j`, then `(j−k) a_{j−1} + (j−k+2) a_j = p_{j+k−2, j−k+1}`. -/
theorem tangentStep_eq_coeff {k j : ℕ} (hk : 2 ≤ k) (hkj : k ≤ j) (a : ℕ → ℕ)
    (h1 : (a (j - 1) : ℤ) = (tanDerivPoly (j + k - 3)).coeff (j - k))
    (h2 : (a j : ℤ) = (tanDerivPoly (j + k - 3)).coeff (j - k + 2)) :
    (tangentStep k j a j : ℤ) = (tanDerivPoly (j + k - 2)).coeff (j - k + 1) := by
  rw [tangentStep, Function.update_self]
  push_cast
  rw [h1, h2, show j + k - 2 = j + k - 3 + 1 by omega, coeff_tanDerivPoly_succ]

/-- Exercise 4.38: Algorithm TangentNumbers is correct — after the passes `k = 2, …, m` the row
holds `T_1, …, T_m`. -/
theorem algorithm_tangentNumbers_correct {m : ℕ} (hm : 1 ≤ m) :
    ∀ j, 1 ≤ j → j ≤ m → (tangentNumbersModel m j : ℤ) = tangentNumber j :=
  fun _ h1 hjm => tangentNumbersModel_eq hm h1 hjm

end Exercise438

section Exercise439

open Finset Polynomial

theorem eval_one_tanDerivPoly_nonneg (n : ℕ) : 0 ≤ (tanDerivPoly n).eval 1 := by
  have hdeg : (tanDerivPoly n).natDegree < n + 2 := by rw [natDegree_tanDerivPoly]; omega
  rw [eval_eq_sum_range' hdeg]
  exact sum_nonneg fun i _ => by simpa using coeff_tanDerivPoly_nonneg n i

/-- `P_n(1) ≤ 2^n (n+1)!`: from `P_{n+1} = P_n' (1 + X²)`, `P_{n+1}(1) = 2 P_n'(1)`, and
`P_n'(1) = ∑ i p_{n,i} ≤ (n+1) P_n(1)`. -/
theorem eval_one_tanDerivPoly_le (n : ℕ) :
    (tanDerivPoly n).eval 1 ≤ 2 ^ n * ((n + 1).factorial : ℤ) := by
  induction n with
  | zero => simp [tanDerivPoly_zero]
  | succ n ih =>
    rw [tanDerivPoly_succ, eval_mul, eval_add, eval_one, eval_pow, eval_X, one_pow]
    have hder : (tanDerivPoly n).derivative.eval 1 ≤ (n + 1) * (tanDerivPoly n).eval 1 := by
      rw [derivative_eval, eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def, mul_sum]
      refine sum_le_sum fun i hi => ?_
      have hi' : i ≤ n + 1 := by
        have := le_natDegree_of_mem_supp i hi
        rwa [natDegree_tanDerivPoly] at this
      have hnn := coeff_tanDerivPoly_nonneg n i
      have hic : (i : ℤ) ≤ n + 1 := by exact_mod_cast hi'
      simp only [one_pow, mul_one]
      nlinarith
    have hP := eval_one_tanDerivPoly_nonneg n
    have h0 : (0 : ℤ) ≤ 2 ^ n * ((n + 1).factorial : ℤ) := by positivity
    calc (tanDerivPoly n).derivative.eval 1 * (1 + 1)
        ≤ (n + 1) * (tanDerivPoly n).eval 1 * 2 := by linarith
      _ ≤ (n + 1) * (2 ^ n * ((n + 1).factorial : ℤ)) * 2 := by
          have : (0 : ℤ) ≤ n + 1 := by positivity
          nlinarith
      _ ≤ 2 ^ (n + 1) * ((n + 1 + 1).factorial : ℤ) := by
          rw [Nat.factorial_succ (n + 1), pow_succ]
          push_cast
          nlinarith [h0]

/-- Every coefficient is at most the value at `1` (all coefficients are nonnegative). -/
theorem coeff_tanDerivPoly_le_eval_one (n i : ℕ) :
    (tanDerivPoly n).coeff i ≤ (tanDerivPoly n).eval 1 := by
  have hdeg : (tanDerivPoly n).natDegree < n + 2 := by rw [natDegree_tanDerivPoly]; omega
  rw [eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one]
  rcases Nat.lt_or_ge i (n + 2) with hi | hi
  · exact single_le_sum (fun j _ => coeff_tanDerivPoly_nonneg n j) (mem_range.mpr hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_tanDerivPoly]; omega)]
    exact sum_nonneg fun j _ => coeff_tanDerivPoly_nonneg n j

/-- The intermediate entries `p_{n,i}`, `n + 1 ≤ 2m`, of Algorithm TangentNumbers have at most
`2m (lg(2m) + 2)` bits. -/
theorem size_coeff_tanDerivPoly_le {m n i : ℕ} (hn : n + 1 ≤ 2 * m) :
    Nat.size ((tanDerivPoly n).coeff i).toNat ≤ 2 * m * (Nat.log 2 (2 * m) + 2) := by
  have hnn := coeff_tanDerivPoly_nonneg n i
  have h1 : ((tanDerivPoly n).coeff i).toNat ≤ 2 ^ n * (n + 1).factorial := by
    have h := (coeff_tanDerivPoly_le_eval_one n i).trans (eval_one_tanDerivPoly_le n)
    have ht : ((((tanDerivPoly n).coeff i).toNat : ℕ) : ℤ) = (tanDerivPoly n).coeff i :=
      Int.toNat_of_nonneg hnn
    exact_mod_cast ht ▸ h
  have hfac : (n + 1).factorial < 2 ^ ((n + 1) * (Nat.log 2 (n + 1) + 1)) :=
    lt_of_lt_of_le (Nat.lt_size_self _)
      (Nat.pow_le_pow_right (by norm_num) (size_factorial_le (Nat.succ_pos n)))
  have hlog : Nat.log 2 (n + 1) ≤ Nat.log 2 (2 * m) := Nat.log_mono_right hn
  have hexp : n + (n + 1) * (Nat.log 2 (n + 1) + 1) ≤ 2 * m * (Nat.log 2 (2 * m) + 2) := by
    have := Nat.mul_le_mul hn (Nat.add_le_add_right hlog 1)
    nlinarith
  rw [Nat.size_le]
  calc ((tanDerivPoly n).coeff i).toNat ≤ 2 ^ n * (n + 1).factorial := h1
    _ < 2 ^ n * 2 ^ ((n + 1) * (Nat.log 2 (n + 1) + 1)) :=
        Nat.mul_lt_mul_of_pos_left hfac (by positivity)
    _ = 2 ^ (n + (n + 1) * (Nat.log 2 (n + 1) + 1)) := by rw [← pow_add]
    _ ≤ 2 ^ (2 * m * (Nat.log 2 (2 * m) + 2)) := Nat.pow_le_pow_right (by norm_num) hexp

/-- The bit cost of Algorithm TangentNumbers: pass `k = 2, …, m`, step `j = k, …, m`, each
charged the bit length of the entry `p_{j+k−3, j−k+2}` it rewrites (the `O(log T_j)` of the
exercise's cost model). -/
noncomputable def tangentAlgorithmBits (m : ℕ) : ℕ :=
  ∑ k ∈ Icc 2 m, ∑ j ∈ Icc k m, Nat.size ((tanDerivPoly (j + k - 3)).coeff (j - k + 2)).toNat

/-- Exercise 4.39: the algorithm costs at most `m² · 2m (lg(2m) + 2) = O(m³ log m)`. -/
theorem tangentAlgorithmBits_le (m : ℕ) :
    tangentAlgorithmBits m ≤ m ^ 2 * (2 * m * (Nat.log 2 (2 * m) + 2)) := by
  unfold tangentAlgorithmBits
  set B := 2 * m * (Nat.log 2 (2 * m) + 2)
  have hB : ∀ k ∈ Icc 2 m, ∀ j ∈ Icc k m,
      Nat.size ((tanDerivPoly (j + k - 3)).coeff (j - k + 2)).toNat ≤ B := by
    intro k hk j hj
    have hk' := mem_Icc.mp hk
    have hj' := mem_Icc.mp hj
    exact size_coeff_tanDerivPoly_le (by omega)
  calc ∑ k ∈ Icc 2 m, ∑ j ∈ Icc k m, Nat.size ((tanDerivPoly (j + k - 3)).coeff (j - k + 2)).toNat
      ≤ ∑ k ∈ Icc 2 m, ∑ _j ∈ Icc k m, B :=
        sum_le_sum fun k hk => sum_le_sum fun j hj => hB k hk j hj
    _ = ∑ k ∈ Icc 2 m, (Icc k m).card * B := by simp [sum_const]
    _ ≤ ∑ _k ∈ Icc 2 m, m * B :=
        sum_le_sum fun k hk => by
          have := (mem_Icc.mp hk).1
          rw [Nat.card_Icc]; exact Nat.mul_le_mul_right _ (by omega)
    _ = (Icc 2 m).card * (m * B) := by rw [sum_const, smul_eq_mul]
    _ ≤ m * (m * B) := by rw [Nat.card_Icc]; exact Nat.mul_le_mul_right _ (by omega)
    _ = m ^ 2 * B := by ring

end Exercise439

section Exercise440

open Finset Polynomial

/-- The secant polynomials: `Dⁿ sec x = Q_n(tan x) sec x`, with `Q_0 = 1` and
`Q_{n+1} = X Q_n + (1 + X²) Q_n'` (from `D sec = sec tan`, `D tan = 1 + tan²`). -/
noncomputable def secDerivPoly : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => Polynomial.X * secDerivPoly n
    + (1 + Polynomial.X ^ 2) * Polynomial.derivative (secDerivPoly n)

theorem secDerivPoly_zero : secDerivPoly 0 = 1 := rfl

theorem secDerivPoly_succ (n : ℕ) :
    secDerivPoly (n + 1) = Polynomial.X * secDerivPoly n
      + (1 + Polynomial.X ^ 2) * Polynomial.derivative (secDerivPoly n) := rfl

/-- `q_{n+1,0} = q_{n,1}`. -/
theorem coeff_secDerivPoly_succ_zero (n : ℕ) :
    (secDerivPoly (n + 1)).coeff 0 = (secDerivPoly n).coeff 1 := by
  rw [secDerivPoly_succ, coeff_add, coeff_X_mul_zero, add_mul, one_mul, coeff_add,
    Polynomial.coeff_derivative, Polynomial.coeff_X_pow_mul']
  simp

/-- The secant analogue of (4.63): `q_{n+1,j+1} = (j+1) q_{n,j} + (j+2) q_{n,j+2}`. -/
theorem coeff_secDerivPoly_succ (n j : ℕ) :
    (secDerivPoly (n + 1)).coeff (j + 1)
      = (j + 1) * (secDerivPoly n).coeff j + (j + 2) * (secDerivPoly n).coeff (j + 2) := by
  rw [secDerivPoly_succ, coeff_add, coeff_X_mul, add_mul, one_mul, coeff_add,
    Polynomial.coeff_derivative, Polynomial.coeff_X_pow_mul']
  rcases j with _ | j
  · simp
    ring
  · rw [ite_eq_left (by omega), show j + 1 + 1 - 2 = j by omega, Polynomial.coeff_derivative,
      show j + 1 + 2 = j + 1 + 1 + 1 from rfl]
    push_cast
    ring

theorem coeff_secDerivPoly_nonneg (n j : ℕ) : 0 ≤ (secDerivPoly n).coeff j := by
  induction n generalizing j with
  | zero =>
    rw [secDerivPoly_zero, Polynomial.coeff_one]
    split_ifs <;> norm_num
  | succ n ih =>
    rcases j with _ | j
    · rw [coeff_secDerivPoly_succ_zero]; exact ih 1
    · rw [coeff_secDerivPoly_succ]
      have h1 := ih j
      have h2 := ih (j + 2)
      positivity

theorem coeff_secDerivPoly_eq_zero_of_lt (n : ℕ) : ∀ j, n < j → (secDerivPoly n).coeff j = 0 := by
  induction n with
  | zero =>
    intro j hj
    rw [secDerivPoly_zero, Polynomial.coeff_one, ite_eq_right (by omega)]
  | succ n ih =>
    intro j hj
    rcases j with _ | j
    · omega
    · rw [coeff_secDerivPoly_succ, ih j (by omega), ih (j + 2) (by omega)]
      ring

/-- The leading coefficient `q_{n,n} = n!`: the initial row of the algorithm. -/
theorem coeff_secDerivPoly_top (n : ℕ) : (secDerivPoly n).coeff n = n.factorial := by
  induction n with
  | zero => simp [secDerivPoly_zero]
  | succ n ih =>
    rw [coeff_secDerivPoly_succ, ih, coeff_secDerivPoly_eq_zero_of_lt n (n + 2) (by omega),
      Nat.factorial_succ]
    push_cast
    ring

/-- `Dⁿ sec x = Q_n(tan x) sec x` wherever `cos x ≠ 0`. -/
theorem iteratedDeriv_sec (n : ℕ) : ∀ x : ℝ, Real.cos x ≠ 0 →
    iteratedDeriv n (fun y => (Real.cos y)⁻¹) x
      = ((secDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan x) * (Real.cos x)⁻¹ := by
  induction n with
  | zero => intro x _; simp [secDerivPoly_zero]
  | succ n ih =>
    intro x hx
    have hU : IsOpen {y : ℝ | Real.cos y ≠ 0} := isOpen_ne_fun Real.continuous_cos continuous_const
    have heq : iteratedDeriv n (fun y => (Real.cos y)⁻¹) =ᶠ[nhds x]
        fun y => ((secDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y) * (Real.cos y)⁻¹ :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => ih y hy
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd1 : HasDerivAt (fun y => ((secDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y))
        ((derivative ((secDerivPoly n).map (Int.castRingHom ℝ))).eval (Real.tan x)
          * (1 / Real.cos x ^ 2)) x :=
      (Polynomial.hasDerivAt _ (Real.tan x)).comp x (Real.hasDerivAt_tan hx)
    have hd2 : HasDerivAt (fun y => (Real.cos y)⁻¹) (-(-Real.sin x) / Real.cos x ^ 2) x :=
      (Real.hasDerivAt_cos x).inv hx
    have hd : HasDerivAt
        (fun y => ((secDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y) * (Real.cos y)⁻¹)
        ((derivative ((secDerivPoly n).map (Int.castRingHom ℝ))).eval (Real.tan x)
            * (1 / Real.cos x ^ 2) * (Real.cos x)⁻¹
          + ((secDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan x)
            * (-(-Real.sin x) / Real.cos x ^ 2)) x := hd1.mul hd2
    rw [hd.deriv, secDerivPoly_succ, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X, derivative_map, eval_add, eval_mul, eval_mul, eval_add, eval_one,
      eval_pow, eval_X,
      show (1 : ℝ) + Real.tan x ^ 2 = (Real.cos x ^ 2)⁻¹ by
        rw [← Real.inv_one_add_tan_sq hx, inv_inv],
      ← Real.tan_mul_cos hx]
    field_simp
    ring

/-- `Dⁿ sec 0 = q_{n,0}`. -/
theorem iteratedDeriv_sec_zero (n : ℕ) :
    iteratedDeriv n (fun y => (Real.cos y)⁻¹) 0 = ((secDerivPoly n).coeff 0 : ℝ) := by
  rw [iteratedDeriv_sec n 0 (by simp), Real.tan_zero, Real.cos_zero, inv_one, mul_one,
    ← coeff_zero_eq_eval_zero, Polynomial.coeff_map, eq_intCast]

/-- The secant numbers `S_k = D^(2k) sec 0 = q_{2k,0}`: `∑ S_k x^(2k)/(2k)! = sec x`. -/
noncomputable def secantNumber (k : ℕ) : ℤ := (secDerivPoly (2 * k)).coeff 0

theorem iteratedDeriv_sec_zero_eq (k : ℕ) :
    iteratedDeriv (2 * k) (fun y => (Real.cos y)⁻¹) 0 = (secantNumber k : ℝ) :=
  iteratedDeriv_sec_zero _

theorem secantNumber_zero : secantNumber 0 = 1 := by simp [secantNumber, secDerivPoly_zero]

theorem secantNumber_one : secantNumber 1 = 1 := by
  have h11 := coeff_secDerivPoly_top 1
  have h20 := coeff_secDerivPoly_succ_zero 1
  norm_num [h11] at h20
  rw [secantNumber]
  norm_num [h20]

theorem secantNumber_two : secantNumber 2 = 5 := by
  have h11 := coeff_secDerivPoly_top 1
  have h20 := coeff_secDerivPoly_succ_zero 1
  norm_num [h11] at h20
  have h22 := coeff_secDerivPoly_top 2
  norm_num [Nat.factorial] at h22
  have h31 := coeff_secDerivPoly_succ 2 0
  norm_num [h20, h22] at h31
  have h40 := coeff_secDerivPoly_succ_zero 3
  norm_num [h31] at h40
  rw [secantNumber]
  norm_num [h40]

/-! The in-place algorithm. -/

/-- The initial row: `S_j ← j!` (`S_0 = 1`, `S_k = k S_{k−1}`). -/
def secantInit (j : ℕ) : ℕ := j.factorial

/-- One update `S_j ← (j − k) S_{j−1} + (j − k + 1) S_j`. -/
def secantStep (k j : ℕ) (a : ℕ → ℕ) : ℕ → ℕ :=
  Function.update a j ((j - k) * a (j - 1) + (j - k + 1) * a j)

/-- The inner loop of pass `k` after `s` steps (`j = k + 1, …, k + s`). -/
def secantPass (k : ℕ) (a : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => a
  | s + 1 => secantStep k (k + 1 + s) (secantPass k a s)

/-- The outer loop after `r` passes (`k = 1, …, r`) on a row `S_0, …, S_m`. -/
def secantOuter (m : ℕ) (a : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => a
  | r + 1 => secantPass (r + 1) (secantOuter m a r) (m - (r + 1))

/-- Algorithm SecantNumbers: the row after the passes `k = 1, …, m`. -/
def secantNumbersModel (m : ℕ) : ℕ → ℕ := secantOuter m secantInit m

/-- One update is one instance of the secant recurrence: if `a_{j−1} = q_{j+k−1, j−k−1}` and
`a_j = q_{j+k−1, j−k+1}` (`k + 1 ≤ j`), then `(j−k) a_{j−1} + (j−k+1) a_j = q_{j+k, j−k}`. -/
theorem secantStep_eq_coeff {k j : ℕ} (hkj : k + 1 ≤ j) (a : ℕ → ℕ)
    (h1 : (a (j - 1) : ℤ) = (secDerivPoly (j + k - 1)).coeff (j - k - 1))
    (h2 : (a j : ℤ) = (secDerivPoly (j + k - 1)).coeff (j - k + 1)) :
    (secantStep k j a j : ℤ) = (secDerivPoly (j + k)).coeff (j - k) := by
  obtain ⟨i, hi⟩ : ∃ i, j - k = i + 1 := ⟨j - k - 1, by omega⟩
  rw [secantStep, Function.update_self]
  push_cast
  rw [h1, h2, show j + k = j + k - 1 + 1 by omega, hi, coeff_secDerivPoly_succ,
    show j + k - 1 + 1 - 1 = j + k - 1 by omega, show i + 1 - 1 = i by omega,
    show i + 1 + 1 = i + 2 by omega]
  push_cast
  ring

/-- The invariant of pass `k ≥ 1`: positions `j < k` hold `S_j`, position `k` holds
`q_{2k−1,1} = S_k`, positions `k < j ≤ k + s` already hold `q_{j+k, j−k}`, positions `j > k + s`
still hold `q_{j+k−1, j−k+1}`. -/
theorem secantPass_spec {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (a : ℕ → ℕ)
    (hfin : ∀ j, j < k → (a j : ℤ) = secantNumber j)
    (hrow : ∀ j, k ≤ j → j ≤ m → (a j : ℤ) = (secDerivPoly (j + k - 1)).coeff (j - k + 1))
    (s : ℕ) :
    (∀ j, j < k → (secantPass k a s j : ℤ) = secantNumber j)
      ∧ (secantPass k a s k : ℤ) = (secDerivPoly (2 * k - 1)).coeff 1
      ∧ (∀ j, k + 1 ≤ j → j < k + 1 + s → j ≤ m →
          (secantPass k a s j : ℤ) = (secDerivPoly (j + k)).coeff (j - k))
      ∧ (∀ j, k + 1 + s ≤ j → j ≤ m →
          (secantPass k a s j : ℤ) = (secDerivPoly (j + k - 1)).coeff (j - k + 1)) := by
  induction s with
  | zero =>
    refine ⟨hfin, ?_, fun j _ hj _ => absurd hj (by omega), fun j hj hjm => hrow j (by omega) hjm⟩
    simp only [secantPass]
    rw [hrow k le_rfl hkm, show k + k - 1 = 2 * k - 1 by omega, Nat.sub_self]
  | succ s ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    simp only [secantPass]
    refine ⟨fun j hj => ?_, ?_, fun j hkj hj hjm => ?_, fun j hj hjm => ?_⟩
    · rw [secantStep, Function.update_of_ne (by omega)]
      exact ih1 j hj
    · rw [secantStep, Function.update_of_ne (by omega)]
      exact ih2
    · rcases eq_or_ne j (k + 1 + s) with rfl | hne
      · have h4 := ih4 (k + 1 + s) le_rfl hjm
        have h1 : (secantPass k a s (k + 1 + s - 1) : ℤ)
            = (secDerivPoly (k + 1 + s + k - 1)).coeff (k + 1 + s - k - 1) := by
          rcases Nat.eq_zero_or_pos s with rfl | hs
          · rw [show k + 1 + 0 - 1 = k by omega, show k + 1 + 0 + k - 1 = 2 * k - 1 + 1 by omega,
              show k + 1 + 0 - k - 1 = 0 by omega, coeff_secDerivPoly_succ_zero]
            exact ih2
          · rw [ih3 (k + 1 + s - 1) (by omega) (by omega) (by omega),
              show k + 1 + s - 1 + k = k + 1 + s + k - 1 by omega,
              show k + 1 + s - 1 - k = k + 1 + s - k - 1 by omega]
        exact secantStep_eq_coeff (by omega) _ h1 h4
      · rw [secantStep, Function.update_of_ne hne]
        exact ih3 j hkj (by omega) hjm
    · rw [secantStep, Function.update_of_ne (by omega)]
      exact ih4 j (by omega) hjm

/-- After the passes `k = 1, …, r` (`r ≤ m`): positions `j ≤ r` hold `S_j`, the rest hold
`q_{j+r, j−r}`. -/
theorem secantOuter_spec (m : ℕ) : ∀ r, r ≤ m →
    (∀ j, j < r + 1 → (secantOuter m secantInit r j : ℤ) = secantNumber j)
      ∧ (∀ j, r + 1 ≤ j → j ≤ m →
          (secantOuter m secantInit r j : ℤ) = (secDerivPoly (j + r)).coeff (j - r)) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, fun j _ _ => ?_⟩
    · obtain rfl : j = 0 := by omega
      simp [secantOuter, secantInit, secantNumber_zero]
    · simp only [secantOuter, secantInit]
      rw [add_zero, Nat.sub_zero, coeff_secDerivPoly_top]
  | succ r ih =>
    intro hr
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hs := secantPass_spec (k := r + 1) (m := m) (by omega) hr (secantOuter m secantInit r)
      ih1 (fun j hj hjm => by
        rw [ih2 j hj hjm, show j + (r + 1) - 1 = j + r by omega,
          show j - (r + 1) + 1 = j - r by omega]) (m - (r + 1))
    obtain ⟨h1, h2, h3, _⟩ := hs
    simp only [secantOuter]
    refine ⟨fun j hj => ?_, fun j hj hjm => h3 j hj (by omega) hjm⟩
    rcases Nat.lt_or_ge j (r + 1) with hlt | hge
    · exact h1 j hlt
    · obtain rfl : j = r + 1 := by omega
      rw [h2, secantNumber, show 2 * (r + 1) = 2 * (r + 1) - 1 + 1 by omega,
        coeff_secDerivPoly_succ_zero, Nat.add_sub_cancel]

/-- Exercise 4.40: Algorithm SecantNumbers computes `S_0, …, S_m` in place. -/
theorem secantNumbersModel_eq {m j : ℕ} (hjm : j ≤ m) :
    (secantNumbersModel m j : ℤ) = secantNumber j :=
  (secantOuter_spec m m le_rfl).1 j (by omega)

theorem secantNumbersModel_three :
    secantNumbersModel 3 0 = 1 ∧ secantNumbersModel 3 1 = 1 ∧ secantNumbersModel 3 2 = 5 ∧
      secantNumbersModel 3 3 = 61 := by
  decide

end Exercise440

section Exercise441

open PowerSeries

/-- `E(x) = ∑ x^k/(k+1)! = (e^x − 1)/x`, the series whose reciprocal is `∑ B_k x^k/k!`. -/
noncomputable def recipSeries : ℚ⟦X⟧ := mk fun k => 1 / ((k + 1).factorial : ℚ)

theorem X_mul_recipSeries : X * recipSeries = exp ℚ - 1 := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, coeff_exp_sub_one]; simp
  · rw [coeff_succ_X_mul, recipSeries, coeff_mk, coeff_exp_sub_one, ite_eq_right (by omega)]

/-- (4.56) as a reciprocal: `∑ B_k x^k/k! · ∑ x^k/(k+1)! = 1`. -/
theorem bernoulliPowerSeries_mul_recipSeries : bernoulliPowerSeries ℚ * recipSeries = 1 := by
  apply mul_right_cancel₀ (X_ne_zero (R := ℚ))
  rw [mul_assoc, mul_comm recipSeries, X_mul_recipSeries, bernoulliPowerSeries_mul_exp_sub_one,
    one_mul]

/-- One Newton step for a reciprocal: `R' = R(2 − ER)` satisfies `1 − ER' = (1 − ER)²`, so if
`R` is correct modulo `x^m` then `R'` is correct modulo `x^(2m)`. -/
theorem newton_reciprocal_step (E R : ℚ⟦X⟧) :
    1 - E * (R * (2 - E * R)) = (1 - E * R) ^ 2 := by ring

theorem newton_reciprocal_step_dvd {E R : ℚ⟦X⟧} {m : ℕ} (h : X ^ m ∣ 1 - E * R) :
    X ^ (2 * m) ∣ 1 - E * (R * (2 - E * R)) := by
  rw [newton_reciprocal_step, pow_two, two_mul, pow_add]
  exact mul_dvd_mul h h

/-- The coefficients `B_k/k!` of the reciprocal become the integers `num B_k` after scaling by
`k! · den B_k`: the series can be handled over `ℤ` with `O(k log k)`-bit coefficients
(Exercise 4.37). -/
theorem scaled_coeff_eq_num (k : ℕ) :
    bernoulli k / k.factorial * (k.factorial * (bernoulli k).den) = (bernoulli k).num := by
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, mul_comm (k.factorial : ℚ), ← mul_assoc, mul_div_assoc, div_self hf,
    mul_one, Rat.mul_den_eq_num]

/-- `lg y ≤ y` for real `y ≥ 1` (via `y < ⌊y⌋ + 1 ≤ 2^⌊y⌋`). -/
theorem logb_two_le_self {y : ℝ} (hy : 1 ≤ y) : Real.logb 2 y ≤ y := by
  rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith)]
  have hm : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hm' : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (⌊y⌋₊ : ℕ) := by
    have := Nat.lt_two_pow_self (n := ⌊y⌋₊)
    exact_mod_cast this
  calc y ≤ ⌊y⌋₊ + 1 := hm'.le
    _ ≤ (2 : ℝ) ^ (⌊y⌋₊ : ℕ) := h2
    _ = (2 : ℝ) ^ ((⌊y⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
    _ ≤ (2 : ℝ) ^ y := Real.rpow_le_rpow_of_exponent_le one_le_two hm

/-- In the quasi-linear model, one multiplication of `n² lg n`-bit integers (the Kronecker
substitution of two length-`n` polynomials with `O(n lg n)`-bit coefficients) costs at most
`3 n² (lg n)²`. -/
theorem quasiLinearCost_sq_log_le {n : ℝ} (hn : 2 ≤ n) :
    quasiLinearCost (n ^ 2 * Real.logb 2 n) ≤ 3 * n ^ 2 * Real.logb 2 n ^ 2 := by
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn
  have hlglg : Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) (logb_two_le_self (by linarith))
  unfold quasiLinearCost
  rw [Real.logb_mul (by positivity) (by linarith), Real.logb_pow]
  have h0 : 0 ≤ n ^ 2 * Real.logb 2 n := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hlglg h0]

end Exercise441

section Exercise442

open Finset PowerSeries

/-- Algorithm SeriesExponential: `b_0 = 1`, `k b_k = ∑_{j=1}^k j a_j b_{k−j}` (written with
`j = i + 1`). -/
noncomputable def seriesExp (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => (∑ i ∈ range (k + 1), ((i + 1 : ℕ) : ℚ) * a (i + 1) * seriesExp a (k - i)) / (k + 1)
termination_by k => k
decreasing_by omega

theorem seriesExp_zero (a : ℕ → ℚ) : seriesExp a 0 = 1 := by rw [seriesExp]

theorem seriesExp_succ (a : ℕ → ℚ) (k : ℕ) :
    seriesExp a (k + 1)
      = (∑ i ∈ range (k + 1), ((i + 1 : ℕ) : ℚ) * a (i + 1) * seriesExp a (k - i)) / (k + 1) := by
  rw [seriesExp]

theorem constantCoeff_mk_seriesExp (a : ℕ → ℚ) : constantCoeff (mk (seriesExp a)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, seriesExp_zero]

/-- The recurrence is the coefficient form of `B' = A' B`. -/
theorem derivative_mk_seriesExp (a : ℕ → ℚ) :
    d⁄dX (mk (seriesExp a)) = d⁄dX (mk a) * mk (seriesExp a) := by
  ext k
  rw [coeff_derivative, coeff_mk, seriesExp_succ, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (d⁄dX (mk a)) * coeff j (mk (seriesExp a)))]
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hk]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_derivative, coeff_mk, coeff_mk]
  push_cast
  ring

/-- (a): the output `B = ∑ b_k x^k` is the exponential of the input `A = ∑ a_k x^k` (`a_0 = 0`),
in the sense of Exercise 4.1: `log B = A`. Since `b_k` depends only on `a_1, …, a_k`, the first
`m + 1` coefficients are determined by `a_1, …, a_m`, i.e. `B = exp A + O(x^(m+1))`. -/
theorem logSeries_mk_seriesExp (a : ℕ → ℚ) (ha : a 0 = 0) :
    logSeries (mk (seriesExp a)) = mk a := by
  symm
  apply logSeries_unique
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, ha]
  · rw [derivative_mk_seriesExp, mul_assoc,
      PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_mk_seriesExp]; exact one_ne_zero), mul_one]

/-- (b): the coefficients of the Stirling series (4.38) as a series in `1/z`:
`a_{2k−1} = B_{2k}/(2k(2k−1))`, `a_{2k} = 0`. -/
noncomputable def stirlingLogCoeff (j : ℕ) : ℚ :=
  if j % 2 = 1 then bernoulli (j + 1) / ((j + 1) * j) else 0

/-- The terms of (4.38) are `a_j / x^j`. -/
theorem stirlingTerm_eq_stirlingLogCoeff (m : ℕ) (x : ℝ) :
    stirlingTerm (m + 1) x = (stirlingLogCoeff (2 * m + 1) : ℝ) / x ^ (2 * m + 1) := by
  rw [stirlingTerm, stirlingLogCoeff, ite_eq_left (by omega),
    show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
  push_cast
  rw [div_div]
  congr 1
  ring

/-- The coefficients `b_k` of `n! ∼ (n/e)^n √(2πn) ∑ b_k/n^k`. -/
noncomputable def stirlingCoeff : ℕ → ℚ := seriesExp stirlingLogCoeff

theorem stirlingLogCoeff_one : stirlingLogCoeff 1 = 1 / 12 := by
  simp [stirlingLogCoeff, bernoulli_two]; norm_num

theorem stirlingLogCoeff_two : stirlingLogCoeff 2 = 0 := by simp [stirlingLogCoeff]

theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

theorem stirlingLogCoeff_three : stirlingLogCoeff 3 = -1 / 360 := by
  simp [stirlingLogCoeff, bernoulli_four']; norm_num

theorem stirlingCoeff_zero : stirlingCoeff 0 = 1 := seriesExp_zero _

theorem stirlingCoeff_one : stirlingCoeff 1 = 1 / 12 := by
  rw [stirlingCoeff, seriesExp_succ]
  simp [stirlingLogCoeff_one, seriesExp_zero]

theorem stirlingCoeff_two : stirlingCoeff 2 = 1 / 288 := by
  have h1 := stirlingCoeff_one
  rw [stirlingCoeff] at h1 ⊢
  rw [seriesExp_succ]
  simp [sum_range_succ, stirlingLogCoeff_one, stirlingLogCoeff_two, seriesExp_zero, h1]
  norm_num

theorem stirlingCoeff_three : stirlingCoeff 3 = -139 / 51840 := by
  have h1 := stirlingCoeff_one
  have h2 := stirlingCoeff_two
  rw [stirlingCoeff] at h1 h2 ⊢
  rw [seriesExp_succ]
  simp [sum_range_succ, stirlingLogCoeff_one, stirlingLogCoeff_two, stirlingLogCoeff_three,
    seriesExp_zero, h1, h2]
  norm_num

end Exercise442

section Exercise443

/-- The algebraic deduction: if `K = (π/2)(1 + k²/4) + ε₁`, `|ε₁| ≤ A k⁴` (4.69), and
`K' = (2/π) ln(4/k) K − k²/4 + ε₂`, `|ε₂| ≤ B k⁴` (4.70), then
`ln(4/k) = (1 − k²/4) K' + k²/4 + E` with `|E| ≤ k⁴ ((1/16 + 2A/π) ln(4/k) + 1/16 + B)`.
Exactly, `E = (ln(4/k) − 1) k⁴/16 − (1 − k²/4)((2/π) ln(4/k) ε₁ + ε₂)`. -/
theorem second_order_deduction {k K K' A B : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (h69 : |K - Real.pi / 2 * (1 + k ^ 2 / 4)| ≤ A * k ^ 4)
    (h70 : |K' - (2 / Real.pi * Real.log (4 / k) * K - k ^ 2 / 4)| ≤ B * k ^ 4) :
    |Real.log (4 / k) - ((1 - k ^ 2 / 4) * K' + k ^ 2 / 4)|
      ≤ k ^ 4 * ((1 / 16 + 2 * A / Real.pi) * Real.log (4 / k) + 1 / 16 + B) := by
  set L := Real.log (4 / k) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    calc Real.exp 1 ≤ 4 := this
      _ ≤ 4 / k := by rw [le_div_iff₀ hk]; nlinarith
  set ε₁ := K - Real.pi / 2 * (1 + k ^ 2 / 4) with hε₁
  set ε₂ := K' - (2 / Real.pi * L * K - k ^ 2 / 4) with hε₂
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hE : L - ((1 - k ^ 2 / 4) * K' + k ^ 2 / 4)
      = (L - 1) * k ^ 4 / 16 - (1 - k ^ 2 / 4) * (2 / Real.pi * L * ε₁ + ε₂) := by
    rw [hε₁, hε₂]
    field_simp
    ring
  have hk4 : 0 ≤ k ^ 4 := by positivity
  have hone : 0 ≤ 1 - k ^ 2 / 4 := by nlinarith
  have hone' : 1 - k ^ 2 / 4 ≤ 1 := by nlinarith
  have hA : 0 ≤ A := by
    have := (abs_nonneg _).trans h69
    nlinarith [pow_pos hk 4]
  have hB : 0 ≤ B := by
    have := (abs_nonneg _).trans h70
    nlinarith [pow_pos hk 4]
  rw [hE]
  calc |(L - 1) * k ^ 4 / 16 - (1 - k ^ 2 / 4) * (2 / Real.pi * L * ε₁ + ε₂)|
      ≤ |(L - 1) * k ^ 4 / 16| + |(1 - k ^ 2 / 4) * (2 / Real.pi * L * ε₁ + ε₂)| := abs_sub _ _
    _ ≤ (L + 1) * k ^ 4 / 16 + 1 * (2 / Real.pi * L * (A * k ^ 4) + B * k ^ 4) := by
        gcongr
        · rw [abs_div, abs_mul, abs_of_nonneg hk4, abs_of_nonneg (by linarith : (0:ℝ) ≤ L - 1),
            abs_of_pos (by norm_num : (0:ℝ) < 16)]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hk4)
            (by norm_num)
        · rw [abs_mul, abs_of_nonneg hone]
          gcongr
          calc |2 / Real.pi * L * ε₁ + ε₂| ≤ |2 / Real.pi * L * ε₁| + |ε₂| := abs_add_le _ _
            _ ≤ 2 / Real.pi * L * (A * k ^ 4) + B * k ^ 4 := by
                gcongr
                rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 / Real.pi * L)]
                gcongr
    _ = k ^ 4 * ((1 / 16 + 2 * A / Real.pi) * L + 1 / 16 + B) := by field_simp; ring

/-- The expansion with the proven (4.69) constant `A = 3π/16` (`ellipticK_bounds`, `k² ≤ 1/2`):
`ln(4/k) = (1 − k²/4) (π/2)/AGM(1,k) + k²/4 + O(k⁴ ln(4/k))`, with
`|O(·)| ≤ k⁴ ((7/16) ln(4/k) + 1/16 + B)` where `B` is the second-order constant of (4.70)
(an assumption here; numerically `B ≈ 21/128`). -/
theorem second_order_expansion {k B : ℝ} (hk : 0 < k) (hk2 : k ^ 2 ≤ 1 / 2)
    (h70 : |Real.pi / 2 / AGM 1 k
      - (2 / Real.pi * Real.log (4 / k) * ellipticK k - k ^ 2 / 4)| ≤ B * k ^ 4) :
    |Real.log (4 / k) - ((1 - k ^ 2 / 4) * (Real.pi / 2 / AGM 1 k) + k ^ 2 / 4)|
      ≤ k ^ 4 * (7 / 16 * Real.log (4 / k) + 1 / 16 + B) := by
  have hk1 : k ≤ 1 := by nlinarith
  obtain ⟨hlo, hhi⟩ := ellipticK_bounds hk2
  have h69 : |ellipticK k - Real.pi / 2 * (1 + k ^ 2 / 4)| ≤ 3 * Real.pi / 16 * k ^ 4 := by
    rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]
  have h := second_order_deduction hk hk1 h69 h70
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  calc _ ≤ _ := h
    _ = k ^ 4 * (7 / 16 * Real.log (4 / k) + 1 / 16 + B) := by
        congr 1
        field_simp
        ring

/-- The second-order AGM logarithm: `ln x ≈ (1 − 4/x²) (π/2)/AGM(1, 4/x) + 4/x²`. -/
noncomputable def agmLog2 (x : ℝ) : ℝ := (1 - 4 / x ^ 2) * agmLog x + 4 / x ^ 2

/-- Transport of an effective bound `|ln(4/k) − ((1 − k²/4) K' + k²/4)| ≤ k⁴ (c₁ ln(4/k) + c₂)`
(valid for `0 < k ≤ 1/2`) to `agmLog2`: `|agmLog2 x − ln x| ≤ (4/x)⁴ (c₁ ln x + c₂)` for `x ≥ 8`.
Numerically (see the ledger) `c₁ = 5/64`, `c₂ = 0` work. -/
theorem abs_agmLog2_sub_log_le {c₁ c₂ : ℝ}
    (hE : ∀ k : ℝ, 0 < k → k ≤ 1 / 2 →
      |Real.log (4 / k) - ((1 - k ^ 2 / 4) * (Real.pi / 2 / AGM 1 k) + k ^ 2 / 4)|
        ≤ k ^ 4 * (c₁ * Real.log (4 / k) + c₂))
    {x : ℝ} (hx : 8 ≤ x) :
    |agmLog2 x - Real.log x| ≤ (4 / x) ^ 4 * (c₁ * Real.log x + c₂) := by
  have hx0 : 0 < x := by linarith
  have hk : 0 < 4 / x := by positivity
  have hk2 : 4 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have h := hE (4 / x) hk hk2
  rw [show (4 : ℝ) / (4 / x) = x by field_simp] at h
  have e1 : (1 - 4 / x ^ 2) * (Real.pi / 2 / AGM 1 (4 / x)) + 4 / x ^ 2
      = (1 - (4 / x) ^ 2 / 4) * (Real.pi / 2 / AGM 1 (4 / x)) + (4 / x) ^ 2 / 4 := by ring
  rw [agmLog2, agmLog, abs_sub_comm, e1]
  exact h

/-- Sufficient condition for `n` bits: `x⁴ ≥ 256 (c₁ ln x + c₂) 2^n` (so `x ≳ 2^(n/4)`), given
the transported bound. -/
theorem agmLog2_precision {c₁ c₂ x : ℝ} {n : ℕ} (hx : 8 ≤ x)
    (hbound : |agmLog2 x - Real.log x| ≤ (4 / x) ^ 4 * (c₁ * Real.log x + c₂))
    (hn : 256 * (c₁ * Real.log x + c₂) * 2 ^ n ≤ x ^ 4) :
    |agmLog2 x - Real.log x| ≤ (1 / 2) ^ n := by
  have hx0 : 0 < x := by linarith
  refine hbound.trans ?_
  rw [div_pow, show (4 : ℝ) ^ 4 = 256 by norm_num, div_mul_eq_mul_div, div_le_iff₀ (by positivity),
    one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  exact hn

end Exercise443

section Exercise444

/-- (4.71) turned around: `|2 ln(4/k) AGM(1,k) − π| ≤ (k²/2)(2 − ln k)` for `0 < k ≤ 1`. -/
theorem abs_two_mul_log_mul_AGM_sub_pi {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    |2 * Real.log (4 / k) * AGM 1 k - Real.pi| ≤ k ^ 2 / 2 * (2 - Real.log k) := by
  have hA : 0 < AGM 1 k := lt_of_lt_of_le (lt_min one_pos hk) (min_le_AGM one_pos hk)
  have hA1 : AGM 1 k ≤ 1 :=
    (AGM_le_max one_pos hk).trans (by rw [max_le_iff]; exact ⟨le_rfl, hk1⟩)
  have h := abs_pi_div_AGM_sub_log_le hk hk1
  have e : 2 * Real.log (4 / k) * AGM 1 k - Real.pi
      = -(2 * AGM 1 k) * (Real.pi / 2 / AGM 1 k - Real.log (4 / k)) := by
    field_simp
    ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hlogk : Real.log k ≤ 0 := Real.log_nonpos hk.le hk1
  calc 2 * AGM 1 k * |Real.pi / 2 / AGM 1 k - Real.log (4 / k)|
      ≤ 2 * 1 * (k ^ 2 / 4 * (2 - Real.log k)) := by
        gcongr
    _ = k ^ 2 / 2 * (2 - Real.log k) := by ring

/-- `π` from (4.71) with a logarithm known exactly: at `4/k = e^j`,
`|2j · AGM(1, 4e^(−j)) − π| ≤ 8 e^(−2j) (j + 2 − ln 4)` for `j ≥ ln 4`. -/
theorem abs_pi_approx_exp {j : ℝ} (hj : Real.log 4 ≤ j) :
    |2 * j * AGM 1 (4 * Real.exp (-j)) - Real.pi|
      ≤ 8 * Real.exp (-(2 * j)) * (j + 2 - Real.log 4) := by
  set k := 4 * Real.exp (-j) with hk
  have hk0 : 0 < k := by positivity
  have hk1 : k ≤ 1 := by
    rw [hk, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos j),
      ← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_le_exp.mpr hj
  have hlog : Real.log (4 / k) = j := by
    rw [hk, show (4 : ℝ) / (4 * Real.exp (-j)) = Real.exp j by
      rw [Real.exp_neg]; field_simp, Real.log_exp]
  have hlogk : Real.log k = Real.log 4 - j := by
    rw [hk, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring
  have h := abs_two_mul_log_mul_AGM_sub_pi hk0 hk1
  rw [hlog, hlogk] at h
  calc |2 * j * AGM 1 k - Real.pi| ≤ k ^ 2 / 2 * (2 - (Real.log 4 - j)) := h
    _ = 8 * Real.exp (-(2 * j)) * (j + 2 - Real.log 4) := by
        rw [hk, mul_pow, ← Real.exp_nat_mul]
        push_cast
        ring_nf

/-- `ln 2` from (4.71) at `x = 2^m`:
`|(π/2)/(m AGM(1, 2^(2−m))) − ln 2| ≤ 4^(2−m)(2 + (m−2) ln 2)/(4m)` for `m ≥ 2`. -/
theorem abs_log_two_approx {m : ℕ} (hm : 2 ≤ m) :
    |Real.pi / 2 / AGM 1 (4 / 2 ^ m) / m - Real.log 2|
      ≤ (4 / 2 ^ m) ^ 2 / 4 * (2 + (m - 2) * Real.log 2) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h2m : (4 : ℝ) ≤ 2 ^ m := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hk0 : (0 : ℝ) < 4 / 2 ^ m := by positivity
  have hk1 : (4 : ℝ) / 2 ^ m ≤ 1 := by rw [div_le_one (by positivity)]; exact h2m
  have h := abs_pi_div_AGM_sub_log_le hk0 hk1
  have hlog : Real.log (4 / (4 / 2 ^ m)) = m * Real.log 2 := by
    rw [show (4 : ℝ) / (4 / 2 ^ m) = 2 ^ m by field_simp, Real.log_pow]
  have hlogk : Real.log (4 / 2 ^ m) = 2 * Real.log 2 - m * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hlog, hlogk] at h
  have e : Real.pi / 2 / AGM 1 (4 / 2 ^ m) / m - Real.log 2
      = (Real.pi / 2 / AGM 1 (4 / 2 ^ m) - m * Real.log 2) / m := by
    field_simp
  rw [e, abs_div, abs_of_pos hm0]
  gcongr
  calc _ ≤ _ := h
    _ = (4 / 2 ^ m) ^ 2 / 4 * (2 + (m - 2) * Real.log 2) := by ring

/-- The lower bound `AGM(1,k) ≥ (π/2)/(ln(4/k) + (k²/4)(2 − ln k))` used to propagate an error
in `π` through `ln 2 ≈ (π/2)/(m AGM)`. -/
theorem pi_div_two_div_le_AGM {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    Real.pi / 2 / (Real.log (4 / k) + k ^ 2 / 4 * (2 - Real.log k)) ≤ AGM 1 k := by
  have hA : 0 < AGM 1 k := lt_of_lt_of_le (lt_min one_pos hk) (min_le_AGM one_pos hk)
  have h := (abs_le.mp (abs_pi_div_AGM_sub_log_le hk hk1)).2
  have hL : 0 < Real.log (4 / k) := Real.log_pos (by rw [lt_div_iff₀ hk]; linarith)
  have hlogk : Real.log k ≤ 0 := Real.log_nonpos hk.le hk1
  have hden : 0 < Real.log (4 / k) + k ^ 2 / 4 * (2 - Real.log k) := by
    have := mul_nonneg (by positivity : (0:ℝ) ≤ k ^ 2 / 4) (by linarith : (0:ℝ) ≤ 2 - Real.log k)
    linarith
  rw [div_le_iff₀ hden]
  have : Real.pi / 2 / AGM 1 k * AGM 1 k = Real.pi / 2 := by field_simp
  nlinarith [this]

/-- An approximate `π̃` with `|π̃ − π| ≤ δ` gives `ln 2` to within the (4.71) error plus
`δ/(2m AGM(1, 2^(2−m)))`; the `AGM` is bounded below by `pi_div_two_div_le_AGM`, so this is
`≈ δ (m ln 2)/(π m) = O(δ)`. -/
theorem abs_log_two_approx_of_pi {m : ℕ} (hm : 2 ≤ m) {p δ : ℝ} (hp : |p - Real.pi| ≤ δ) :
    |p / 2 / AGM 1 (4 / 2 ^ m) / m - Real.log 2|
      ≤ δ / (2 * AGM 1 (4 / 2 ^ m) * m)
        + (4 / 2 ^ m) ^ 2 / 4 * (2 + (m - 2) * Real.log 2) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hk0 : (0 : ℝ) < 4 / 2 ^ m := by positivity
  have hA : 0 < AGM 1 (4 / 2 ^ m) := lt_of_lt_of_le (lt_min one_pos hk0) (min_le_AGM one_pos hk0)
  have h := abs_log_two_approx hm
  have e : p / 2 / AGM 1 (4 / 2 ^ m) / m - Real.log 2
      = (p - Real.pi) / (2 * AGM 1 (4 / 2 ^ m) * m)
        + (Real.pi / 2 / AGM 1 (4 / 2 ^ m) / m - Real.log 2) := by
    field_simp
    ring
  rw [e]
  have hden : 0 < 2 * AGM 1 (4 / 2 ^ m) * m := by positivity
  have h1 : |(p - Real.pi) / (2 * AGM 1 (4 / 2 ^ m) * m)| ≤ δ / (2 * AGM 1 (4 / 2 ^ m) * m) := by
    rw [abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right hp hden.le
  calc _ ≤ |(p - Real.pi) / (2 * AGM 1 (4 / 2 ^ m) * m)|
        + |Real.pi / 2 / AGM 1 (4 / 2 ^ m) / m - Real.log 2| := abs_add_le _ _
    _ ≤ δ / (2 * AGM 1 (4 / 2 ^ m) * m)
        + (4 / 2 ^ m) ^ 2 / 4 * (2 + (m - 2) * Real.log 2) / m := add_le_add h1 h

end Exercise444

section Exercise445

/-- Method (A): `2θ₂θ₃ = 2v`, `θ₂² + θ₃² = u − 2v` with `u = (θ₂+θ₃)²`, `v = θ₂θ₃`. -/
theorem methodA_eq (a b : ℝ) :
    2 * a * b = 2 * (a * b) ∧ a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := ⟨by ring, by ring⟩

/-- Method (B): `θ₂² + θ₃² = (u + w)/2`, `2θ₂θ₃ = (u − w)/2` with `w = (θ₂−θ₃)²`. -/
theorem methodB_eq (a b : ℝ) :
    a ^ 2 + b ^ 2 = ((a + b) ^ 2 + (a - b) ^ 2) / 2 ∧
      2 * a * b = ((a + b) ^ 2 - (a - b) ^ 2) / 2 :=
  ⟨sq_add_sq_eq_half_add a b, two_mul_mul_eq_half_sub a b⟩

/-- (A) is well conditioned: with relative errors `|ε₁|, |ε₂| ≤ ε` in `u` and `v` (`a, b ≥ 0`),
the computed `u(1+ε₁) − 2v(1+ε₂)` is within `3ε(a² + b²)` of `a² + b²`. -/
theorem methodA_relError_le {a b ε ε₁ ε₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h₁ : |ε₁| ≤ ε)
    (h₂ : |ε₂| ≤ ε) :
    |(a + b) ^ 2 * (1 + ε₁) - 2 * (a * b) * (1 + ε₂) - (a ^ 2 + b ^ 2)|
      ≤ 3 * ε * (a ^ 2 + b ^ 2) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans h₁
  have e : (a + b) ^ 2 * (1 + ε₁) - 2 * (a * b) * (1 + ε₂) - (a ^ 2 + b ^ 2)
      = (a + b) ^ 2 * ε₁ - 2 * (a * b) * ε₂ := by ring
  have hab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hab' : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  rw [e]
  calc |(a + b) ^ 2 * ε₁ - 2 * (a * b) * ε₂|
      ≤ |(a + b) ^ 2 * ε₁| + |2 * (a * b) * ε₂| := abs_sub _ _
    _ = (a + b) ^ 2 * |ε₁| + 2 * (a * b) * |ε₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a + b) ^ 2),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (a * b))]
    _ ≤ 2 * (a ^ 2 + b ^ 2) * ε + (a ^ 2 + b ^ 2) * ε := by gcongr
    _ = 3 * ε * (a ^ 2 + b ^ 2) := by ring

/-- (B) is ill conditioned for `2ab = (u − w)/2`: relative errors `ε` in `u` and `w` give an
absolute error up to `ε(a² + b²)` (attained for `ε₁ = ε = −ε₂`), i.e. a relative error
`ε (a² + b²)/(2ab) ≥ ε · b/(2a)` — unbounded as `a/b → 0`. -/
theorem methodB_amplification {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε) :
    |((a + b) ^ 2 * (1 + ε) - (a - b) ^ 2 * (1 - ε)) / 2 - 2 * a * b| = ε * (a ^ 2 + b ^ 2) ∧
      ε * (a ^ 2 + b ^ 2) / (2 * a * b) ≥ ε * b / (2 * a) := by
  constructor
  · rw [show ((a + b) ^ 2 * (1 + ε) - (a - b) ^ 2 * (1 - ε)) / 2 - 2 * a * b
        = ε * (a ^ 2 + b ^ 2) by ring, abs_of_nonneg (by positivity)]
  · rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ ε * a ^ 2 * (2 * a) := by positivity
    nlinarith

/-- `θ₂(q) ≤ 2 q^(1/4)/(1 − q)` for `0 < q < 1`: the small factor in (B)'s amplification
`θ₃/(2θ₂) ≥ (1 − q)/(4 q^(1/4))`. -/
theorem theta2_le_two_rpow_div {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta2 q ≤ 2 * q ^ (1 / 4 : ℝ) / (1 - q) := by
  rw [theta2_eq_rpow_mul hq0.le hq1, theta2Int_eq_two_mul_tsum hq0 hq1]
  have hr : 0 ≤ q ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos hq0 _).le
  have ht : ∑' n : ℕ, q ^ (n * (n + 1)) ≤ q ^ 0 / (1 - q) :=
    tsum_pow_le_of_le hq0.le hq1 (M := 0) fun n => by nlinarith
  rw [pow_zero] at ht
  calc q ^ (1 / 4 : ℝ) * (2 * ∑' n : ℕ, q ^ (n * (n + 1)))
      ≤ q ^ (1 / 4 : ℝ) * (2 * (1 / (1 - q))) := by gcongr
    _ = 2 * q ^ (1 / 4 : ℝ) / (1 - q) := by ring

end Exercise445

section Exercise446

/-- The doubling principle: a complex product costs exactly twice a real one in transforms
(`4 + 2` against `2 + 1`). -/
theorem fftCost_complex_mul_eq_two_mul : fftCost 4 2 = 2 * fftCost 2 1 := by norm_num [fftCost]

/-- …and a complex squaring exactly twice a real one (`2 + 2` against `1 + 1`). -/
theorem fftCost_complex_sq_eq_two_mul : fftCost 2 2 = 2 * fftCost 1 1 := by norm_num [fftCost]

/-- Table 4.1's complex reciprocal through `1/z = z̄/|z|²`: `|z|² = a² + b²` with the transforms
of `a, b` shared (`2` forward, `1` backward, `1`), a real reciprocal (`13/9`), then `a r`, `b r`
with the stored transforms and one transform of `r` (`1` forward, `2` backward, `1`): `31/9`. -/
theorem complex_reciprocal_via_norm : fftCost 2 1 + 13 / 9 + fftCost 1 2 = 31 / 9 := by
  norm_num [fftCost]

/-- Table 4.1's complex square root through `x = √((|z| + a)/2)`, `y = b/(2x)`: `|z|² (1)`, three
real square roots or two square roots and a division: `1 + 4/3 + 4/3 + 5/3 = 16/3`. -/
theorem complex_sqrt_via_norm : (1 : ℚ) + 4 / 3 + 4 / 3 + 5 / 3 = 16 / 3 := by norm_num

/-- Improved: the real Newton reciprocal (`13/9 M`) run over `ℂ` costs twice, `26/9 < 31/9`. -/
theorem complex_reciprocal_improved : (2 : ℚ) * (13 / 9) < 31 / 9 := by norm_num

/-- Improved: complex division as a complex Newton iteration, `2 · 5/3 = 10/3 < 43/9`. -/
theorem complex_division_improved : (2 : ℚ) * (5 / 3) < 43 / 9 := by norm_num

/-- Improved: the complex square root as a complex Newton iteration, `2 · 4/3 = 8/3 < 16/3`. -/
theorem complex_sqrt_improved : (2 : ℚ) * (4 / 3) < 16 / 3 := by norm_num

/-- Improved: a complex AGM iteration (one complex product and one complex square root, with the
same transform reuse as the real `2M` iteration) costs `2 · 2 = 4 < 20/3`. -/
theorem complex_agm_iteration_improved : (2 : ℚ) * 2 < 20 / 3 := by norm_num

/-- Improved: `ln z` by the complex AGM, `2 lg n` iterations of cost `4`, `8 lg n < (40/3) lg n`. -/
theorem complex_log_improved {n : ℝ} (hn : 0 < Real.logb 2 n) :
    2 * 2 * (2 * Real.logb 2 n) < 40 / 3 * Real.logb 2 n := by linarith

end Exercise446

section Exercise447

open Finset

/-- One level of the splitting tree under `M(m) = m^c`: `2^k (N/2^k)^c = N^c (2^(1−c))^k`. -/
theorem two_pow_mul_div_rpow {N c : ℝ} (hN : 0 ≤ N) (k : ℕ) :
    (2 : ℝ) ^ k * (N / 2 ^ k) ^ c = N ^ c * ((2 : ℝ) ^ (1 - c)) ^ k := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [Real.div_rpow hN h2k.le, ← Real.rpow_natCast 2 k, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2 : ℝ) ^ (1 - c)) k, ← Real.rpow_mul (by norm_num),
    show (1 - c) * (k : ℝ) = (k : ℝ) - k * c by ring, Real.rpow_sub (by norm_num)]
  ring

/-- (4.80) for `M(m) = m^c`, `c > 1`: the level costs are geometric, so
`∑_{k=1}^{L} 2^k (N/2^k)^c ≤ N^c · 2^(1−c)/(1 − 2^(1−c))` for every `L`. -/
theorem binary_splitting_cost_pow {N c : ℝ} (hN : 0 ≤ N) (hc : 1 < c) (L : ℕ) :
    ∑ k ∈ Icc 1 L, (2 : ℝ) ^ k * (N / 2 ^ k) ^ c
      ≤ N ^ c * ((2 : ℝ) ^ (1 - c) / (1 - 2 ^ (1 - c))) := by
  set r : ℝ := (2 : ℝ) ^ (1 - c) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hgeom : ∑ k ∈ Icc 1 L, r ^ k ≤ r / (1 - r) := by
    have h := geom_sum_Ico_le_of_lt_one hr0 hr1 (m := 1) (n := L + 1)
    rwa [pow_one, ← Order.succ_eq_add_one, Finset.Ico_succ_right_eq_Icc] at h
  calc ∑ k ∈ Icc 1 L, (2 : ℝ) ^ k * (N / 2 ^ k) ^ c
      = ∑ k ∈ Icc 1 L, N ^ c * r ^ k := sum_congr rfl fun k _ => two_pow_mul_div_rpow hN k
    _ = N ^ c * ∑ k ∈ Icc 1 L, r ^ k := by rw [mul_sum]
    _ ≤ N ^ c * (r / (1 - r)) := by gcongr

/-- With `N = n lg n` and `M(n) = n^c`: the bound is `(lg n)^c · M(n) · 2^(1−c)/(1 − 2^(1−c))`,
i.e. `α = c`. -/
theorem binary_splitting_cost_pow_eq {n c : ℝ} (hn : 1 ≤ n) (hc : 1 < c) (L : ℕ) :
    ∑ k ∈ Icc 1 L, (2 : ℝ) ^ k * (n * Real.logb 2 n / 2 ^ k) ^ c
      ≤ Real.logb 2 n ^ c * n ^ c * ((2 : ℝ) ^ (1 - c) / (1 - 2 ^ (1 - c))) := by
  have hlg : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hn
  have h := binary_splitting_cost_pow (N := n * Real.logb 2 n) (by positivity) hc L
  rwa [Real.mul_rpow (by linarith) hlg, mul_comm (n ^ c)] at h

/-- `α = c ≤ 2`: `(lg n)^c ≤ (lg n)²` for `n ≥ 2`. -/
theorem rpow_logb_le_sq {n c : ℝ} (hn : 2 ≤ n) (hc : c ≤ 2) :
    Real.logb 2 n ^ c ≤ Real.logb 2 n ^ 2 := by
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn
  calc Real.logb 2 n ^ c ≤ Real.logb 2 n ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlg hc
    _ = Real.logb 2 n ^ 2 := by norm_cast

end Exercise447

section Exercise448

open Polynomial

/-- `f` is holonomic (D-finite) on `s`: some linear differential operator with polynomial
coefficients and nonzero leading coefficient annihilates `f` on `s`. -/
def IsHolonomicOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ (r : ℕ) (p : Fin (r + 1) → ℝ[X]), p (Fin.last r) ≠ 0 ∧
    ∀ x ∈ s, ∑ i : Fin (r + 1), (p i).eval x * iteratedDeriv i f x = 0

/-- Salvy's function `exp(x²) + x/(1 − x²)`. -/
noncomputable def salvyFun (x : ℝ) : ℝ := Real.exp (x ^ 2) + x / (1 - x ^ 2)

/-- Its derivative. -/
noncomputable def salvyFun' (x : ℝ) : ℝ :=
  2 * x * Real.exp (x ^ 2) + (1 + x ^ 2) / (1 - x ^ 2) ^ 2

/-- Its second derivative. -/
noncomputable def salvyFun'' (x : ℝ) : ℝ :=
  (2 + 4 * x ^ 2) * Real.exp (x ^ 2) + 2 * x * (3 + x ^ 2) / (1 - x ^ 2) ^ 3

/-- `exp(x²)` is holonomic: `f' − 2x f = 0`. -/
theorem exp_sq_ode (x : ℝ) :
    deriv (fun y => Real.exp (y ^ 2)) x - 2 * x * Real.exp (x ^ 2) = 0 := by
  rw [((hasDerivAt_pow 2 x).exp).deriv]; ring

/-- `x/(1 − x²)` is holonomic: `x(1 − x²) g' − (1 + x²) g = 0` away from `x² = 1`. -/
theorem ratPart_ode {x : ℝ} (hx : x ^ 2 ≠ 1) :
    x * (1 - x ^ 2) * deriv (fun y => y / (1 - y ^ 2)) x - (1 + x ^ 2) * (x / (1 - x ^ 2)) = 0 := by
  have hne : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h : HasDerivAt (fun y : ℝ => y / (1 - y ^ 2))
      ((1 * (1 - x ^ 2) - id x * -(↑(2 : ℕ) * x ^ (2 - 1))) / (1 - x ^ 2) ^ 2) x :=
    (hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_sub 1) hne
  rw [h.deriv]
  simp only [id]
  field_simp
  ring

theorem hasDerivAt_salvyFun {x : ℝ} (hx : x ^ 2 ≠ 1) : HasDerivAt salvyFun (salvyFun' x) x := by
  have hne : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h := ((hasDerivAt_pow 2 x).exp).add
    ((hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_sub 1) hne)
  refine h.congr_deriv ?_
  simp only [salvyFun', id]
  field_simp
  ring

theorem hasDerivAt_salvyFun' {x : ℝ} (hx : x ^ 2 ≠ 1) :
    HasDerivAt salvyFun' (salvyFun'' x) x := by
  have hne : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hne2 : (1 - x ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have h := (((hasDerivAt_id x).const_mul 2).mul ((hasDerivAt_pow 2 x).exp)).add
    (((hasDerivAt_pow 2 x).const_add 1).div (((hasDerivAt_pow 2 x).const_sub 1).pow 2) hne2)
  refine h.congr_deriv ?_
  simp only [salvyFun'', id, Pi.pow_apply]
  field_simp
  ring

theorem isOpen_sq_ne_one : IsOpen {x : ℝ | x ^ 2 ≠ 1} :=
  isOpen_ne_fun (continuous_pow 2) continuous_const

theorem deriv_salvyFun {x : ℝ} (hx : x ^ 2 ≠ 1) : deriv salvyFun x = salvyFun' x :=
  (hasDerivAt_salvyFun hx).deriv

theorem deriv_deriv_salvyFun {x : ℝ} (hx : x ^ 2 ≠ 1) :
    deriv (deriv salvyFun) x = salvyFun'' x := by
  have hev : deriv salvyFun =ᶠ[nhds x] salvyFun' :=
    Filter.eventually_of_mem (isOpen_sq_ne_one.mem_nhds hx) fun y hy => deriv_salvyFun hy
  rw [hev.deriv_eq, (hasDerivAt_salvyFun' hx).deriv]

/-- The explicit annihilating operator of `exp(x²) + x/(1 − x²)`:
`(1−x²)(1−x²+2x⁴) h'' − 2x(2+x²+3x⁴−2x⁶) h' + 2(2x⁶+3x⁴+4x²−1) h = 0`. -/
theorem salvyFun_ode {x : ℝ} (hx : x ^ 2 ≠ 1) :
    (1 - x ^ 2) * (1 - x ^ 2 + 2 * x ^ 4) * salvyFun'' x
      - 2 * x * (2 + x ^ 2 + 3 * x ^ 4 - 2 * x ^ 6) * salvyFun' x
      + 2 * (2 * x ^ 6 + 3 * x ^ 4 + 4 * x ^ 2 - 1) * salvyFun x = 0 := by
  have hne : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp only [salvyFun, salvyFun', salvyFun'']
  field_simp
  ring

/-- The answer to Exercise 4.48: Salvy's function is holonomic on `{x | x² ≠ 1}`. -/
theorem salvyFun_isHolonomicOn : IsHolonomicOn salvyFun {x | x ^ 2 ≠ 1} := by
  refine ⟨2, ![Polynomial.C 2 * (2 * Polynomial.X ^ 6 + 3 * Polynomial.X ^ 4
      + 4 * Polynomial.X ^ 2 - 1),
    -(Polynomial.C 2 * Polynomial.X * (2 + Polynomial.X ^ 2 + 3 * Polynomial.X ^ 4
      - 2 * Polynomial.X ^ 6)),
    (1 - Polynomial.X ^ 2) * (1 - Polynomial.X ^ 2 + 2 * Polynomial.X ^ 4)], ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  · intro x hx
    have hx' : x ^ 2 ≠ 1 := hx
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue,
      Matrix.head_cons, Matrix.tail_cons, iteratedDeriv_zero, iteratedDeriv_succ,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_neg,
      Polynomial.eval_ofNat, Fin.val_zero, Fin.val_one, Fin.val_two]
    rw [deriv_salvyFun hx', deriv_deriv_salvyFun hx']
    linear_combination salvyFun_ode hx'

end Exercise448

section Exercise449

open Finset

/-- Root size (bits) of the binary-splitting tree in bit-burst step `i`: about `n/2^i` terms,
each with `2^i + O(lg n)`-bit recurrence coefficients, so `S_i = n + n lg n/2^i`.  (The proof of
Theorem 4.2 used the uniform bound `n lg n` for every step.) -/
noncomputable def burstStepSize (n i : ℕ) : ℝ := n + n * Real.logb 2 n / 2 ^ i

/-- Binary splitting with `L` levels on an `S`-bit product costs at most `L · M(S)`. -/
theorem binary_splitting_levels_le {S : ℝ} (hS : 1 ≤ S) (L : ℕ) :
    ∑ k ∈ Icc 1 L, 2 ^ k * quasiLinearCost (S / 2 ^ k) ≤ L * quasiLinearCost S := by
  calc _ ≤ ∑ _k ∈ Icc 1 L, quasiLinearCost S :=
        sum_le_sum fun k _ => two_pow_mul_quasiLinearCost_div_le hS k
    _ = _ := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

theorem quasiLinearCost_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ quasiLinearCost a :=
  mul_nonneg (by linarith) (Real.logb_nonneg one_lt_two ha)

theorem logb_two_mul {a : ℝ} (ha : 0 < a) : Real.logb 2 (2 * a) = 1 + Real.logb 2 a := by
  rw [Real.logb_mul (by norm_num) ha.ne', Real.logb_self_eq_one one_lt_two]

/-- `M(a + b) ≤ 4 (M(a) + M(b))` for `a ≥ 2`, `b ≥ 1`: `a + b ≤ 2 max(a, b)` and
`M(2m) = 2m(1 + lg m) ≤ 4 M(m)` for `m ≥ 2`. -/
theorem quasiLinearCost_add_le {a b : ℝ} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    quasiLinearCost (a + b) ≤ 4 * quasiLinearCost a + 4 * quasiLinearCost b := by
  unfold quasiLinearCost
  have hlga : 1 ≤ Real.logb 2 a := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact ha
  have hlgb : 0 ≤ Real.logb 2 b := Real.logb_nonneg one_lt_two hb
  have hMa : 0 ≤ a * Real.logb 2 a := mul_nonneg (by linarith) (by linarith)
  have hMb : 0 ≤ b * Real.logb 2 b := mul_nonneg (by linarith) hlgb
  rcases le_or_gt b a with hba | hab
  · have h : Real.logb 2 (a + b) ≤ 1 + Real.logb 2 a := by
      rw [← logb_two_mul (by linarith)]
      exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ a + b),
      mul_nonneg (sub_nonneg.mpr hba) (by linarith : (0 : ℝ) ≤ 1 + Real.logb 2 a),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a) (sub_nonneg.mpr hlga)]
  · have hlgb1 : 1 ≤ Real.logb 2 b := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; linarith
    have h : Real.logb 2 (a + b) ≤ 1 + Real.logb 2 b := by
      rw [← logb_two_mul (by linarith)]
      exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ a + b),
      mul_nonneg (sub_nonneg.mpr hab.le) (by linarith : (0 : ℝ) ≤ 1 + Real.logb 2 b),
      mul_nonneg (by linarith : (0 : ℝ) ≤ b) (sub_nonneg.mpr hlgb1)]

/-- `M(m/2^k) ≤ M(m)/2^k` for `m ≥ 1`. -/
theorem quasiLinearCost_div_two_pow_le {m : ℝ} (hm : 1 ≤ m) (k : ℕ) :
    quasiLinearCost (m / 2 ^ k) ≤ quasiLinearCost m / 2 ^ k := by
  rw [le_div_iff₀ (by positivity)]
  linarith [two_pow_mul_quasiLinearCost_div_le hm k]

/-- `M(n lg n) ≤ 2 lg n · M(n)` for `n ≥ 2`. -/
theorem quasiLinearCost_natCast_mul_logb_le {n : ℕ} (hn : 2 ≤ n) :
    quasiLinearCost (n * Real.logb 2 n) ≤ 2 * Real.logb 2 n * quasiLinearCost n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
    exact_mod_cast hn
  unfold quasiLinearCost
  have hlglg : Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) (logb_two_natCast_le_self (by omega))
  rw [Real.logb_mul (by positivity) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hlglg (by positivity : (0 : ℝ) ≤ n * Real.logb 2 n)]

/-- The per-step sizes sum geometrically: for `2^L ≤ n lg n`,
`∑_{i≤L} M(S_i) ≤ (4(L+1) + 16 lg n) M(n)`. -/
theorem sum_quasiLinearCost_burstStepSize_le {n : ℕ} (hn : 2 ≤ n) {L : ℕ}
    (hL : (2 : ℝ) ^ L ≤ n * Real.logb 2 n) :
    ∑ i ∈ range (L + 1), quasiLinearCost (burstStepSize n i)
      ≤ (4 * (L + 1) + 16 * Real.logb 2 n) * quasiLinearCost n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn2
  have hm : 1 ≤ (n : ℝ) * Real.logb 2 n := by nlinarith
  have hb : ∀ i ∈ range (L + 1), 1 ≤ (n : ℝ) * Real.logb 2 n / 2 ^ i := by
    intro i hi
    rw [mem_range] at hi
    rw [le_div_iff₀ (by positivity), one_mul]
    exact (pow_le_pow_right₀ one_le_two (by omega)).trans hL
  have hterm : ∀ i ∈ range (L + 1), quasiLinearCost (burstStepSize n i)
      ≤ 4 * quasiLinearCost n + 4 * (quasiLinearCost (n * Real.logb 2 n) * (1 / 2) ^ i) := by
    intro i hi
    refine (quasiLinearCost_add_le hn2 (hb i hi)).trans ?_
    have := quasiLinearCost_div_two_pow_le hm i
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    linarith
  have hgeom := sum_geometric_two_le (L + 1)
  have hMm : 0 ≤ quasiLinearCost (n * Real.logb 2 n) := quasiLinearCost_nonneg hm
  have hMn : 0 ≤ quasiLinearCost n := quasiLinearCost_nonneg (by linarith)
  have hM2 := quasiLinearCost_natCast_mul_logb_le hn
  calc ∑ i ∈ range (L + 1), quasiLinearCost (burstStepSize n i)
      ≤ ∑ i ∈ range (L + 1),
          (4 * quasiLinearCost n + 4 * (quasiLinearCost (n * Real.logb 2 n) * (1 / 2) ^ i)) :=
        sum_le_sum hterm
    _ = 4 * (L + 1) * quasiLinearCost n
        + 4 * quasiLinearCost (n * Real.logb 2 n) * ∑ i ∈ range (L + 1), (1 / 2 : ℝ) ^ i := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
        congr 1
        · push_cast; ring
        · exact sum_congr rfl fun i _ => by ring
    _ ≤ 4 * (L + 1) * quasiLinearCost n + 4 * quasiLinearCost (n * Real.logb 2 n) * 2 := by
        gcongr
    _ ≤ (4 * (L + 1) + 16 * Real.logb 2 n) * quasiLinearCost n := by nlinarith

/-- Exercise 4.49: with the per-step sizes `S_i`, the whole bit-burst algorithm (`⌈lg n⌉ + 1`
steps, each a binary splitting of at most `lg n + 1` levels) costs at most `56 (lg n)² M(n)`,
i.e. `O(M(n) log² n)` instead of Theorem 4.2's `O(M(n) log³ n)`. -/
theorem bit_burst_cost {n : ℕ} (hn : 4 ≤ n) :
    ∑ i ∈ range (Nat.clog 2 n + 1), (Real.logb 2 n + 1) * quasiLinearCost (burstStepSize n i)
      ≤ 56 * Real.logb 2 n ^ 2 * quasiLinearCost n := by
  have hn2 : 2 ≤ n := by omega
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlg : 2 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_two]; norm_num
    exact_mod_cast hn
  have hclog := clog_le_logb_add_one hn2
  have hL : (2 : ℝ) ^ (Nat.clog 2 n) ≤ n * Real.logb 2 n := by
    have h1 : (2 : ℝ) ^ (Nat.clog 2 n) ≤ 2 ^ (Real.logb 2 n + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two hclog
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
      Real.rpow_one] at h1
    nlinarith
  have hS := sum_quasiLinearCost_burstStepSize_le hn2 hL
  have hMn : 0 ≤ quasiLinearCost n := quasiLinearCost_nonneg (by linarith)
  rw [← mul_sum]
  calc (Real.logb 2 n + 1) * ∑ i ∈ range (Nat.clog 2 n + 1), quasiLinearCost (burstStepSize n i)
      ≤ (Real.logb 2 n + 1) * ((4 * (Nat.clog 2 n + 1) + 16 * Real.logb 2 n) * quasiLinearCost n) :=
        mul_le_mul_of_nonneg_left hS (by linarith)
    _ ≤ (2 * Real.logb 2 n) * (28 * Real.logb 2 n * quasiLinearCost n) := by
        apply mul_le_mul (by linarith) _ (mul_nonneg (by linarith) hMn) (by linarith)
        exact mul_le_mul_of_nonneg_right (by linarith) hMn
    _ = 56 * Real.logb 2 n ^ 2 * quasiLinearCost n := by ring

end Exercise449

section Exercise450

open Finset Complex

/-- Partial fractions: for a primitive `k`-th root of unity `ζ` and `z^k ≠ 1`,
`∑_{m<k} ζ^m/(z − ζ^m) = k/(z^k − 1)`. -/
theorem sum_primitiveRoot_div_eq {ζ : ℂ} {k : ℕ} (hζ : IsPrimitiveRoot ζ k) (hk : 0 < k) {z : ℂ}
    (hz : z ^ k ≠ 1) : ∑ m ∈ range k, ζ ^ m / (z - ζ ^ m) = k / (z ^ k - 1) := by
  have hzk : z ^ k - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hne : ∀ m, z - ζ ^ m ≠ 0 := fun m h => by
    apply hz
    rw [sub_eq_zero.mp h, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hterm : ∀ m ∈ range k, ζ ^ m / (z - ζ ^ m)
      = (∑ i ∈ range k, z ^ i * (ζ ^ (k - i)) ^ m) / (z ^ k - 1) := by
    intro m _
    rw [div_eq_div_iff (hne m) hzk]
    have h := geom_sum₂_mul z (ζ ^ m) k
    rw [← pow_mul, mul_comm m k, pow_mul, hζ.pow_eq_one, one_pow] at h
    rw [← h, ← mul_assoc, mul_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have e : k - i = (k - 1 - i) + 1 := by omega
    rw [e, ← pow_mul, ← pow_mul, mul_left_comm, ← pow_add]
    congr 2
    ring
  rw [sum_congr rfl hterm, ← sum_div, sum_comm]
  congr 1
  have horth : ∀ i ∈ range k, ∑ m ∈ range k, z ^ i * (ζ ^ (k - i)) ^ m
      = if i = 0 then (k : ℂ) else 0 := by
    intro i hi
    rw [mem_range] at hi
    have h := sum_zpow_primitiveRoot hζ ((k - i : ℕ) : ℤ)
    rw [zpow_natCast] at h
    rw [← mul_sum, h]
    split_ifs with hd hi0 hi0
    · subst hi0; simp
    · exfalso
      have := Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp hd)
      omega
    · exfalso; apply hd; subst hi0; simp
    · simp
  rw [sum_congr rfl horth]
  simp [hk]

/-- `S_{j,k} = (1/k) ∑_{m<k} f(ζ^m) ζ^(−jm)` (4.84) for a function `f`, `ζ = e^(2πi/k)`. -/
noncomputable def aliasSumFun (f : ℂ → ℂ) (j k : ℕ) : ℂ :=
  (1 / k : ℂ) * ∑ m ∈ range k,
    f (exp (2 * Real.pi * I / k) ^ m) * (exp (2 * Real.pi * I / k))⁻¹ ^ (j * m)

/-- `aliasSum` (the series form of `ContourIntegration.lean`) is `aliasSumFun` of the sum. -/
theorem aliasSum_eq_aliasSumFun (a : ℕ → ℂ) (j k : ℕ) :
    aliasSum a j k = aliasSumFun (fun z => ∑' l : ℕ, a l * z ^ l) j k := rfl

/-- A finite sum of circle integrals. -/
theorem circleIntegral_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ∀ i ∈ s, CircleIntegrable (F i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, F i z) = ∑ i ∈ s, ∮ z in C(c, R), F i z := by
  simp only [circleIntegral, smul_sum]
  exact intervalIntegral.integral_finsetSum fun i hi => (hF i hi).out

/-- `S_{j,k} = (2πi)⁻¹ ∮_{|z|=R} z^(k−j−1)/(z^k − 1) f(z) dz` for `j < k`, `f` holomorphic on
`|z| ≤ R`, `R > 1`: each partial fraction `ζ^m/(z − ζ^m)` contributes `ζ^m · ζ^(m(k−j−1)) f(ζ^m)`
by Cauchy's integral formula. -/
theorem aliasSumFun_eq_circleIntegral {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) {j k : ℕ} (hjk : j < k) :
    aliasSumFun f j k
      = (2 * Real.pi * I)⁻¹ * ∮ z in C(0, R), z ^ (k - j - 1) / (z ^ k - 1) * f z := by
  have hk : 0 < k := by omega
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hR0 : 0 ≤ R := by linarith
  set ζ : ℂ := exp (2 * Real.pi * I / k) with hζdef
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk.ne'
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hk.ne'
  have hζm : ∀ m : ℕ, ζ ^ m ∈ Metric.ball (0 : ℂ) R := fun m => by
    rw [Metric.mem_ball, dist_zero_right, norm_pow, hnorm, one_pow]; exact hR
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R, z ^ k ≠ 1 := by
    intro z hz h1
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have : ‖z ^ k‖ = 1 := by rw [h1, norm_one]
    rw [norm_pow, hz] at this
    exact absurd this (one_lt_pow₀ hR hk.ne').ne'
  have hne : ∀ m, ∀ z ∈ Metric.sphere (0 : ℂ) R, z - ζ ^ m ≠ 0 := by
    intro m z hz h
    rw [Metric.mem_sphere, dist_zero_right, sub_eq_zero.mp h, norm_pow, hnorm, one_pow] at hz
    linarith
  have hg : DifferentiableOn ℂ (fun z => z ^ (k - j - 1) * f z) (Metric.closedBall 0 R) :=
    (differentiableOn_id.pow _).mul hf
  have hfc : ContinuousOn f (Metric.sphere 0 R) :=
    hf.continuousOn.mono Metric.sphere_subset_closedBall
  have hEq : Set.EqOn (fun z => z ^ (k - j - 1) / (z ^ k - 1) * f z)
      (fun z => ∑ m ∈ range k, (1 / k : ℂ) * ζ ^ m * ((z - ζ ^ m)⁻¹ * (z ^ (k - j - 1) * f z)))
      (Metric.sphere 0 R) := by
    intro z hz
    have hzk : z ^ k - 1 ≠ 0 := sub_ne_zero.mpr (hsph z hz)
    have h := sum_primitiveRoot_div_eq hζ hk (hsph z hz)
    have e : ∑ m ∈ range k, (1 / k : ℂ) * ζ ^ m * ((z - ζ ^ m)⁻¹ * (z ^ (k - j - 1) * f z))
        = (1 / k : ℂ) * (z ^ (k - j - 1) * f z) * ∑ m ∈ range k, ζ ^ m / (z - ζ ^ m) := by
      rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
    simp only
    rw [e, h]
    field_simp
  have hint : ∀ m ∈ range k, CircleIntegrable
      (fun z => (1 / k : ℂ) * ζ ^ m * ((z - ζ ^ m)⁻¹ * (z ^ (k - j - 1) * f z))) 0 R := by
    intro m _
    refine ContinuousOn.circleIntegrable hR0 ?_
    exact continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).inv₀ (hne m)).mul
      ((continuous_pow _).continuousOn.mul hfc))
  rw [circleIntegral.integral_congr hR0 hEq, circleIntegral_sum _ _ _ _ hint]
  have hterm : ∀ m ∈ range k,
      (∮ z in C(0, R), (1 / k : ℂ) * ζ ^ m * ((z - ζ ^ m)⁻¹ * (z ^ (k - j - 1) * f z)))
        = (1 / k : ℂ) * ζ ^ m * ((2 * Real.pi * I) * ((ζ ^ m) ^ (k - j - 1) * f (ζ ^ m))) := by
    intro m _
    rw [circleIntegral.integral_const_mul]
    congr 1
    simpa only [smul_eq_mul] using hg.circleIntegral_sub_inv_smul (hζm m)
  rw [sum_congr rfl hterm]
  unfold aliasSumFun
  rw [← hζdef, mul_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have hpow : ζ ^ m * (ζ ^ m) ^ (k - j - 1) = ζ⁻¹ ^ (j * m) := by
    rw [inv_pow]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ', ← pow_mul, ← pow_add]
    have e : m * (k - j - 1 + 1) + j * m = k * m := by
      have : k - j - 1 + 1 = k - j := by omega
      rw [this, mul_comm j m, ← mul_add, Nat.sub_add_cancel hjk.le, mul_comm]
    rw [e, pow_mul, hζ.pow_eq_one, one_pow]
  have h2π : (2 * Real.pi * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have e : (2 * Real.pi * I)⁻¹ * ((1 / k : ℂ) * ζ ^ m
      * ((2 * Real.pi * I) * ((ζ ^ m) ^ (k - j - 1) * f (ζ ^ m))))
      = (1 / k : ℂ) * (f (ζ ^ m) * (ζ ^ m * (ζ ^ m) ^ (k - j - 1))) := by
    field_simp
  rw [e, hpow]

/-- The Cauchy coefficient `a_i = (2πi)⁻¹ ∮_{|z|=R} f(z) z^(−i−1) dz` (4.83). -/
noncomputable def cauchyCoeff (f : ℂ → ℂ) (R : ℝ) (i : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(0, R), f z / z ^ (i + 1)

/-- The Cauchy coefficients are the Taylor coefficients: `f(z) = ∑ a_i z^i` on `|z| < R`. -/
theorem hasSum_cauchyCoeff {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun i : ℕ => cauchyCoeff f R i * z ^ i) (f z) := by
  lift R to NNReal using hR.le
  have hR' : (0 : NNReal) < R := by exact_mod_cast hR
  have h := hf.hasFPowerSeriesOnBall hR'
  have hz' : z ∈ Metric.eball (0 : ℂ) (R : ENNReal) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hz
  have h2 := h.hasSum hz'
  rw [zero_add] at h2
  convert h2 using 1
  funext n
  rw [cauchyPowerSeries_apply, cauchyCoeff]
  simp only [sub_zero, smul_eq_mul]
  have e' : (∮ w in C(0, R), (z / w) ^ n * (w⁻¹ * f w))
      = z ^ n * ∮ w in C(0, R), f w / w ^ (n + 1) := by
    rw [← circleIntegral.integral_const_mul]
    congr 1
    funext w
    rw [div_pow, pow_succ]
    ring
  rw [e']
  ring

/-- `S_{j,k} − a_j = (2πi)⁻¹ ∮_{|z|=R} f(z)/(z^(j+1)(z^k − 1)) dz` for `j < k`. -/
theorem aliasSumFun_sub_cauchyCoeff {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) {j k : ℕ} (hjk : j < k) :
    aliasSumFun f j k - cauchyCoeff f R j
      = (2 * Real.pi * I)⁻¹ * ∮ z in C(0, R), f z / (z ^ (j + 1) * (z ^ k - 1)) := by
  have hk : 0 < k := by omega
  have hR0 : 0 ≤ R := by linarith
  have hfc : ContinuousOn f (Metric.sphere 0 R) :=
    hf.continuousOn.mono Metric.sphere_subset_closedBall
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R, z ^ k - 1 ≠ 0 := by
    intro z hz h1
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have : ‖z ^ k‖ = 1 := by rw [sub_eq_zero.mp h1, norm_one]
    rw [norm_pow, hz] at this
    exact absurd this (one_lt_pow₀ hR hk.ne').ne'
  have hz0 : ∀ z ∈ Metric.sphere (0 : ℂ) R, z ≠ 0 := by
    intro z hz h
    rw [Metric.mem_sphere, dist_zero_right, h, norm_zero] at hz
    linarith
  have h1 : CircleIntegrable (fun z => z ^ (k - j - 1) / (z ^ k - 1) * f z) 0 R :=
    ContinuousOn.circleIntegrable hR0 (((continuous_pow _).continuousOn.div
      ((continuous_pow _).continuousOn.sub continuousOn_const) hsph).mul hfc)
  have h2 : CircleIntegrable (fun z => f z / z ^ (j + 1)) 0 R :=
    ContinuousOn.circleIntegrable hR0
      (hfc.div (continuous_pow _).continuousOn fun z hz => pow_ne_zero _ (hz0 z hz))
  rw [aliasSumFun_eq_circleIntegral hR hf hjk, cauchyCoeff, ← mul_sub,
    ← circleIntegral.integral_sub h1 h2]
  congr 1
  apply circleIntegral.integral_congr hR0
  intro z hz
  have hzk := hsph z hz
  have hz0' := hz0 z hz
  have e : z ^ (k - j - 1) * z ^ (j + 1) = z ^ k := by
    rw [← pow_add]; congr 1; omega
  simp only
  rw [← e] at hzk ⊢
  field_simp
  ring

/-- Expanding `1/(z^k − 1) = ∑_{l≥1} z^(−lk)` on `|z| = R > 1` under the integral sign
(dominated convergence): `∮ f/(z^(j+1)(z^k − 1)) = ∑_{l≥0} ∮ f/z^(j+(l+1)k+1)`. -/
theorem hasSum_circleIntegral_div_pow {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (j : ℕ) {k : ℕ} (hk : 0 < k) :
    HasSum (fun l : ℕ => ∮ z in C(0, R), f z / z ^ (j + (l + 1) * k + 1))
      (∮ z in C(0, R), f z / (z ^ (j + 1) * (z ^ k - 1))) := by
  have hR0 : 0 < R := by linarith
  have hfc : ContinuousOn f (Metric.sphere 0 R) :=
    hf.continuousOn.mono Metric.sphere_subset_closedBall
  have hcont : Continuous (f ∘ circleMap 0 R) :=
    hfc.comp_continuous (continuous_circleMap 0 R) (circleMap_mem_sphere 0 hR0.le)
  obtain ⟨Mf, hMf⟩ : ∃ Mf, ∀ θ, ‖f (circleMap 0 R θ)‖ ≤ Mf := by
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hfc
    exact ⟨C, fun θ => hC _ (circleMap_mem_sphere 0 hR0.le θ)⟩
  have hcm : ∀ θ, ‖circleMap 0 R θ‖ = R := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hR0]
  have hcm0 : ∀ θ, circleMap 0 R θ ≠ 0 := fun θ h => by
    have := hcm θ; rw [h, norm_zero] at this; linarith
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hr : (R⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hR) hk.ne'
  have hRk : 1 < R ^ k := one_lt_pow₀ hR hk.ne'
  simp only [circleIntegral]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun l _ => R * Mf * ((R⁻¹) ^ k) ^ l) ?_ ?_ ?_ ?_ ?_
  · intro l
    refine Continuous.aestronglyMeasurable ?_
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).smul
      (hcont.div ((continuous_circleMap 0 R).pow _) fun θ => pow_ne_zero _ (hcm0 θ))
  · intro l
    refine Filter.Eventually.of_forall fun θ _ => ?_
    rw [deriv_circleMap, smul_eq_mul, norm_mul, norm_mul, norm_I, mul_one, norm_div, norm_pow,
      hcm]
    have hle : l * k ≤ j + (l + 1) * k + 1 :=
      (Nat.mul_le_mul_right _ (Nat.le_succ l)).trans ((Nat.le_add_left _ _).trans (Nat.le_succ _))
    calc R * (‖f (circleMap 0 R θ)‖ / R ^ (j + (l + 1) * k + 1))
        ≤ R * (Mf / R ^ (l * k)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div₀ hMf0 (hMf θ) (by positivity) (pow_le_pow_right₀ hR.le hle)) hR0.le
      _ = R * Mf * ((R⁻¹) ^ k) ^ l := by
          rw [← pow_mul, inv_pow, mul_comm k l, div_eq_mul_inv]; ring
  · exact Filter.Eventually.of_forall fun θ _ =>
      (summable_geometric_of_lt_one (by positivity) hr).mul_left _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    set z := circleMap 0 R θ with hz
    have hz0 : z ≠ 0 := hcm0 θ
    have hzk : ‖(z ^ k)⁻¹‖ < 1 := by
      rw [norm_inv, norm_pow, hcm]; exact inv_lt_one_of_one_lt₀ hRk
    have hzk1 : z ^ k - 1 ≠ 0 := by
      intro h
      have : ‖z ^ k‖ = 1 := by rw [sub_eq_zero.mp h, norm_one]
      rw [norm_pow, hcm] at this
      exact absurd this hRk.ne'
    have hzk2 : 1 - (z ^ k)⁻¹ ≠ 0 := by
      intro h
      apply hzk1
      have h1 : (z ^ k)⁻¹ = 1 := (sub_eq_zero.mp h).symm
      rw [inv_eq_one] at h1
      rw [h1, sub_self]
    have hgeom := (hasSum_geometric_of_norm_lt_one hzk).mul_left
      (deriv (circleMap 0 R) θ • (f z / z ^ (j + 1) * (z ^ k)⁻¹))
    convert hgeom using 1
    · funext l
      rw [smul_eq_mul, smul_eq_mul,
        show j + (l + 1) * k + 1 = (j + 1) + k + k * l by ring, pow_add, pow_add, pow_mul]
      simp only [div_eq_mul_inv, mul_inv, inv_pow]
      ring
    · rw [smul_eq_mul, smul_eq_mul]
      field_simp

/-- (4.85) from the contour integral: `S_{j,k} − a_j = ∑_{l≥1} a_{j+lk}` for `j < k` — the
observations at `k` points alias the coefficients `a_j, a_{j+k}, a_{j+2k}, …`. -/
theorem aliasSumFun_sub_cauchyCoeff_eq_tsum {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) {j k : ℕ} (hjk : j < k) :
    aliasSumFun f j k - cauchyCoeff f R j = ∑' l : ℕ, cauchyCoeff f R (j + (l + 1) * k) := by
  rw [aliasSumFun_sub_cauchyCoeff hR hf hjk,
    ← (hasSum_circleIntegral_div_pow hR hf j (by omega : 0 < k)).tsum_eq, ← tsum_mul_left]
  rfl

end Exercise450

section Exercise451

open Finset Complex ComplexConjugate

variable {g : ℂ → ℂ}

/-- `conj (e^(2πi/k)) = (e^(2πi/k))⁻¹`. -/
theorem conj_exp_two_pi_div (k : ℕ) :
    conj (exp (2 * Real.pi * I / k)) = (exp (2 * Real.pi * I / k))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

/-- For even `k`, `(e^(2πi/k))^(k/2) = −1`. -/
theorem exp_two_pi_div_pow_half {k : ℕ} (hk : k % 2 = 0) (hk0 : 0 < k) :
    exp (2 * Real.pi * I / k) ^ (k / 2) = -1 := by
  have hk2 : ((k / 2 : ℕ) : ℂ) * 2 = (k : ℂ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hk)
  have hk2' : ((k / 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k / 2 ≠ 0)
  rw [← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I]
  congr 1
  rw [← hk2]
  field_simp

/-- Conjugation symmetry alone: if `g(conj z) = conj g(z)`, every sample `g(w^m)`, `m < k`, is
`g(w^r)` or `conj g(w^r)` for some `r ≤ k/2` — about `k/2` evaluations suffice. -/
theorem sample_reduce_conj (hg : ∀ z, g (conj z) = conj (g z)) {k : ℕ} (hk0 : 0 < k) {m : ℕ}
    (hm : m < k) :
    ∃ r ≤ k / 2, g (exp (2 * Real.pi * I / k) ^ m) = g (exp (2 * Real.pi * I / k) ^ r)
      ∨ g (exp (2 * Real.pi * I / k) ^ m) = conj (g (exp (2 * Real.pi * I / k) ^ r)) := by
  have hζ : IsPrimitiveRoot (exp (2 * Real.pi * I / k)) k := Complex.isPrimitiveRoot_exp k hk0.ne'
  by_cases h : m ≤ k / 2
  · exact ⟨m, h, Or.inl rfl⟩
  · refine ⟨k - m, by omega, Or.inr ?_⟩
    rw [← hg, map_pow, conj_exp_two_pi_div, inv_pow]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, Nat.add_sub_cancel' hm.le, hζ.pow_eq_one]

/-- Even `k`, `g` even and conjugation-symmetric: every sample `g(w^m)` is `g(w^r)` or
`conj g(w^r)` for some `r ≤ k/4` — about `k/4` evaluations suffice. -/
theorem sample_reduce_even (hg : ∀ z, g (conj z) = conj (g z)) (hge : ∀ z, g (-z) = g z)
    {k : ℕ} (hk : k % 2 = 0) (hk0 : 0 < k) {m : ℕ} (hm : m < k) :
    ∃ r ≤ k / 4, g (exp (2 * Real.pi * I / k) ^ m) = g (exp (2 * Real.pi * I / k) ^ r)
      ∨ g (exp (2 * Real.pi * I / k) ^ m) = conj (g (exp (2 * Real.pi * I / k) ^ r)) := by
  have hk2 : 0 < k / 2 := by omega
  obtain ⟨m₁, q, hm₁, hq, rfl⟩ : ∃ m₁ q, m₁ < k / 2 ∧ q ≤ 1 ∧ m = m₁ + k / 2 * q := by
    refine ⟨m % (k / 2), m / (k / 2), Nat.mod_lt _ hk2, ?_, (Nat.mod_add_div m (k / 2)).symm⟩
    have := (Nat.div_lt_iff_lt_mul hk2).mpr (show m < 2 * (k / 2) by omega)
    omega
  have hval : g (exp (2 * Real.pi * I / k) ^ (m₁ + k / 2 * q))
      = g (exp (2 * Real.pi * I / k) ^ m₁) := by
    rw [pow_add, pow_mul, exp_two_pi_div_pow_half hk hk0]
    interval_cases q <;> simp [hge]
  by_cases h : m₁ ≤ k / 4
  · exact ⟨m₁, h, Or.inl hval⟩
  · refine ⟨k / 2 - m₁, by omega, Or.inr ?_⟩
    rw [hval, ← hg, map_pow, conj_exp_two_pi_div, inv_pow, ← hge]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [neg_mul, ← pow_add, show m₁ + (k / 2 - m₁) = k / 2 by omega,
      exp_two_pi_div_pow_half hk hk0, neg_neg]

/-- The function (4.86) is even and conjugation-symmetric, so both reductions apply; in the
series form this is `bernoulliCoeff_odd` (odd coefficients vanish) and the coefficients are real
(`bernoulliCoeff` is a rational cast). -/
theorem bernoulliCoeff_conj (l : ℕ) : conj (bernoulliCoeff l) = bernoulliCoeff l := by
  rw [bernoulliCoeff, ← Complex.ofReal_ratCast, Complex.conj_ofReal]

/-- For odd `k`, the aliased coefficients `a_{2j+lk}` with `l` odd vanish, so the `k`-point sum
equals the `2k`-point sum: `S_{2j,k} = S_{2j,2k}`. -/
theorem bernoulli_aliasSum_odd {j k : ℕ} (hk : k % 2 = 1) (hjk : 2 * j < k) :
    aliasSum bernoulliCoeff (2 * j) k = aliasSum bernoulliCoeff (2 * j) (2 * k) := by
  have ha : Summable fun l => ‖bernoulliCoeff l‖ :=
    summable_norm_of_le (by positivity)
      (by rw [div_lt_one (by positivity)]; linarith [Real.pi_gt_three]) norm_bernoulliCoeff_le
  have h1 := aliasSum_sub_eq ha hjk
  have h2 := aliasSum_sub_eq ha (by omega : 2 * j < 2 * k)
  have hs : ∀ φ : ℕ → ℕ, Function.Injective φ → Summable fun l => bernoulliCoeff (φ l) :=
    fun φ hφ => ha.of_norm.comp_injective hφ
  have hk0 : 0 < k := by omega
  have hsplit := tsum_even_add_odd (f := fun l => bernoulliCoeff (2 * j + (l + 1) * k))
    (hs (fun i => 2 * j + (2 * i + 1) * k) fun i₁ i₂ h => by
      have : (2 * i₁ + 1) * k = (2 * i₂ + 1) * k := by simpa using h
      have := Nat.eq_of_mul_eq_mul_right hk0 this
      omega)
    (hs (fun i => 2 * j + (2 * i + 1 + 1) * k) fun i₁ i₂ h => by
      have : (2 * i₁ + 1 + 1) * k = (2 * i₂ + 1 + 1) * k := by simpa using h
      have := Nat.eq_of_mul_eq_mul_right hk0 this
      omega)
  obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
  have hz : ∀ i : ℕ, bernoulliCoeff (2 * j + (2 * i + 1) * (2 * t + 1)) = 0 := fun i => by
    rw [show 2 * j + (2 * i + 1) * (2 * t + 1) = 2 * (j + 2 * i * t + i + t) + 1 by ring]
    exact bernoulliCoeff_odd _
  have hodd : ∑' i : ℕ, bernoulliCoeff (2 * j + (2 * i + 1 + 1) * (2 * t + 1))
      = ∑' i : ℕ, bernoulliCoeff (2 * j + (i + 1) * (2 * (2 * t + 1))) :=
    tsum_congr fun i => by congr 1; ring
  rw [hodd] at hsplit
  simp only [hz, tsum_zero, zero_add] at hsplit
  linear_combination h1 - h2 - hsplit

/-- The improved error bound for odd `k`: `O((2π)^(−2k))` instead of `O((2π)^(−k))`. -/
theorem norm_bernoulli_aliasSum_sub_le_odd {j k : ℕ} (hj : 1 ≤ j) (hk : k % 2 = 1)
    (hjk : 2 * j < k) :
    ‖aliasSum bernoulliCoeff (2 * j) k - (scaledBernoulli j : ℂ)‖
      ≤ Real.pi ^ 2 / 6 * (1 / (2 * Real.pi)) ^ (2 * k) / (1 - (1 / (2 * Real.pi)) ^ (2 * k))
        * ‖(scaledBernoulli j : ℂ)‖ := by
  rw [bernoulli_aliasSum_odd hk hjk]
  exact norm_bernoulli_aliasSum_sub_le hj (by omega)

end Exercise451

end BZ

end Azurite
