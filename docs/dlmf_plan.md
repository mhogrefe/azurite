# DLMF formalization ledger

A walk through the NIST Digital Library of Mathematical Functions (<https://dlmf.nist.gov>),
one Lean theorem per equation, in `Azurite/DLMF/ChapterC/SectionS.lean` with the theorem
`dlmf_C_S_N` for equation C.S.N (suffixes for the several equalities of one equation).  Each
theorem is either a thin restatement of a Mathlib lemma, named in its docstring and here, or a
proof of its own.  Statements follow the DLMF text (variables, hypotheses, ranges); where the
DLMF leaves a type implicit (for example the ring of the binomial theorem) the theorem is stated
at the natural generality.

## Chapter 1: Algebraic and Analytic Methods

### §1.2 Elementary Algebra (`Azurite/DLMF/Chapter1/Section2.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.2.1 | `dlmf_1_2_1` (in `ℕ`, exact division), `dlmf_1_2_1_cast` (in `ℂ`), `dlmf_1_2_1_symm` | `Nat.choose_eq_factorial_div_factorial`, `Nat.cast_choose`, `Nat.choose_symm` |
| 1.2.2 | `dlmf_1_2_2` (any commutative semiring) | `add_pow` |
| 1.2.3 | `dlmf_1_2_3` | `Nat.sum_range_choose` |
| 1.2.4 | `dlmf_1_2_4` (`n ≥ 1`) | `Int.alternating_sum_range_choose_of_ne` |
| 1.2.5 | `dlmf_1_2_5` (`n ≥ 1`; the sum over even `k ≤ n`) | proven from 1.2.3 and 1.2.4 |
| 1.2.6 | `dlmf_1_2_6` (falling product), `dlmf_1_2_6_asc` (`(−1)^k (−z)_k / k!`), `dlmf_1_2_6_neg` (`(−1)^k C(k − z − 1, k)`), for `z : ℂ` with `Ring.choose` | `Ring.descPochhammer_eq_factorial_smul_choose`, `descPochhammer_eval_eq_prod_range`, `ascPochhammer_eval_neg_eq_descPochhammer`; helper `descPochhammer_smeval_eq_prod` |
| 1.2.7 | `dlmf_1_2_7` (with `k + 1`) | `Ring.choose_succ_succ` |
| 1.2.8 | `dlmf_1_2_8` | proven (induction with 1.2.7) |
| 1.2.9 | `dlmf_1_2_9` | proven (induction with 1.2.7) |
| 1.2.10 | `dlmf_1_2_10_two_mul` (any commutative ring, `2 ∑ = 2na + n(n−1)d`), `dlmf_1_2_10` and `dlmf_1_2_10_last` (`n a + n(n−1)d/2 = n(a + ℓ)/2`, field of characteristic zero) | proven (induction) |
| 1.2.11 | `dlmf_1_2_11` (`x ≠ 1`, division ring) | `geom_sum_eq` |
| 1.2.12 | `dlmf_1_2_12` (existence of the `Aⱼ`; `α : Fin n → K` injective, `deg f < n`, `x` not a pole, any field `K`) | proven: `partialFractions_poly` (the polynomial identity `f = ∑ Aⱼ ∏_{k≠j} (X − αₖ)` by `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`) |
| 1.2.13 | `dlmf_1_2_13` (`Aⱼ = f(αⱼ) / ∏_{k≠j} (αⱼ − αₖ)`) | proven (same) |
| 1.2.14 | `dlmf_1_2_14` (existence of the `Bⱼ`, field of characteristic zero) | proven |
| 1.2.15 | `dlmf_1_2_15` (`Bⱼ = f^{(n−j)}(α) / (n − j)!`, indexed `j = i + 1`) | `sum_taylor_eq`, `taylor_coeff`, `factorial_smul_hasseDeriv` (helper `eval_iterate_derivative_eq_factorial_mul`) |
| 1.2.16 | `dlmf_1_2_16` (polynomials `fⱼ`, `deg fⱼ < mⱼ`, for positive `mⱼ` and `deg f < ∑ mⱼ`) | `eq_quo_mul_prod_add_sum_rem_mul_prod` (`pairwise_coprime_X_sub_C`; the quotient vanishes by a `natDegree` count) |
| 1.2.17 | `arithMean`, `dlmf_1_2_17` | definition |
| 1.2.18 | `geomMean` (`(∏ aⱼ)^(1/n)`, `Real.rpow`), `dlmf_1_2_18` | definition |
| 1.2.19 | `harmMean`, `dlmf_1_2_19` (`1/H = (1/n) ∑ 1/aⱼ`) | definition |
| 1.2.20 | `IsWeights p` (`pⱼ > 0`, `∑ pⱼ = 1`), `dlmf_1_2_20`; `isWeights_const` for `pⱼ = 1/n` | definition |
| 1.2.21 | `weightedMean p a r`, `dlmf_1_2_21` (`r ≠ 0`, outside the case of 1.2.22) | definition |
| 1.2.22 | `dlmf_1_2_22` (`M(r) = 0` for `r < 0` and `∏ aⱼ = 0`, built into the definition) | definition |
| 1.2.23 | `dlmf_1_2_23` (`M(r) → max` as `r → ∞`; `n ≥ 1`, `aⱼ ≥ 0`, weights) | proven (squeeze `pⱼ₀^(1/r) max ≤ M(r) ≤ max`, `Real.continuousAt_const_rpow`) |
| 1.2.24 | `dlmf_1_2_24` (`M(r) → min` as `r → −∞`) | proven (1.2.22 when some `aⱼ = 0`; else `M(r) = 1/M'(−r)` for the reciprocals and 1.2.23; `sup'_inv_eq_inv_inf'`) |
| 1.2.25 | `dlmf_1_2_25_arith` (`M(1) = A`), `dlmf_1_2_25_harm` (`M(−1) = H`, `aⱼ > 0`), for `pⱼ = 1/n` | proven |
| 1.2.26 | `dlmf_1_2_26` (`M(r) → G` as `r → 0` in `𝓝[≠] 0`, `pⱼ = 1/n`, `aⱼ > 0`) | proven (`log M(r) = log S(r)/r`, `S(0) = 1`, `HasDerivAt.log`, `hasDerivAt_iff_tendsto_slope_zero`) |
| 1.2.27 | `dlmf_1_2_27` (`Matrix (Fin m) (Fin n) ℂ`, `Matrix.of`) | `Matrix.of_apply` |
| 1.2.28 | `dlmf_1_2_28` (`Aᵀ i j = A j i`) | `Matrix.transpose_apply` |
| 1.2.29 | `dlmf_1_2_29` (entrywise conjugate as `A.map (starRingEnd ℂ)`) | `Matrix.map_apply` |
| 1.2.30 | `dlmf_1_2_30` (`Aᴴ`, `conjTranspose`) | `Matrix.conjTranspose_apply` |
| 1.2.31 | `dlmf_1_2_31` (`(α • A) i j = α aᵢⱼ = aᵢⱼ α`) | `Matrix.smul_apply` |
| 1.2.32 | `dlmf_1_2_32` | `add_comm`, `Matrix.add_apply` |
| 1.2.33 | `dlmf_1_2_33` | `add_assoc`, `Matrix.add_apply` |
| 1.2.34 | `dlmf_1_2_34` (`m × n` times `n × p`) | `Matrix.mul_apply` |
| 1.2.35 | `dlmf_1_2_35` | `Matrix.mul_assoc` |
| 1.2.36 | `dlmf_1_2_36` | `Matrix.mul_add` |
| 1.2.37 | `dlmf_1_2_37` | `Matrix.transpose_mul` |
| 1.2.38–1.2.62 | — | not yet |

Conventions: the partial-fraction identities (§1.2(iii)) are stated between elements of a field `K` (the DLMF has complex constants) at points `x` different from the poles, with `Polynomial.eval` for `f(x)`, `Fin n`-indexed poles and `Finset.univ` sums/products; `Fⱼ^{(k)}` is `derivative^[k]`.  Matrices (§1.2(v)) are `Matrix (Fin m) (Fin n) ℂ` with `Aᵀ`, `Aᴴ` (`Matrix.conjTranspose`) and the entrywise conjugate `A.map (starRingEnd ℂ)`.  The means (§1.2(iv)) are real-valued functions of `a : Fin n → ℝ` (`n ≥ 1` as `[NeZero n]` where a maximum, minimum or `1/n` is involved); the limit `r → 0` of 1.2.26 is along `𝓝[≠] 0` since `M(0)` is undefined.  The generalized binomial coefficient `C(z, k)` of the DLMF is Mathlib's
`Ring.choose z k` (`BinomialRing`), which agrees with `Nat.choose` on the natural numbers
(`Ring.choose_natCast`); the rising factorial `(z)_k` is `(ascPochhammer ℂ k).eval z`.
