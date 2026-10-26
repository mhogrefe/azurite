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
| 1.2.38 | `dlmf_1_2_38` (column vector `replicateCol (Fin 1) v`) | `Matrix.replicateCol_apply` |
| 1.2.39 | `dlmf_1_2_39` (row vector) | `Matrix.transpose_replicateCol`, `replicateRow_apply` |
| 1.2.40 | `scalarProduct u v = ∑ uᵢ v̅ᵢ`, `dlmf_1_2_40` (`= vᴴ u`); bridge `scalarProduct_eq_inner` (`= inner ℂ (toE v) (toE u)`) | `EuclideanSpace.inner_eq_star_dotProduct` |
| 1.2.41 | `dlmf_1_2_41` | proven |
| 1.2.42 | `dlmf_1_2_42` | proven |
| 1.2.43 | `dlmf_1_2_43` | `inner_self_eq_zero` |
| 1.2.44 | `Orthogonal`, `dlmf_1_2_44` | definition |
| 1.2.45 | `lpNorm p v`, `dlmf_1_2_45` | definition |
| 1.2.46 | `dlmf_1_2_46` (`‖v‖₂ = √⟨v, v⟩`, `⟨v, v⟩ = ∑ \|vᵢ\|²`); bridge `lpNorm_two_eq_norm` | `EuclideanSpace.norm_eq`, `Complex.mul_conj` |
| 1.2.47 | `dlmf_1_2_47` | proven |
| 1.2.48 | `linfNorm`, `dlmf_1_2_48` (`n ≥ 1`) | definition |
| 1.2.49 | `dlmf_1_2_49` (`p > 1`) | `Real.holderConjugate_iff` |
| 1.2.50 | `dlmf_1_2_50` (Hölder) | `Real.inner_le_Lp_mul_Lq_of_nonneg` |
| 1.2.51 | `dlmf_1_2_51` (Cauchy–Schwarz, Hölder at `2, 2`), `dlmf_1_2_51_eq` (equality iff `v = c • u`, both nonzero) | `Real.HolderConjugate.two_two`, `norm_inner_eq_norm_iff` |
| 1.2.52 | `dlmf_1_2_52` (triangle inequality, `ℓ²`) | `norm_add_le` |
| 1.2.53 | `dlmf_1_2_53` (identity `I = [δᵢⱼ]`) | `Matrix.one_apply` |
| 1.2.54 | `dlmf_1_2_54` (diagonal: `aᵢⱼ = 0` for `i ≠ j`) | `Matrix.IsDiag` |
| 1.2.55 | `dlmf_1_2_55` (real symmetric: `aⱼᵢ = aᵢⱼ`) | `Matrix.IsSymm.ext_iff` |
| 1.2.56 | `dlmf_1_2_56` (Hermitian: `aⱼᵢ = conj aᵢⱼ`) | `Matrix.IsHermitian.ext_iff` |
| 1.2.57 | `IsTridiagonal`, `dlmf_1_2_57` (`aᵢⱼ = 0` for `|i − j| > 1`) | — |
| 1.2.58 | `dlmf_1_2_58` (`|A| = det A` in index form, orders 1–3) | `Matrix.det`, `det_fin_one_of`, `det_fin_two_of`, `det_fin_three` |
| 1.2.59 | `dlmf_1_2_59` (Leibniz formula `∑_σ sign σ ∏ a_{i,σ(i)}`) | `Matrix.det_apply'`, `det_transpose` |
| 1.2.60 | `dlmf_1_2_60` (`A A⁻¹ = A⁻¹ A = I` for `det A ≠ 0`), `dlmf_1_2_60_unique` (`AB = I` or `BA = I` ⇒ `B = A⁻¹`), `dlmf_1_2_60_cancel` (`AB = AC` ⇒ `B = C`), `dlmf_1_2_60_singular` (fails for `det A = 0`) | `Matrix.mul_nonsing_inv`, `nonsing_inv_mul`, `inv_eq_right_inv`, `inv_eq_left_inv`, `nonsing_inv_mul_cancel_left` |
| 1.2.61 | `dlmf_1_2_61`, `dlmf_1_2_61_unique` (`A b = c ↔ b = A⁻¹ c`, unique solution), `dlmf_1_2_61_singular` (`det A = 0`: no solution or infinitely many), `dlmf_1_2_61_particular` (particular solution plus solutions of `A b = 0`) | `Matrix.mulVec_mulVec`, `one_mulVec`, `exists_mulVec_eq_zero_iff` |
| 1.2.62 | `dlmf_1_2_62` (`tr A = ∑ aᵢᵢ`) | `Matrix.trace` |
| 1.2.63 | `dlmf_1_2_63` (`tr(αA) = α tr A`) | `Matrix.trace_smul` |
| 1.2.64 | `dlmf_1_2_64` (`tr(A + B) = tr A + tr B`) | `Matrix.trace_add` |
| 1.2.65 | `dlmf_1_2_65` (`tr(AB) = tr(BA)`) | `Matrix.trace_mul_comm` |
| 1.2.66 | `dlmf_1_2_66` (`[A, B] = −[B, A] = AB − BA`) | `Ring.lie_def` |
| 1.2.67 | `dlmf_1_2_67` (`‖A‖ = max_{x ≠ 0} ‖Ax‖/‖x‖ = max_{‖x‖ = 1} ‖Ax‖`, `ℓ²`, as `IsGreatest`; helpers `toCLM`, `lpNorm_mulVec_le`, `exists_lpNorm_eq_one_norm_mulVec_eq`) | `Matrix.l2_opNorm_def` (scoped `Matrix.Norms.L2Operator`), `ContinuousLinearMap.le_opNorm`, `opNorm_le_bound`, `isCompact_sphere`, `IsCompact.exists_isMaxOn`, `norm_smul_inv_norm` |
| 1.2.68 | `dlmf_1_2_68` (`‖AB‖ ≤ ‖A‖ ‖B‖`) | `Matrix.l2_opNorm_mul` |
| 1.2.69 | `dlmf_1_2_69` (`‖A + B‖ ≤ ‖A‖ + ‖B‖`) | `norm_add_le` |
| 1.2.70 | `dlmf_1_2_70` (eigenpair: `a ≠ 0`, `A a = λ a`), `dlmf_1_2_70_real` (remark: real `!![0, −1; 1, 0]` has no real eigenvalue, complex eigenpair `(i, (1, −i))`) | `Module.End.HasEigenvector (toLin' A)`, `hasEigenvector_iff`, `mem_eigenspace_iff`; `Matrix.charpoly_fin_two` |
| 1.2.71 | `dlmf_1_2_71` (eigenvalues are the roots of `det(A − λI) = 0`), `dlmf_1_2_71_charpoly` (roots of the characteristic polynomial) | `Matrix.exists_mulVec_eq_zero_iff`; `Module.End.hasEigenvalue_iff_isRoot_charpoly`, `Matrix.charpoly_toLin'` |
| 1.2.72 | `dlmf_1_2_72` (`(A − λI) a = 0`), helper `mulVec_eq_smul_iff` | `Matrix.sub_mulVec`, `smul_mulVec`, `one_mulVec` |
| 1.2.73 | `dlmf_1_2_73_linearIndependent` (prose definition), `IsNonDefective`, `dlmf_1_2_73` (non-defective ⇔ `Λ = S⁻¹ A S` with `S` invertible, `Λ` diagonal), `dlmf_1_2_73_columns` (columns of `S` are eigenvectors for the diagonal entries), `dlmf_1_2_73_multiplicity` (number of equal diagonal entries = root multiplicity in the characteristic polynomial), `dlmf_1_2_73_sum_multiplicity` (multiplicities sum to `n`, every `A`) | `Fintype.linearIndependent_iff`, `Matrix.linearIndependent_cols_iff_isUnit`, `IsDiag.diagonal_diag`, `charpoly_units_conj'`, `charpoly_diagonal`, `Polynomial.roots_multiset_prod_X_sub_C`, `count_roots`, `Splits.natDegree_eq_card_roots`, `charpoly_natDegree_eq_dim` |
| 1.2.74 | `dlmf_1_2_74` (`det A = det(S S⁻¹ A) = det(S⁻¹ A S) = ∏ λᵢ`), `dlmf_1_2_74_roots` (remark: product of the eigenvalues with multiplicity, every `A`) | `Matrix.det_mul`, `det_diagonal`; `Matrix.det_eq_prod_roots_charpoly` |
| 1.2.75 | `dlmf_1_2_75` (`tr A = tr(S S⁻¹ A) = tr(S⁻¹ A S) = ∑ λᵢ`), `dlmf_1_2_75_roots` (remark: sum of the eigenvalues with multiplicity, every `A`) | `Matrix.trace_mul_comm`, `trace_diagonal`; `Matrix.trace_eq_sum_roots_charpoly` |
| 1.2.76 | `dlmf_1_2_76` (`exp A = ∑ Aⁿ/n!` as a `HasSum`, in norm), `dlmf_1_2_76_apply` (entrywise) | `NormedSpace.exp_series_hasSum_exp'` (scoped `Matrix.Norms.L2Operator`), `Pi.hasSum` |
| 1.2.77 | `etr`, `dlmf_1_2_77` (`det(exp A) = exp(tr A) = etr(A)` for non-defective `A`, via the diagonalization), `dlmf_1_2_77_general` (the remark: for every square matrix (Hall 2015, Thm 2.12), a Mathlib TODO; proven by Jacobi's formula: `detCML` (det as a continuous multilinear map of the rows), `hasDerivAt_det_of_hasDerivAt` (`d/dt det M = tr(A) det M` when `M' = A M`), `hasDerivAt_exp_smul_pi` (`d/dt exp(tA) = A exp(tA)` entrywise), `hasDerivAt_det_exp_smul`; then `det(exp(tA)) exp(−t tr A)` is constant) | `Matrix.exp_conj`, `exp_diagonal`, `det_conj`, `trace_mul_cycle`, `Pi.coe_exp`, `Complex.exp_eq_exp_ℂ`, `Complex.exp_sum`; `ContinuousMultilinearMap.hasFDerivAt`, `linearDeriv_apply`, `Matrix.det_updateRow_sum`, `hasDerivAt_exp_smul_const'`, `hasDerivAt_pi`, `is_const_of_deriv_eq_zero` |

Conventions: the partial-fraction identities (§1.2(iii)) are stated between elements of a field `K` (the DLMF has complex constants) at points `x` different from the poles, with `Polynomial.eval` for `f(x)`, `Fin n`-indexed poles and `Finset.univ` sums/products; `Fⱼ^{(k)}` is `derivative^[k]`.  Vectors (§1.2(v)) are `Fin n → ℂ`; the DLMF scalar product is linear in the first argument, the opposite of Mathlib's `inner`, hence `scalarProduct u v = inner ℂ (toE v) (toE u)`.  Matrices (§1.2(v)) are `Matrix (Fin m) (Fin n) ℂ` with `Aᵀ`, `Aᴴ` (`Matrix.conjTranspose`) and the entrywise conjugate `A.map (starRingEnd ℂ)`.  The means (§1.2(iv)) are real-valued functions of `a : Fin n → ℝ` (`n ≥ 1` as `[NeZero n]` where a maximum, minimum or `1/n` is involved); the limit `r → 0` of 1.2.26 is along `𝓝[≠] 0` since `M(0)` is undefined.  The generalized binomial coefficient `C(z, k)` of the DLMF is Mathlib's
`Ring.choose z k` (`BinomialRing`), which agrees with `Nat.choose` on the natural numbers
(`Ring.choose_natCast`); the rising factorial `(z)_k` is `(ascPochhammer ℂ k).eval z`.
