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

### §1.3 Determinants, Linear Operators, and Spectral Expansions (`Azurite/DLMF/Chapter1/Section3.lean`)

Prose statements (no equation number) are named `dlmf_1_3_i_<topic>` after their subsection.

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.3.1 | `dlmf_1_3_1` (`2 × 2`) | `Matrix.det_fin_two` |
| 1.3.2 | `dlmf_1_3_2` (`3 × 3`: first-row expansion in `2 × 2` minors, and the full expansion) | `Matrix.det_fin_three`, `det_fin_two_of` |
| 1.3.3 | `minor` (delete row `j`, column `k`: `submatrix` along `Fin.succAbove`), `cofactor`, `dlmf_1_3_3`, `dlmf_1_3_3_adjugate` (`adjugate A k j = cofactor A j k`) | `Matrix.adjugate_fin_succ_eq_det_submatrix` |
| 1.3.4 | `dlmf_1_3_4` (expansion by the `j`-th row) | `Matrix.det_succ_row` |
| §1.3(i) prose | `dlmf_1_3_i_swap_rows`, `dlmf_1_3_i_swap_cols` (interchange changes sign), `dlmf_1_3_i_row_eq`, `dlmf_1_3_i_col_eq` (identical rows/columns give `0`), `dlmf_1_3_i_smul_row`, `dlmf_1_3_i_smul_col` (factor `μ`), `dlmf_1_3_i_add_smul_row`, `dlmf_1_3_i_add_smul_col` (adding `μ` times another row/column) | `Matrix.det_permute`, `det_permute'`, `Equiv.Perm.sign_swap`, `det_zero_of_row_eq`, `det_zero_of_column_eq`, `det_updateRow_smul`, `det_updateCol_smul`, `det_updateRow_add_smul_self`, `det_updateCol_add_smul_self` |
| 1.3.5 | `dlmf_1_3_5` | `Matrix.det_transpose` |
| 1.3.6 | `dlmf_1_3_6` (`det A⁻¹ = 1 / det A`, every `A` with Mathlib's inverse) | `Matrix.det_nonsing_inv`, `Ring.inverse_eq_inv'` |
| 1.3.7 | `dlmf_1_3_7` | `Matrix.det_mul` |
| §1.3(i) prose | `dlmf_1_3_i_isUpperTriangular`, `dlmf_1_3_i_isLowerTriangular` (definitions), `dlmf_1_3_i_det_upperTriangular`, `dlmf_1_3_i_det_lowerTriangular`, `dlmf_1_3_i_det_diagonal` (`det A = ∏ aᵢᵢ`) | `Matrix.IsUpperTriangular`, `IsLowerTriangular`, `det_of_isUpperTriangular`, `det_of_isLowerTriangular`, `IsDiag.diagonal_diag`, `det_diagonal` |
| 1.3.8 | `dlmf_1_3_8` (Hadamard, `n = 2`, real entries) | — (Lagrange's identity, `nlinarith`) |
| 1.3.9 | `dlmf_1_3_9` (Hadamard's inequality `det A² ≤ ∏ⱼ ∑ₖ aⱼₖ²`, real entries; helpers `rowE`, `det_eq_basisFun_det`, `exists_det_eq_prod_inner` (`det A = ± ∏ ⟪eᵢ, aᵢ⟫` for the Gram–Schmidt orthonormal basis), `inner_sq_le_sum_sq`, `det_sq_eq_prod_inner_sq`) | `InnerProductSpace.gramSchmidtOrthonormalBasis_det`, `gramSchmidtOrthonormalBasis_inv_triangular`, `OrthonormalBasis.det_to_matrix_orthonormalBasis_real`, `Module.Basis.toMatrix_mul_toMatrix`, `abs_real_inner_le_norm`, `Finset.prod_le_prod₀` |
| 1.3.10 | `dlmf_1_3_10` (equality iff `∑ₗ aⱼₗ aₖₗ = 0` for all `j ≠ k`, or some `∑ₖ aⱼₖ² = 0`) | `norm_inner_eq_norm_iff`, `Finset.mul_prod_erase`, `Matrix.det_eq_zero_of_row_eq_zero` |
| 1.3.11 | `dlmf_1_3_11` (`det [fₖ(xⱼ)]` changes sign under `xᵢ ↔ xᵢ'`) | `dlmf_1_3_i_swap_rows` |
| 1.3.12 | `dlmf_1_3_12` (`det [f(xⱼ, yₖ)]` alternating in `x` and in `y`) | `dlmf_1_3_i_swap_rows`, `dlmf_1_3_i_swap_cols` |
| 1.3.13 | `dlmf_1_3_13` (Vandermonde `det [xⱼ^(k−1)] = ∏_{j<k} (xₖ − xⱼ)`) | `Matrix.det_vandermonde` |
| 1.3.14 | `dlmf_1_3_14` (Cauchy `det [1/(aⱼ − bₖ)] = (−1)^(n(n−1)/2) ∏_{j<k} (aₖ − aⱼ)(bₖ − bⱼ) / ∏_{j,k} (aⱼ − bₖ)` for `aⱼ ≠ bₖ`; `cauchyMatrix`, `det_cauchyMatrix_succ` (peel the first row and column by row/column operations and `det_succ_column_zero`), `det_cauchyMatrix_mul` (induction)) | `Matrix.det_eq_of_forall_row_eq_smul_add_const` (+ column version `det_eq_of_forall_col_eq_smul_add_const`), `det_succ_column_zero`, `Fin.prod_Ioi_zero`, `Fin.prod_Ioi_succ`, `Nat.triangle_succ` |
| 1.3.15 | `dlmf_1_3_15` (circulant `= ∏ₖ (a₁ + a₂ωₖ + ⋯ + aₙωₖ^(n−1))`, `ωₖ = exp(2πik/n)`; `circ` (entry `(j, k) = a (k − j)`), `circ_mul_eq` (`C F = F diag(λ)`, columns of `F` the eigenvectors `(ωₖ^i)ᵢ`), `det_circ_of_isPrimitiveRoot` (any primitive root)) | `Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.pow_inj`, `Matrix.det_vandermonde_ne_zero_iff`, `Fin.val_add` |
| 1.3.16 | `krat`, `dlmf_1_3_16` (`tⱼₖ`, indices shifted to start at `0`) | — |
| 1.3.17 | `dlmf_1_3_17` (Krattenthaler's formula; `det_krat` by induction: `det_krat_succ` (polynomial of degree `n` in `xₙ` vanishing at `x₀, …, xₙ₋₁`: `kratPoly`, `det_kratPoly_expand`, `det_kratPoly_coeff`, `det_kratPoly_natDegree_le`), `det_kratOnes` (leading coefficient by column operations), helpers `prod_Ioi_castSucc_eq`, `prod_Iio_succ_eq`, `prod_Ioi_castSucc_eq'`) | `Matrix.det_eq_of_forall_col_eq_smul_add_pred`, `det_succ_row`, `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `RingHom.map_det`, `Fin.snoc_init_self` |
| 1.3.18 | `infDet`, `dlmf_1_3_18` (`Dₙ[a]`), `InfDetConverges` (`D_∞[a] = L`) | — |
| 1.3.19 | `IsHillType`, `dlmf_1_3_19` (`∑ |a_{j,k} − δ_{j,k}| < ∞`); `dlmf_1_3_iii_hill_converges` (Hill-type determinants always converge, von Koch's theorem: `hillMinor`, `det_eq_det_submatrix_compl` (unit rows collapse, block triangularity), `det_one_add_eq_sum_compl` (principal-minor expansion), `norm_det_le_prod_sum` (`|det M| ≤ ∏ⱼ ∑ᵢ |Mᵢⱼ|`), `norm_hillMinor_le`, `summable_prod_finset` (`∑_S ∏_{j∈S} rⱼ ≤ exp ∑ rⱼ`), `infDet_eq_sum_hillMinor` (`shiftZ` reindexing), `tendsto_powerset_Icc`) | `Matrix.BlockTriangular.det_fintype`, `MultilinearMap.map_add_univ`, `Finset.prod_univ_sum`, `Finset.prod_add`, `summable_of_sum_le`, `Summable.of_norm_bounded`, `HasSum.prod_fiberwise`, `Summable.prod_factor`, `Finset.sum_nbij'`, `Matrix.det_submatrix_equiv_self` |
| §1.3(iv) prose | `dlmf_1_3_iv_linear` (`A(αa + βb) = αAa + βAb`), `dlmf_1_3_iv_adjoint` (`⟨Aa, b⟩ = ⟨a, Aᴴb⟩`), `dlmf_1_3_iv_adjoint_unique` (`A* = Aᴴ` is the only adjoint), `dlmf_1_3_iv_adjoint_real` (`A* = Aᵀ`), `dlmf_1_3_iv_selfAdjoint`, `dlmf_1_3_iv_selfAdjoint_real`, `dlmf_1_3_iv_eigenvalue_real`, `dlmf_1_3_iv_spectrum` (spectrum = the `n` real eigenvalues), `dlmf_1_3_iv_spectral` (orthonormal eigenvector columns, `S` unitary, `S⁻¹ = Sᴴ`, `SᴴAS = [λᵢδᵢⱼ]`), `dlmf_1_3_iv_spectral_real` (`S` orthogonal), `dlmf_1_3_iv_simultaneous` (`[A, B] = 0` ⇒ orthonormal basis of simultaneous eigenvectors); helpers `exists_unitary_diagonalization`, `scalarProduct_col`, `scalarProduct_single`, `single_scalarProduct`, `scalarProduct_orthonormalBasis`, `toEuclideanLin_apply_eq`, `exists_orthonormalBasis_subordinate` | `Matrix.mulVec_single_one`, `dotProduct_mulVec`, `vecMul_transpose`, `IsHermitian.spectrum_eq_image_range`, `IsHermitian.eigenvectorUnitary`, `mulVec_eigenvectorBasis`, `conjStarAlgAut_star_eigenvectorUnitary`, `mem_unitaryGroup_iff'`, `mem_orthogonalGroup_iff'`, `conjTranspose_eq_transpose_of_trivial`, `isSymmetric_toEuclideanLin_iff`, `LinearMap.IsSymmetric.directSum_isInternal_of_commute`, `orthogonalFamily_eigenspace_inf_eigenspace`, `DirectSum.isInternal_ne_bot_iff`, `iSupIndep.fintypeNeBotOfFiniteDimensional`, `DirectSum.IsInternal.subordinateOrthonormalBasis` |
| 1.3.20 | `dlmf_1_3_20` (`u = ∑ cᵢ aᵢ`, `cᵢ = ⟨u, aᵢ⟩`, for `aᵢ` orthonormal in the DLMF scalar product); `orthonormalBasisOf` | `OrthonormalBasis.mk`, `LinearIndependent.span_eq_top_of_card_eq_finrank'`, `OrthonormalBasis.sum_repr'` |
| 1.3.21 | `dlmf_1_3_21` (Parseval `‖u‖² = ∑ |cᵢ|²`) | `OrthonormalBasis.repr` (isometry), `EuclideanSpace.norm_sq_eq`, `repr_apply_apply` |

§1.3 is complete.

### §1.4 Calculus of One Variable (`Azurite/DLMF/Chapter1/Section4.lean`)

Prose statements (no equation number) are named `dlmf_1_4_i_<topic>`, `dlmf_1_4_ii_<topic>`, …
after their subsection.

| Equation | Theorem | Mathlib |
|---|---|---|
| §1.4(i) prose | `dlmf_1_4_i_nondecreasing`, `dlmf_1_4_i_increasing`, `dlmf_1_4_i_nonincreasing`, `dlmf_1_4_i_decreasing` (the four cases with `x₁ < x₂`), `IsMonotonic`, `IsStrictlyMonotonic`, `isMonotonic_iff`, `IsStrictlyMonotonic.isMonotonic` | `MonotoneOn`, `StrictMonoOn`, `AntitoneOn`, `StrictAntiOn`, `StrictMonoOn.monotoneOn` |
| 1.4.1 | `dlmf_1_4_1` (continuous on the right iff `f(c+) = f(c)`) | `ContinuousWithinAt`, `continuousWithinAt_Ioi_iff_Ici` |
| 1.4.2 | `dlmf_1_4_2` (`ε`–`δ`: `|f(c + α) − f(c)| < ε` for `0 ≤ α < δ`) | `Metric.continuousWithinAt_iff` |
| 1.4.3 | `dlmf_1_4_3` (continuous on the left iff `f(c−) = f(c)`), `dlmf_1_4_3_eps` (`ε`–`δ`) | `continuousWithinAt_Iio_iff_Iic`, `Metric.continuousWithinAt_iff` |
| §1.4(ii) prose | `dlmf_1_4_ii_continuousAt` (both sides), `dlmf_1_4_ii_C_open` (`C(a, b)`), `dlmf_1_4_ii_C_closed` (`C[a, b]` for `a < b`), `HasRemovableSingularity` (+ `.continuousAt_update`), `dlmf_1_4_ii_sin_div_removable` (`(sin x)/x` at `0`), `HasSimpleDiscontinuity`, `IsPiecewiseContinuous` (+ `ContinuousOn.isPiecewiseContinuous`), `dlmf_1_4_ii_step_piecewiseContinuous` (unit step, cf. Figure 1.4.1) | `continuousAt_iff_continuous_left_right`, `IsOpen.continuousOn_iff`, `Icc_mem_nhdsGE`, `Icc_mem_nhdsLE`, `Real.continuous_sinc`, `Real.sinc_of_ne_zero` |
| 1.4.4 | `dlmf_1_4_4` (`HasDerivAt f f' x` iff the difference quotient tends to `f'`), `dlmf_1_4_4_differentiable` (differentiable iff the limit exists) | `hasDerivAt_iff_tendsto_slope_zero` |
| 1.4.5 | `dlmf_1_4_5` | `deriv_add` |
| 1.4.6 | `dlmf_1_4_6` | `deriv_mul` |
| 1.4.7 | `dlmf_1_4_7` (`g(x) ≠ 0`) | `deriv_div` |
| 1.4.8 | `dlmf_1_4_8` (`f⁽²⁾ = (f')'`) | `iteratedDeriv_succ`, `iteratedDeriv_one` |
| 1.4.9 | `dlmf_1_4_9` | `iteratedDeriv_succ` |
| §1.4(iii) prose | `dlmf_1_4_iii_Cn` (`Cⁿ(I)` iff `f, …, f⁽ⁿ⁾` exist and are continuous, `UniqueDiffOn I`), `dlmf_1_4_iii_Cinfty` | `contDiffOn_nat_iff_continuousOn_differentiableOn_deriv`, `contDiffOn_infty` |
| 1.4.10 | `dlmf_1_4_10` (chain rule) | `deriv_comp` |
| §1.4(iii) prose | `dlmf_1_4_iii_max`, `dlmf_1_4_iii_min` (`f ≤ f(c)` / `f ≥ f(c)` on `[c − δ, c + δ]` ⇒ `f'(c) = 0`) | `IsLocalMax.deriv_eq_zero`, `IsLocalMin.deriv_eq_zero` |
| 1.4.11 | `dlmf_1_4_11` (mean value theorem) | `exists_deriv_eq_slope` |
| §1.4(iii) prose | `dlmf_1_4_iii_monotone` (`f' ≥ 0`), `dlmf_1_4_iii_antitone` (`f' ≤ 0`), `dlmf_1_4_iii_const` (`f' = 0`) on `(a, b)` | `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos` |
| 1.4.12 | `dlmf_1_4_12` (Leibniz, `∑ C(n, k) f⁽ⁿ⁻ᵏ⁾ g⁽ᵏ⁾`) | `iteratedDeriv_mul`, `Finset.sum_range_reflect`, `Nat.choose_symm` |
| 1.4.13 | `dlmf_1_4_13` (DLMF's multiplicity form `∑_{m₁+2m₂+⋯+nmₙ=n} n!/(m₁!⋯mₙ!) f⁽ᵏ⁾(g) ∏ (g⁽ʲ⁾/j!)^{mⱼ}`, the solutions indexed by `Nat.Partition n` with `mⱼ = count j`), `dlmf_1_4_13_tuples` (literally over the tuples `multiplicityVectors n`; bijection `multiplicities`/`partitionOfMultiplicities`), `dlmf_1_4_13_partitions` (Mathlib's ordered-set-partition form), `dlmf_1_4_13_two`, `dlmf_1_4_13_three`. The bridge is `Azurite/DLMF/Chapter1/SetPartitionCount.lean`: `cnt_eq_bell` (the number of ordered finpartitions of `Fin n` with block sizes `s` is `Multiset.bell s` — Mathlib's TODO), by induction via `OrderedFinpartition.extendEquiv` (`sizes_extendLeft`, `sizes_extendMiddle`, `cnt_succ`) with the weight `wt` (`wt_erase_one`, `wt_grow`, `cnt_mul_wt`, `bell_mul_wt`); then `iteratedDeriv_comp_eq_sum_partition` (regrouping by `Finset.sum_comp`) and `bell_cast_eq` | `iteratedDeriv_comp_eq_sum_orderedFinpartition`, `OrderedFinpartition.extendEquiv`, `Multiset.bell_mul_eq`, `Finset.prod_multiset_map_count`, `Finset.sum_comp`, `Nat.Partition`, `iteratedDeriv_comp_two`, `iteratedDeriv_comp_three` |
| 1.4.14–1.4.15 | `dlmf_1_4_15` (L'Hôpital `0/0`), `dlmf_1_4_15_atTop` (`∞/∞`, proven here: `lhopital_atTop_estimate`, `lhopital_atTop_right_on_Ioo` via Cauchy's MVT on `[x, y]`, `lhopital_atTop_left_on_Ioo` by reflection) | `deriv.lhopital_zero_nhdsNE`, `exists_ratio_hasDerivAt_eq_ratio_slope`, `exists_hasDerivAt_eq_slope`, `differentiableAt_of_deriv_ne_zero`, `tendsto_neg_nhdsGT_neg` |
| §1.4(iv) prose | `IsAntiderivOn`, `IsAntiderivOn.add_const`, `dlmf_1_4_iv_antideriv` (`∫ f dx = F(x) + C`: two indefinite integrals on an open preconnected set differ by a constant) | `IsOpen.is_const_of_deriv_eq_zero` |
| 1.4.16 | `dlmf_1_4_16` (`F g − H` is an indefinite integral of `f g` when `F' = f`, `H' = F g'`), `dlmf_1_4_16_definite` | `HasDerivAt.mul`, `intervalIntegral.integral_mul_deriv_eq_deriv_mul` |
| 1.4.17 | `dlmf_1_4_17` (`xⁿ⁺¹/(n + 1)`, `n : ℤ`, `n ≠ −1`, `x ≠ 0` or `n ≥ 0`), `dlmf_1_4_17_neg_one` (`ln|x|`, `x ≠ 0`), `dlmf_1_4_17_rpow` (real `n ≠ −1`, `x > 0`) | `hasDerivAt_zpow`, `Real.hasDerivAt_log`, `Real.log_abs`, `Real.hasDerivAt_rpow_const` |
| 1.4.18 | `TaggedPartition`, `TaggedPartition.riemannSum`, `HasRiemannIntegral`, `RiemannIntegrable`, `HasRiemannIntegral.unique` (via `uniformPartition`); `dlmf_1_4_18` (continuous `f`: Riemann sums → `∫ x in a..b, f x`), from `hasRiemannIntegral_of_bounded` (bounded and continuous off a finite set: uniform continuity away from `η`-windows, `sum_lengths_le` by Lebesgue measure, `sum_biUnion_le_of_nonneg`, `riemannSum_sub_integral`, `abs_error_term_le`) and `intervalIntegrable_of_bounded` | `intervalIntegral.sum_integral_adjacent_intervals`, `intervalIntegral.norm_integral_le_of_norm_le_const`, `IsCompact.uniformContinuousOn_of_continuous`, `IsCompact.exists_bound_of_continuousOn`, `measure_biUnion_finset`, `IntegrableOn.of_bound`, `sdiff_null_ae_eq_self` |
| §1.4(v) prose | `dlmf_1_4_v_piecewise` (piecewise continuity suffices; `IsPiecewiseContinuous.exists_bound` by local boundedness and compactness) | `IsCompact.elim_nhds_subcover'`, `nhdsLT_sup_nhdsGT` |
| 1.4.19 | `dlmf_1_4_19` (`∫(cf + dg) = c∫f + d∫g`), `HasRiemannIntegral.linear` (for the Riemann sums) | `intervalIntegral.integral_add`, `integral_const_mul` |
| 1.4.20 | `dlmf_1_4_20` | `intervalIntegral.integral_symm` |
| 1.4.21 | `dlmf_1_4_21` | `intervalIntegral.integral_add_adjacent_intervals` |
| 1.4.22 | `ConvergesAtTop`, `ConvergesAtBot` (the improper integrals as limits), `dlmf_1_4_22`, `dlmf_1_4_22_Iic` (for integrable `f` the limits are `∫_{(a,∞)} f`, `∫_{(−∞,a]} f`) | `intervalIntegral_tendsto_integral_Ioi`, `intervalIntegral_tendsto_integral_Iic` |
| 1.4.23 | `ConvergesLeft`, `ConvergesRight` (singular endpoint), `dlmf_1_4_23`, `dlmf_1_4_23_right` | `intervalIntegral.continuousOn_primitive_interval`, `integral_interval_sub_left` |
| §1.4(v) prose | `dlmf_1_4_v_abs_atTop`, `dlmf_1_4_v_abs_left` (absolute convergence implies convergence, and integrability) | `integrableOn_Ioi_of_intervalIntegral_norm_tendsto`, `integrableOn_Ioc_of_intervalIntegral_norm_bounded_right` |
| §1.4(v) prose (Stieltjes, Lebesgue, Lebesgue–Stieltjes) | `dlmf_1_4_v_stieltjes_measure` (`dα((c, d]) = α(d) − α(c)`; Mathlib's `StieltjesFunction` is nondecreasing and right-continuous, `Monotone.stieltjesFunction` regularizes), `dlmf_1_4_v_lebesgue` (`volume = dα` for `α(x) = x`), `TaggedPartition.stieltjesSum`, `HasStieltjesIntegral` (Riemann–Stieltjes sums), `hasStieltjesIntegral_of_deriv` (differentiable `α` with continuous `α' = w`, continuous `f`: limit `∫ f w`, via the mean value theorem and `dlmf_1_4_18`) | `StieltjesFunction.measure_Ioc`, `Real.volume_eq_stieltjes_id`, `exists_hasDerivAt_eq_slope` |
| 1.4.23_1 | `dlmf_1_4_23_1` (`α(d) − α(c) = ∫_c^d w`, `w ≥ 0` locally integrable ⇒ `dα = volume.withDensity w`); `dlmf_1_4_v_absCont_of_deriv`, `stieltjesOfDeriv`, `stieltjesOfDeriv_measure` (`α' = w` continuous) | `Measure.ext_of_Ioc'`, `withDensity_apply`, `ofReal_integral_eq_lintegral_ofReal`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `monotone_of_deriv_nonneg` |
| 1.4.23_2 | `dlmf_1_4_23_2` (`∫_{(a,b)} f dα = ∫_a^b f w`) | `restrict_withDensity`, `integral_withDensity_eq_integral_toReal_smul₀`, `integral_Ioc_eq_integral_Ioo` |
| §1.4(v) prose (discontinuous `α`) | `heaviside` (`H(x − x₀)`, right-continuous), `heaviside_measure` (`dα = δ(x − x₀) dx`, the Dirac measure), `dlmf_1_4_v_heaviside` (`∫_{(a,b)} f dα = f(xₙ)` if `xₙ ∈ (a, b)`, else `0`) | `Measure.dirac_apply'`, `setIntegral_dirac` |
| 1.4.23_3 | `dlmf_1_4_23_3` (`α = α_w + ∑ wₙ H(x − xₙ)`, `f` continuous, `xₙ ∈ (a, b)`: `∫ f dα = ∫ w f + ∑ wₙ f(xₙ)`); `measure_sum_smul`, `integrable_sum_dirac`, `integral_sum_dirac` | `StieltjesFunction.measure_add`, `measure_smul`, `integral_add_measure`, `integral_smul_nnreal_measure`, `integrable_dirac`, `ContinuousOn.integrableOn_compact` |
| 1.4.24 | `HasPrincipalValue` (`lim_{ε→0+} (∫_a^{c−ε} f + ∫_{c+ε}^b f)`), `dlmf_1_4_24` (equals `∫_a^b f` when that exists; `tendsto_sub_nhdsGT`, `tendsto_add_nhdsGT`), `dlmf_1_4_24_inv` (`⨍_{−1}^1 dx/x = 0`) | `intervalIntegral.continuousOn_primitive_interval`, `integral_interval_sub_left`, `integral_inv` |
| 1.4.25 | `HasPrincipalValueInfty` (`lim_{b→∞} ∫_{−b}^b f`), `dlmf_1_4_25` (equals `∫ f` for integrable `f`), `dlmf_1_4_25_id` (`⨍ x dx = 0`) | `intervalIntegral_tendsto_integral`, `integral_id` |
| 1.4.26 | `dlmf_1_4_26` (`F' = f` continuous) | `intervalIntegral.integral_eq_sub_of_hasDerivAt` |
| 1.4.27 | `dlmf_1_4_27` (`f` continuous) | `Continuous.integral_hasStrictDerivAt` |
| 1.4.28 | `dlmf_1_4_28` (`φ'` continuous, `f` continuous on `φ([a, b])`), `dlmf_1_4_28_piecewise` (right derivative, integrable) | `intervalIntegral.integral_comp_mul_deriv'`, `integral_comp_mul_deriv'''` |
| 1.4.29 | `dlmf_1_4_29` (first mean value theorem, `c ∈ [a, b]`) | `exists_eq_const_mul_intervalIntegral_of_nonneg` |
| 1.4.30 | `dlmf_1_4_30` (`f` monotonic: nondecreasing or nonincreasing), `dlmf_1_4_30_monotone`, `intervalIntegrable_mul_of_monotoneOn` | `exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn` (applied to `f − f(a)`), `MonotoneOn.intervalIntegrable`, `Integrable.bdd_mul` |
| 1.4.31 | `primitive`, `repeatedIntegral` (`(n + 1)`-fold primitive), `dlmf_1_4_31` (Cauchy's formula `(1/n!) ∫_a^b (b − x)^n f`, `f` continuous; induction with `integral_pow_mul_eq_succ_mul_primitive`) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `intervalIntegral.continuous_primitive` |
| 1.4.32 | `l2NormSq` (`‖f‖₂² = ∫_a^b |f|²`), `dlmf_1_4_32` (square-integrable iff `MemLp f 2`) | `memLp_two_iff_integrable_sq` |
| 1.4.33 | `dlmf_1_4_33` (`𝒱_{a,b}(f) = eVariationOn f s`, supremum over point sets `x₀ < ⋯ < xₙ` of the closure `s`), `dlmf_1_4_v_variation_closure`, `dlmf_1_4_v_boundedVariationOn_iff`, `dlmf_1_4_v_boundedVariationOn_iff_bdd`, `leftVariation`, `leftVariation_eq_variationOnFromTo`, `dlmf_1_4_v_jordan` (`g = 𝒱_{a,x}(f)`, `h = g − f` nondecreasing bounded, `f = g − h`) | `eVariationOn`, `eVariationOn.eVariationOn_eq_strictMonoOn`, `BoundedVariationOn`, `eVariationOn.add_le_union`, `eVariationOn.edist_le` |
| Olver §11.3 | `olver_11_3` (`𝒱 ≥ ‖f(b) − f(a)‖`), `olver_11_01` (monotonic `f`: `𝒱 = |f(b) − f(a)|`), `olver_11_3_subdivision` (subdivision at the extrema), `eVariationOn_neg` | `MonotoneOn.eVariationOn_eq`, `eVariationOn.sum` |
| 1.4.34 | `olver_11_02` (`𝒱_{a,b}(f) = ∫_a^b ‖f'‖`, `f'` continuous on `[a, b]`, `E`-valued; `≤` by FTC, `≥` by Riemann sums of `‖f'‖` + uniform continuity, `sum_norm_sub_le_integral`), `exists_Icc_exhaustion`, `eVariationOn_eq_integral_of_isOpen` (open interval, Olver §11.4 incl. (11.03)), `dlmf_1_4_34` (`f` continuous on `[a, b]`, `f'` on `(a, b)`), `dlmf_1_4_34_Ioi`, `dlmf_1_4_34_Iio`, `dlmf_1_4_34_univ`, `dlmf_1_4_34_real`, `olver_11_5` (complex `f`), `variationIntegral`, `variationIntegral_symm`, `variationIntegral_eq_toReal` (DLMF's extension to arbitrary `a, b`) | `dlmf_1_4_18`, `eVariationOn.sum_le`, `tendsto_setIntegral_of_monotone`, `eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt` and the `inter_Iio/Ioi` endpoint lemmas |
| Olver Ex. 11.1 | `olver_ex_11_1_add` (`𝒱(f + g) ≤ 𝒱(f) + 𝒱(g)`), `olver_ex_11_1_norm`, `olver_ex_11_1_abs` (`𝒱(|f|) ≤ 𝒱(f)`), `olver_ex_11_1_abs_eq` (equality for continuous real `f` on an interval: refine by zeros of `f`) | `edist_add_add_le`, `LipschitzOnWith.comp_eVariationOn_le`, `intermediate_value_Icc` |
| Olver Ex. 11.2 | (ii) `olver_ex_11_2_ii` (step function, `𝒱_{−1,1} = 1`), (iii) `olver_ex_11_2_iii` (`𝒱_{−∞,∞}(sech) = 2`; `eVariationOn_Iic_of_monotoneOn`, `eVariationOn_Ici_of_antitoneOn`); (i), (iv) and Ex. 11.3–11.4 (variation along a path) not formalized | `eVariationOn.union`, `eVariationOn.eq_biSup_inter_Icc` |
| 1.4.35–1.4.36 | `taylorSum`, `iteratedDerivWithin_Icc_left`, `taylorWithinEval_eq_taylorSum`, `dlmf_1_4_35_36` (`f ∈ C^{n+1}[a, b]`, `a < x ≤ b`: `f(x) = ∑ f^{(k)}(a)/k! (x − a)^k + f^{(n+1)}(c)/(n+1)! (x − a)^{n+1}`, `a < c < x`; one-sided derivatives within `[a, b]`) | `taylor_mean_remainder_lagrange_iteratedDeriv`, `taylor_within_apply`, `iteratedFDerivWithin_inter'`, `iteratedDerivWithin_eq_iteratedDeriv` |
| 1.4.37 | `dlmf_1_4_37` (`R_n = (1/n!) ∫_a^x (x − t)^n f^{(n+1)}(t) dt`, `a ≤ x ≤ b`) | `taylor_integral_remainder`, `intervalIntegral.integral_congr_ae` |
| §1.4(vii) prose | `dlmf_1_4_vii_localMax`, `dlmf_1_4_vii_localMin` (`f'(x₀) = 0`, `f''(x₀) < 0` (`> 0`); only differentiability at `x₀` assumed), `dlmf_1_4_vii_isMaxOn`, `dlmf_1_4_vii_isMinOn` (overall extremum on `[a, b]` is a local extremum or an end point), `dlmf_1_4_vii_exists_max`, `dlmf_1_4_vii_exists_min` (continuous `f` attains them) | `isLocalMax_of_deriv_deriv_neg`, `isLocalMin_of_deriv_deriv_pos`, `IsMaxOn.isLocalMax`, `IsCompact.exists_isMaxOn` |
| 1.4.38 | `convexOn_iff_dlmf` (any interval), `dlmf_1_4_38` (`(a, b)`), `dlmf_1_4_38_Icc` (closed intervals); Figure 1.4.2 (`g(t) ≤ l(t)`) is the same inequality | `ConvexOn` |
| §1.4(viii) prose | `dlmf_1_4_viii_deriv2` (twice differentiable: convex iff `f'' ≥ 0` on `(a, b)`), `convexOn_iff_tangent_le`, `dlmf_1_4_viii_tangent` (convex iff the curve does not lie below its tangent; differentiability suffices) | `convexOn_of_deriv2_nonneg'`, `ConvexOn.monotoneOn_deriv`, `MonotoneOn.derivWithin_nonneg`, `ConvexOn.deriv_le_slope`, `ConvexOn.slope_le_deriv` |

§1.4 is complete.

### §1.5 Calculus of Two or More Variables (`Azurite/DLMF/Chapter1/Section5.lean`)

`f(x, y)` is a curried `f : ℝ → ℝ → ℝ`; plane continuity/differentiability is that of
`Function.uncurry f` (the max metric on `ℝ × ℝ` matches `|α|, |β| < δ`).

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.5.1 | `dlmf_1_5_1` (continuity at `(a, b)` as a limit) | `ContinuousAt` |
| 1.5.2 | `dlmf_1_5_2` (`ε`–`δ` with `|α|, |β| < δ`) | `Metric.continuousAt_iff`, `Prod.dist_eq` |
| §1.5(i) prose | `dlmf_1_5_i_continuousOn` (continuous on an open `D` iff at all its points), `IsPiecewiseContinuous₂` (piecewise continuous in each variable) | `IsOpen.continuousOn_iff` |
| 1.5.3–1.5.4 | `partialX`, `partialY`, `dlmf_1_5_3`, `dlmf_1_5_4` (difference-quotient limits ↔ `HasDerivAt`), `partialX_eq_of_tendsto`, `partialY_eq_of_tendsto` | `hasDerivAt_iff_tendsto_slope_zero` |
| 1.5.5 | `partialXY`, `partialYX`, `partialXX`, `partialYY`, `dlmf_1_5_5` | — |
| §1.5(i) prose | `IsContinuouslyDifferentiable` (`f, f_x, f_y` exist and are continuous), `isContinuouslyDifferentiable_iff` (iff `C¹`), `IsContinuouslyDifferentiable.hasStrictFDerivAt`, `fderiv_uncurry_eq`, `IsTwiceContinuouslyDifferentiable`, `isTwiceContinuouslyDifferentiable_iff` (iff `C²`); helpers `hasDerivAt_partialX/Y`, `partialX/Y_of_hasFDerivAt`, `clm_apply_pair`, `fderiv_uncurry_apply` | `hasStrictFDerivAt_uncurry_coprod`, `contDiff_one_iff_fderiv`, `contDiff_succ_iff_fderiv` |
| 1.5.6 | `dlmf_1_5_6` (`∂²f/∂x∂y = ∂²f/∂y∂x` for twice-continuously differentiable `f`) | `ContDiffAt.isSymmSndFDerivAt`, `HasFDerivAt.clm_apply` |
| 1.5.7 | `dlmf_1_5_7` (`f` differentiable at `(x(t), y(t))`) | `HasFDerivAt.comp_hasDerivAt` |
| 1.5.8 | `dlmf_1_5_8` | — |
| 1.5.9 | `dlmf_1_5_9` (three intermediate variables; `clm_apply_triple`) | `HasFDerivAt.comp_hasDerivAt` |
| §1.5(i) prose (implicit function theorem) | `dlmf_1_5_i_implicit` (`F` continuously differentiable, `F(a, b) = 0`, `F_y(a, b) ≠ 0`: `g` with `g(a) = b`, `F(x, g x) = 0` near `a`, zeros of `F` near `(a, b)` = graph of `g`, `g` `C¹` near `a`, `g' = −F_x/F_y` near `a`) | `ContDiffAt.implicitFunction`, `ContDiffAt.contDiffAt_implicitFunction`, `ContDiffAt.eventually` |
| §1.5(ii) prose (notations) | module doc: physicists' `θ` (polar angle) and `φ` (azimuth) | — |
| 1.5.10 | `dlmf_1_5_10` (`(x, y) = (r cos φ, r sin φ)`, `0 ≤ r`, `0 ≤ φ < 2π`), `polarPullback` | `Complex.norm_mul_cos_arg`, `Complex.norm_mul_sin_arg`, `Complex.arg` bounds |
| 1.5.11–1.5.12 | `dlmf_1_5_11`, `dlmf_1_5_12` (`r ≠ 0`, `f` differentiable at the point; `hasDerivAt_polar_r`, `hasDerivAt_polar_φ`) | — (chain rule `dlmf_1_5_7`) |
| 1.5.13 | `dlmf_1_5_13` (`f_xx + f_yy = f_rr + f_r/r + f_φφ/r²`, twice-continuously differentiable `f`, `r ≠ 0`; `hasDerivAt_polar_rr`, `hasDerivAt_polar_φφ`, `IsTwiceContinuouslyDifferentiable.differentiable`) | — |
| 1.5.14 | `dlmf_1_5_14` (cylindrical representation), `dlmf_1_5_14_partial` (1.5.11–1.5.12 still apply) | — |
| 1.5.15 | `laplacian3`, `dlmf_1_5_15` (`∇²f = f_rr + f_r/r + f_φφ/r² + f_zz`) | — |
| 1.5.16 | `dlmf_1_5_16` (spherical representation, `0 ≤ θ ≤ π`; `exists_polar_of_nonneg`), `sphericalPullback` | `Complex.arg_nonneg_iff` |
| 1.5.17 | `dlmf_1_5_17` (`f` `C²` on `ℝ³`, `ρ ≠ 0`, `sin θ ≠ 0`; cylindrical Laplacian + polar coordinates in the `(z, r)` half-plane) | `ContDiff.comp` |
| 1.5.18 | `dirDeriv` (`λ ∂/∂x + μ ∂/∂y`), `iterate_dirDeriv` (`(λ∂x + μ∂y)^k f = D^k f((λ, μ), …)`), `taylor_remainder_le` (`Cⁿ` on a normed space: remainder `≤ ε‖y‖ⁿ`), `norm_le_sqrt_sq_add_sq`, `dlmf_1_5_18` (`f` `C^{n+1}`: `R_n/(λ² + μ²)^{n/2} → 0` as `(λ, μ) → 0`) | `map_add_eq_sum_add_integral_iteratedFDeriv`, `iteratedFDeriv_succ_apply_left`, `HasFDerivAt.continuousMultilinear_apply_const` |
| 1.5.19–1.5.21 | `taylor_two`, `quadratic_lower_bound`, `isLocalMin_of_quadratic`, `dlmf_1_5_19_min`, `dlmf_1_5_19_max` (`C²` `f`: `f_x = f_y = 0`, `f_xx > 0` (`< 0`), `f_xx f_yy − f_xy² > 0` ⇒ local min (max)), `dlmf_1_5_20_21` (second-order term positive definite iff 1.5.20–1.5.21) | `dlmf_1_5_6` |
| 1.5.22 | `hasDerivAt_integral_param` (fixed limits), `hasDerivAt_integral_variable` (`f`, `f_x` continuous on the plane), `dlmf_1_5_22` (DLMF conditions (a)–(b) on `[a, b] × [c, d]`, at `a < x₀ < b`; clamping), `hasDerivAt_integral_Icc` | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `intervalIntegral.integral_hasStrictFDerivAt`, `hasStrictFDerivAt_uncurry_coprod`, `continuous_parametric_intervalIntegral_of_continuous` |
| 1.5.23–1.5.24 | `dlmf_1_5_24` (`d` finite, `[a, b] × [c, d)`, `ConvergesLeft`), `dlmf_1_5_24_atTop` (`d = ∞`, `ConvergesAtTop`); 1.5.23 stated as `|G(x) − ∫_c^{c₁} ∂f/∂x| < ε`, `G` the value of `∫_c^d ∂f/∂x` | `hasDerivAt_of_tendstoUniformlyOn`, `Metric.tendstoUniformlyOn_iff` |
| 1.5.25–1.5.27 | `doubleRiemannSum` (grid of two `TaggedPartition`s, a point `τ j k` of each cell), `HasDoubleRiemannIntegral` (limit as `max((xⱼ₊₁ − xⱼ) + (yₖ₊₁ − yₖ)) → 0`), `hasDoubleRiemannIntegral_of_continuous`, `exists_continuous_extension_rect`, `dlmf_1_5_27` (`f` continuous on `R`: the limit exists and equals the Lebesgue double integral) | `Metric.uniformContinuousOn_iff`, `IsCompact.uniformContinuousOn_of_continuous`, `intervalIntegral.sum_integral_adjacent_intervals`, `intervalIntegral.integral_finsetSum` |
| 1.5.27 (piecewise continuous) | `IsPiecewiseContinuousRect` (bounded, continuous off finitely many continuous curves `y = φᵢ(x)`, `x = ψⱼ(y)`), `ContinuousOn.isPiecewiseContinuousRect`, `stripY`, `stripX`, `volume_stripY_le`, `volume_stripX_le` (area `≤ 2r(b − a)`), `IsPiecewiseContinuousRect.integrableOn`, `exists_continuous_extension_of_isClosed` (Tietze + clamping), `TaggedPartition.sum_lengths_le_of_near`, `hasDoubleRiemannIntegral_of_degenerate`, `dlmf_1_5_27_piecewise` (Riemann sums → Lebesgue integral; `f` replaced by a continuous `g` off `η`-strips, errors `O(Mη)`) | `Measure.prod_apply`, `Measure.measurePreserving_swap`, `ContinuousMap.exists_restrict_eq`, `Integrable.of_bound`, `norm_setIntegral_le_of_norm_le_const`, `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` |
| 1.5.28–1.5.29 | `extendByZero` (`f*`), `HasDoubleRiemannIntegralOn` (Riemann form of 1.5.29), `dlmf_1_5_29` (Lebesgue form, `D ⊆ R` measurable) | `setIntegral_indicator` |
| 1.5.29–1.5.31, 1.5.34 (Riemann form) | `isPiecewiseContinuousRect_extendByZero_regionX`, `isPiecewiseContinuousRect_extendByZero_regionY` (`f*` is piecewise continuous: discontinuities along the bounding curves and the sides), `dlmf_1_5_31_riemann`, `dlmf_1_5_34_riemann` (`∬_R f* dA` exists as a Riemann limit, `= ∬_D f dA =` repeated integral) | `isOpen_lt`, `ContinuousAt.congr_of_eventuallyEq` |
| 1.5.30–1.5.32 | `regionX`, `isCompact_regionX`, `dlmf_1_5_31` (`f` continuous on `D`, `φ₁ ≤ φ₂` continuous: `∬_D f dA = ∫_a^b ∫_{φ₁}^{φ₂} f dy dx`) | `integral_prod`, `integral_indicator`, `ContinuousOn.integrableOn_compact` |
| 1.5.33–1.5.34 | `regionY`, `isCompact_regionY`, `dlmf_1_5_34` | `integral_prod_symm` |
| 1.5.35 | `dlmf_1_5_35` (change of order of integration) | — |
| 1.5.36 | `dlmf_1_5_36` (arbitrary intervals `s`, `t`; `f` measurable on `s × t`; one repeated integral absolutely convergent) | `integral_integral_swap`, `integrable_prod_iff`, `integrable_prod_iff'` |
| 1.5.37 | `regionXYZ`, `dlmf_1_5_37` (triple integral over `a ≤ x ≤ b`, `φ₁ ≤ y ≤ φ₂`, `ψ₁ ≤ z ≤ ψ₂` as a repeated integral, via `dlmf_1_5_31` on each slice) | `integral_prod` |
| §1.5(v) prose (Lebesgue) | the double/triple integrals over `D` are Lebesgue integrals throughout; `dlmf_1_5_27`/`dlmf_1_5_27_piecewise` identify the Riemann limit with them | — |
| 1.5.38 | `jacobian2` (`det` of the matrix of partials), `dlmf_1_5_38` (`f_x g_y − f_y g_x`) | `Matrix.det_fin_two_of` |
| 1.5.39 | `dlmf_1_5_39` (`∂(x, y)/∂(r, φ) = r`) | — |
| 1.5.40 | `partialX3`, `partialY3`, `partialZ3`, `jacobian3` | `Matrix.det_fin_three` |
| 1.5.41 | `dlmf_1_5_41` (`∂(x, y, z)/∂(ρ, θ, φ) = ρ² sin θ`) | — |
| §1.5(vi) bridge | `ContinuousLinearMap.det_prod_two`, `ContinuousLinearMap.det_prod_three` (`finThreeEquivProd`), `det_fderiv_eq_jacobian2`, `det_fderiv_eq_jacobian3`, `partialX3_of_hasFDerivAt` (and `Y3`, `Z3`) | `LinearMap.det_toMatrix`, `Module.Basis.finTwoProd`, `LinearMap.det_conj`, `LinearMap.det_toMatrix'`, `Fin.consLinearEquiv` |
| 1.5.42 | `dlmf_1_5_42` (`D = F(D*)`, `F` differentiable on `D*`, one-to-one off a null set `N`) | `integral_image_eq_integral_abs_det_fderiv_smul`, `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` |
| 1.5.43 | `dlmf_1_5_43` (triple integrals, likewise) | same |

§1.5 is complete.

### §1.6 Vectors and Vector-Valued Functions (`Azurite/DLMF/Chapter1/Section6.lean`)

Vectors are `a : Fin 3 → ℝ` (components `a 0, a 1, a 2`), with Mathlib's dot product `⬝ᵥ` and
cross product `⨯₃`; the Euclidean magnitude is `vnorm` (Lean's norm on `Fin 3 → ℝ` is the sup norm).

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.6.1 | `dlmf_1_6_1` | — |
| 1.6.2 | `dlmf_1_6_2` (`a · b = a₁b₁ + a₂b₂ + a₃b₃`) | `dotProduct` |
| 1.6.3 | `vnorm` (`√(a · a)`), `dlmf_1_6_3` (= norm in `EuclideanSpace ℝ (Fin 3)`), `inner_toLp` | `EuclideanSpace.norm_eq`, `EuclideanSpace.inner_eq_star_dotProduct` |
| 1.6.4 | `vangle`, `vangle_mem_Icc`, `dlmf_1_6_4` (`cos θ = a · b/(‖a‖ ‖b‖)`) | `InnerProductGeometry.angle`, `InnerProductGeometry.cos_angle` |
| 1.6.5–1.6.6 | `unitI`, `unitJ`, `unitK`, `dlmf_1_6_6` | — |
| 1.6.7–1.6.8 | `dlmf_1_6_7`, `dlmf_1_6_8` | `cross_apply` |
| 1.6.9 | `dlmf_1_6_9_det` (formal determinant expanded along the first row), `dlmf_1_6_9` (components), `dot_cross_self_eq` (Lagrange's identity), `vnorm_cross` (`‖a × b‖ = ‖a‖ ‖b‖ sin θ`), `dlmf_1_6_9_normal` (`a × b = ‖a‖ ‖b‖ (sin θ) n`, `n` unit, normal, `det [a, b, n] > 0`) | `triple_product_eq_det`, `triple_product_permutation`, `InnerProductGeometry.sin_angle_mul_norm_mul_norm` |
| §1.6(i) prose | `dlmf_1_6_i_area` (base `‖a‖` × height `= ‖a × b‖`), `dlmf_1_6_i_volume` (Lebesgue volume of the parallelepiped `= |a · (b × c)|`) | `Measure.addHaar_parallelepiped`, `addHaarMeasure_eq_volume_pi` |
| 1.6.10 | `dlmf_1_6_10` | — |
| 1.6.11 | `dlmf_1_6_11` | — |
| 1.6.12 | `dlmf_1_6_12` (summation convention as an explicit sum) | `dotProduct` |
| 1.6.13 | `unitE`, `unitE_eq`, `dlmf_1_6_13` (`aⱼ eⱼ = a`) | `Pi.single` |
| 1.6.14 | `leviCivita`, `dlmf_1_6_14` (`ε_{σ(1)σ(2)σ(3)} = sign σ`; `0` if not a permutation; kernel `decide`) | `Equiv.Perm.sign` |
| 1.6.15 | `dlmf_1_6_15` | — |
| 1.6.16 | `dlmf_1_6_16` (`ε_{jkℓ}ε_{ℓmn} = δδ − δδ`, kernel `decide`) | — |
| 1.6.17 | `dlmf_1_6_17` (`eⱼ × eₖ = ε_{jkℓ} eℓ`) | `cross_apply` |
| 1.6.18 | `dlmf_1_6_18` | — |
| §1.6(ii) prose | `sum_leviCivita_eq_triple`, `dlmf_1_6_ii_volume` (volume `= |ε_{jkℓ} aⱼ bₖ cℓ|`) | — |
| 1.6.19 | `pd` (`∂f/∂xᵢ = Df(p) eᵢ`), `hasDerivAt_pd`, `dlmf_1_6_19` (= derivative of `t ↦ f(p + t eᵢ)`) | `HasFDerivAt.comp_hasDerivAt` |
| 1.6.20 | `grad3`, `dlmf_1_6_20` | — |
| 1.6.21 | `div3`, `dlmf_1_6_21` | — |
| 1.6.22 | `curl3` (components), `dlmf_1_6_22` (formal determinant as `(∇ × F)ℓ = ε_{ℓjk} ∂ⱼFₖ`) | — |
| 1.6.23–1.6.24 | `pd_add`, `pd_sub`, `pd_mul`, `pd_div`, `dlmf_1_6_23`, `dlmf_1_6_24` (differentiable at `p`, `g(p) ≠ 0`) | `fderiv_mul`, `fderiv_add`, `fderiv_sub`, `HasDerivAt.div` |
| 1.6.25–1.6.26 | `dlmf_1_6_25`, `dlmf_1_6_26` | `differentiableAt_pi` |
| 1.6.27 | `dlmf_1_6_27` (`div curl F = 0`, `C²`); `pd_pd_eq`, `pd_comm`, `contDiff_pd`, `differentiable_pd` | `ContDiffAt.isSymmSndFDerivAt`, `HasFDerivAt.clm_apply`, `contDiff_pi` |
| 1.6.28 | `dlmf_1_6_28` | — |
| 1.6.29 | `dlmf_1_6_29` (`curl grad f = 0`) | — |
| 1.6.30 | `lap3`, `dlmf_1_6_30` (`∇²f = ∇ · ∇f = ∑ ∂ᵢ²f`) | — |
| 1.6.31 | `pd_mul_fun`, `dlmf_1_6_31` | — |
| 1.6.32 | `dlmf_1_6_32` (via 1.6.26 and 1.6.29) | — |
| 1.6.33 | `dlmf_1_6_33` | — |
| 1.6.34 | `vlap3`, `pd_sum`, `dlmf_1_6_34` (`curl curl F = ∇(∇ · F) − ∇²F`) | `fderiv_fun_sum` |
| 1.6.35– | — | not yet (§1.6(iv) path and line integrals onward) |

### §1.11 Zeros of Polynomials (`Azurite/DLMF/Chapter1/Section11.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| §1.11(ii) prose (number of zeros) | `dlmf_1_11_ii_card_roots` (complex coefficients), `dlmf_1_11_ii_card_roots_real` (real coefficients, zeros in `ℂ`) | `IsAlgClosed.card_roots_eq_natDegree`, `IsAlgClosed.card_roots_map_eq_natDegree_of_injective` |
| §1.11(ii) prose (odd/even degree) | `dlmf_1_11_ii_odd`, `dlmf_1_11_ii_even`, `monic_tendsto_atTop`, `exists_root_Ioo_of_mul_neg`, `monic_exists_pos_root` | `tendsto_atTop_of_leadingCoeff_nonneg`, `intermediate_value_Icc`, `comp_neg_X_leadingCoeff_eq` |
| §1.11(ii) prose (Descartes' rule of signs) | `dlmf_1_11_ii_descartes` (bound and **parity**), `dlmf_1_11_ii_descartes_neg` (`f(−z)`, negative zeros); parity proof: `neg_one_pow_signVariations` (lists), `coeffList_head`, `coeffList_getLast`, `neg_one_pow_signVariations_poly`, `sign_eval_zero_eq_sign_leadingCoeff` (IVT), `neg_one_pow_countP_roots_pos`, `signVariations_X_pow_mul`, `nat_mod_two_eq_of_neg_one_pow_eq` | `roots_countP_pos_le_signVariations` (bound only), `List.signVariations_cons_cons_of_ne_zero`, `roots_comp_neg_X`, `Multiset.prod_X_sub_C_dvd_iff_le_roots` |
| 1.11.8 | `exampleF`, `dlmf_1_11_8` (`f(−z)`), `exampleF_coeffList`, `exampleF_neg_coeffList`, `dlmf_1_11_ii_example` (one sign change each; one positive, one negative, six non-real zeros) | `filter_roots_map_range_eq_map_roots` |
| §1.11(ii) prose (reciprocals) | `dlmf_1_11_ii_reverse_coeff` (`zⁿ f(1/z)` is `reverse`), `dlmf_1_11_ii_reverse` | `eval₂_reverse_eq_zero_iff`, `coeff_reverse` |
| 1.11.9 | `discriminantOfZeros`, `dlmf_1_11_9` (Mathlib's `discr` = `aₙ^{2n−2} ∏_{j<k}(zⱼ − zₖ)²`), `prod_prod_erase_sub`, `sum_card_Ioi`, `dlmf_1_11_9_complex` | `resultant_deriv`, `resultant_eq_prod_eval`, `eval_multiset_prod_X_sub_C_derivative`, `discr_C` |
| 1.11.10 | `dlmf_1_11_10` (general `k`), `dlmf_1_11_10_sum`, `dlmf_1_11_10_pairs`, `dlmf_1_11_10_prod` | `coeff_eq_esymm_roots_of_card` |
