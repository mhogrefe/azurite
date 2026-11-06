# DLMF formalization ledger

Discrepancies with the DLMF found along the way are collected in `docs/dlmf_errata.md`.

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
| Olver Ex. 11.2 | (ii) `olver_ex_11_2_ii` (step function, `𝒱_{−1,1} = 1`), (iii) `olver_ex_11_2_iii` (`𝒱_{−∞,∞}(sech) = 2`; `eVariationOn_Iic_of_monotoneOn`, `eVariationOn_Ici_of_antitoneOn`); (i) `olver_ex_11_2_i` (`𝒱_{0,1}{sin²(nπx)} = 2|n|`), (iv) `olver_ex_11_2_iv` (`= 2/e`) (`Section4Olver.lean`) | `eVariationOn.union`, `eVariationOn.eq_biSup_inter_Icc` |
| Olver §11.5 (paths), Ex. 11.3–11.4 | `pathVariation` (`𝒱_𝒫(f) = ∑ ∫ |f′(z(τ)) z′(τ)| dτ`), `olver_ex_11_4` (= sup over ordered points of the path, the variation of `f ∘ Γ`), `olver_ex_11_3_i` (`= 2`), `olver_ex_11_3_ii` (`= 2`), `olver_ex_11_3_iii` (`= 4e² − 2`), `sqPath`, `eVariationOn_sqPath` (`Section4Olver.lean`) | `eVariationOn.sum'`, `DifferentiableOn.deriv` |
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
| 1.5.3–1.5.4 | `partialX`, `iterPartialY`, `dlmf_1_5_3`, `dlmf_1_5_4` (difference-quotient limits ↔ `HasDerivAt`), `partialX_eq_of_tendsto`, `partialY_eq_of_tendsto` | `hasDerivAt_iff_tendsto_slope_zero` |
| 1.5.5 | `iterPartialXY`, `partialYX`, `partialXX`, `partialYY`, `dlmf_1_5_5` | — |
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
| 1.6.35 | `dlmf_1_6_35` (`c' = (x', y', z')`) | `deriv_pi` |
| 1.6.36 | `pathLength`, `dlmf_1_6_36` (length = total variation of the path, `C¹` paths) | `EuclideanSpace.equiv`; `olver_11_02` (§1.4) |
| 1.6.37 | `pathIntegral`, `dlmf_1_6_37`, `continuous_vnorm`, `vnorm_smul` | — |
| 1.6.38 | `lineIntegral`, `dlmf_1_6_38` (`∫ F₁ dx + F₂ dy + F₃ dz`) | — |
| 1.6.39–1.6.40 | `deriv_comp_reparam`, `lineIntegral_comp`, `dlmf_1_6_39`, `dlmf_1_6_40` (`C¹` reparametrizations; monotonicity not needed) | `intervalIntegral.integral_comp_mul_deriv`, `HasDerivAt.scomp` |
| 1.6.41 | `dlmf_1_6_41` (monotone `h`), `dlmf_1_6_41_antitone` | `HasDerivWithinAt.nonneg_of_monotoneOn`, `uniqueDiffWithinAt_iff_accPt`, `uniqueDiffOn_Icc` |
| 1.6.42 | `fderiv_apply_eq_grad`, `dlmf_1_6_42` | `intervalIntegral.integral_eq_sub_of_hasDerivAt` |
| §1.6(iv) prose | `IsSimpleClosedPath`, `IsPiecewiseDifferentiablePath` | — |
| 1.6.43–1.6.44 | `lineIntegral2`, `rectBoundaryIntegral`, `rectBoundaryIntegral_eq`, `dlmf_1_6_44_rect` (Green's theorem for rectangles), `dlmf_1_6_iv_area` (area via `−y i`, `x j`, `−½y i + ½x j`); general regions: see the next rows | `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`; `partialX_of_hasFDerivAt` (§1.5) |
| 1.6.44 (regions between graphs) | `lineIntegral2_graph`, `lineIntegral2_vertical`, `regionXBoundaryIntegral`, `dlmf_1_6_44_regionX` (`S = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}`, `φᵢ` `C¹`: `F₁ dx` part by Fubini + FTC, `F₂ dy` part by Leibniz 1.5.22 for `H(x) = ∫_{φ₁}^{φ₂} F₂ dy`), `dlmf_1_6_iv_area_regionX` | `dlmf_1_5_31`, `hasDerivAt_integral_variable` (§1.5), `continuous_parametric_intervalIntegral_of_continuous` |
| 1.6.44 (general closed curves) | `toComplexPath`, `IsSimpleClosedPlanePath`, `planeInterior` (`S` = union of the bounded components of the complement of the curve), `preimage_planeInterior`/`planeInterior_eq_image` (= `JordanCurve.jordanInterior` in `ℂ`), `fderiv_comp_equivRealProd`, **`dlmf_1_6_44`** (closed piecewise-`C¹` curve `JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b`, positively oriented = winding number `1` on `S`, `F₁ F₂` `C¹`), `lineIntegral2_eq_mul_setIntegral` (constant winding number `w` on `S`), `dlmf_1_6_44_nhds` + `lineIntegral2_eq_mul_setIntegral_of_contDiffOn` (fields `C¹` on an open `U ⊇ S ∪ C`, via `isCompact_closure_planeInterior_union` and the smooth cutoff `exists_contDiff_eqOn_nhds`), `dlmf_1_6_44_simple` (simple closed curve, no orientation hypothesis: positively oriented with Green's formula or negatively oriented with a minus sign), `lineIntegral2_reverse`, `planeInterior_reverse`, `dlmf_1_6_44_simple_or_reverse`, `planeInterior_nonempty_isConnected`, `dlmf_1_6_iv_area_general`. Engine in `Azurite/JordanCurve/`: `WindingNumber` (contour integral, integer-valued locally constant winding number, `= 0` on unbounded components), `CauchyPompeiu` (`∫ ∂̄g/(p − z) = −π g(z)` for compactly supported `C¹` `g`, via polar coordinates), `Green` (`∮ g dz = 2i ∫ ∂̄g · W` by Fubini + the null curve; bump cutoff; real form; `lineIntegralRe_eq_setIntegral_jordanInterior`), `Interior` (`jordanInterior`/`jordanExterior`; Jordan curve theorem transported from the vendored `jordan_curve` via `AddCircle.liftIco`: unique bounded and unbounded components, winding number constant on the interior, `IsPositivelyOriented`), `Orientation` (`W = ±1` on the interior of a Jordan curve: jump of the winding number across a regular arc, by rescaling + dominated convergence; `ClosedPiecewiseC1.reverse`) | `integral_univ_inv_one_add_sq`, `exists_contDiff_support_eq_eq_one_iff`, `exists_open_between_and_isCompact_closure`, `integrableOn_ball_of_norm_le_rpow`, `integral_integral_swap`, `Complex.integral_comp_polarCoord_symm`, `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`, `ContDiffBump`, `Complex.volume_preserving_equiv_real_prod`, `AddCircle.liftIco_continuous`, `AddCircle.homeomorphCircle`, `Homeomorph.image_connectedComponentIn`; vendored `step_A_exists_bounded`, `step_B_bounded_unique`, `exists_unbounded_component`, `unbounded_component_unique` |
| §1.6(v) | Surfaces and integrals over surfaces, in `Azurite/DLMF/Chapter1/Section6Surfaces.lean` | |
| 1.6.45 | `surfaceParam` (`Φ : ℝ × ℝ → ℝ³` on an open `D`) | |
| 1.6.46–1.6.47 | `tangentU`, `tangentV` (`DΦ` applied to the coordinate directions), `tangentU_surfaceParam`, `tangentV_surfaceParam`, `dlmf_1_6_46`, `dlmf_1_6_47`, tangency `hasDerivAt_tangentU`/`hasDerivAt_tangentV` | `hasFDerivAt_pi'`, `partialX_of_hasFDerivAt` (§1.5) |
| §1.6(v) prose | `IsSmoothAt`, `IsSmoothSurface`, normal `dlmf_1_6_v_normal`; area independent of the parametrization `cross_tangent_comp` (`T_u × T_v` scales by `det Dψ`), `surfaceIntegral_comp`, `dlmf_1_6_v_area_reparam`; orientation `IsOrientationPreserving`, `IsOrientationReversing`, `IsOrientable`, `det_pos_or_neg` | `integral_image_eq_integral_abs_det_fderiv_smul`, `ContinuousLinearMap.det_prod_two` (§1.5) |
| 1.6.48–1.6.49 | `surfaceArea`, `dlmf_1_6_48`, `dlmf_1_6_49` (`‖T_u × T_v‖` via the Jacobians `jacobian2`) | |
| 1.6.50 | `sphereParam`, `dlmf_1_6_50` (`ρ² |sin θ|`) | |
| 1.6.51 | `graphParam`, `vnorm_cross_graphParam`, `dlmf_1_6_51` | |
| 1.6.52–1.6.53 | `revolutionXParam`, `revolutionYParam`, `vnorm_cross_revolutionXParam`, `vnorm_cross_revolutionYParam`, `setIntegral_Ioo_prod_angle`, `dlmf_1_6_52`, `dlmf_1_6_53` (parameters `(a, b) × (0, 2π)`) | `integral_prod_mul`, `Measure.prod_restrict` |
| 1.6.54–1.6.55 | `surfaceIntegral`, `fluxIntegral`, `dlmf_1_6_54`, `dlmf_1_6_55`, `fluxIntegral_comp` | |
| 1.6.56 | `dlmf_1_6_56` (both preserving or both reversing: equal), `dlmf_1_6_56_neg` (otherwise: negatives); second parametrization `Φ ∘ ψ` for a one-to-one differentiable change of parameters `ψ` | |
| 1.6.57 | `dlmf_1_6_57` (Stokes for `S = Φ(D)`, `D` bounded by a positively oriented closed piecewise-`C¹` curve `γ`, `Φ` `C²` near `D ∪ γ`, boundary `Φ ∘ γ`; pull-back to Green 1.6.44: `partialX_sub_partialY_pullback`, `lineIntegral2_pullback`, `hasDerivAt_dotProduct`, `dot_fderiv_sub`). Single-chart surfaces only (no gluing of several parametrizations) | `dlmf_1_6_44_nhds` (§1.6(iv)), `ContDiffAt.isSymmSndFDerivAt` |
| 1.6.58 | `boxFace`, `boxFlux`, `dlmf_1_6_58` (divergence theorem for boxes `[a, b] ⊂ ℝ³`, outward normals `±eᵢ`) | `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` |
| 1.6.59–1.6.60 | `boxNormalDerivIntegral` (`∬ f ∂g/∂n dA`), `dlmf_1_6_59`, `dlmf_1_6_60` (boxes) | `dlmf_1_6_25` |
| 1.6.58–1.6.60 (general regions) | In `Azurite/DLMF/Chapter1/Section6Gauss.lean`: `SurfacePiece`, `ClosedSurface` (pieces with cancelling boundary curves), solid angle `ClosedSurface.windingNumber`, `ClosedSurface.flux_eq_integral` (`∬_S F · dS = ∭ (∇ · F) W` for `F ∈ C¹_c`: Newton kernel identity in polar coordinates `integral_newton`, Newton field `div3_newtonField`, Poincaré lemma `curl3_vectorPotential`, Stokes 1.6.57 on each piece, Fubini `SurfacePiece.flux_newtonField`, mollification), `ClosedSurface.BoundsOutward` (`W = 1_V` a.e.), **`dlmf_1_6_58_general`**, **`dlmf_1_6_59_general`**, **`dlmf_1_6_60_general`** (fields `C¹`/`C²` on an open set containing `V̄ ∪ S`). Geometric outward normal ⇒ `BoundsOutward`: see the orientation row | `homeomorphUnitSphereProd`, `Measure.toSphere_apply_univ`, `EuclideanSpace.volume_ball_fin_three`, `HasCompactSupport.hasFDerivAt_convolution_right`, `hasFDerivAt_integral_of_dominated_of_fderiv_le''`, `ContDiffBump.convolution_tendsto_right_of_continuous`, `exists_contDiff_support_eq_eq_one_iff` |
| 1.6.58–1.6.60 (outward orientation) | In `Azurite/DLMF/Chapter1/Section6GaussOrientation.lean`: `ClosedSurface.OutwardBoundary S V` (`V` bounded, `frontier V = S`, connected interior and exterior, one exterior-to-interior segment crossing `S` once at an interior parameter point against the normal) ⇒ `ClosedSurface.BoundsOutward` (`boundsOutward_of_crossing`). Crossing map `Ψ(τ, p) = Φ(p) − y₀ − τ v` with Jacobian `−v · (T_u × T_v)` (`det_crossDeriv`, `det_eq_triple`), Fubini `SurfacePiece.flux_segField_eq`, inverse function theorem + change of variables ⇒ segment-field flux `−1` (`exists_flux_segField_eq_neg_one`) ⇒ jump `W(y₀ + v) = W(y₀) + 1` (`windingNumber_add_eq_add_one`); surface null (`volume_image`); `W = 0` outside by constancy + decay. **`dlmf_1_6_58_outward`**, **`dlmf_1_6_59_outward`**, **`dlmf_1_6_60_outward`**. Connectedness of interior/exterior is a hypothesis there; `Section6GaussSeparation.lean` derives it via Jordan–Brouwer | `ContDiffAt.toOpenPartialHomeomorph`, `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`, `integral_image_eq_integral_abs_det_fderiv_smul`, `setIntegral_prod_swap`, `volume_preserving_piFinSuccAbove`, `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`, `Measure.addHaar_submodule` |
| 1.6.58–1.6.60 (Jordan–Brouwer) | `Section6JordanBrouwer.lean`: `LocallyTwoSided`, `subset_closure_connectedComponentIn` (Lima), `connectedComponentIn_two`, `frontier_connectedComponentIn`, `isPreconnected_of_compl_eq_union`, `IsLocallyGraphAt`/`IsLocallyGraph`, `jordanBrouwer_le_two` (ℝⁿ, n ≥ 2: at most two components, unique unbounded one), `isLocallyGraphAt_of_hasStrictFDerivAt` (regular level sets); `Section6GaussSeparation.lean`: **`ClosedSurface.jordanBrouwer`** (exactly two components, `W = 0` / `±1`), `outwardBoundary_of_isLocallyGraph`, `dlmf_1_6_58_jordanBrouwer`, example `Sphere3.jordanBrouwer` (ledger `docs/jordan_brouwer_plan.md`) | `IsOpen.connectedComponentIn`, `isPreconnected_iff_subset_of_disjoint`, `HasStrictFDerivAt.implicitToOpenPartialHomeomorph`, `isConnected_compl_singleton_of_one_lt_rank`, `Real.injOn_cos`, `Complex.cos_arg` |
| 1.6.58 (examples) | In `Azurite/DLMF/Chapter1/Section6GaussExamples.lean`: rectangles as Green regions (`Rect`, `Rect.planeInterior_eq`, `Rect.isPositivelyOriented`, `SurfacePiece.ofRect`); the box `Box3.surface` (six affine faces, edges cancel: `Box3.face_closed`; flux = Mathlib's box flux `Box3.surface_flux`; solid angle `1`/`0` via the cut-off point source `cutSource` and Mathlib's box divergence theorem; `Box3.boundsOutward`, `Box3.gauss`); general properties of the solid angle (continuity, local constancy `ClosedSurface.eventually_windingNumber_eq`, constancy on connected sets, decay `exists_abs_windingNumber_le`); the sphere `Sphere3.surface` (one chart, poles and a doubled meridian: `Sphere3.boundaryIntegral_piece`; `W = 1` at the centre, `1` on the ball, `0` outside; `Sphere3.boundsOutward`, `Sphere3.gauss`) | `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`, `Measure.univ_pi_Ioo_ae_eq_Icc`, `volume_preserving_finTwoArrow`, `setIntegral_prod_swap`, `Measure.addHaar_sphere`, `continuousAt_of_dominated` |

### §1.7 Inequalities (`Azurite/DLMF/Chapter1/Section7.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.7.1 | `dlmf_1_7_1` (Cauchy–Schwarz for finite sums), via `lagrange_identity` (`∑ᵢ∑ⱼ (aᵢbⱼ − aⱼbᵢ)² = 2((∑a²)(∑b²) − (∑ab)²)`) | `Finset.sum_mul_sum` |
| §1.7(i) prose (Cauchy–Schwarz equality) | `dlmf_1_7_1_eq_iff` (equality iff `aⱼ = c bⱼ` for all `j`, **or `b = 0`**: DLMF's wording omits the degenerate case), `dlmf_1_7_1_eq_iff_of_ne` (DLMF's wording, `b ≠ 0`) | |
| §1.7(i) prose (Cauchy–Schwarz converse) | `dlmf_1_7_1_converse` (test `b = √(B/∑a²) a`) | |
| 1.7.2 | `dlmf_1_7_2` (Hölder, `p > 1`, `1/p + 1/q = 1`, `aⱼ, bⱼ ≥ 0`), `holderConjugate_of_one_div` | `Real.inner_le_Lp_mul_Lq_of_nonneg` |
| §1.7(i) prose (Hölder equality) | `dlmf_1_7_2_eq_iff` (iff `aⱼᵖ = c bⱼ^q` for all `j`, or `b = 0`; normalized sequences + equality case of weighted AM–GM), `dlmf_1_7_2_eq_iff_of_ne` | `Real.geom_mean_le_arith_mean2_weighted`, `Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos` |
| §1.7(i) prose (Hölder converse) | `dlmf_1_7_2_converse` (test `bⱼ = (B/∑aᵖ)^{1/q} aⱼ^{p−1}`) | `Real.HolderConjugate.sub_one_mul_conj` |
| 1.7.3 | `dlmf_1_7_3` (Minkowski, `p > 1`) | `Real.Lp_add_le_of_nonneg` |
| §1.7(i) prose (Minkowski equality, reverse for `0 < p < 1`) | `dlmf_1_7_3_eq_iff`, `dlmf_1_7_3_eq_iff_of_ne`, `dlmf_1_7_3_reverse`, `dlmf_1_7_3_reverse_eq_iff`, `dlmf_1_7_3_reverse_eq_iff_of_ne`; one argument for both: `lpSum`, `sum_strictConvexOn` (termwise Jensen with equality case), `minkowski_aux` (`a + b = (α + β)(λ a/α + μ b/β)`, `σ tᵖ` strictly convex with `σ = ±1`), `lpSum_add_eq_iff` | `strictConvexOn_rpow`, `Real.strictConcaveOn_rpow`, `Finset.sum_eq_sum_iff_of_le` |
| 1.7.4 | `eIoo` (interval with endpoints in `[−∞, +∞]`), `dlmf_1_7_4`; general measure: `sq_integral_mul_le` (`∫ (f − t g)² ≥ 0`, `integral_sub_mul_sq`) | |
| §1.7(ii) prose (Cauchy–Schwarz equality) | `dlmf_1_7_4_eq_iff` (`A f = B g` a.e., `A`, `B` not both zero; general `sq_integral_mul_eq_iff`), `dlmf_1_7_4_eq_iff_of_continuousOn` (for every `x` in `(a, b)`: `ae_eIoo_iff_forall`) | `Measure.eqOn_open_of_ae_eq` |
| 1.7.5 | `dlmf_1_7_5`; general: `integral_mul_le_and_eq_iff` (normalized Young `young_rpow`, integrated) | `Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos`, `integral_eq_zero_iff_of_nonneg_ae` |
| §1.7(ii) prose (Hölder equality) | `dlmf_1_7_5_eq_iff` (`A fᵖ = B g^q` a.e.), `dlmf_1_7_5_eq_iff_of_continuousOn` | |
| 1.7.6 | `dlmf_1_7_6`; general: `lpInt`, `lpInt_add_le`, `minkowski_integral_aux` (pointwise strict convexity integrated), `integrable_rpow_add` (`(x + y)ᵖ ≤ 2ᵖ(xᵖ + yᵖ)`) | `strictConvexOn_rpow` |
| §1.7(ii) prose (Minkowski equality, reverse for `0 < p < 1`) | `dlmf_1_7_6_eq_iff`, `dlmf_1_7_6_eq_iff_of_continuousOn`, `dlmf_1_7_6_reverse` (general `lpInt_add_ge`), `dlmf_1_7_6_reverse_eq_iff`, `dlmf_1_7_6_reverse_eq_iff_of_continuousOn`; general `lpInt_add_eq_iff` | `Real.strictConcaveOn_rpow` |
| 1.7.7 | `dlmf_1_7_7` (`H ≤ G ≤ A`, positive `aⱼ`), `dlmf_1_7_7_harmMean_eq_iff`, `dlmf_1_7_7_geomMean_eq_iff` (equality iff all equal); from 1.7.9 at `r = −1, 0, 1` with equal weights, `powerMean_uniform_zero` | `Real.finsetProd_rpow` |
| 1.7.8 | `dlmf_1_7_8` (`min ≤ M(r) ≤ max`, `r ≠ 0`), `dlmf_1_7_8_eq_sup'_iff`, `dlmf_1_7_8_eq_inf'_iff`, `dlmf_1_7_8_eq_iff` (DLMF's combined equality case); via `powerMean_le_sup'`, `inf'_le_powerMean` (monotonicity + limits 1.2.23–1.2.24) | |
| 1.7.9 | `powerMean` (`M(r)` for all real `r`, `M(0) = ∏ aⱼ^{pⱼ}`), `dlmf_1_7_9`, `dlmf_1_7_9_eq_iff` (equality iff all equal, or `s ≤ 0` and some `aⱼ = 0`); `powerMean_mono` from `powerMean_le_of_pos` (strict Jensen for `x^{s/r}`), `powerMean_zero_le` (weighted AM–GM), `powerMean_neg` (reciprocals), `powerMean_eq_zero_of_nonpos` | `StrictConvexOn.map_sum_eq_iff`, `ConvexOn.map_sum_le`, `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos` |
| 1.7.10 | `dlmf_1_7_10` (`φ` convex on `(a, b)`, endpoints in `[−∞, +∞]`, `φ ∘ f` integrable); general `convexOn_intervalIntegral_le` (open convex set), `exists_affine_le_of_convexOn` (supporting line), `exists_mem_Icc_le_intervalIntegral` | `ConvexOn.slope_mono_adjacent`, `intervalIntegral.intervalIntegral_pos_of_pos_on` |
| 1.7.11 | `dlmf_1_7_11` (`≤`), `dlmf_1_7_11_lt` (strict unless `f` a.e. constant; **DLMF prints `<` unconditionally, false for constant `f`**), `dlmf_1_7_11_eq_iff` | `StrictConvexOn.ae_eq_const_or_map_average_lt`, `strictConvexOn_exp` |

### §1.8 Fourier Series (`Azurite/DLMF/Chapter1/Section8.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.8.1 | `dlmf_1_8_1` (continuous `2π`-periodic `f` with summable `cₙ`: pointwise `HasSum` of `aₙ cos nx + bₙ sin nx` to `f(x) − ½a₀`; DLMF's series is formal) | `HasSum.nat_add_neg`, `hasSum_nat_add_iff'` |
| 1.8.2 | `fourierA`, `fourierB`, `dlmf_1_8_2_a`, `dlmf_1_8_2_b` | |
| §1.8(i) prose (even/odd) | `dlmf_1_8_i_even` (`bₙ = 0`), `dlmf_1_8_i_odd` (`aₙ = 0`) | `intervalIntegral.integral_comp_neg` |
| 1.8.3 | `dlmf_1_8_3` (pointwise `HasSum` of `cₙ e^{inx}`), `fourierCoeff_lift_eq` | `has_pointwise_sum_fourier_series_of_summable`, `Continuous.quotient_liftOn'` |
| 1.8.4 | `fourierC`, `dlmf_1_8_4`, `fourierC_eq_fourierCoeffOn`; relations `fourierC_natCast`, `fourierC_neg_natCast`, `fourierC_zero` | `fourierCoeffOn_eq_integral`, `fourier_coe_apply` |
| 1.8.5 | `dlmf_1_8_5` (from 1.8.6_1 with `g = f`) | `Complex.hasSum_ofReal` |
| 1.8.6 | `dlmf_1_8_6` | `hasSum_sq_fourierCoeffOn` |
| 1.8.6_1 | `dlmf_1_8_6_1`, `fourier_pair_mul_conj` | |
| 1.8.6_2 | `dlmf_1_8_6_2` (polarization `four_mul_mul_conj`, linearity `fourierC_add_mul`) | |
| 1.8.7 | `dlmf_1_8_7` (`aₙ, bₙ, c±ₙ = o(n⁻ᵐ)` for a chain of right derivatives ending in an integrable `f⁽ᵐ⁾`), `fourierC_eq_div_of_hasDerivWithinAt`, `fourierC_iterate`, `isLittleO_of_tendsto_pow_mul` | `fourierCoeffOn_of_hasDeriv_right` |
| §1.8(i) prose (uniqueness) | `dlmf_1_8_i_uniqueness`, `dlmf_1_8_i_uniqueness_ab`, `eq_zero_of_fourierC_eq_zero`, `memLp_of_continuous` | `Measure.eqOn_open_of_ae_eq`, `toIocMod_mem_Ioc` |
| 1.8.8 | `lebesgueConst`, `dlmf_1_8_8` | |
| 1.8.9 | `dlmf_1_8_9` (`IsEquivalent`); `lebesgueConst_bounds`, `inv_sin_sub_inv_le_one`, `sincAbs_bounds`, `piece_lower`, `piece_upper`, `integral_abs_sin_period` | `Real.sin_ge_sub_cube`, `Real.mul_le_sin`, `log_add_one_le_harmonic`, `harmonic_le_one_add_log`, `Real.isLittleO_const_log_atTop` |
| 1.8.10 | `dlmf_1_8_10`, `dlmf_1_8_10_atBot`, `tendsto_intervalIntegral_mul_exp_cocompact` | `Real.tendsto_integral_exp_smul_cocompact` |
| 1.8.11 | `fourierPartialSum`, `dlmf_1_8_11` (Dirichlet: partial sums → `½f(x−) + ½f(x+)` for `f` periodic, integrable on a period, with one-sided derivatives at `x` based at `f(x±)`; no finiteness of discontinuities needed); `halfDirichlet`, `two_mul_halfDirichlet_mul_sin`, `integral_halfDirichlet`, `fourierPartialSum_eq_integral`, `fourierPartialSum_eq_fold`, `intervalIntegrable_dirichlet_quotient`, `tendsto_integral_mul_sin` | `intervalIntegral.integral_comp_add_right`, `Function.Periodic.intervalIntegral_add_eq`, `mem_nhdsGT_iff_exists_Ioo_subset` |
| §1.8(ii) prose (non-uniform at jumps) | `dlmf_1_8_ii_nonuniform` (uniform convergence near `x` to a limit equal to `f` off `x` forces `f(x−) = f(x+)`) | `TendstoUniformlyOn.continuousOn` |
| 1.8.12 | `dlmf_1_8_12` (all real `x`; `f` periodic and square-integrable on a period), `hasSum_integral_of_mem` (Parseval 1.8.6_1 against `orientedIndicator`), `fourierA_orientedIndicator`, `fourierB_orientedIndicator` | `setIntegral_indicator` |
| §1.8(iii) prose (termwise differentiation) | `dlmf_1_8_iii_deriv` (`f ∈ C²` periodic: `f′(x) = ∑ n (bₙ cos nx − aₙ sin nx)`); `fourierC_deriv`, `fourierA_deriv`, `fourierB_deriv`, `periodic_deriv` | `Summable.of_norm_bounded_eventually`, `Real.summable_one_div_int_pow`, `intervalIntegral.integral_deriv_eq_sub` |
| 1.8.13 | moved by DLMF to 1.8.6_1 (`dlmf_1_8_6_1`) | |
| 1.8.14 | In `Azurite/DLMF/Chapter1/Section8Poisson.lean`: `dlmf_1_8_14` (DLMF hypotheses `f ∈ C²`, `f`, `f″` integrable; both series converge); `norm_le_integral_add`, `norm_deriv_le_integral` (weight `6(t−a)(a+1−t)`), `poisson_aux` (`f′` integrable, translates summable on compacts), `summable_integral_norm_Ioc`, `norm_fourier_le` | `Real.tsum_eq_tsum_fourier`, `Real.fourier_deriv`, `Real.integrable_of_summable_norm_Icc`, `hasSum_integral_iUnion` |
| §1.8(iv) prose (1.14.1 form) | `dlmf_1_8_iv_fourier` (integral `= √(2π) 𝓕(f)(−2πn)`) | |
| 1.8.15 | `dlmf_1_8_15` (continuous, bounded variation, integrable on `[0, ∞)`; right series via partial sums); Jordan's test: `dirichlet1`, `abs_integral_dirichlet1_le`, `tendsto_integral_mul_sin_real`, `tendsto_integral_monotone_mul_dirichlet1`, `tendsto_integral_bv_mul_dirichlet1`, `abs_integral_bv_mul_dirichlet1_le`; pieces `integral_piece_eq`, `tendsto_piece`, `abs_piece_le`, `hasSum_pieces`, `integral_mul_dirichlet1_eq` | `exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn` (second mean value theorem), `variationOnFromTo.monotoneOn`, `variationOnFromTo.sub_self_monotoneOn`, `eVariationOn.comp_le_of_monotoneOn`, `tendsto_tsum_of_dominated_convergence`, `intervalIntegral_tendsto_integral_Ioi` |
| 1.8.16 | `dlmf_1_8_16` (`ℜω > 0`, complex `x`) | `Complex.tsum_exp_neg_quadratic`, `summable_jacobiTheta₂_term_iff`, `Complex.inv_cpow` |

### §1.9 Calculus of a Complex Variable (`Azurite/DLMF/Chapter1/Section9.lean`, `Section9Integration.lean`, `Section9CauchyJordan.lean`, `Section9Conformal.lean`, `Section9Series.lean`, `Section9Limits.lean`, `Section9PowerSeries.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.9.1–1.9.2 | `dlmf_1_9_1` (`z = ℜz + iℑz`, `i² = −1`), `dlmf_1_9_2` | `Complex.re_add_im`, `Complex.I_sq` |
| 1.9.3–1.9.4 | `dlmf_1_9_3`, `dlmf_1_9_4` | `Complex.norm_mul_cos_arg`, `Complex.norm_add_mul_I` |
| 1.9.5–1.9.6 | `dlmf_1_9_5_first`/`_second`/`_third`/`_fourth` (quadrants; real axis included in the 1st/2nd, imaginary axis excluded), `dlmf_1_9_6`; `arg_eq_arctan_of_re_pos`, `arcsin_div_sqrt_eq_arctan` | `Complex.tan_arg`, `Real.arctan_tan`, `Complex.arg_of_re_neg_of_im_nonneg` |
| 1.9.7 | `IsPhase`, `dlmf_1_9_7` (phases `= ph z + 2nπ`), `dlmf_1_9_7_principal_isPhase`, `dlmf_1_9_7_principal_range`, `dlmf_1_9_7_principal_unique`, `dlmf_1_9_7_continuousAt`, `dlmf_1_9_7_negative_axis` (value `π`, limit `−π` from below) | `Complex.exp_eq_exp_iff_exists_int`, `Complex.continuousAt_arg`, `Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero` |
| 1.9.8–1.9.12 | `dlmf_1_9_8` … `dlmf_1_9_12` | `Complex.abs_re_le_norm`, `Complex.exp_mul_I`, `Complex.norm_conj` |
| 1.9.13 | `dlmf_1_9_13` (general phases), `dlmf_1_9_13_principal` (`ph z ≠ π`) | `Complex.arg_conj`, `Complex.exp_conj` |
| 1.9.14–1.9.17, 1.9.19 | `dlmf_1_9_14` … `dlmf_1_9_17`, `dlmf_1_9_19` | `norm_mul`, `norm_div` |
| 1.9.18, 1.9.20 | `dlmf_1_9_18`, `dlmf_1_9_20` (general phases); `_principal` (up to `2nπ`), `_principal_counterexample` | |
| 1.9.21 | `dlmf_1_9_21` (even/odd binomial sums with sign `(−1)^⌊k/2⌋`), `re_I_pow`, `im_I_pow` | `add_pow` |
| 1.9.22 | `dlmf_1_9_22` (De Moivre, `n ∈ ℤ`) | `Complex.exp_int_mul` |
| 1.9.23 | `dlmf_1_9_23` | `abs_norm_sub_norm_le`, `norm_add_le` |
| §1.9(ii) prose (continuity) | `dlmf_1_9_ii_continuousAt`, `dlmf_1_9_ii_continuousAt₂` (two variables), `dlmf_1_9_ii_continuousOn` (on a region) | `Metric.continuousAt_iff`, `Metric.continuousOn_iff` |
| §1.9(ii) prose (point sets) | `dlmf_1_9_ii_isOpen`, `IsLimitPoint`, `isLimitPoint_iff_accPt`, `dlmf_1_9_ii_limitPoint_infinite`, `dlmf_1_9_ii_closure`; `PolygonallyJoined` (chain of segments), `dlmf_1_9_ii_domain` (open: connected ⇔ polygonally connected); `dlmf_1_9_ii_boundary`, `dlmf_1_9_ii_closed_domain`, `IsRegion`, `dlmf_1_9_ii_interior_points` | `closure_eq_self_union_derivedSet`, `IsPreconnected.induction₂'`, `Convex.isPathConnected`, `frontier_eq_closure_inter_closure` |
| 1.9.24 | `dlmf_1_9_24`, `dlmf_1_9_ii_continuousAt_of_differentiableAt` | `hasDerivAt_iff_tendsto_slope_zero` |
| 1.9.25 | `dlmf_1_9_25`, `hasDerivAt_partials`, `hasDerivAt_horizontal`, `hasDerivAt_vertical`; converse `dlmf_1_9_25_converse` (needs only `∂u/∂x`, `∂v/∂x` continuous) | `HasDerivAt.comp_ofReal`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, `hasDerivAt_iff_isLittleO_nhds_zero` |
| §1.9(ii) prose (analyticity) | `dlmf_1_9_ii_analyticAt`, `dlmf_1_9_ii_entire`, `dlmf_1_9_ii_iterate_deriv` | `analyticAt_iff_eventually_differentiableAt`, `DifferentiableOn.deriv` |
| 1.9.26 | `dlmf_1_9_26` (`u` and `v`), `laplace_re` | `Filter.EventuallyEq.deriv_eq` |
| 1.9.27 | `dlmf_1_9_27` (`u` and `v`, `r > 0`), `laplace_polar_re` | |
| §1.9(iii) arcs and contours | `IsArc`, `IsContour`, `IsSimpleContour`, `IsSimpleClosedContour` (`Section9Integration.lean`); `IsArc.isContour`, `IsContour.nonempty_closedPiecewiseC1`, `IsSimpleClosedContour.isJordanCurve` | `JordanCurve.ClosedPiecewiseC1`, `JordanCurve.IsJordanCurve` |
| 1.9.28 | `contourIntegral`, `dlmf_1_9_28` (`z` differentiable off a countable set), `ClosedPiecewiseC1.contourIntegral_eq` (piecewise = single integral); infinite-integral remark: `ContourConvergesAtTop`/`AtBot`/`Left`/`Right`, `contourConvergesAtTop_of_integrableOn`, `contourConvergesAtBot_of_integrableOn`, `contourConvergesLeft_of_intervalIntegrable`, `contourConvergesRight_of_intervalIntegrable`, `contourConvergesAtTop_exp_neg` | `intervalIntegral.sum_integral_adjacent_intervals` |
| §1.9(iii) Jordan curve theorem | `dlmf_1_9_iii_jordan` (interior/exterior open, connected, disjoint, cover the complement, bounded/unbounded, frontier = `C`; continuity suffices), `frontier_connectedComponentIn_jordan` | vendored `JordanCurve.component_boundary_eq` |
| 1.9.29 | `dlmf_1_9_29_jordan` (DLMF's hypotheses: simple closed contour, `f` continuous on interior ∪ `C`, analytic inside; `Section9CauchyJordan.lean` — smooth approximation + Lipschitz cutoff + Green + Minkowski bound `exists_volume_thickening_le`); `dlmf_1_9_29` (any closed piecewise-`C¹` curve, `f` analytic on an open set ⊇ interior ∪ `C`); homology form `ClosedPiecewiseC1.contourIntegral_eq_zero` (`windingSupport`) | `JordanCurve.contourIntegral_eq_integral_dbar'`, `exists_contDiff_support_eq_eq_one_iff` |
| 1.9.30 | `dlmf_1_9_30_jordan` (DLMF's hypotheses), `dlmf_1_9_30` (positively oriented, analytic neighbourhood); homology form `contourIntegral_div_sub` | `differentiableOn_dslope`, `JordanCurve.contourIntegral_inv_eq` |
| 1.9.31 | `dlmf_1_9_31_jordan` (DLMF's hypotheses), `dlmf_1_9_31` (all `n ≥ 0`, analytic neighbourhood); homology form `contourIntegral_div_sub_pow`, `iteratedDeriv_succ_eq_dslope`, `contourIntegral_inv_pow_eq_zero` | `iteratedDeriv_fun_mul`, `sub_smul_dslope` |
| §1.9(iii) Liouville | `dlmf_1_9_iii_liouville` | `Differentiable.exists_const_forall_eq_of_bounded` |
| 1.9.32 | `dlmf_1_9_32` (`𝒩(C, z₀) = windingNumber ∈ ℤ`), `dlmf_1_9_32_simple` (1 inside, 0 outside), `dlmf_1_9_iii_orientation` | `JordanCurve.isPositivelyOriented_or_isNegativelyOriented` |
| 1.9.33 | `dlmf_1_9_33` | `InnerProductSpace.HarmonicOnNhd.circleAverage_eq` |
| 1.9.34 | `poissonIntegral`, `dlmf_1_9_34` (polar form), `dlmf_1_9_34_harmonic`, `dlmf_1_9_34_tendsto` (boundary values) | `poissonKernel`, `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`, `HarmonicOnNhd.circleAverage_poissonKernel_smul`, `AnalyticAt.harmonicAt_re` |
| 1.9.35 | `diskAtInfty`, `dlmf_1_9_35` (neighbourhood basis of `∞` in `OnePoint ℂ`), `diskAtInfty_mem_nhds` (`Section9Conformal.lean`) | `OnePoint.hasBasis_nhds_infty` |
| 1.9.36 | `dlmf_1_9_36` (as limits `w → ∞`, `cobounded ℂ`), `tendsto_coe_nhds_infty_iff` | `tendsto_add_const_cobounded` |
| 1.9.37 | `dlmf_1_9_37` (`z ≠ 0`), `dlmf_1_9_37_infty` (`∞·∞`) | `tendsto_mul_left_cobounded`, `Tendsto.atTop_mul_atTop₀` |
| 1.9.38 | `dlmf_1_9_38` | `tendsto_inv₀_cobounded` |
| 1.9.39 | `dlmf_1_9_39` | `tendsto_inv₀_nhdsNE_zero` |
| §1.9(iv) analytic at `∞` | `invChart`, `AnalyticAtInfty`, `derivInfty`, `AnalyticAtInfty.tendsto` | |
| §1.9(iv) conformal transformation | `tangentAngle`, `dlmf_1_9_iv_conformal` (signed tangent angle preserved), `dlmf_1_9_iv_conformalAt`, `dlmf_1_9_iv_linear` | `Complex.arg_mul_coe_angle`, `DifferentiableAt.conformalAt` |
| 1.9.40 | `mobius`, `mobiusExt` (on `OnePoint ℂ`) | `OnePoint.elim` |
| 1.9.41 | `dlmf_1_9_41` (values and limits), `tendsto_mobius_pole`, `tendsto_mobius_infty` | `Tendsto.pos_mul_atTop` |
| 1.9.42 | `dlmf_1_9_42` | `HasDerivAt.div` |
| 1.9.43 | `dlmf_1_9_43` (+ analytic at `∞`), `invChart_mobius` | |
| 1.9.44 | `dlmf_1_9_44`, `dlmf_1_9_44_left`, `mobiusExt_leftInverse` | |
| §1.9(iv) bilinear prose | `dlmf_1_9_iv_bilinear` (bijective, continuous both ways on `ℂ ∪ {∞}`, conformal at finite points, `∞`, and the pole), `continuous_mobiusExt` | `OnePoint.continuous_iff`, `continuousAt_iff_punctured_nhds` |
| 1.9.45 | `crossRatio`, `dlmf_1_9_45` (invariance, finite points), `dlmf_1_9_45_infty` (limiting form `z₄ → ∞`), `mobius_sub_mobius`; on `ℂ ∪ {∞}`: `crossRatioExt` (homogeneous coordinates), `crossRatioExt_coe`, `crossRatioExt_infty₁`–`₄`, `dlmf_1_9_45_limits`, `dlmf_1_9_45_ext` (invariance for all points incl. the pole and `∞`) | |
| §1.9(v) sequences | `dlmf_1_9_v_tendsto_iff`, `dlmf_1_9_v_converges_iff` (`Section9Series.lean`) | `Complex.re_add_im` |
| §1.9(v) series | `partialSum`, `SeriesConverges` (DLMF: partial sums, not Mathlib's unconditional `Summable`), `SeriesDiverges`, `SeriesConvergesAbsolutely` (`seriesConvergesAbsolutely_iff`: = `Summable ‖zₙ‖`), `dlmf_1_9_v_absolutely`, `SeriesConverges.tendsto_zero` | `hasSum_iff_tendsto_nat_of_nonneg`, `Summable.of_norm` |
| §1.9(v) root and ratio tests | `dlmf_1_9_v_root_lt`, `dlmf_1_9_v_root_gt`, `dlmf_1_9_v_ratio_lt` (`zₙ ≠ 0` eventually), `dlmf_1_9_v_ratio_gt` (divergence absolute and outright) | `summable_of_ratio_test_tendsto_lt_one`, `summable_geometric_of_lt_one` |
| 1.9.46 | `ConvergesPointwiseOn`, `dlmf_1_9_46_of_uniform` | `TendstoUniformlyOn.tendsto_at` |
| 1.9.47 | `dlmf_1_9_47`, `SeriesConvergesUniformlyOn` | `Metric.tendstoUniformlyOn_iff` |
| §1.9(v) Weierstrass `M`-test | `dlmf_1_9_v_Mtest` | `tendstoUniformlyOn_tsum_nat` |
| §1.9(v) doubly-infinite series | `doublePartialSum`, `DoubleSeriesConverges`, `DoubleSeriesConvergesUniformlyOn`, `dlmf_1_9_v_doubly`, `dlmf_1_9_v_doubly_uniform`, `doublePartialSum_eq`, `uniformCauchySeqOn_of_split` | `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` |
| §1.9(vi) circle of convergence | `psum`, `pradius` (`Section9PowerSeries.lean`), `dlmf_1_9_vi_converges`, `dlmf_1_9_vi_diverges`, `dlmf_1_9_vi_uniform`, `dlmf_1_9_vi_analytic` | `FormalMultilinearSeries.ofScalars`, `summable_norm_mul_pow`, `le_radius_of_tendsto` |
| 1.9.48 | `dlmf_1_9_48` | |
| 1.9.49 | `dlmf_1_9_49` (Cauchy–Hadamard) | `FormalMultilinearSeries.radius_eq_liminf` |
| 1.9.50 | `dlmf_1_9_50` | |
| 1.9.51 | `dlmf_1_9_51` (absolutely convergent), `dlmf_1_9_51_psum` (inside both circles) | `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` |
| 1.9.52 | `cauchyCoeff` | |
| 1.9.53–1.9.54 | `dlmf_1_9_54` (`a₀ ≠ 0`, small `|z|`), `pradius_recipCoeff_pos`, `cauchyCoeff_recipCoeff` | |
| 1.9.55 | `dlmf_1_9_55` | |
| 1.9.56 | `recipCoeff`, `dlmf_1_9_56` | |
| 1.9.57 | `dlmf_1_9_57` (`a₀ = 1`, principal log), `exists_ball_slitPlane`, `cauchyCoeff_logCoeff` | `Complex.hasDerivAt_log`, `IsOpen.eqOn_of_deriv_eq` |
| 1.9.58 | `dlmf_1_9_58` | |
| 1.9.59 | `logCoeff`, `dlmf_1_9_59` (all `n ≥ 1`) | |
| 1.9.60 | `dlmf_1_9_60` (principal power), `cauchyCoeff_powCoeff` | `IsOpen.is_const_of_deriv_eq_zero`, `cpow_def_of_ne_zero` |
| 1.9.61 | `dlmf_1_9_61` | |
| 1.9.62 | `powCoeff`, `dlmf_1_9_62` | |
| 1.9.63 | `dlmf_1_9_63` (`Nat.ascFactorial` for `(n+1)_m`), `hasDerivAt_psum`, `dcoeff`, `le_pradius_dcoeff`, `iterate_dcoeff_apply` | `hasDerivAt_tsum_of_isPreconnected` |
| §1.9(vi) coefficient growth | `norm_le_of_recursion`, `pradius_pos_of_bound`, `exists_coeff_bound` | |
| 1.9.64 | `DoubleSeqConverges`, `doubleSeqConverges_iff` (`Section9Limits.lean`) | `Metric.tendsto_atTop` |
| 1.9.65 | `dlmf_1_9_65`, `dlmf_1_9_65_swap` (inner limits exist ⇒ repeated limits exist and equal) | `le_of_tendsto` |
| 1.9.66 | `doubleSeriesPartial`, `DoubleSeriesConvergesTo`, `DoubleSeriesConvergesAbsolutely` | |
| 1.9.67 | `dlmf_1_9_67`, `summable_norm_of_doubleSeriesConvergesAbsolutely`, `tendsto_range_product` | `summable_of_sum_le`, `HasSum.prod_fiberwise`, `Summable.prod_factor` |
| 1.9.68 | `dlmf_1_9_68` (finite contour `z : [a, b] → D`, continuous, integrable `z′`) | `TendstoUniformlyOn.continuousOn`, `intervalIntegral.integral_finsetSum` |
| 1.9.69–1.9.70 | `dlmf_1_9_69_iff_70` (the conditions coincide) | `lintegral_tsum` |
| 1.9.71 | `dlmf_1_9_71` (`eIoo a b`, `EReal` endpoints) | `integral_tsum`, `ae_lt_top'` |

### §1.10 Functions of a Complex Variable (`Azurite/DLMF/Chapter1/Section10.lean`, `Section10Continuation.lean`, `Section10Laurent.lean`, `Section10Bloch.lean`, `Section10Schottky.lean`, `Section10Picard.lean`, `Section10Residue.lean`, `Section10MaxModulus.lean`, `Section10Multivalued.lean`, `Section10Inverse.lean`, `Section10ContourIntegrals.lean`, `Section10Products.lean`, `Section10PartialFractions.lean`, `Section10Generating.lean`)

| DLMF | Azurite | Mathlib |
|---|---|---|
| 1.10.1 | `dlmf_1_10_1`, `dlmf_1_10_1_radius` (radius `≥ R`) | `Complex.hasSum_taylorSeries_on_eball` |
| 1.10.2 | `dlmf_1_10_2` | `NormedSpace.expSeries_div_hasSum_exp` |
| 1.10.3 | `dlmf_1_10_3` | `Complex.hasSum_taylorSeries_log` |
| 1.10.4 | `dlmf_1_10_4`, `ringChoose_eq_ascPochhammer` | `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero` |
| §1.10(i) zeros | `IsZeroOfOrder`, `IsSimpleZero`, `isZeroOfOrder_iff_analyticOrderAt`, `isZeroOfOrder_iff_exists`, `isSimpleZero_iff` | `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`, `AnalyticAt.analyticOrderAt_eq_natCast` |
| §1.10(ii) identity theorem | `dlmf_1_10_ii_identity` (limit point), `dlmf_1_10_ii_identity_arc` (arc), `accPt_arc` (`Section10Continuation.lean`) | `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` |
| §1.10(ii) continuation | `IsAnalyticContinuation`, `IsAnalyticContinuation.unique`, `IsContinuationAlong` | |
| §1.10(ii) functional equations | `dlmf_1_10_ii_functional` (real-segment identity ⇒ identity on a connected domain), `dlmf_1_10_ii_functional₂` (two variables), `exp_add_of_real` | `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` |
| 1.10.5 | `dlmf_1_10_5` (Schwarz reflection; `Ω ∪ L ∪ conj Ω` open), `schwarzReflection`, `rectBoundary_split` | `isConservativeOn_and_continuousOn_iff_isDifferentiableOn` (Morera), `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`, `HasDerivAt.conj_conj` |
| 1.10.6 | `annulus`, `dlmf_1_10_6` (doubly-infinite series), `hasSum_laurent`, `two_pi_I_mul_eq_annulus`, `hasSum_inner_laurent`; `dlmf_1_10_6_uniform`, `dlmf_1_10_6_compact` (uniform/absolute on compacts) (`Section10Laurent.lean`) | `circleIntegral_eq_of_differentiable_on_annulus_off_countable`, `hasSum_two_pi_I_cauchyPowerSeries_integral` |
| 1.10.7 | `laurentCoeff`, `laurentCoeff_eq` (independent of `r`), `norm_laurentCoeff_le` | `circleIntegral.norm_integral_le_of_norm_le_const` |
| §1.10(iii) singularities | `IsIsolatedSingularity`, `IsRemovableSingularity`, `IsPoleOfOrder`, `IsPole`, `IsEssentialSingularity`, `isPole_iff`, `singularity_trichotomy`, `IsRemovableSingularity.hasSum`, `isRemovableSingularity_of_tendsto`, `sin_div_removable`, `residue`, `residue_eq`, `IsMeromorphicDLMF`, `…AtInfty` | `hasDerivAt_iff_tendsto_slope` |
| §1.10(iii) Picard's theorem | `dlmf_1_10_iii_picard` (at most one omitted value near an isolated essential singularity), `dlmf_1_10_iii_picard_infinite` (every other value taken infinitely often), `little_picard`; via `bloch` (`Section10Bloch.lean`), `schottky` (`Section10Schottky.lean`), `norm_le_chainBound`, `bdd_or_inv_bdd`, `not_essential_of_omits` (`Section10Picard.lean`) | `Complex.norm_le_of_forall_mem_frontier_norm_le`, `Complex.differentiableOn_update_limUnder_of_bddAbove`, `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`, `Differentiable.apply_eq_apply_of_bounded` |
| §1.10(iii) infinitely many poles | `IsEssentialSingularityAtInftyOfPoles`, `IsMeromorphicDLMF.finite_poles`, `exists_pole_norm_gt`, `not_differentiableOn_inv_of_poles` (`Section10Picard.lean`) | `IsCompact.elim_nhds_subcover` |
| 1.10.8 | `dlmf_1_10_8`, `ClosedPiecewiseC1.contourIntegral_eq_sum_residues` (DLMF's hypotheses: boundary continuity, finitely many singularities); `principalPart`, `differentiableOn_principalPart`, `norm_sub_principalPart_le`, `ClosedPiecewiseC1.contourIntegral_principalPart` (`Section10Residue.lean`) | `differentiableOn_update_limUnder_of_bddAbove`, `Complex.differentiableOn_tsum_of_summable_norm` |
| 1.10.9 | `dlmf_1_10_9` (integral form), `dlmf_1_10_9_phase` (`(2π)⁻¹ Δ_C ph f`, any continuous branch), `residue_mul_logDeriv`, `ClosedPiecewiseC1.contourIntegral_mul_logDeriv`, `eq_exp_primitive_mul`, `contourIntegral_logDeriv_eq_phase` | `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`, `intervalIntegral.integral_hasDerivAt_right`, `intermediate_value_Icc` |
| 1.10.10 | `dlmf_1_10_10` | |
| §1.10(iv) Rouché | `dlmf_1_10_iv_rouche`, `exists_zeros_finset`, `exists_factor_of_analyticOrderAt`, `contourIntegral_logDeriv_eq_card` | `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `Set.Infinite.exists_accPt_of_subset_isCompact`, `HasDerivAt.clog` |
| §1.10(v) analytic functions | `dlmf_1_10_v_maxModulus`, `dlmf_1_10_v_boundary` (`Section10MaxModulus.lean`) | `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, `Complex.exists_mem_frontier_isMaxOn_norm` |
| §1.10(v) harmonic functions | `dlmf_1_10_v_harmonic`, `dlmf_1_10_v_harmonic_boundary`, `harmonic_eventually_eq_of_isMax` | `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` |
| 1.10.11 | `dlmf_1_10_11`, `dlmf_1_10_11_eq_iff` (equality case) | `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, `Complex.norm_deriv_le_div_of_mapsTo_ball`, `Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'` |
| §1.10(vi) branches, `√z` | `IsBranch`, `sqrtMV`, `sqrtMV_eq`, `dlmf_1_10_vi_sqrt_slit`, `dlmf_1_10_vi_sqrt_upper` (`Section10Multivalued.lean`) | `Complex.cpow`, `Complex.slitPlane` |
| §1.10(vi) branch points | `IsBranchPoint`, `cutNbhd`, `dlmf_1_10_vi_branchPoint_sqrt`, `dlmf_1_10_vi_branchPoints_powPair` | `Complex.exp_eq_one_iff` |
| §1.10(vi) `(1 − z)^α (1 + z)^β` | `powPairMV`, `powPairPrin`, `cutPlanePM1`, `dlmf_1_10_vi_powPair_branch`, `dlmf_1_10_vi_powPair_real` | `starConvex_one_slitPlane` |
| §1.10(vi) continuation | `ClosedPiecewiseC1.dlmf_1_10_vi_continuation`, `…_continuation_mn`, `exists_log_lift`, `log_lift_sub_eq`, `eq_of_mapsTo_countable` | `Cardinal.Real.Icc_countable_iff` |
| 1.10.12 | `dlmf_1_10_12`, `dlmf_1_10_12_unique` (`Section10Inverse.lean`) | `HasStrictFDerivAt.toOpenPartialHomeomorph`, `OpenPartialHomeomorph.hasDerivAt_symm` |
| 1.10.13 | `dlmf_1_10_13`, `inversionCoeff` | `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` |
| 1.10.14 | `dlmf_1_10_14`, `lagrangeCoeff`, `hasSum_lagrange` | `circleIntegral.integral_eq_zero_of_hasDerivWithinAt` |
| 1.10.15 | `extPowMV`, `extBranch`, `extBranch_mem_rootMV`, `dlmf_1_10_15_integer` | `AnalyticAt.analyticOrderAt_eq_natCast` |
| 1.10.16–1.10.17 | `dlmf_1_10_16` (all branches of `(w − w₀)^{1/μ}` via `rootMV`) | — |
| 1.10.18 | `dlmf_1_10_18`, `continuousOn_deriv_param`, `hasDerivAt_integral_param_complex` (`Section10ContourIntegrals.lean`) | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` |
| §1.10(viii) infinite/singular endpoint | `dlmf_1_10_viii_improper`, `IntegralConvergesUniformlyOn`, `upperLimit_atTop`, `upperLimit_nhdsLT` | `TendstoLocallyUniformlyOn.differentiableOn`, `TendstoLocallyUniformlyOn.deriv` |
| 1.10.19 | `dlmf_1_10_19_atTop`, `dlmf_1_10_19_nhdsLT` | `Metric.tendstoUniformlyOn_iff` |
| §1.10(viii) M-test | `dlmf_1_10_viii_Mtest` | `tendsto_integral_filter_of_dominated_convergence` |
| §1.10(ix) convergence | `partialProd`, `InfProdConverges`, `InfProdConvergesAbsolutely`, `InfProdConvergesUniformlyOn`, `InfProdConverges.exists_tendsto`, `dlmf_1_10_ix_log`, `dlmf_1_10_ix_abs`, `InfProdConvergesAbsolutely.infProdConverges` (`Section10Products.lean`) | `Complex.exp_eq_one_iff`, `tendsto_atTop_ciSup` |
| 1.10.20–1.10.21 | `dlmf_1_10_20` (explicit `1 + aₙ ≠ 0`), `dlmf_1_10_ix_Mtest` | `tendstoUniformlyOn_tsum_nat`, `TendstoLocallyUniformlyOn.differentiableOn`, `Complex.norm_log_one_add_half_le_self` |
| 1.10.22 | `dlmf_1_10_22`, `weierstrassProduct`, `weierstrassE`, `norm_weierstrassE_sub_one_le` | `Complex.norm_exp_sub_one_sub_id_le`, `Complex.norm_exp_sub_one_le` |
| 1.10.23 | `dlmf_1_10_23` (`Section10PartialFractions.lean`) | `TendstoLocallyUniformlyOn.differentiableOn` |
| 1.10.24 | `dlmf_1_10_24` | `logDeriv_fun_prod`, `TendstoLocallyUniformlyOn.deriv` |
| 1.10.25 | `dlmf_1_10_25` (extra `‖zₙ‖ → ∞`), `mittagLeffler`, `mittagLeffler_split`, `norm_mlTerm_le` | `differentiableOn_tsum_of_summable_norm`, `circleIntegral.integral_sub_center_inv` |
| 1.10.26–1.10.27 | `dlmf_1_10_27`, `circleIntegral_pow_div_pow` (`Section10Generating.lean`) | `intervalIntegral.hasSum_integral_of_dominated_convergence`, `circleIntegral.integral_sub_zpow_of_ne` |

### §1.11 Zeros of Polynomials (`Azurite/DLMF/Chapter1/Section11.lean`, `Section11Division.lean`, `Section11LowDegree.lean`, `Section11Roots.lean`, `Section11Stable.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.11.1–1.11.3 | `horner`, `hornerStep`, `horner_top`, `horner_succ`, `dlmf_1_11_2`, `dlmf_1_11_2_poly` (`Section11Division.lean`) | `Finset.sum_range_sub`, `Polynomial.as_sum_range_C_mul_X_pow` |
| 1.11.4 | `dlmf_1_11_4`, `dlmf_1_11_4_poly` | `Polynomial.eval_eq_sum_range` |
| 1.11.5–1.11.6 | `dlmf_1_11_5`, `dlmf_1_11_6`, `horner_shift`, `horner_map` | `Polynomial.derivative_mul` |
| 1.11.7 | `dlmf_1_11_7` (existence and uniqueness) | `EuclideanDomain.div_add_mod`, `Polynomial.degree_mod_lt`, `Polynomial.degree_le_mul_left` |
| §1.11(ii) prose (number of zeros) | `dlmf_1_11_ii_card_roots` (complex coefficients), `dlmf_1_11_ii_card_roots_real` (real coefficients, zeros in `ℂ`) | `IsAlgClosed.card_roots_eq_natDegree`, `IsAlgClosed.card_roots_map_eq_natDegree_of_injective` |
| §1.11(ii) prose (odd/even degree) | `dlmf_1_11_ii_odd`, `dlmf_1_11_ii_even`, `monic_tendsto_atTop`, `exists_root_Ioo_of_mul_neg`, `monic_exists_pos_root` | `tendsto_atTop_of_leadingCoeff_nonneg`, `intermediate_value_Icc`, `comp_neg_X_leadingCoeff_eq` |
| §1.11(ii) prose (Descartes' rule of signs) | `dlmf_1_11_ii_descartes` (bound and **parity**), `dlmf_1_11_ii_descartes_neg` (`f(−z)`, negative zeros); parity proof: `neg_one_pow_signVariations` (lists), `coeffList_head`, `coeffList_getLast`, `neg_one_pow_signVariations_poly`, `sign_eval_zero_eq_sign_leadingCoeff` (IVT), `neg_one_pow_countP_roots_pos`, `signVariations_X_pow_mul`, `nat_mod_two_eq_of_neg_one_pow_eq` | `roots_countP_pos_le_signVariations` (bound only), `List.signVariations_cons_cons_of_ne_zero`, `roots_comp_neg_X`, `Multiset.prod_X_sub_C_dvd_iff_le_roots` |
| 1.11.8 | `tlogF`, `dlmf_1_11_8` (`f(−z)`), `exampleF_coeffList`, `exampleF_neg_coeffList`, `dlmf_1_11_ii_example` (one sign change each; one positive, one negative, six non-real zeros) | `filter_roots_map_range_eq_map_roots` |
| 1.11.11 | `dlmf_1_11_11` (roots, sum, product) (`Section11LowDegree.lean`) | — |
| §1.11(iii) cubic reduction | `cubicP`, `cubicQ`, `dlmf_1_11_iii_cubic_reduce`, `cubic_coeffs_eq_zero` | — |
| 1.11.12 | `cubicD`, `dlmf_1_11_12` (`D = ∏ (wᵢ − wⱼ)²`) | — |
| 1.11.13–1.11.15 | `dlmf_1_11_14`, `cubic_factor`, `dlmf_1_11_15` (`ρ`), `dlmf_1_11_iii_cubic_roots`, `dlmf_1_11_iii_cubic_example` | `Real.cos_pi_div_three`, `Real.sin_pi_div_three`, `Real.rpow_inv_natCast_pow` |
| 1.11.16–1.11.17 | `quarticP`, `quarticQ`, `quarticR`, `dlmf_1_11_16`, `quarticD`, `dlmf_1_11_17` | — |
| 1.11.18–1.11.20 | `dlmf_1_11_19` (resolvent cubic), `dlmf_1_11_20` (sign choice exists), `dlmf_1_11_iii_quartic_example` | — |
| 1.11.21 | `dlmf_1_11_21`, `pow_sub_eq_prod`, `roots_injOn`, `pow_eq_iff_of_prod` (`Section11Roots.lean`) | `X_pow_sub_C_eq_prod`, `Complex.isPrimitiveRoot_exp`, `mul_geom_sum` |
| §1.11(iv) `zⁿ + 1 = 0` | `dlmf_1_11_iv_neg_one` | `Complex.exp_pi_mul_I` |
| 1.11.22–1.11.23 | `dlmf_1_11_23` | `Complex.norm_mul_exp_arg_mul_I`, `Real.rpow_inv_natCast_pow` |
| 1.11.24 | `IsStable` (`Section11Stable.lean`) | — |
| 1.11.25–1.11.26 | `hurwitzD`, `hdet`, `dlmf_1_11_25_one`, `dlmf_1_11_25_two`, `dlmf_1_11_25_three` | `Matrix.det_fin_two`, `Matrix.det_fin_three` |
| §1.11(v) Hurwitz criterion | `dlmf_1_11_v_hurwitz` (full proof): `hurwitz_criterion`, `hStable_routh_iff`, `hdet_succ`, `hpoly_routh`, `exists_rhp_root_iff_of_homotopy`, `exists_root_within`, `norm_le_of_root`, `div_pos_of_hStable`, `isStable_iff_hStable` | `C_leadingCoeff_mul_prod_multiset_X_sub_C`, `Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`, `Matrix.det_succ_column_zero`, `isClopen_iff` (`ConnectedSpace unitInterval`) |
| §1.11(ii) prose (reciprocals) | `dlmf_1_11_ii_reverse_coeff` (`zⁿ f(1/z)` is `reverse`), `dlmf_1_11_ii_reverse` | `eval₂_reverse_eq_zero_iff`, `coeff_reverse` |
| 1.11.9 | `discriminantOfZeros`, `dlmf_1_11_9` (Mathlib's `discr` = `aₙ^{2n−2} ∏_{j<k}(zⱼ − zₖ)²`), `prod_prod_erase_sub`, `sum_card_Ioi`, `dlmf_1_11_9_complex` | `resultant_deriv`, `resultant_eq_prod_eval`, `eval_multiset_prod_X_sub_C_derivative`, `discr_C` |
| 1.11.10 | `dlmf_1_11_10` (general `k`), `dlmf_1_11_10_sum`, `dlmf_1_11_10_pairs`, `dlmf_1_11_10_prod` | `coeff_eq_esymm_roots_of_card` |

### §1.12 Continued Fractions (`Azurite/DLMF/Chapter1/Section12.lean`, `Section12Contraction.lean`, `Section12Convergence.lean`, `Section12VanVleck.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.12.1–1.12.3 | `cfw`, `cfConv`, `CfConverges` (notation, approximants, convergence) | — |
| 1.12.4 | `dlmf_1_12_4` (`Cₙ = Aₙ/Bₙ`, under `CfNonzero`), `cfA`, `cfB`, `cfP`, `cfQ` | — |
| 1.12.5–1.12.6 | `dlmf_1_12_5`, `dlmf_1_12_6` | — |
| 1.12.7 | `dlmf_1_12_7` (determinant formula) | `Finset.prod_Icc_succ_top` |
| 1.12.8–1.12.9 | `dlmf_1_12_8`, `dlmf_1_12_9` | — |
| 1.12.10–1.12.14 | `dlmf_1_12_10`, `dlmf_1_12_11`, `dlmf_1_12_12`, `dlmf_1_12_13`, `dlmf_1_12_14` | — |
| 1.12.15–1.12.16 | `dlmf_1_12_15` (`A′ₙ = (∏ d_k)Aₙ`), `dlmf_1_12_16` (same convergents) | — |
| 1.12.17 | `dlmf_1_12_17_one`, `dlmf_1_12_17_two`, `cfD`, `cfD_values` | — |
| 1.12.18–1.12.19 | `dlmf_1_12_18` (`Bₙ = 1`, `Aₙ` = partial sum), `dlmf_1_12_19` | — |
| 1.12.20–1.12.21 | `cfw`, `CfNonzero`, `dlmf_1_12_21`, `dlmf_1_12_21_limits` (`Cₙ(0)`, `Cₙ(∞)` as a limit over `ℂ`) | `tendsto_inv₀_cobounded` |
| 1.12.22 | `dlmf_1_12_22`, `cfPoint`, `convPt`, `cfPoint_eq_iff`, `cramer` (`Section12Contraction.lean`) | `OnePoint` |
| §1.12(iv) contraction/extension | `IsContraction`, `IsExtension`, `dlmf_1_12_iv_even_exists`, `dlmf_1_12_iv_odd_exists`, `convPt_add_two_eq_iff` | — |
| 1.12.23 | `evenA`, `evenB`, `evenScale`, `dlmf_1_12_23_numer`, `dlmf_1_12_23`, `cf_two_step` | — |
| 1.12.24 | `oddA`, `oddB`, `oddScale`, `dlmf_1_12_24_numer`, `dlmf_1_12_24` | — |
| §1.12(v) convergence | `CfConvergent` (`Section12Convergence.lean`) | — |
| 1.12.25 | `dlmf_1_12_25` (Pringsheim), `pringsheim_denom`, `cfNonzero_of_pringsheim` | `summable_of_sum_range_le` |
| 1.12.26–1.12.27 | `dlmf_1_12_27` (sector of the convergents), `VVSector`, `arg_sector_iff`, `vanVleck_tails`; `dlmf_1_12_v_vanVleck_ph` (`|ph C| ≤ π/2`) | `Complex.arg_of_re_nonneg`, `Real.arcsin_lt_arcsin` |
| 1.12.28 (+ even/odd convergence) | `dlmf_1_12_28` (Van Vleck, full proof, `Section12VanVleck.lean`): `posC_even_tendsto`, `posC_odd_tendsto`, `posC_tendsto` (Seidel–Stern), `stern_stolz`, `coeff_tendsto_of_bounded`, `tendsto_of_bounded_power_series` (Vitali, power-series form), `vvFamily`, `vvFamily_sector`, `cfConv_differentiableOn`, `norm_cfConv_le` | `Complex.hasSum_taylorSeries_on_ball`, `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, `tendsto_tsum_of_dominated_convergence`, `tendsto_atTop_ciSup` |

### §1.13 Differential Equations (`Azurite/DLMF/Chapter1/Section13.lean`, `Section13Primitive.lean`, `Section13Parameter.lean`, `Section13Inhomogeneous.lean`, `Section13Change.lean`, `Section13Products.lean`, `Section13SturmLiouville.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| §1.13(i) simply-connected | `IsSimplyConnectedDLMF` (complement in `OnePoint ℂ` connected), `IsSCDomain`; `windingNumber_eq_zero_of_simplyConnected`, `contourIntegral_eq_zero_of_simplyConnected`, `exists_primitive_of_simplyConnected` (`Section13Primitive.lean`, via polygonal chains: `polygon`, `chainInt_eq_zero_of_closed`, `chainInt_add_segInt`) | `DifferentiableOn.isExactOn_ball`, `IsPreconnected.constant` |
| 1.13.1 | `IsODESolution`, `IsODESolution.analyticOnNhd`, `IsODESolution.linearCombo` | `DifferentiableOn.analyticOnNhd` |
| §1.13(i) existence, uniqueness | `dlmf_1_13_i_exists` (Picard iteration `picard` along chains, `norm_iter_le`, `picardLim_hasDerivAt`), `dlmf_1_13_i_eq_zero`, `dlmf_1_13_i_unique`, `dlmf_1_13_i_infinite` | `image_norm_le_of_norm_deriv_right_le_deriv_boundary`, `hasDerivAt_of_tendstoLocallyUniformlyOn`, `tendstoUniformlyOn_tsum_nat` |
| 1.13.2 | `IsFundamentalPair`, `dlmf_1_13_2` | — |
| 1.13.3 | `dlmf_1_13_3`, `isFundamentalPair_of_wronskian_ne_zero` | — |
| 1.13.4 | `wronskian`, `dlmf_1_13_4` (determinant form); `wronskianN` (`n` arguments), `wronskianN_two` | `Matrix.det_fin_two_of` |
| 1.13.5 | `dlmf_1_13_5` (any primitive), `dlmf_1_13_5_primitive` (normalized at `z₀`), `wronskian_eq_zero_or_ne_zero`, `dlmf_1_13_i_wronskian_const` (`f = 0`); `n`th order: `hasDerivAt_det` (Jacobi), `IsODESolutionN`, `dlmf_1_13_5_orderN`, `dlmf_1_13_5_orderN_general` | `IsOpen.exists_is_const_of_deriv_eq_zero`, `ContinuousMultilinearMap.hasFDerivAt`, `Matrix.det_updateRow_sum` |
| 1.13.6 | `dlmf_1_13_6` (TFAE: fundamental pair, `𝒲 ≠ 0` in `D`, linear independence) | — |
| 1.13.7 | `dlmf_1_13_ii` (`Section13Parameter.lean`; `D` open and connected; analyticity in `z` not needed): `exists_hasDerivAt_param`, `param_bounds`, `param_quot_bounds`, `odeC`, `odeC_quot_sub`, `exists_tendsto_of_dist_le`, `norm_le_along_chain_gronwall` | `norm_le_gronwallBound_of_norm_deriv_right_le`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `hasDerivAt_iff_tendsto_slope_zero` |
| 1.13.8 | `IsInhomSolution` (`Section13Inhomogeneous.lean`), `IsInhomSolution.sub`, `IsInhomSolution.add_hom`, `dlmf_1_13_iii_exists_particular`, `dlmf_1_13_iii_exists`, `dlmf_1_13_iii_infinite` | — |
| 1.13.9 | `dlmf_1_13_9`, `dlmf_1_13_9_converse` | — |
| 1.13.10 | `dlmf_1_13_10` (variation of parameters, any primitives) | — |
| 1.13.11–1.13.12 | `dlmf_1_13_11` (`Section13Change.lean`; `ξ = 1/z`) | `hasDerivAt_inv` |
| 1.13.13–1.13.15 | `dlmfH`, `dlmf_1_13_14` (iff, `P′ = f`) | — |
| 1.13.16–1.13.17 | `dlmf_1_13_17_identity`, `dlmf_1_13_17` (iff, `η′ = e^{−P}`) | — |
| 1.13.18–1.13.20 | `schwarzian`, `dlmf_1_13_20` (first form, `q² ż = 1`), `dlmf_1_13_19` (Liouville), `schwarzian_alg`, `sq_mul_deriv_relations` | — |
| 1.13.21–1.13.22 | `dlmf_1_13_21` (Cayley), `dlmf_1_13_22` (inverse), `deriv_comp_three` | `Filter.EventuallyEq.deriv` |
| 1.13.23 | `dlmf_1_13_23` (`Section13Products.lean`), `deriv_three_mul` | — |
| 1.13.24–1.13.25 | `dlmf_1_13_25` (`I ≠ J` in `D`), `dlmf_1_13_25_quotient` (the quotient is `U′V − UV′`) | — |
| §1.13(vi)–(vii) | references only (singularities, closed-form solutions): not formalized | — |
| 1.13.26–1.13.28 | `IsSLSolution`, `UnmixedBC`, `PeriodicBC`, `IsRegularUnmixed`, `IsSLEigenvalue`, `IsSLEigenfunction` (`Section13SturmLiouville.lean`; `p`, `ρ` `C²` and positive on `ℝ`) | — |
| 1.13.29–1.13.31 | `lvT`, `lvX`, `lvW`, `lvU`, `lvQhat`, `lv_identity`, `dlmf_1_13_29`, `isLiouvilleSolution_lvW`, `isSLSolution_lvU`, `IsLiouvilleEigenvalue` | `HasDerivAt.of_local_left_inverse`, `continuousAt_of_monotoneOn_of_image_mem_nhds`, `Continuous.integral_hasStrictDerivAt` |
| §1.13(viii) (i)–(iii) | `dlmf_1_13_viii_eigenvalues_unmixed` (+ `lvBC₁`, `lvBC₂`, `lvBC_ne`, `lv_bc_eq`), `dlmf_1_13_viii_zeros`, `dlmf_1_13_viii_zeros'`, `lv_periodic_iff`, `dlmf_1_13_viii_eigenvalues_periodic` (periodic case needs `p, ρ, p′, ρ′` equal at `a`, `b`) | `Function.Injective.encard_image` |

### §1.14 Integral Transforms (`Azurite/DLMF/Chapter1/Section14.lean`, `Section14Parseval.lean`, `Section14Inversion.lean`, `Section14CosSin.lean`, `Section14Laplace.lean`, `Section14LaplaceInversion.lean`, `Section14Mellin.lean`, `Section14Hilbert*.lean`, `Section14Stieltjes*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.14.1 | `dlmfFourier`, `dlmfFourier_eq_fourier`, `fourier_eq_dlmfFourier` | `Real.fourier_real_eq_integral_exp_smul` |
| 1.14.2 (+ continuity, decay) | `dlmf_1_14_2`, `dlmf_1_14_i_continuous`, `dlmf_1_14_i_tendsto_zero`, `dlmf_1_14_i_tendsto_atTop`, `dlmf_1_14_i_tendsto_atBot` | `Real.zero_at_infty_fourier`, `continuous_of_dominated` |
| 1.14.3 | `dlmf_1_14_3`, `dlmf_1_14_3'` (`Section14Inversion.lean`; principal value as a limit over `[−R, R]`; `f(u±)` exist by `exists_tendsto_of_bv`): Dirichlet integral `tendsto_sinInt`, Jordan `tendsto_integral_bv_mul_sinc_complex`, `partial_inverse_eq` | `integral_integral_swap`, `exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn`, `variationOnFromTo.monotoneOn` |
| 1.14.4 | `dlmf_1_14_4` (principal value; `C¹` ⇒ locally Lipschitz ⇒ BV) | `ContDiffOn.exists_lipschitzOnWith`, `LipschitzOnWith.locallyBoundedVariationOn` |
| 1.14.5 | `dlmfConv`, `dlmf_1_14_5_integrable`, `dlmf_1_14_5` | `Real.fourier_mul_convolution_eq`, `Integrable.integrable_convolution` |
| 1.14.6 | `dlmf_1_14_6` (`Section14Parseval.lean`), `dlmf_inversion`, `continuous_dlmfConv`, `integrable_dlmfFourier_mul` | `Integrable.fourierInv_fourier_eq` |
| 1.14.7 | `dlmf_1_14_7` | — |
| 1.14.7_5 | `dlmf_1_14_7_5` (polarization) | — |
| 1.14.8 | `dlmf_1_14_8`, `plancherel`, `integrable_and_integral_fourier_of_nonneg`, `continuous_integral_mul_add` | `Real.tendsto_integral_gaussian_smul'`, `VectorFourier.integral_fourierIntegral_smul_eq_flip`, `Lp.instContinuousVAddDomAddAct`, `lintegral_tendsto_of_tendsto_of_monotone` |
| §1.14(i) Poisson | see `dlmf_1_8_14`, `dlmf_1_8_iv_fourier` (§1.8(iv)) | — |
| §1.14(i) uniqueness | `dlmf_1_14_i_unique` | `Continuous.fourierInv_fourier_eq` |
| 1.14.9–1.14.10 | `dlmfFourierCos`, `dlmfFourierSin` (`Section14CosSin.lean`), `evenExt`, `oddExt`, `dlmfFourier_evenExt`, `dlmfFourier_oddExt` | `integral_comp_neg_Ioi` |
| 1.14.11–1.14.12 | `dlmf_1_14_11`, `dlmf_1_14_12` (`u > 0`; limits of `∫₀^R`; from `dlmf_1_14_3`) | — |
| 1.14.13–1.14.16 | `dlmf_1_14_13`, `dlmf_1_14_14`, `dlmf_1_14_15`, `dlmf_1_14_16` (from `dlmf_1_14_7`) | `memLp_two_iff_integrable_sq_norm` |
| 1.14.17–1.14.18 | `laplace`, `ExpGrowth` (`Section14Laplace.lean`; measurable + growth replaces piecewise continuity), `integrableOn_laplace`, `norm_laplace_le`, `analyticOnNhd_laplace`, `hasDerivAt_laplace` | `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `exp_neg_integrableOn_Ioi` |
| 1.14.19 | `dlmf_1_14_19` (filter `comap re atTop`) | — |
| 1.14.20 | `dlmf_1_14_20`, `dlmf_1_14_20_bv`, `dlmf_1_14_20_shift` (`Section14LaplaceInversion.lean`), `laplace_eq_dlmfFourier`, `boundedVariationOn_mul` | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` |
| 1.14.21–1.14.22 | `dlmf_1_14_21`, `dlmf_1_14_22`, `setIntegral_Ioi_shift` | `integral_add_right_eq_self` |
| 1.14.23 | `dlmf_1_14_23`, `iteratedDeriv_laplace`, `ExpGrowth.pow_mul` | `Real.pow_div_factorial_le_exp` |
| 1.14.24 | `dlmf_1_14_24`, `integrableOn_laplace_div` | `integral_integral_swap`, `integrable_prod_iff'` |
| 1.14.25–1.14.26 | `dlmf_1_14_25`, `dlmf_1_14_26`, `laplace_split` | — |
| 1.14.27–1.14.29 | `dlmf_1_14_27`, `dlmf_1_14_28`, `dlmf_1_14_29`, `ibp_piece`, `ibp_tail` | `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`, `intervalIntegral_tendsto_integral_Ioi` |
| 1.14.30–1.14.31 | `laplaceConv`, `dlmf_1_14_31` | `integral_convolution` |
| §1.14(iii) uniqueness | `dlmf_1_14_iii_unique`, `eq_zero_of_fourier_eq_zero` | — |
| 1.14.32 | Mathlib `mellin` (`Section14Mellin.lean`), `mellin_eq_integral_exp`, `mellinConvergent_iff_exp`, `mellinLine`, `mellin_eq_dlmfFourier`, `setIntegral_Ioi_zero_eq_exp` | `mellin`, `MellinConvergent`, `integral_image_eq_integral_abs_deriv_smul` |
| §1.14(iv) strip | `dlmf_1_14_iv_analytic`, `hasDerivAt_mellin`, `mellinConvergent_of_re`, `abs_mul_exp_le` (integrability on `(a, b)`, not `O`-bounds) | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` |
| 1.14.33 | `dlmf_1_14_33_atTop`, `dlmf_1_14_33_atBot` | — |
| §1.14(iv) Note | `dlmf_1_14_iv_note` | `mellinConvergent_of_isBigO_rpow` |
| 1.14.34 | `dlmf_1_14_34`, `dlmf_1_14_34'` (from `dlmf_1_14_3`) | `eVariationOn.comp_le_of_antitoneOn` |
| 1.14.35 | `dlmf_1_14_35` | `mellinInv_mellin_eq` |
| a.e. inversion | `fourierInv_fourier_ae`, `mellinInv_mellin_ae`, `mellinInv_mellin_ae_mul`, `integral_fourier_mul` (not in Mathlib) | `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `HasCompactSupport.toSchwartzMap`, `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` |
| 1.14.36–1.14.37 | `dlmf_1_14_36` (either hypothesis), `dlmf_1_14_36_of_right`, `dlmf_1_14_37` | `integral_integral_swap`, `Integrable.mul_prod`, `integral_comp_mul_left_Ioi` |
| 1.14.38 | `dlmf_1_14_38`, `mellin_conj_of_real` | `Complex.conj_mul'` |
| 1.14.39–1.14.40 | `mellinConv`, `dlmf_1_14_40`, `mellinConv_exp`, `mellinConvergent_mellinConv` | `integral_convolution` |
| 1.14.41 | `HasHilbert`, `hilbert`, `hilbertTrunc`, `hilbertTrunc_eq_pv` (`Section14Hilbert.lean`; PV at `x` and `∞`) | `intervalIntegral.integral_comp_add_left` |
| 1.14.42 | `dlmf_1_14_42` (`f` integrable, continuous at `x`), `tendsto_conjPoisson_sub`, `conjPoisson_eq` | `integrableOn_Ioi_rpow_of_lt` |
| 1.14.43 | `dlmf_1_14_43` (`f` integrable), `tendsto_hilbertTrunc` | `intervalIntegral_tendsto_integral_Ioi` |
| §1.14(v) multiplier | `hasHilbert_dlmfFourier`, `hasHilbert_of_fourier`, `hilbertMultiplier`, `integral_sin_mul_div_eq`, `tendsto_sinInt_mul` | `integral_integral_swap`, `tendsto_integral_filter_of_dominated_convergence` |
| 1.14.44 | `dlmf_1_14_44`, `hasHilbert_hilbert`, `integrable_dlmfFourier_of_contDiff` | `Real.fourier_deriv` |
| 1.14.45 | `dlmf_1_14_45` (`Section14HilbertLp.lean`; all `p > 1`, sharp constant, a.e. existence; DLMF's constant should be `A_p^p`), `dlmf_1_14_45_two`; arc ledger `docs/hilbert_lp_plan.md` | `integral2_divergence_prod_of_hasFDerivAt`, `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`, `Lp.cauchy_complete_eLpNorm`, `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` |
| 1.14.46 | `dlmf_1_14_46`, `dlmf_1_14_46_of_bv`, `lipschitzWith_dlmfFourier` (limit of `∫_{−R}^R`) | `LipschitzOnWith.comp_eVariationOn_le` |
| 1.14.47 | `stieltjesPartial`, `StieltjesConverges`, `stieltjes` (improper at `∞`; `Section14Stieltjes.lean`) | — |
| §1.14(vi) convergence | `dlmf_1_14_vi_converges` (`s > 0`, `f = O(t^{−δ})`), `dlmf_1_14_vi_uniform` (convergence at one `s₀ ∈ ℂ \ (−∞, 0]` ⇒ uniform on compacts of the cut plane, via Abel/Dirichlet with the primitive: `integral_mul_eq_primitive`, `norm_integral_mul_le_abel` in `Section14StieltjesAbel.lean`), `tendsto_stieltjesPartial`, `exists_mul_one_add_le_norm`, `dlmf_1_14_vi_analytic` | `integral_integral_swap`, `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`, `Complex.slitPlane`, `TendstoLocallyUniformlyOn.differentiableOn` |
| 1.14.48 | `dlmf_1_14_48` (all `m`, the integral converging at every `s` off the cut), `stieltjesPow`, `hasDerivAt_stieltjesPow`, `tendstoLocallyUniformlyOn_iteratedDeriv` | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `TendstoLocallyUniformlyOn.deriv` |
| 1.14.49 | `dlmf_1_14_49` (one-sided limits `f(σ±)`, `σ > 0`; `Section14StieltjesInversion.lean`): Poisson kernel `poissonK`, `stieltjesPartial_sub`, `abs_integral_near_le` (near `σ`, arctan), `exists_norm_tail_le` (Abel with the decreasing multiplier `(1 + t)·kernel`) | `Real.hasDerivAt_arctan`, `Real.tendsto_arctan_atTop` |
| 1.14.50 | `dlmf_1_14_50` (`Section14StieltjesLaplace.lean`; `f` integrable on every `[0, R]`, so in particular piecewise continuous; `ℜs > 0`): the inner `ℒf(x)` (`laplaceImp`, improper) converges for `x > 0` and `ℒ(ℒf)(s) = 𝒮f(s)` with the outer integral improper at `0+` and `∞` (conditional convergence allowed); `integral_box` (Fubini on `[ε, X] × [0, R]`), `stieltjesPhi`, `tendsto_stieltjesPhi_zero` (Abelian theorem), `tendsto_stieltjesPhi_atTop` | `integral_exp_mul_complex`, `Complex.norm_exp_sub_one_le`, `intervalIntegral.continuousAt_of_dominated_interval` |
| Table 1.14.1 (Fourier transforms) | rows `dlmf_table_1_14_1_r1` … `_r10` (`r1_zero` at `x = 0`): elementary rows in `Section14TableFourier.lean` (half-line integrals, `t = u²` + complex Gaussian, principal square roots), `sinh/sinh` and `cosh/cosh` in `Section14TableHyperbolic.lean` (geometric series + tangent partial fractions from `cot_series_rep'`; row 7 from row 6), `sin(at²)`, `cos(at²)` in `Section14TableFresnel.lean` (improper `∫_{−R}^{R}`; Abel convergence + Abelian theorem with `e^{−εt²}`); ledger `docs/dlmf_table_1_14_1_plan.md` | `fourierIntegral_gaussian`, `integral_gaussian_complex_Ioi`, `integral_comp_rpow_Ioi`, `cot_series_rep'`, `hasSum_integral_of_summable_integral_norm`, `continuousAt_cpow_const` |
| Table 1.14.2 (Fourier cosine transforms) | rows `dlmf_table_1_14_2_r1` … `_r10` in `Section14TableCos.lean` (box, `e^{−at}`, `e^{−at²}`; `1/(a²+t²)`, `1/(a²+t²)²`, `4a³/(4a⁴+t⁴)` by cosine inversion `dlmfFourierCos_dlmfFourierCos`; `sin(at²)`, `cos(at²)` as improper limits from Table 1.14.1) and `Section14TableCosLog.lean` (logarithms via `ln(1+a²/t²) = ∫_0^1 2sa²/(t²+(sa)²) ds` + Fubini). **Errata:** row 4 needs `|ph a| < π/4` (stated `|ℑa| < ℜa`; `ℜa > 0` lets `4a⁴+t⁴` vanish); row 10's literal `ln(quotient)` needs `|ph a|, |ph b| < π/4` (`_r10`), the general `ℜa, ℜb > 0` form is `ln(a²+t²) − ln(b²+t²)` (`_r10_sub`) | `dlmf_1_14_11`, `integral_integral_swap`, `integrable_prod_iff`, `HasDerivAt.clog_real`, `log_exp`, `abs_arg_lt_pi_div_two_iff` |
| Table 1.14.3 (Fourier sine transforms) | rows `dlmf_table_1_14_3_r1` … `_r13`: Lebesgue rows 5–10 in `Section14TableSin.lean` (exponentials; by parts `dlmfFourierSin_deriv` from Table 1.14.2 rows 2, 6; Fubini `dlmfFourierSin_div` for `g(t)/t`, row 7 with principal complex `arctan`); improper rows 1, 2, 4, 11 and row 3 in `Section14TableSinImproper.lean` (Dirichlet, `t = u²` + Fresnel from Table 1.14.2 rows 7–8, Frullani for row 11); row 13 in `Section14TableSinLog.lean` (by parts across the log singularity + `∫_0^∞ (cos ax − cos xt)/(t² − a²) dt` as the limit `b → ia`); row 12 in `Section14TableSinArctan.lean`. **Discrepancy:** row 12's integral diverges even as an improper integral (`_r12_not_tendsto`); DLMF's value holds as the Abel limit `ε → 0+` of `∫ e^{−εt} …` (`_r12`) | `integral_comp_mul_deriv'''`, `integral_eq_of_hasDerivAt_off_countable_of_le`, `integral_Ioi_mul_deriv_eq_deriv_mul`, `tendsto_integral_filter_of_dominated_convergence`, `Complex.arctan`, `Real.continuous_mul_log` |
| Table 1.14.4 (Laplace transforms) | rows `dlmf_table_1_14_4_r1` … `_r16`: rows 1–12 in `Section14TableLaplace.lean` (`∫_0^∞ tⁿ e^{−ct} = n!/c^{n+1}` by induction, `laplace_two_exp`; row 3 from the half-integer Gamma integral); rows 13–16 in `Section14TableLaplaceLog.lean` (Fubini over a segment parameter; principal-log identities; row 16 via `arctan(va/s)`). **Discrepancy:** row 14's printed condition `ℜ(s + a) > 0` is insufficient (`_r14_condition`, `a = 1`, `s = 1/2`); proved for `ℜs > |ℜa|`. Row 15 for `ℜs > |ℑa|` (DLMF's `ℜs > 0` for real `a`); row 16 for real `a` | `integral_Ioi_mul_deriv_eq_deriv_mul`, `integral_integral_swap`, `HasDerivAt.clog_real`, `log_exp`, `Complex.cosh_mul_I`, `integrableOn_const_iff` |
| Table 1.14.5 (Mellin transforms) | rows `dlmf_table_1_14_5_r1` … `_r11`: `Section14TableMellin.lean` (rows 1, 2 via `x = e^{−u}` and Table 1.14.4; core `∫_0^∞ x^{s−1}/(1 + ax) dx = a^{−s}π/sin(πs)` by Fubini + Gamma for `a = 1`, scaling, continuation in `a` over the slit plane; rows 4, 10, 11), `Section14TableMellinLog.lean` (`mellin_by_parts`; rows 5, 7, 8, 9), `Section14TableMellinPV.lean` (`𝓜[ln|1 − x|] = π cot(sπ)/s` as `θ → π`; row 6 by the identity theorem in `s`, for `s ≠ 0`; row 3 as an explicit principal value). Row 2 for `ℜs > 0` (DLMF: `ℜs > 1`); row 9 with `arccot x = arctan(1/x)` | `mellin_comp_mul_left`, `mellin_comp_rpow`, `mellin_comp_inv`, `Complex.Gamma_mul_Gamma_one_sub`, `integral_cpow_mul_exp_neg_mul_Ioi`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` |

### §1.15 Summability Methods (`Azurite/DLMF/Chapter1/Section15.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.15.1 | `dlmf_1_15_1` (`partialSum` of §1.9(v)) | — |
| 1.15.2–1.15.3 | `AbelSum` (series convergent for `0 < x < 1`) | — |
| 1.15.4–1.15.5 | `CesaroSum`; `cesaroSum_iff_cesaroGenSum_one` | — |
| 1.15.6–1.15.7 | `CesaroGenSum` (literal, `ascPochhammer`), `cesaroCoeff`, `cesaroGen_eq`, `cesaroCoeff_eq_sum` (Pascal), `sum_cesaroCoeff_mul` (summation by parts via power series) | `ascPochhammer_succ_eval`, `PowerSeries.coeff_mul` |
| 1.15.8–1.15.9 | `BorelSum` (series convergent for all `t`) | — |
| §1.15(ii), 1.15.10–1.15.11 | `IsRegularMethod`; `dlmf_1_15_11` (Abel), `dlmf_1_15_ii_cesaro`, `dlmf_1_15_ii_borel`, `dlmf_1_15_ii_cesaroGen` (`α ≥ 0`), all via the Toeplitz lemma `tendsto_tsum_weights`; `dlmf_1_15_ii` collects them. **Discrepancy:** `(C,α)` is not regular for `−1 < α < 0` (`dlmf_1_15_ii_cesaroGen_not_regular`; `(α+1)ₙ/n! → 0`, sparse positive counterexample), contrary to DLMF's "all of the methods … are regular" | `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`, `Filter.Tendsto.cesaro_smul`, `NormedSpace.expSeries_div_hasSum_exp` |
| 1.15.12–1.15.14 | `diskPoisson`, `dlmf_1_15_12` (`Section15Fourier.lean`), `dlmf_1_15_13`, `dlmf_1_15_14` (uniform on `[δ, 2π − δ]`) | `HasSum.of_nat_of_neg_add_one`, `hasSum_geometric_of_norm_lt_one` |
| 1.15.15–1.15.17 | `fejerK`, `dlmf_1_15_15`, `fejerK_eq_sum` (average of §1.8 Dirichlet kernels), `dlmf_1_15_16`, `dlmf_1_15_17` | `Real.cos_sub_cos`, `Set.Countable.ae_notMem` |
| 1.15.18–1.15.20 | `abelMean`, `fourierF`, `dlmf_1_15_18`, `dlmf_1_15_19`, `dlmf_1_15_20` (termwise integration) | `integral_tsum_of_summable_integral_norm` |
| 1.15.21–1.15.23 | `cesaroMeanF`, `fourierSym`, `dlmf_1_15_21`, `dlmf_1_15_22`, `dlmf_1_15_23` | — |
| 1.15.24 | `dlmf_1_15_24_abel` (`r → 1−`), `dlmf_1_15_24_cesaro`, `_abel_uniform`, `_cesaro_uniform` (continuous `f`); general approximate identity `tendsto_kernel_mean`, `tendstoUniformly_kernel_mean` | `Function.Periodic.intervalIntegral_add_eq`, `IsCompact.uniformContinuousOn_of_continuous` |
| 1.15.25–1.15.28 | `fourierG`, `dlmf_1_15_26`, `dlmf_1_15_27` (analytic in the disk), `dlmf_1_15_iii_re` (`u = A`), `dlmf_1_15_28` (`v`), `dlmf_1_15_iii_harmonic` (`A` harmonic, via `dlmf_1_9_27`) | `Complex.differentiableOn_tsum_of_summable_norm`, `tsum_of_nat_of_neg_add_one`, `conj_tsum` |
| 1.15.29–1.15.32, §1.15(iv) | `IntegralConverges` (1.4.22 sense), `IntegralAbelSum` (improper Abel integrals), `IntegralCesaroSum`, `dlmf_1_15_30` (Lebesgue case), `dlmf_1_15_32`; regularity `dlmf_1_15_iv`, `dlmf_1_15_iv_of_integrable` (`Section15Integrals.lean`; by parts against the primitive on each half line) | `intervalIntegral_tendsto_integral_Ioi`, `integral_exp_mul_Ioi`, `IntervalIntegrable.iff_comp_neg` |
| 1.15.33–1.15.38, §1.15(v) | `halfPlanePoisson` (`Section15FourierIntegrals.lean`), `dlmf_1_15_34`, `dlmf_1_15_35`; `poissonMean` (1.15.36, Fourier form), `dlmf_1_15_37`, `dlmf_1_15_38` (`L¹` convergence + integrability); general `L¹` approximate identity `tendsto_integral_kernel_conv_sub` from continuity of translation `tendsto_integral_translate_sub` (density of `C_c`); `tendsto_tail_dilate` | `Integrable.exists_hasCompactSupport_integral_sub_le`, `integral_integral_swap`, `integrable_prod_iff`, `Measure.integral_comp_mul_left` |
| 1.15.39–1.15.40 | `fourierPhi`, `dlmf_1_15_39_analytic` (via `cauchyExt` of §1.14), `dlmf_1_15_39` (`ℜΦ = h`), `dlmf_1_15_40` (`ℑΦ`), `dlmf_1_15_40_hilbert`. **Discrepancy:** at continuity points `ℑΦ(x+iy) → −ℋf(x)`, not `ℋf(x)`: 1.15.40's kernel is `(x−t)/…` while DLMF's own 1.14.41–1.14.42 use `(t−x)/…` | `dlmf_1_14_42`, `integral_re` |
| 1.15.41–1.15.46 | `fejerKernel`, `dlmf_1_15_42` (from `integral_one_sub_cos_div_sq`: `∫ (1−cos s)/s² = π` by parts against `sinInt`), `dlmf_1_15_43`; `fejerMean` (1.15.44), `dlmf_1_15_45` (Fubini + `integral_triangle_cexp`), `dlmf_1_15_46` (`L¹` convergence + integrability) | `intervalIntegral_integral_swap`, `integral_comp_abs`, `Complex.two_cos`, `intervalIntegral_tendsto_integral_Ioi` |
| 1.15.47–1.15.48, §1.15(vi) | `fracIntegral` (`Section15Fractional.lean`), `fracIntegralFrom` (lower limit `a`), `dlmf_1_15_47`; `dlmf_1_15_48` (`f` continuous on `[0, ∞)`), general `fracIntegralFrom_add` (only `∫ \|f\|(x−t)^{ℜα+ℜβ−1} < ∞`; Fubini on the triangle + `integral_beta_shift`); 1.4.31 link `fracIntegralFrom_natCast` (= `repeatedIntegral`) | `Complex.Gamma_mul_Gamma_eq_betaIntegral`, `Complex.betaIntegral_convergent`, `integral_integral_swap`, `integrable_prod_iff'`, `Complex.mul_cpow_ofReal_nonneg` |
| 1.15.49–1.15.50 | `fracIntegral_pow`, `dlmf_1_15_50` (`HasSum`, assuming `∑ \|aₖ\| xᵏ < ∞`) | `intervalIntegral.hasSum_integral_of_dominated_convergence`, `Complex.Gamma_nat_eq_factorial` |
| §1.15(vi) closing remarks | upper limit `fracIntegralTo`, reflection `fracIntegralTo_eq`, semigroup `fracIntegralTo_add`; `a = ∞`: `fracIntegralWeyl`, `tendsto_fracIntegralTo_atTop` | `intervalIntegral.integral_comp_neg`, `intervalIntegral_tendsto_integral_Ioi` |
| 1.15.51, §1.15(vii) | `fracDeriv` (`Section15FractionalDeriv.lean`, `n = ⌊ℜα⌋+1`), `dlmf_1_15_51` (every integer `n > ℜα`, `x > 0`, `f` continuous on `[0,∞)`); `continuousOn_fracIntegral`, `iteratedDeriv_fracIntegral_nat`, `iteratedDeriv_fracIntegral_add`, `fracDeriv_natCast`, `fracDeriv_fracIntegral`, `fracDeriv_fracIntegral_self` | `continuousWithinAt_of_dominated`, `intervalIntegral.integral_hasDerivAt_right`, `EventuallyEq.iteratedDeriv_eq` |
| 1.15.52 | `dlmf_1_15_52` (ordinary `D^k`, `Dⁿ`), `dlmf_1_15_52_fracDeriv` | `iteratedDeriv_eq_iterate` |
| 1.15.53 | `dlmf_1_15_53` (`f = I^γ g`, `ℜγ > ℜ(α+β)`), `dlmf_1_15_53_self` (`γ = α+β`); `fracDeriv_cpow`, `dlmf_1_15_vii_half_deriv` (`D^{1/2}D ≠ D^{3/2}`). **Discrepancy:** false under DLMF's proviso alone (`dlmf_1_15_53_counterexample`: `α = 1/3`, `β = 3/2`, `f = t^{1/2}`; `D^β f = 0` but `D^{11/6} f ≠ 0`) | `Complex.hasStrictDerivAt_cpow_const`, `Complex.Gamma_ne_zero_of_re_pos` |
| 1.15.54–1.15.55, §1.15(viii) | `littlewood` (`Section15Tauberian.lean`; Karamata–Wielandt: step `1_{[e^{−1},1]} = t + t(1−t)h(t)`, polynomial sandwich, samples `x_N = e^{−1/(N+1/2)}`), `dlmf_1_15_55` (`AbelSum` of a real series + `aₙ > −K/n` ⇒ `SeriesConverges`); tools `karamata_poly`, `abel_poly`, `exists_poly_sandwich`, `tauberPoint` | `exists_polynomial_near_of_continuousOn`, `Polynomial.induction_on'`, `integral_pow`, `Real.add_one_le_exp` |
| 1.15.56–1.15.57 | `hardy_littlewood_nonneg`, `dlmf_1_15_57_nonneg` (`aₙ ≥ 0`; summability on `(0,1)` assumed), `dlmf_1_15_57_bounded` (complex `aₙ`, `\|aₙ\| ≤ K`, via `aₙ + K` on real and imaginary parts) | `Complex.hasSum_iff`, `tsum_geometric_of_lt_one` |

### §1.16 Distributions (`Azurite/DLMF/Chapter1/Section16*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| §1.16(i) definitions | `dlmf_1_16_i_support`, `dlmf_1_16_i_compact_support`, `IsTestFunction`, `testSpace` (`𝒟(I)`, `I` any open set), `isTestFunction_iff_testFunction` (= Mathlib `𝓓(Ω, ℂ)`), `TestConvergesDLMF` (literal), `TestConverges` (corrected), `TestConverges.unique` | `TestFunction`, `tsupport`, `HasCompactSupport` |
| 1.16.1–1.16.2 | `dlmf_1_16_1`, `IsDistribution`, `distributionSpace` (`𝒟*(I)`). **Discrepancy:** with DLMF's literal convergence (no condition on `supp φ`), `0 → φ` for every `φ` (`testConvergesDLMF_zero`), so every "distribution" is `0` (`dlmf_1_16_2_literal`); the standard definition adds `supp φ ⊆ K` | `isClopen_iff`, `noncompact_univ` |
| 1.16.3, 1.16.3_5 | `regularDist`, `dlmf_1_16_3`, `isDistribution_regularDist`, `IsRegularDist`, `regularDist_ae_eq`; `stieltjesDist`, `dlmf_1_16_3_5`, `isDistribution_stieltjesDist`; generic `weightedDist` | `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `LocallyIntegrableOn.integrableOn_compact_subset`, `StieltjesFunction.measure` |
| 1.16.4–1.16.5 | `dlmf_1_16_4`, `dlmf_1_16_5` | — |
| 1.16.6 | `mulTest`, `mulDist`, `dlmf_1_16_6`, `isDistribution_mulDist` (`α` smooth on `I`), via `TestConverges.mul` and the Leibniz bound `norm_iteratedDeriv_mul_le` | `norm_iteratedFDerivWithin_mul_le`, `iteratedFDerivWithin_of_isOpen` |
| 1.16.7 | `DistConverges`, `dlmf_1_16_7`, example `distConverges_regularDist` | — |
| 1.16.8–1.16.9, §1.16(ii) | `derivTest`, `TestConverges.deriv`, `derivDist`, `dlmf_1_16_8`, `dlmf_1_16_9`, `isDistribution_derivDist(_iterate)` (`Section16Derivatives.lean`); `distDeriv` (`Df = Λ_f'`), `distDeriv_of_contDiffOn` (`C¹` ⇒ `Λ_{f'}`) | `contDiff_infty_iff_deriv`, `tsupport_deriv_subset`, `HasCompactSupport.deriv` |
| 1.16.9_5 | `dlmf_1_16_9_5` (`μ_α = Dα`) via `integral_stieltjes_eq_neg` (`∫ φ dα = −∫ α φ'`, Fubini); absolutely continuous case `distDeriv_stieltjes_of_density` (`Dα = Λ_w`, from `dlmf_1_4_23_1`) | `integral_integral_swap`, `StieltjesFunction.measure_Ioc`, `Monotone.locallyIntegrable`, `integral_withDensity_eq_integral_toReal_smul₀` |
| 1.16.10–1.16.12, §1.16(iii) | `diracDist`, `dlmf_1_16_10`, `dlmf_1_16_11`, `isDistribution_diracDist`, `dlmf_1_16_12`; singular: `diracDist_not_isRegular` (bump functions + `tendsto_setIntegral_of_antitone`) | `ContDiffBump`, `tendsto_setIntegral_of_antitone`, `Real.volume_singleton` |
| 1.16.13–1.16.16, §1.16(iv) | `heavisideH` (`Section16Heaviside.lean`, `H(0) = 0`), `dlmf_1_16_14`, `dlmf_1_16_15`, `dlmf_1_16_16` (`DH(x−x₀) = δ_{x₀}`); `δ_{x₀} = μ_α` for `α = H(·−x₀)` (`stieltjesFunction_heavisideH` = §1.4(v) `heaviside x₀`, `diracDist_eq_stieltjesDist`), `dlmf_1_16_16_stieltjes` | `rightLim_eq_of_tendsto`, `Monotone.stieltjesFunction`, `integral_dirac` |
| 1.16.17–1.16.18 | `IsPiecewiseSmooth` (smooth one-sided pieces), `jump` (`σₙ`), `tendsto_iteratedDeriv` (one-sided limits), `distDeriv_piecewise` (`m = 1`), `dlmf_1_16_18` (induction; `derivDistₗ`) | `integral_add_compl`, `intervalIntegral.integral_mul_deriv_eq_deriv_mul` |
| 1.16.19–1.16.20 | `posPart`, `posPow`, `dlmf_1_16_19`, `locallyIntegrable_posPow` (`α > −1`), `dlmf_1_16_20` (`α > 0`) | `intervalIntegral.intervalIntegrable_rpow'`, `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`, `Real.hasDerivAt_rpow_const` |
| 1.16.21 | `posPowDist`, `posPowDist_zero`, `posPowDist_succ`, `posPowDist_indep` (independent of `n`, non-integer `α`), `derivDist_posPowDist` (power rule) | `ascPochhammer_succ_eval`, `ascPochhammer_succ_left` |
| 1.16.22–1.16.23 | `lnPos`, `dlmf_1_16_22`, `negPowDist`, `dlmf_1_16_23`, `derivDist_negPowDist` (power rule), `negPowDist_zero_apply_of_pos` (`x₊^{−1}` acts as `1/x` on `(0,∞)`) | `intervalIntegral.intervalIntegrable_log'`, `Real.contDiffOn_log` |
| §1.16(v) definitions | `IsTempTest` (`Section16Tempered.lean`, DLMF's `O(\|x\|^{−N})`), `isTempTest_iff_bound` (1.16.24 bounds), `tempSpace`, `isTempTest_iff_schwartz`, `tempEquiv` (`𝒯 ≃ 𝓢(ℝ, ℂ)`) | `SchwartzMap`, `norm_iteratedFDeriv_eq_norm_iteratedDeriv`, `cocompact_eq_atBot_atTop` |
| 1.16.24 | `TempConverges`, `WeightedConverges`, `tempConverges_iff` (DLMF ⇔ weighted uniform), `tempConverges_iff_tendsto` (⇔ topology of `𝓢`) | `schwartz_withSeminorms`, `SchwartzMap.seminorm_le_bound`, `SchwartzMap.le_seminorm` |
| §1.16(v) tempered distributions | `IsTempDist`, `temperedSpace` (`𝒯*`), `isTempDist_iff_continuous`, `isTempDist_iff_exists_clm` (= Mathlib `𝓢'(ℝ, ℂ)`); `tempDeriv`, `isTempDist_tempDeriv`, `tempDeriv_iterate_apply`; examples `tempDirac`, `isTempTest_of_isTestFunction`, `TestConverges.tempConverges`, `IsTempDist.isDistribution` (`𝒯* ⊆ 𝒟*`), `tempRegular` (polynomially bounded `f`), `tempRegular_comp_testToTemp` | `continuous_iff_seqContinuous`, `SchwartzMap.instFirstCountableTopology`, `integrable_inv_one_add_sq` |
| 1.16.25 | `TempDistConverges`, `dlmf_1_16_25` | — |
| §1.16(vi) setup | `partialDeriv`, `partialDeriv_comm` (Schwarz), `partialWord`, `partialWord_perm`, `wordOf`, `mDeriv` (`φ⁽ᵏ⁾`), `partialWord_eq_mDeriv` (`Section16Several.lean`, `ℝⁿ = Fin n → ℝ`) | `ContDiffAt.isSymmSndFDerivAt`, `List.Perm.foldr_eq`, `List.perm_iff_count` |
| §1.16(vi) `𝒟ₙ`, distributions | `IsTestFunctionN`, `testSpaceN`, `isTestFunctionN_iff_testFunction` (= Mathlib `𝓓`), `TestConvergesNDLMF`, `TestConvergesN`, `TestConvergesN.unique`, `IsDistributionN`, `distSpaceN`, `partialDist`, `mDerivDist_apply`. **Discrepancy** (as in §1.16(i)): literal convergence gives `0 → φ` for all `φ` (`testConvergesNDLMF_zero`, `n ≥ 1`), so only `Λ = 0` (`dlmf_1_16_vi_literal`) | `noncompact_univ`, `Filter.EventuallyEq.fderiv_eq` |
| 1.16.26–1.16.27 | `regularDistN`, `dlmf_1_16_26`, `isDistributionN_regularDistN`, `distDerivN`, `dlmf_1_16_27` | `LocallyIntegrable.integrableOn_isCompact` |
| 1.16.28, `𝒯*ₙ` | `monomialN`, `IsTempTestN`, `isTempTestN_iff_schwartz` (= Mathlib `𝓢(ℝⁿ, ℂ)`, via `iteratedFDeriv_unitVec`, `norm_multilinear_le_sum`, `norm_pow_le_one_add_sum`), `isTempTestN_of_isTestFunctionN`, `tempSpaceN`, `tempEquivN`, `IsTempDistN`, `temperedSpaceN`, `isTempDistN_iff_exists_clm` | `iteratedFDeriv_succ_apply_left`, `fderiv_continuousMultilinear_apply_const_apply`, `ContinuousMultilinearMap.map_sum`, `map_smul_univ` |
| 1.16.29, §1.16(vii) | `dotL` (`−x·t/(2π)`), `fourierN`, `dlmf_1_16_29` (`Section16Fourier.lean`); `fourierIntegralCLM`/`fourierCLM` (`𝓕` continuous on `𝓢(ℝⁿ, ℂ)`, Mathlib's estimate rerun for `L`), `isTempTestN_fourierN` (`𝓕φ ∈ 𝒯ₙ`), `fourierTest`; `fourierN_partialDeriv` (`𝓕(∂ⱼφ) = −i xⱼ𝓕φ`), `partialDeriv_fourierN` (`∂ⱼ𝓕φ = 𝓕(i tⱼφ)`) | `VectorFourier.fourierIntegral`, `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`, `VectorFourier.contDiff_fourierIntegral`, `VectorFourier.fourierIntegral_fderiv`, `VectorFourier.hasFDerivAt_fourierIntegral`, `SchwartzMap.mkCLM` |
| 1.16.30–1.16.34 | `DT` (`Dⱼ`), `XT`, `DW`, `XW`, `polyEvalN` (`P`), `PD` (`P(D)`), `PX`, `PXneg` (`P₋`), `coe_PD`; `dlmf_1_16_33`, `dlmf_1_16_34` | `SchwartzMap.smulLeftCLM`, `ContinuousLinearMap.hasTemperateGrowth` |
| 1.16.35–1.16.37 | `fourierDist`, `dlmf_1_16_35`, `isTempDistN_fourierDist` (`𝓕(u)` tempered), `DD`, `DDW`, `PDD`, `dlmf_1_16_36`, `dlmf_1_16_37` | — |
| §1.16(viii) setup | `fourier1CLM` (DLMF `𝓕` on `𝓢(ℝ, ℂ)`), `coe_fourier1CLM` (= `dlmfFourier`), `fourierTest1`, `fourierTest1_fourierTest1` (`𝓕𝓕φ = φ₋`), `fourierDist1`, `isTempDist_fourierDist1`; `boundedTemp`, `tempOne`, `tempSign`, `tempH` (`Section16FourierSpecial.lean`) | `SchwartzMap.fourierTransformCLM`, `SchwartzMap.compCLMOfContinuousLinearEquiv`, `ContinuousLinearEquiv.unitsEquivAut` |
| 1.16.38–1.16.43 | `dlmf_1_16_38`, `dlmf_1_16_39` (`𝓕(δ) = 1/√(2π)`), `dlmf_1_16_40` (`√(2π) 𝓕(δ) = 1`), `dlmf_1_16_41`, `dlmf_1_16_42` (`𝓕(1) = √(2π) δ`), `dlmf_1_16_43` (`𝓕(1)/√(2π) = δ`) | — |
| 1.16.44–1.16.47 | `dlmf_1_16_44`, `integral_Ioi_deriv_temp`, `dlmf_1_16_45_sign`, `dlmf_1_16_45_heaviside`, `dlmf_1_16_46`; `tempX`, `hasDerivAt_dlmfFourier_temp`, `derivTempTest_fourierTest1`, `fourierDist1_tempDeriv` (`𝓕(u′) = (x/i)𝓕(u)`), `dlmf_1_16_47` | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` |
| 1.16.48–1.16.51 | `pvInvX`, `integrableOn_pvInvX`, `tendsto_pvInvX` (PV limit), `pvDist`; `tendsto_conjPoissonInt_zero`, `dlmf_1_16_49` (via damping `e^{−ε|x|}` and §1.14's conjugate Poisson integral), `dlmf_1_16_48`, `tempH_eq`, `dlmf_1_16_50`, `dlmf_1_16_51` | `norm_image_sub_le_of_norm_deriv_le_segment'`, `tendsto_integral_filter_of_dominated_convergence`, `integral_comp_neg_Ioi` |

### §1.17 Integral and Series Representations of the Dirac Delta (`Azurite/DLMF/Chapter1/Section17*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.17.1–1.17.2 | `dlmf_1_17_1_2_not_function` (no function vanishing off `0` satisfies 1.17.2 for all test functions; `exists_testFunction_one`), `dlmf_1_17_2` (Dirac distribution), `dlmf_1_17_2_measure` (`Measure.dirac`) (`Section17.lean`) | `ContDiffBump`, `integral_dirac` |
| 1.17.3–1.17.4 | `IsDeltaSequence`, `dlmf_1_17_4` (delta sequence ⇔ regular distributions converge to `δ_a`) | — |
| 1.17.5 | `gaussDelta`, `dlmf_1_17_5`, `integral_gaussDelta`, `integral_Ioi_gaussDelta`, `isDeltaSequence_gaussDelta`, `dlmf_1_17_4_gaussDelta` | `integral_gaussian`, `integral_gaussian_Ioi` |
| 1.17.6–1.17.7 | `gaussPeak` (`2√(n/π) e^{−(n−N)t²}`), `tendstoUniformlyOn_gaussPeak`, `tendsto_setIntegral_Ioi_gaussDelta`, `tendsto_integral_gaussDelta` (`→ ½φ(a−) + ½φ(a+)`), `dlmf_1_17_6`, `dlmf_1_17_6_growth` (`φ = O(e^{αx²})`), `dlmf_1_17_7` (piecewise continuous) | `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux`, `integrableOn_peak_smul_of_integrableOn_of_tendsto`, `LocallyIntegrable.integrable_of_isBigO_cocompact`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` |
| 1.17.8 | `dlmf_1_17_8` (Fourier inversion, `Section17Integral.lean`) | — (§1.14 `dlmf_inversion`) |
| 1.17.9–1.17.11 | `dlmf_1_17_9_not_integrable` (inner integral diverges), `dlmf_1_17_10`, `fourierGaussDelta`, `dlmf_1_17_11` (= `gaussDelta`, all `n`), `dlmf_1_17_9` (generalized integral under 1.17.6 hypotheses) | `fourierIntegral_gaussian`, `Complex.ofReal_cpow` |
| 1.17.12 | `dlmf_1_17_12` (distributional limit of 1.17.11), `dlmf_1_17_12_tempered` (= 1.16.43) | — |
| 1.17.12_1–1.17.12_2 | `dlmf_1_17_12_1`, `dlmf_1_17_12_2` (cosine/sine inversion 1.14.11, 1.14.12) | — |
| 1.17.14 (`ℓ = 0`) | `mul_sinc`, `dlmf_1_17_14_zero_integrand`, `dlmf_1_17_14_zero` (`𝗃₀ = sinc`, reduces to 1.17.12_2) | `Real.sinc` |
| 1.17.13–1.17.16 | **Deferred**: Hankel (Bessel `J_ν`), spherical Bessel `ℓ ≥ 1`, Coulomb, Airy completeness | — |
| 1.17.17 | `dlmf_1_17_17` (Fourier summation formula, `Section17Series.lean`) | — (§1.8 `dlmf_1_8_3`) |
| 1.17.18 | `dlmf_1_17_18_not_summable`, `dlmf_1_17_18_not_tendsto` (series and symmetric partial sums diverge) | `Summable.tendsto_cofinite_zero` |
| 1.17.19–1.17.20 | `dirichletDelta`, `sum_Icc_cexp_eq_halfDirichlet`, `dirichletDelta_eq`, `dlmf_1_17_20`, `integral_dirichletDelta_mul` (= Fourier partial sum), `dlmf_1_17_19_dirichlet` (1.8.11 conditions), `dlmf_1_17_19` (differentiable at `a`). **Discrepancy:** false for merely continuous periodic `φ`: `dlmf_1_17_19_counterexample` (`dirichletFunctional`, `le_norm_dirichletFunctional` ≥ `Lₙ/2 − 1`, `tendsto_lebesgueConst_atTop`, Banach–Steinhaus) | `banach_steinhaus`, `ContinuousLinearMap.le_opNorm` |
| 1.17.21 | `dlmf_1_17_21` (Dirac comb: `∫ δₙ(x−a)φ → ∑ₘ φ(a+2πm)` for test functions, via Poisson 1.8.14) | `tendsto_atTop_finset_of_monotone` |
| 1.17.22–1.17.25 | **Deferred**: Legendre, Laguerre, Hermite, spherical-harmonic completeness (Chs. 14, 18) | — |

### §1.18 Linear Second Order Differential Operators and Eigenfunction Expansions (`Azurite/DLMF/Chapter1/Section18*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| §1.18(i) axioms, 1.18.1 | `dlmfInner` (`⟨u, v⟩ = ⟪v, u⟫`), `dlmf_1_18_i_linear`, `dlmf_1_18_i_conj`, `dlmf_1_18_i_nonneg`, `dlmf_1_18_i_definite`, `dlmfInnerCore` (DLMF axioms ⇒ `InnerProductSpace.Core`), `dlmf_1_18_1` (`Section18.lean`) | `InnerProductSpace.Core`, `inner_self_eq_norm_sq_to_K` |
| §1.18(i) definitions | `IsNormalized`, `IsOrthogonalDLMF`, `IsOrthonormalSet` (↔ `Orthonormal`), `IsHilbertSpace` (↔ `CompleteSpace`) | `Metric.complete_of_cauchySeq_tendsto`, `cauchySeq_iff_tendsto_dist_atTop_0` |
| 1.18.2–1.18.5 | `dlmf_1_18_2` (Bessel), `IsCompleteOrthonormal`, `isCompleteOrthonormal_iff` (= `HilbertBasis`), `tsum_norm_sq_hilbertBasis`, `dlmf_1_18_4`; `IsSeparableDLMF`, `countable_of_orthonormal_subtype`, `isSeparableDLMF_iff` (↔ `SeparableSpace`) | `Orthonormal.tsum_inner_products_le`, `HilbertBasis.mkOfOrthogonalEqBot`, `exists_hilbertBasis`, `Set.PairwiseDisjoint.countable_of_isOpen`, `TopologicalSpace.IsSeparable.span` |
| 1.18.6–1.18.7 | `dlmf_1_18_6` (unique `v = ∑ cₙvₙ`, norm convergence) | `HilbertBasis.hasSum_repr_symm`, `memℓp_gen` |
| 1.18.8–1.18.10 | `dlmf_1_18_8`, `dlmf_1_18_9`, `dlmf_1_18_10` (`V ≃ₗᵢ ℓ²`) | `lp.norm_rpow_eq_tsum`, `lp.inner_eq_tsum`, `HilbertBasis.mk`, `nonempty_denumerable` |
| 1.18.11–1.18.12, §1.18(ii) | `dlmf_1_18_11`, `dlmf_1_18_ii_identify`, `dlmf_1_18_ii_identify_Lp`, `dlmf_1_18_ii_separable`, `dlmfInner_Lp_eq`, `dlmf_1_18_12`, `dlmf_1_18_ii_dx` (`Section18L2.lean`; `L²(X, dα) = Lp ℂ 2 (α.measure.restrict X)`) | `memLp_two_iff_integrable_sq_norm`, `L2.inner_def`, `Lp.SecondCountableTopology`, `Real.volume_eq_stieltjes_id` |
| 1.18.13–1.18.16 | `dlmf_1_18_13`, `integral_norm_sq_Lp`, `dlmf_1_18_14`, `coeFn_finsetSum_Lp`, `dlmf_1_18_16` (mean convergence) | `HilbertBasis.hasSum_repr`, `Lp.coeFn_smul` |
| 1.18.17–1.18.20 | `kernelPartial`, `dlmf_1_18_17_partial`, `dlmf_1_18_17` (partial-kernel form), `dlmf_1_18_19` (weak completeness relation), `dlmf_1_18_20` | `HilbertBasis.hasSum_inner_mul_inner`, `L2.integrable_inner`, `orthonormal_iff_ite` |
| 1.18.21–1.18.22, §1.18(iii) | `IsLinearOperator` (↔ `LinearMap`), `opNormDLMF`, `IsBoundedOperator`, `norm_le_of_bddAbove_sphere`, `isBoundedOperator_iff` (↔ continuous), `opNormDLMF_eq`, `dense_iff_seq`, `IsBoundedOn`, `existsUnique_extension` (`Section18Operators.lean`) | `ContinuousLinearMap.sSup_sphere_eq_norm`, `ContinuousLinearMap.extend`, `Continuous.ext_on` |
| 1.18.23–1.18.24 | `dlmf_1_18_23`, `eq_adjoint_of_dlmf`, `isSelfAdjoint_iff_dlmf`, `IsSymmetricOn`, `IsSymmetricOn.eigenvalue_real`, `dlmf_1_18_24`, `eigenSubmodule`, `orthogonalize_eigenfunctions` (Gram–Schmidt) | `ContinuousLinearMap.eq_adjoint_iff`, `gramSchmidtNormed_orthonormal`, `span_gramSchmidtNormed_range` |
| 1.18.25–1.18.27 | `dlmf_1_18_26` (IBP twice), `dlmf_1_18_27` (Dirichlet), `IsDirichletC2`, `dlmf_1_18_iii_symmetric` (`Section18DiffOp.lean`). **Discrepancy:** `𝒟(T*) ≠ 𝒟(T)`, `T` not self-adjoint: `InAdjointDomainDirichlet`, `dlmf_1_18_iii_not_selfAdjoint` (`g = ((x−c)|x−c| − d(x−c))/2`) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `Measure.eqOn_of_ae_eq`, `Filter.EventuallyEq.deriv` |
| 1.18.28, §1.18(iv) | `schrodingerOp`, `wronskianConj`, `schrodinger_lagrange_identity`, `hasDerivAt_wronskianConj`, `dlmf_1_18_iv_green` (Green's formula), `IsC2c`, `dlmf_1_18_iv_symmetric` (symmetric on `C²_c(X)`), `c2cSubmodule`, `dlmf_1_18_iv_dense` (dense in `L²(X)`), `schrodinger_eigen_relation`, `wronskianConj_dirichlet`, `schrodinger_eigenvalue_real`, `schrodinger_eigen_orthogonal` (`Section18Schrodinger.lean`) | `integral_eq_zero_of_hasDerivAt_of_integrable`, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `Submodule.topologicalClosure_eq_top_iff`, `HasDerivAt.star` |
| 1.18.29–1.18.33, §1.18(v) general | `eigenCoeff` (`f̂(λₙ)`), `eigenCoeff_eq_repr`, `dlmf_1_18_29`, `dlmf_1_18_30` (weak completeness), `dlmf_1_18_31`, `dlmf_1_18_33` (`Section18Spectral.lean`) | `HilbertBasis.hasSum_repr`, `HilbertBasis.hasSum_inner_mul_inner` |
| 1.18.34–1.18.35 | `dlmf_1_18_34` (`Tf = ∑ λₙ f̂ₙ φₙ`, symmetric `T`), `memℓp_mul_of_bound`, `norm_mul_lp_le`, `multLp`, `spectralCalculus` (`F(T)`, bounded `F`), `eigenCoeff_spectralCalculus`, `dlmf_1_18_35`, `spectralCalculus_basis`, `norm_spectralCalculus_le`; kernel forms `tendsto_integral_sub_partialSum`, `kernelWeighted`, `sum_eq_integral_kernelWeighted`, `dlmf_1_18_34_kernel`, `dlmf_1_18_35_kernel` | `LinearMap.mkContinuous`, `lp.norm_rpow_eq_tsum` |
| 1.18.36–1.18.38, Example 1 | `L2pi`, `sinFun`, `cosNorm`, `cosFun`, `expFun`, `dlmf_1_18_36`, `dlmf_1_18_37`, `dlmf_1_18_37_eigen`, `dlmf_1_18_38` (eigen + boundary conditions), `dlmf_1_18_38_multiplicity`; trig integrals `integral_sin_mul_sin_pi`, `integral_cos_mul_cos_pi`, `integral_exp_mul_conj_pi`; `orthonormal_sinVec/cosVec/expVec`; completeness `hasSum_norm_sq_expVec` (period-π Fourier), `hasSum_norm_sq_sinVec`/`cosVec` (odd/even extension + 1.8.5), `exists_hilbertBasis_sinVec/cosVec/expVec` (`Section18Example1.lean`) | `hasSum_sq_fourierCoeffOn`, `fourierCoeffOn_eq_integral`, `integral_exp_mul_complex`, `IntervalIntegrable.iff_comp_neg`, `Lp.stronglyMeasurable` |
| 1.18.39–1.18.40 | `dlmf_1_18_39` (weak completeness relation), `dlmf_1_18_40_coeff`, `dlmfInner_expVec_eq_fourierCoeffOn` (= 1.8.4, period π), `dlmf_1_18_40`; `hasSum_sinVec`, `hasSum_cosVec` (1.8.1–1.8.2 from Cases 1–2) | `HilbertBasis.hasSum_repr` |
| 1.18.41, Hermite | `physHermite` (physicists' `Hₙ`), `derivative_physHermite_succ`, `physHermite_ode`, `natDegree_leadingCoeff_physHermite`, `gaussFun`, `hasDerivAt_gaussFun`, `dlmf_1_18_41` (eigenvalue `2n+1`) (`Section18Hermite.lean`) | `Polynomial.degree_sub_lt_left`, `Polynomial.leadingCoeff_sub_of_degree_lt` |
| 1.18.42 | polynomial×Gaussian lemmas (`integrable_poly_gauss`, `tendsto_poly_gauss`), `integral_mul_physHermite_succ` (IBP on ℝ), `integral_physHermite_mul` (`√π 2ⁿ n! δ`), `L2R`, `gaussVec`, `hermiteNorm`, `hermitePhi`, `hermiteVec`, `orthonormal_hermiteVec`; completeness `dlmfInner_gaussVec_eq_zero` (moments), `memLp_exp_abs`, `eq_zero_of_forall_dlmfInner_hermiteVec` (exp series + Fourier uniqueness), `exists_hilbertBasis_hermiteVec` | `integral_mul_deriv_eq_deriv_mul`, `integrable_rpow_mul_exp_neg_mul_sq`, `integral_gaussian`, `integral_tsum_of_summable_integral_norm`, `NormedSpace.expSeries_div_hasSum_exp`, `integrable_cexp_quadratic'`; §1.14 `fourierInv_fourier_ae` |
| 1.18.43 | `hermiteKernel`, `hermiteKernel_eq`, `tendsto_integral_sub_partialSum_L2R`, `dlmf_1_18_43` (mean convergence); boundary conditions `dlmf_1_18_v_hermite_boundary` | — |
| 1.18.44–1.18.48, §1.18(vi) general | `L2sigma`, `contCoeff` (`f̂ = U f`, 1.18.47), `dlmfInner_map`, `dlmf_1_18_44`, `dlmf_1_18_45` (weak), `dlmf_1_18_46`, `dlmf_1_18_48`, `dlmf_1_18_48_L2` (`Section18Continuous.lean`) | `LinearIsometry.inner_map_map` |
| 1.18.49–1.18.52 | `InDomT`, `opT`, `dlmf_1_18_49`, `opT_symmetric`, `opT_no_eigenvalue`; `truncMul`, `multOp`, `coeFn_multOp`, `spectralOp` (`F(T)`), `dlmf_1_18_50`, `dlmf_1_18_51`; `resDist`, `resolvent`, `dlmf_1_18_52`, `resolvent_sub_opT`, `inDomT_resolvent` | `MemLp.of_le_mul`, `Lp.norm_le_mul_norm_of_ae_le_mul` |
| 1.18.53 | `sub_resolventFun`, `dlmf_1_18_53` (Stieltjes inversion a.e., Poisson integral of `|f̂|²`) | — (§1.14 `ae_tendsto_poissonKernel`) |
| 1.18.54 | `tendsto_tail_pK`, `tendsto_poissonInt_of_continuousAt`, `one_div_sokhotski`, `dlmf_1_18_54` (Sokhotski–Plemelj, integrable `f`, continuous at `x`, `ℋf(x)` exists) (`Section18Plemelj.lean`). **Discrepancy:** `f ∈ C(X)` insufficient: `dlmf_1_18_54_counterexample` (`f = 1` on `[0,∞)`) | `tendsto_integral_peak_smul_of_integrable_of_tendsto`, `not_integrableOn_Ioi_inv`; §1.14 `dlmf_1_14_42` |
| 1.18.55–1.18.58, §1.18(vi) Example 1 | **Deferred**: Bessel–Hankel transform (Bessel functions `J_ν`, Ch. 10), like 1.17.13 | — |
| 1.18.59, Example 2 | `cosMoment`, `sinMoment`, `dlmfFourier_eq_moments`, `dlmf_1_18_59_partial` (= symmetric Fourier inversion), `dlmf_1_18_59` (BV, via 1.14.3), `dlmf_1_18_59_smooth` (C¹, via 1.14.4), `dlmf_1_18_59_even`/`_odd` (cosine/sine pairs) (`Section18SinCos.lean`) | `integral_neg_eq_self`, `integral_comp_neg_Ioi` |
| §1.18(vii) | **Descriptive (references only)**: band spectra for periodic `q`, Anderson localization, the almost Mathieu equation; no equations. Not formalized | — |
| 1.18.60–1.18.65, §1.18(viii) | `hatC`, `hatP`, `pointFun`, `contSuper`, `dlmfInner_U`, `dlmfInner_withLp`, `dlmfInner_lp`, `hatP_eq`, `dlmf_1_18_60` (weak), `dlmf_1_18_61`, `dlmf_1_18_62` (weak), `dlmf_1_18_63` (weak), `dlmf_1_18_64`, `dlmf_1_18_65` (`Section18Mixed.lean`; `U : V ≃ₗᵢ WithLp 2 (L²σ_c × ℓ²(ι))`) | `WithLp.prod_inner_apply`, `WithLp.prod_norm_sq_eq_of_L2`, `lp.inner_single_left`, `lp.hasSum_single`, `prodContinuousLinearEquiv` |
| 1.18.66 | `truncW`, `diagOp`, `diagOp_apply`, `mixedSpectralOp`, `dlmfInner_mixedSpectralOp` (analog of 1.18.51), `mixedResolvent`, `dlmf_1_18_66`; poles `norm_sub_ofReal_ge`, `tendsto_sub_ofReal_nhdsNE`, `dlmf_1_18_66_residue` (residue `|f̂(λₘ)|²` at isolated `λₘ < 0`); resonances/dilatation descriptive | `tendsto_tsum_of_dominated_convergence` (Tannery), `tendsto_integral_filter_of_dominated_convergence` |
| §1.18(viii) Example 1 | `wellFun`, `expShift`, `integral_expShift_mul_deriv_deriv`, `exists_radius_testFunction`, `dlmf_1_18_viii_delta_well` (δ-well eigenfunction `e^{−α\|x−a\|/2}`, eigenvalue `−α²/4`, distributional), `memLp_wellFun`, `delta_well_eigenvalue_neg`; `trialFun`, `kinetic_trialFun`, `tendsto_kinetic_trialFun`, `tendsto_potential_trialFun`, `dlmf_1_18_viii_trial` (`∫q < 0` ⇒ negative energy) (`Section18BoundState.lean`); **Simon's theorem** `dlmf_1_18_viii_simon` (continuous `q` supported in `[−R, R]`, `∫q ≤ 0`, `q < 0` somewhere ⇒ `κ > 0`, nonzero `ψ ∈ L²`, `−ψ″ + qψ = −κ²ψ`) by shooting: `simonU`, `simonG`, `simonG_k0_pos`, `simonG_zero_neg` (Jacobi identity), `exists_simonG_eq_zero`, `simonU_left`/`simonU_right` (exponential tails) (`Section18Simon.lean`), on linear-ODE infrastructure `volterraIter`, `odeSol`, `odeSolD`, `continuous_odeSol` (joint in parameter), `hasDerivAt_odeSol(D)`, `ode2_eq_zero(_left/_right)` (Grönwall uniqueness) (`Section18ODE.lean`). 2D analog not formalized; DLMF omits Simon's decay hypothesis (compact support used) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `Measure.integral_comp_mul_left`, `continuousOn_tsum`, `Continuous.integral_hasStrictDerivAt`, `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`, `intermediate_value_Icc`, `IsLocalMin.hasDerivAt_eq_zero` |
| 1.18.67, §1.18(viii) Example 2 | `radialOp` (`ℒ_ℓ`); `laplacianXYZ`, `deriv_deriv_line`, `laplacianXYZ_radial` (`Δ(g(r)(x+iy)^ℓ) = (g″ + 2(ℓ+1)g′/r)(x+iy)^ℓ`), `dlmf_1_18_67` (`−½Δψ + Vψ = (ℒ_ℓ u)/r^{ℓ+1} · (x+iy)^ℓ` for `ψ = u/r^{ℓ+1} · (x+iy)^ℓ`), `dlmf_1_18_67_eigen` (`Section18Radial3D.lean`); `radialBoundary`, `hasDerivAt_radialBoundary` (Hardy-type identity), `radial_energy_le`, `radial_eigen_eq_zero` (`V ≥ −1/(8r²)` ⇒ no negative eigenvalue), `tendsto_radialBoundaryForm_of_hasDerivAt`, `shallowWell`, `dlmf_1_18_viii_shallow_well` (a well with no bound state for any `ℓ`), `radial_L2_weight` (`Section18Radial.lean`); Coulomb `V = −1/r`: `coulombCoeff`, `coulombPoly`, `coulombResidual_eq_zero`, `coulombFun`, `radialOp_coulombFun`, `memLp_coulombFun`, `coulombEigenvalue`, `dlmf_1_18_viii_coulomb` (eigenvalues `−1/(2n²)`, `n ≥ ℓ+1`, accumulating at `0`), `integral_coulombFun_mul` (orthogonality) (`Section18Coulomb.lean`). Only `Y_ℓ^ℓ` (`(x+iy)^ℓ`) in the reduction; deep-well existence and the Bethe–Salpeter transform pair not formalized. DLMF imprecision: the measure `r² dr` belongs to `R = u/r`, not to the `u` of 1.18.67 (measure `dr`) | `Polynomial.coeff_X_pow_mul'`, `Polynomial.coeff_derivative`, `integrable_of_isBigO_exp_neg`, `intervalIntegral_tendsto_integral_Ioi`, `HasDerivAt.ofReal_comp`, `HasDerivAt.comp_ofReal` |
| 1.18.68–1.18.70, §1.18(ix) Self-Adjoint Operators | `dlmf_1_18_68` (adjoint domain = bounded `sup |⟨Tv,w⟩|`), `dlmf_1_18_69`, `IsSymmetricDLMF` (1.18.70), `IsSymmetricDLMF.le_adjoint` (`T ⊂ T*`), `le_adjoint_adjoint` (`T ⊂ T** ⊂ T*`), `adjoint_antitone`, `adjoint_adjoint_adjoint`, `IsEssentiallySelfAdjointDLMF`, `isEssentiallySelfAdjoint_iff` (`Section18Unbounded.lean`) | `LinearPMap.adjoint`, `LinearPMap.adjoint_isFormalAdjoint`, `IsFormalAdjoint.le_adjoint`, `LinearPMap.isSelfAdjoint_def` |
| §1.18(ix) Spectrum of an Operator | `shiftOp`, `ResolventBounded`, `resolventSetDLMF`, `spectrumDLMF`, point/continuous/residual parts, `mem_pointSpectrumDLMF_iff`, `spectrumDLMF_eq_union`, `spectrumDLMF_disjoint`, `spectrumDLMF_toPMap` (= Banach-algebra spectrum), `spectrumDLMF_bounded`, `IsSelfAdjoint.mem_resolventSetDLMF_iff`, `IsSelfAdjoint.spectrumDLMF_real` (real, closed, no residual), `IsSymmetricDLMF.inner_eq_zero_of_eigen`, `eigenspaceDLMF`, `IsSelfAdjoint.exists_hilbertBasis_eigenspace` (`Section18OpSpectrum.lean`) | `spectrum.isCompact`, `ContinuousLinearMap.isUnit_iff_bijective`, `AntilipschitzWith.isClosed_range`, `Submodule.topologicalClosure_eq_top_iff`, `exists_hilbertBasis` |
| §1.18(ix) Self-adjoint extensions of a symmetric Operator | `deficiencySpace` (`N_z`), `deficiencySpace_eq_orthogonal`, `dlmf_1_18_ix_deficiency_const` (`dim N_z` constant per half-plane), `deficiencyIndices` (`Section18Deficiency.lean`); `isClosed_range_shiftOp`, `vonNeumann_decomp`/`vonNeumann_unique` (`D(T*) = D(T**) ⊕ N_i ⊕ N_{−i}`), `boundaryForm`, `vonNeumannExt`, `vonNeumannExt_isSelfAdjoint_iff`, `eq_vonNeumannExt_of_selfAdjoint` (Cayley map), `exists_selfAdjoint_ext_iff` (`⇔ N_i ≅ N_{−i}`), `exists_selfAdjoint_ext_iff_finrank`, `rank_eq_of_selfAdjoint_ext` (`Section18VonNeumann.lean`). DLMF imprecisions: `U` must be onto; `n₊ = n₋` must mean Hilbert dimension | `Submodule.orthogonal_orthogonal_eq_closure`, `Submodule.exists_add_mem_mem_orthogonal`, `LinearPMap.adjoint_isClosed`, `IsLocallyConstant.apply_eq_of_preconnectedSpace`, `stdOrthonormalBasis` |
| §1.18(ix) Self-adjoint extensions of (1.18.28) and the Weyl alternative | `minOp` (ℒ on `C²_c(X)` ⊂ `L²(X)`), `isSymmetricDLMF_minOp`, `dlmf_1_18_ix_maxDomain` (`𝒟(ℒ*)` = distributions `ℒw ∈ L²`) (`Section18WeylMin.lean`); `integral_primitive_mul_deriv` (Fubini IBP), `ae_eq_affine_of_integral_deriv_deriv` (2nd-order du Bois-Reymond), `weak_regularity` (`Section18WeylReg.lean`); `dlmf_1_18_ix_deficiency_iff` (`N_z` = ordinary `L²` solutions), `dlmf_1_18_ix_finrank_le` (`dim ∈ {0,1,2}`), `dlmf_1_18_ix_conj_iff`, `dlmf_1_18_ix_deficiency_eq`, `dlmf_1_18_ix_exists_selfAdjoint` (`Section18WeylDef.lean`); complex ODE existence `exists_solution_on` (`Section18WeylODE.lean`); `dlmf_1_18_ix_weyl_alternative` (`n₁, n₂ ∈ {1,2}`) (`Section18WeylEnd.lean`); `finrank_eq_two_iff` (limit circle ⇔ all solutions `L²`), `dlmf_1_18_ix_index_indep` (independent of `c`, `z`), `exists_decomp_of_finrank_one`, `side_identity`, `dlmf_1_18_ix_index_formula` (`n = n₁ + n₂ − 2`) (`Section18WeylLP.lean`). Boundary values (1.18.71): `IsBoundaryValue`, `maxRep` (`C¹` representative), `graphBounded_of_tendsto` (Banach–Steinhaus), `dlmf_1_18_71_left`/`_right` (limits `α f + β f′` are boundary values at `a`/`b`) (`Section18WeylBV.lean`); cut-offs `mem_adjoint_cutoff`, `dlmf_1_18_ix_boundary_values_LP_left`/`_right` (`n₁ = 1` ⇒ no nonzero boundary values at `a`) (`Section18WeylBV2.lean`); Lagrange identity, `wronskianBV`, Plücker identity, `boundaryValuesLeft`/`Right`, `dlmf_1_18_ix_boundaryValuesLeft_LC` (`n₁ = 2` ⇒ two-dimensional class) (`Section18WeylLC.lean`); `dlmf_1_18_ix_ext_LP_LP` (`ℒ*` unique s.a. extension), `dlmf_1_18_ix_ext_LC_LP`/`_LP_LC` (s.a. extensions = `ker B₁` resp. `ker B₂`) (`Section18WeylExt.lean`). DLMF error: with limit circle at both ends not every s.a. extension is given by separated conditions `B₁ = 0, B₂ = 0` (D–S Cor. XIII.2.31 requires separated conditions); counterexample `dlmf_1_18_ix_ext_LC_LC_counterexample` (`q = 0` on `(0,1)`, extension through `e^{2πix}`) (`Section18WeylCounter.lean`) | `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `ContDiffBump.normed`, `integral_integral_swap`, `Submodule.mkQ`, `rank_eq_of_equiv_equiv`, `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` |

## Chapter 2: Asymptotic Approximations

### §2.1 Definitions and Elementary Properties (`Azurite/DLMF/Chapter2/Section1*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| §2.1(i) setting | `approachIn` (`x → c` in `𝐗` as `𝓝[𝐗 ∖ {c}] c`), `approachIn_neBot_iff` (proper iff `c` is a limit point), `approachIn_univ` | `AccPt`, `nhdsWithin` |
| 2.1.1–2.1.3 | `AsympEqDLMF`, `IsLittleODLMF`, `IsBigODLMF` (literal ratio definitions along any filter), `IsBigOOnDLMF` (`O` on a whole set); `dlmf_2_1_1`, `dlmf_2_1_2`, `dlmf_2_1_3`, `dlmf_2_1_3_on` (= Mathlib's when `φ` is eventually nonzero) | `isEquivalent_iff_tendsto_one`, `isLittleO_iff_tendsto'`, `isBigO_iff_div_isBoundedUnder` |
| 2.1.4–2.1.7 | `dlmf_2_1_4` (`tanh x ∼ x`), `dlmf_2_1_5`, `dlmf_2_1_5_sector` (`\|ph x\| ≤ ½π − δ`), `dlmf_2_1_5_ray`, `dlmf_2_1_5_not_halfPlane` (fails in `\|ph x\| < ½π`, along `1 + it`), `dlmf_2_1_6` (bound `1` on all of `ℤ`), `dlmf_2_1_7` | `hasDerivAt_iff_tendsto_slope`, `Complex.cos_arg`, `tendsto_norm_atTop_iff_cobounded`, `Real.sin_add_int_mul_pi`, `Real.abs_sin_le_abs` |
| 2.1.8–2.1.9 | `dlmf_2_1_8` (DLMF's partial-sum convergence near `0`; bounded terms at one point + geometric domination), `dlmf_2_1_9` | `Filter.Tendsto.bddAbove_range`, `tsum_of_norm_bounded`, `Complex.norm_exp_sub_one_sub_id_le` |
| 2.1.10 | `littleOSet`, `bigOSet`; `dlmf_2_1_10_1` (`o ⊆ O`), `dlmf_2_1_10_2` (`o + o ⊆ o`), `dlmf_2_1_10_1_not_reversible`. DLMF imprecision: the second relation is reversible (`dlmf_2_1_10_2_reverse`, `dlmf_2_1_10_2_eq`) | `Set.mem_add` |
| 2.1.11 | `dlmf_2_1_11` (`f` continuous on `[a, ∞)`, complex `ν`); `isLittleO_integral_Ioi` (integrating `o` over tails) (`Section1Integration.lean`) | `integral_Ioi_cpow_of_lt`, `integral_Ioi_rpow_of_lt`, `integrableOn_Ioi_cpow_of_lt` |
| 2.1.12 | `dlmf_2_1_12_const` (`ℜν < −1`: tends to a constant `L`, `∼ L` if `L ≠ 0`), `dlmf_2_1_12_log` (`ν = −1`), `dlmf_2_1_12_pow` (`ℜν > −1`); `isLittleO_intervalIntegral` (integrating `o` over divergent integrals) | `integral_cpow`, `integral_rpow`, `integral_inv_of_pos`, `intervalIntegral_tendsto_integral_Ioi` |
| §2.1(ii) Ritt's theorem | `sectorDLMF`, `closedSectorDLMF`, `closedBall_subset_sectorDLMF`, `ritt_bound` (Cauchy estimate), `dlmf_2_1_ii_ritt` (`O`), `dlmf_2_1_ii_ritt_littleO` (`o`) (`Section1Ritt.lean`) | `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `Complex.arg_mul`, `DifferentiableOn.diffContOnCl_ball` |
| 2.1.13–2.1.15 | `IsAsympExpansionDLMF` (literal), `HasPowExpansion` (expansion in powers of any `y → 0`, via `PowerSeries.trunc`), `isAsympExpansionDLMF_iff`, `dlmf_2_1_15`, `dlmf_2_1_iii_unique` (`Section1Expansion.lean`) | `PowerSeries.trunc_trunc_mul_trunc`, `Polynomial.X_pow_dvd_iff`, `tendsto_inv₀_cobounded` |
| 2.1.16 | `IsAsympExpansionAtDLMF`, `isAsympExpansionAtDLMF_iff`, `dlmf_2_1_16_iff_tendsto`, `dlmf_2_1_iii_unique_at` | |
| §2.1(iii) prose | `dlmf_2_1_iii_convergent` (convergent series), `dlmf_2_1_iii_add`/`_sub`/`_const_mul`/`_mul` (Cauchy product)/`_div` (`b₀ ≠ 0`); `dlmf_2_1_iii_deriv` (termwise differentiation in properly interior closed sectors, via Ritt) and `dlmf_2_1_iii_deriv_counterexample` (`e^{−x} sin(eˣ)`: null expansion, derivative has none). Substitution, logarithms and powers ("compare Olver") and the remark on several expansions are not formalized | `PowerSeries.mul_inv_cancel`, `Summable.sum_add_tsum_nat_add` |
| 2.1.17 | `dlmf_2_1_17` (`0`, `e^{−z}`, `e^{−√z}` in `\|ph z\| ≤ ½π − δ`) | `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` |
| §2.1(iii) existence | `dlmf_2_1_iii_exists_sector` (any sector `\|ph(ze^{−iθ})\| < ω ≤ π`), `dlmf_2_1_iii_exists_real` (positive real axis, real analytic), `dlmf_2_1_iii_exists_at` (2.1.16, sector with vertex `c`): infinitely many analytic functions with given coefficients (Ritt's construction `∑ aₛz^{−s}(1 − e^{−βₛ(ze^{−iθ})^{1/4}})` + null functions `e^{−(ze^{−iθ})^{1/4}}`) (`Section1BorelRitt.lean`) | `differentiableOn_tsum_of_summable_norm`, `norm_image_sub_le_of_norm_deriv_le_segment_01'`, `AnalyticAt.restrictScalars`, `Set.infinite_of_injective_forall_mem` |
| §2.1(iv) sectors | `dlmf_2_1_iv_sector` (closed sector `α ≤ ph x ≤ β`: 2.1.13 uniform in `ph x`) (`Section1Uniform.lean`) | `Complex.norm_mul_exp_arg_mul_I`, `Complex.arg_real_mul` |
| 2.1.18 | `IsUnifAsympExpansionDLMF`, `IsUnifAsympExpansionAtDLMF` (finite `c`), `.isAsympExpansion`, `.isAsympExpansionAt`; `dlmf_2_1_iv_not_uniform` (`e^{−x/u}`) | |
| 2.1.19–2.1.21 | `IsAsympScaleDLMF`, `IsGenAsympExpansionDLMF`, `IsUnifGenAsympExpansionDLMF`; `isAsympExpansionDLMF_iff_gen` (Poincaré = scale `x^{−s}`), `term_isBigO`, `remainder_isLittleO`, `isGenAsympExpansion_trivial` (non-uniqueness) (`Section1Generalized.lean`) | |
| §2.1(v) prose | `dlmf_2_1_v_mul_counterexample` (multiplication fails: scale `1, x⁻¹, x⁻³, x⁻⁴, …`), `dlmf_2_1_v_convergent_wrong_sum` (`e^{−x} ∼ 0`, series converges to `0`) | |

### §2.2 Transcendental Equations (`Azurite/DLMF/Chapter2/Section2*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 2.2.1–2.2.2 | `rootDLMF`, `rootDLMF_spec` (unique root for `y > f(a)`), `tendsto_rootDLMF`, `dlmf_2_2_2` (`x(y) ∼ y`). DLMF imprecision: continuity on `(a, ∞)` alone is not enough, `f` must be continuous at `a` (`dlmf_2_2_1_counterexample`) (`Section2.lean`) | `intermediate_value_Ioo`, `StrictMonoOn.injOn` |
| 2.2.3–2.2.6 | `tlogF`, `tlogT`, `dlmf_2_2_3`, `dlmf_2_2_4`, `dlmf_2_2_5`, `dlmf_2_2_6` (via `\|√(1+u) − 1 − u/2\| ≤ u²/2`) | `strictMonoOn_of_deriv_pos`, `Real.tendsto_pow_log_div_mul_add_atTop` |
| Lagrange's formula | `lagrange_inversion` (formal, `n[wⁿ]H(Ψ) = [v^{n−1}]H′φⁿ`, not in Mathlib), `lagrangeF`, `inv_subst_eq_lagrangeF` (`Section2Lagrange.lean`) | `PowerSeries.derivative_subst`, `PowerSeries.derivative_inv'`, `PowerSeries.eq_X_pow_mul_shift_add_trunc` |
| 2.2.7–2.2.8 | `dlmf_2_2_8` (reversion: `x − y ∼ −F₀ − F₁y⁻¹ − ⋯`), `dlmf_2_2_8_coeff` (`sFₛ` is the `x⁻¹` coefficient of `f(x)ˢ`); `exists_reversion_series`, `HasPowExpansion.div_var`, `.pow`, `isBigO_eval_sub_eval`, `coeff_mul_subst_trunc` (`Section2Reversion.lean`). Validity in `ℂ` and the Airy applications are references only | `PowerSeries.substInvOfIsUnit`, `PowerSeries.subst_substInvOfIsUnit_right`, `Polynomial.sub_dvd_eval_sub`, `geom_sum₂_mul` |

### §2.3 Integrals of a Real Variable (`Azurite/DLMF/Chapter2/Section3*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 2.3.1–2.3.2 | `laplaceIntegral` (improper `lim ∫₀^R`), `laplaceTerm`, `dlmf_2_3_2` (convergence for large `x`, `q` smooth on `(−δ, δ)`, `q` integrable on each `[0, R]`); `laplaceFin_iter` (parts on `[0, δ/2]`), `laplace_tail_le` (tail `O(e^{−(x−x₀)b})` by parts against the primitive of `e^{−x₀t}q`) (`Section3Laplace.lean`) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `intervalIntegral.continuousOn_primitive_interval'` |
| 2.3.3 | `sigmaDLMF`, `dlmf_2_3_3` (error `≤ \|q⁽ⁿ⁾(0)\|/(xⁿ(x − σₙ))`, needs `q⁽ⁿ⁾(0) ≠ 0`); `laplace_error_le` (any `σ` with `\|q⁽ⁿ⁾(t)\| ≤ \|q⁽ⁿ⁾(0)\|e^{σt}`), `iteratedDeriv_growth`, `laplaceIntegral_eq_integral`, `dlmf_2_3_2_of_sigma` | `integral_Ioi_mul_deriv_eq_deriv_mul`, `integral_exp_mul_Ioi`, `integrable_of_isBigO_exp_neg` |
| 2.3.4 | `fourierTerm`, `invPowScale`, `dlmf_2_3_4` (generalized expansion, scale `x^{−(s+1)}`), `dlmf_2_3_4_error` (`≤ x⁻ⁿ 𝒱_{a,b}(q⁽ⁿ⁻¹⁾)`); `fourier_ibp_iter` (`Section3Fourier.lean`) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` |
| 2.3.5 | `fourierIoiIntegral`, `fourierTermIoi`, `dlmf_2_3_5` (uniform convergence as `TendstoUniformlyOn` of the partial integrals), `dlmf_2_3_5_error`; `not_tendsto_exp_I_mul` (boundary terms at `∞` vanish) | `TendstoUniformlyOn`, `tendsto_nhds_unique` |
| 2.3.6 | `dlmf_2_3_6` (= `dlmf_1_4_34`) | |
| 2.3.7–2.3.8 | `watsonExp` (`αₛ = (s+λ)/μ`), `dlmf_2_3_8` (Watson's lemma for the improper `laplaceIntegral`; `q` measurable, integrable on each `[c, R]`, `c > 0`), `watson_bound`, `watson_near_zero` (general kernel `f(xt)` on `(0, b]`), `intervalIntegrable_zero_of_bound`, `laplace_tail_exists` (`Section3Watson.lean`) | `Real.Gamma_eq_integral`, `Real.GammaIntegral_convergent`, `integral_comp_mul_left_Ioi` |
| 2.3.9 | `dlmf_2_3_9` (scale `x^{−αₛ} ln x`, via `ln t = ln(xt) − ln x`), `hasDerivAt_Gamma_integral` (`Γ′(α) = ∫ u^{α−1} ln u e^{−u}`), `abs_log_le_rpow_add_rpow_neg` | `Complex.hasDerivAt_GammaIntegral`, `HasDerivAt.real_of_complex`, `Real.abs_log_mul_self_rpow_lt` |
| 2.3.10–2.3.12 | `dlmf_2_3_12` (`𝓜f` = Mathlib `mellin`; piecewise continuity weakened to measurability + local integrability), `mellin_ofReal_eq`, `eventually_exp_neg_mul_rpow_le_rpow_neg` (`Section3WatsonGeneral.lean`) | `mellin`, `integrableOn_rpow_mul_exp_neg_mul_rpow`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` |
| 2.3.13–2.3.15 | `dlmf_2_3_15` (conditions (a)–(c) on a range `S ⊆ (a, ∞)` containing some `(a, a + δ)`); `laplace_method_core` (`Section3LaplaceMethod.lean`: substitution `w = p(t) − p(a)` near `a` + `watson_near_zero`, exponentially small remainder); `laplace_p'_eventually_pos`, `laplace_p_tendsto` | `integral_image_eq_integral_abs_deriv_smul`, `integrableOn_image_iff_integrableOn_abs_deriv_smul`, `strictMonoOn_of_deriv_pos`, `intermediate_value_Icc` |
| 2.3.16 | `dlmf_2_3_16` (as `t → a+`, equivalent to `v → 0+`); `laplaceMethod_formal` (`Q(μP + XP′)⁻¹P^{(μ−λ)/μ} = B(XP^{1/μ})`), `HasPowExpansion.change_var`, `rpowPS` + laws, `HasPowExpansion.rpow`, `HasPowExpansion.subst`, `lagrange_inversion_second` (`Section3LaplaceSeries.lean`, `Section3LaplaceCoeff.lean`) | `Real.one_add_rpow_hasFPowerSeriesAt_zero`, `PowerSeries.binomialSeries_add`, `PowerSeries.derivative_subst`, `PowerSeries.substInvOfIsUnit` |
| 2.3.17 | `dlmf_2_3_17` (`b₀, b₁, b₂` in DLMF's closed forms), via `coeff_rpowPS_one_two` | |
| 2.3.18 | `laplaceMethodCoeff` (`bₛ = (1/μ)[tˢ]QP^{−(λ+s)/μ}`), `dlmf_2_3_18` (the expansion of `q/v^{(λ+s)/μ}` in `(t − a)^{k−s−1}`; residue = coefficient of `(t − a)^{−1}`) | |
| 2.3.19–2.3.20 | `dlmf_2_3_20` (`∫₀^∞ e^{ixt}q(t) dt ∼ ∑ e^{(s+λ)πi/(2μ)} Γ((s+λ)/μ) aₛ x^{−(s+λ)/μ}`; `q` smooth on `(0, ∞)`, differentiated expansions at `0+`, uniform convergence with base point `1`); `spCutoff`, `spTail`, `spTail_ibp_iter`, `fourier_cutoff_model` (contour rotation `∫₀^∞ t^{α−1}e^{ixt}φ`), `fourier_remainder`, `powSumDeriv`, `integral_rpow_mul_cexp_neg_complex` (`Section3StationaryPhase.lean`) | `Real.smoothTransition`, `Complex.GammaIntegral`, `integral_comp_mul_left_Ioi` |
| 2.3.21 | `dopF` (`F ↦ F′/p′`), `statP` (`P₀ = q`, `Pₛ₊₁ = −(Pₛ/p′)′`... as DLMF's recursion), `DExp` (differentiated power expansions), `lopPS`, `statP_sub_bound` (`Section3StationaryExp.lean`); `exists_smooth_inverse`, `contDiffOn_statP_comp`, `iteratedDeriv_statP_comp` (`Section3StationaryInv.lean`) | `HasStrictDerivAt.to_local_left_inverse`, `contDiffOn_of_locally_contDiffOn` |
| 2.3.22–2.3.23 | `dlmf_2_3_23_d` (case `p(b) = ∞`: expansion with scale `e^{ixp(a)}x^{−αₛ}` of the improper integral, `upperEnd S` = filter `t → b−`), `dlmf_2_3_23` (case `p(b)` finite: two-index error bound `C(x^{−α_N} + x^{−(M+1)})` for the difference from both series), `statP_comp_expansion`, `fourier_endpoint_iter` (`Section3StationaryGeneral.lean`) | `intervalIntegral.integral_deriv_smul_comp'` |
| 2.3.24–2.3.28 | `BleisteinPhase` (`p` `C²` on an open interval `J ∋ 0, α`, `p′(α) = 0`, `p″(α) ≠ 0`, `(t − α)p′(t) > 0`), `bleisteinA` (`a` with the sign of `α`), `bleisteinW`, `dlmf_2_3_25`, `dlmf_2_3_26`, `dlmf_2_3_27`, `dlmf_2_3_27_unsigned_ne` (DLMF's unsigned `a` fails for `α < 0`), `dlmf_2_3_28` (`bleisteinDeriv`; `p″(α)^{1/2}` at `α` by L'Hôpital), `tendsto_bleisteinDeriv`, `strictMonoOn_W` (`Section3BleisteinChange.lean`) | `HasDerivAt.lhopital_zero_nhdsNE`, `strictMonoOn_of_deriv_pos`, `HasDerivAt.sqrt` |
| 2.3.29–2.3.31 | `bleisteinAmp` (`f` of 2.3.30), `dlmf_2_3_29` (any measurable `t`-range `S ⊆ J ∩ (0, ∞)`), `dlmf_2_3_29_Ioo` (`κ = w(k)`, `image_Ioo`), `integrableOn_iff`; 2.3.31 enters as a uniform Taylor remainder bound | `integral_image_eq_integral_abs_deriv_smul`, `integrableOn_image_iff_integrableOn_abs_deriv_smul`, `measurable_image_of_fderivWithin` |
| 2.3.32–2.3.33 | `bleisteinF` (`Fₛ`), `bleisteinG` (`\|τ − y\|ˢ` majorant), `dlmf_2_3_33` (term-by-term integral `= x^{−(λ+s)/2}Fₛ(a√x)`), `dlmf_2_3_32` (uniform in `α`: error after `n` terms `≤ K x^{−(λ+n)/2}Gₙ(a√x)`, given a uniform Taylor remainder bound and `κ ≥ a + δ`), `dlmf_2_3_32_even` (`Gₙ = Fₙ`), `dlmf_2_3_32_integral` (for `I(α, x)` via 2.3.29), `bleisteinF_zero` (`Fₛ(0) = 2^{(λ+s)/2−1}Γ((λ+s)/2)`) (`Section3Bleistein.lean`) | `integral_comp_mul_left_Ioi`, `integrableOn_rpow_mul_exp_neg_mul_sq`, `integral_rpow_mul_exp_neg_mul_rpow` |

### §2.4 Contour Integrals (`Azurite/DLMF/Chapter2/Section4*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 2.4.1 | `laplaceIntegralC` (improper `lim ∫₀^R e^{−zt}q`, complex `z`), `watsonExpC`, `watsonSector δ` (`\|ph z\| ≤ π/2 − δ`), `dlmf_2_4_1` (`λ` complex with `ℜλ > 0`; expansion along `cobounded ℂ ⊓ 𝓟 (watsonSector δ)`, principal powers); `integral_cexp_mul_cpow` (`∫₀^∞ e^{−zt}t^{a−1} = Γ(a)z^{−a}`, `ℜa, ℜz > 0`, by analytic continuation in `z`), `watsonC_near_zero`, `laplace_tail_le_complex`, `laplace_tail_exists_complex` (tail `≤ B(1 + \|z − x₀\|/(ℜz − x₀))e^{−(ℜz−x₀)b}`), `norm_cpow_neg_ge` (`Section4Watson.lean`) | `integral_cpow_mul_exp_neg_mul_Ioi`, `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, `norm_cpow_of_ne_zero`, `norm_mul_cos_arg` |
| 2.4.1 (rotation) | `WatsonSector` (`q` analytic in `α₁ < ph t < α₂`, 2.3.7 and `O(e^{σ\|t\|})` on closed subsectors), `laplaceRay q θ z` (transform along `ph t = θ`), `WatsonSector.dlmf_2_4_1_ray` (branch `e^{iθαₛ}(ze^{iθ})^{−αₛ}`), `dlmf_2_4_1_ray'` (principal powers for `\|ph z + θ\| ≤ π/2 − δ`), `laplaceRay_eq` (rotation of the path by Cauchy on the `exp`-image of a rectangle), `laplaceRay_zero`, `laplaceCont` (continuation along the ray adapted to `ph z`), `dlmf_2_4_1_sector` (2.4.1 in any closed sector inside `−α₂ − π/2 < ph z < −α₁ + π/2`, via a finite grid of rays), `laplaceCont_eq_laplaceIntegralC`; `WatsonSector.bound`, `cpow_polar`, `branch_eq`, `IsGenAsympExpansionDLMF.comp_tendsto'`/`scale_const_mul` (`Section4WatsonRotation.lean`) | `integral_boundary_rect_eq_zero_of_differentiableOn`, `intervalIntegral.integral_deriv_smul_comp'`, `arg_mul_cos_add_sin_mul_I`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` |
| 2.4.2–2.4.3 | `dlmf_2_4_2_continuousOn` (`Q = ℒq` continuous in `ℜz ≥ c` for `e^{−ct}q` integrable), `dlmf_2_4_2_analyticOnNhd` (analytic in `ℜz > c`), `dlmf_2_4_3` (inversion for `q` with continuous derivative on `(0, ∞)`, any `σ ≥ c`; via `dlmf_1_14_20_bv'`, the §1.14(iii) inversion under integrability of `e^{−σt}q` instead of exponential growth), `bromwichPartial`/`bromwich` (`(2πi)^{−1}∫_{σ−iη}^{σ+iη}` with `z = σ + iy`), `boundedVariationOn_Icc_of_deriv`, `bromwich_Gamma_cpow` (`ℒ^{−1}(Γ(α)z^{−α}) = t^{α−1}`) (`Section4Inverse.lean`) | `continuousOn_of_dominated`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `ContDiffOn.exists_lipschitzOnWith`, `LipschitzOnWith.locallyBoundedVariationOn` |
| 2.4.4–2.4.5 | `dlmf_2_4_5` (`Q` analytic in `ℜz > c₀`, `0 ≤ c₀ < c`, with 2.4.4 and its differentiated form as `z → ∞` in `ℜz ≥ c`: the inverse integral converges for every `σ ≥ c`, is independent of `σ`, and `q = bromwich Q c` has the expansion 2.3.7 as `t → 0+`); `DecayHalfPlane` (power bounds on `G`, `G′`), `bound_of_isBigO_halfPlane`, `bromwichPartial_ibp` (one integration by parts), `DecayHalfPlane.tendsto_bromwichPartial`, `bromwich_shift_le` (Cauchy on rectangles), `norm_bromwich_le` (`≤ (2πt)^{−1}e^{σt}K′σ^{−p}J(p+1)`, used with `σ = 1/t`), `integral_line_rpow`; `dlmf_2_4_5_not_absolutely` (DLMF's "converges absolutely" fails for `Γ(λ)z^{−λ}`, `λ ≤ 1`) | `integral_boundary_rect_eq_zero_of_differentiableOn`, `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `integrable_rpow_neg_one_add_norm_sq`, `integrableOn_Ioi_rpow_iff` |
| 2.4.6–2.4.9 | `fourierPartial`/`fourierLim` (`lim ∫_{−η}^{η} g e^{itτ}`), `UnifConvTails T g` (uniform convergence at each limit for `t ≥ T`), `dlmf_2_4_7`, `fourierLim_exists`, `tendsto_fourierLim_zero` (Riemann–Lebesgue + uniform tails), `dlmf_2_4_8` (`q = f + o(e^{ct})`), `tendsto_zero_of_tail_cauchy` (boundary terms vanish: `|g(η)| → L ≠ 0` would make `e^{iη}` converge), `fourierLim_ibp`, `fourierLim_ibp_iter`, `iteratedDeriv_comp_line`, `dlmf_2_4_9` (`q = f + o(t^{−m}e^{ct})`) (`Section4Haar.lean`) | `dlmf_1_8_10`, `cauchySeq_tendsto_of_complete`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `exp_nat_mul_two_pi_mul_I`, `AnalyticOnNhd.iterated_deriv` |
| 2.4.10–2.4.11 | `logBr ω z` (branch of `log` with `ℑ ∈ (ω − π, ω + π]`), `brPow ω c z` (`(t−a)^c` with `ph(t−a)` near `ω`), `sectorBr ω α` (`\|ph z − ω\| < α`), `brPow_polar`, `norm_brPow_le`, `hasDerivAt_brPow`, `mem_slitPlane_of_mem_sectorBr` (`Section4LaplaceBranch.lean`); `UnifSetup` (`P = p₀ + p₁(t−a) + ⋯` analytic, `P(a) ≠ 0`, `ph p₀ = φ₀`), `LogP`, `unif` (`w = (t−a)P(t)^{1/μ}`, the §2.3(iii) substitution), `unifInv` (analytic local inverse, `AnalyticAt.analyticAt_localInverse`), `laplaceG` (`G(w) = e^{−((λ−1)/μ)log P} Q dt/dw`, the function whose Taylor coefficients give `bₛ`), `analyticAt_laplaceG`, `brPow_unif_mu` (`p(t) − p(a) = w^μ`), `brPow_unif`, `unif_mem_sectorBr` (`Section4LaplaceUnif.lean`) | `AnalyticAt.analyticAt_localInverse`, `HasStrictDerivAt.localInverse`, `HasStrictDerivAt.eventually_right_inverse` |
| 2.4.12–2.4.13 | `laplaceContour` (`∫₀^B e^{−zp(γ(u))}q(γ(u))γ′(u) du`), `LaplaceContour` (DLMF (a)–(c) with `θ₂ − θ₁ < π`, `\|θᵢ + μω + ph p₀\| < π/2`), `laplaceCoeff` (`bₛ = gₛ/μ`), `LaplaceContour.dlmf_2_4_12` (`e^{zp(a)}I(z) ∼ Σ Γ((s+λ)/μ) bₛ z^{−(s+λ)/μ}` along `cobounded ℂ ⊓ 𝓟 {θ₁ ≤ ph z ≤ θ₂}`, principal powers); `LaplaceContour.exists_local` (local normal form on the path), `laplaceF`, `norm_laplaceF_le`, `watsonQ` (`v^{(λ−μ)/μ}G(v^{1/μ}e^{iω′})`, `v = \|w\|^μ`), `integral_ray_eq_laplace`, `watsonQ_laplace_expansion` (Watson's lemma 2.4.1 on the ray, parameter `ze^{iμω′}`), `norm_arc_le`, `LaplaceContour.tail_bound` (arc and tail `O(e^{−c\|z\|})`), `isBigODLMF_cpow_of_exp_bound`, `IsGenAsympExpansionDLMF.add_isBigO`/`const_mul'` (`Section4LaplaceMethod.lean`); `deform_to_ray` (deformation of the path onto the ray `ph w = ω′` through a primitive on a rectangle in `log` coordinates), `rectPrimitive`, `hasDerivAt_rectPrimitive`, `sectorDisc` (`Section4LaplaceDeform.lean`) | `dlmf_2_4_1`, `integral_boundary_rect_eq_zero_of_differentiableOn`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `integral_comp_rpow_Ioi`, `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` |
| 2.4.14 | `SaddlePoint` (path `γ` on `(−A, B)` through the simple saddle point `t₀ = γ(0)`, `p(t) = p(t₀) + (t − t₀)²P(t)`, `P(t₀) = \|P(t₀)\|e^{iω₀} ≠ 0`, (b), (c) at both ends, strict `\|θ + 2ω + ω₀\| < π/2`), `SaddlePoint.forward`/`backward` (the two integrals of 2.4.14 as `LaplaceContour`s with `μ = 2`, `λ = 1`, directions `ω`, `ω + π`, branches `ω₀`, `ω₀ − 2π` of `ph p₀`), `dlmf_2_4_14` (`I = ∫_{t₀}^b − ∫_{t₀}^a`), `UnifSetup.sub_two_pi`, `unif_sub_two_pi` (the substitution for the branch `φ₀ − 2π` is `e^{−2πi/μ} w`), `laplaceCoeff_sub_two_pi_two` (`b⁻ₛ = (−1)^{s+1} b⁺ₛ`, via uniqueness of the local inverse), `laplaceCoeff_sub_two_pi_one` (`μ = 1`: identical coefficients, DLMF's remark), `re_deriv_eq_zero_of_isLocalMin`, `not_branch_lt_of_isLocalMin` (`p′(t₀) ≠ 0` at an interior minimum forces equality in 2.4.13); `brPow_natCast`, `setIntegral_Ioo_comp_neg` (`Section4Saddle.lean`) | `HasStrictFDerivAt.localInverse_unique`, `deriv_comp_neg`, `iteratedDeriv_comp_neg`, `Filter.EventuallyEq.iteratedDeriv_eq`, `IsLocalMin.hasDerivAt_eq_zero`, `intervalIntegral.integral_comp_neg` |
| 2.4.15 | `SaddlePoint.dlmf_2_4_15` (`e^{zp(t₀)} I(z) ∼ 2∑ Γ(s+½) b₂ₛ z^{−(s+½)}` along `cobounded ℂ ⊓ 𝓟 {θ₁ ≤ ph z ≤ θ₂}`, by `dlmf_2_4_12` on both halves, the coefficient relation and `IsGenAsympExpansionDLMF.even`), `dlmf_2_4_15'` (DLMF's form with `e^{−zp(t₀)}` on the right), `saddleCoeff`; `IsGenAsympExpansionDLMF.sub`, `.even` (odd terms vanish ⇒ expansion in the even scale), `IsAsympScaleDLMF.congr` (`Section4Saddle.lean`) | `dlmf_2_4_12`, `WatsonSector.isAsympScale_cpow_neg` |
| 2.4.16 | `SaddlePoint.dlmf_2_4_16_b0` (`b₀ = q(t₀)/(2p″(t₀))^{1/2}`, branch `(2\|p″\|)^{1/2}e^{iω₀/2}`), `dlmf_2_4_16_branch` (`p″(t₀) = \|p″(t₀)\|e^{iω₀}`), `saddleCoeff_zero`, `iteratedDeriv_two` (`p″(t₀) = 2P(t₀)`), `UnifSetup.deriv_unifInv_zero` (`Section4Saddle.lean`); `dlmf_2_4_16_b2` (`b₂ = (2q″ − 2(p‴/p″)q′ + (5(p‴)²/(6(p″)²) − p⁗/(2p″))q)/(2p″)^{3/2}`, branch `(2\|p″\|)^{3/2}e^{3iω₀/2}`), `UnifSetup.laplaceCoeff_two` (`b₂` in `P`, `Q`, `E = P^{1/2}`: `t′(0)`, `t″(0)`, `t‴(0)` from differentiating `t′(w)u′(t(w)) = 1` twice, `u′ = E`, `u″ = 2E′`, `u‴ = 3E″` at `t₀`), `sqrtP`, `eventually_deriv2_unifInv`, `deriv3_unifInv_zero`, `iteratedDeriv_two_laplaceG` (`G″(0) = Q″t′³ + 3Q′t′t″ + Qt‴`), `iteratedDeriv_three`/`four` (`p‴ = 6P′`, `p⁗ = 12P″`) (`Section4SaddleCoeff.lean`) | `HasDerivAt.unique`, `HasDerivAt.congr_of_eventuallyEq`, `AnalyticAt.deriv`, `Filter.EventuallyEq.deriv_eq`, `HasDerivAt.div` |
| 2.4.17–2.4.18 | `cfuIntegral` (`I(α,z) = ∫_𝒫 e^{−zp(α,t)}q(α,t) dt`), `cfuCubic` (`⅓w³ + aw² + bw + c`), `cfuQuad` (`w² + 2aw + b`), `CFUTransform` (the change of variable 2.4.18 as data: `w` analytic, one-to-one, `w′ ≠ 0` on an open `U ⊇ 𝒫`, `p = ⅓w³ + aw² + bw + c`; its existence, uniformly in `α` through the confluence, is the theorem of Chester–Friedman–Ursell (1957), not stated by DLMF and not proved), `CFUTransform.dlmf_2_4_18` (`∂p/∂t = 0 ↔ w² + 2aw + b = 0`), `dlmf_2_4_18_vieta` (two saddle points: `w₁ + w₂ = −2a`, `w₁w₂ = b`), `dlmf_2_4_18_coalesce` (double zero of `∂p/∂t` ↔ `b = a²`, `w = −a`), `cfuQuad_eq_zero_iff` (`Section4Coalescing.lean`) | `HasDerivAt.comp`, `Filter.EventuallyEq.deriv_eq` |
| 2.4.19–2.4.21 | `CFUTransform.inv` (`t = t(w)`, analytic on `w(U)` by the inverse function theorem: `analyticAt_inv`, `hasDerivAt_inv`), `amp` (`f(α,w) = q dt/dw`), `dlmf_2_4_20` (`= q (w² + 2aw + b)/(∂p/∂t)`), `dlmf_2_4_20_analytic` (`f` analytic at `w₁`, `w₂` and at the confluence), `dlmf_2_4_19` (`I = e^{−cz}∫_𝒬 exp(−z(⅓w³ + aw² + bw)) f dw` along `w(𝒫)`), `dlmf_2_4_21_cubic` (`w = z^{−1/3}v − a`: `z(⅓w³ + aw² + bw) = ⅓v³ + (b − a²)z^{2/3}v + z(⅔a³ − ab)`), `dlmf_2_4_21` (`I = e^{−z(c + ⅔a³ − ab)} z^{−1/3} ∫ exp(−(⅓v³ + (b − a²)z^{2/3}v)) f(α, z^{−1/3}v − a) dv`, with `z = ζ³`; the Airy/Scorer identification of §9.5 is not formalized) (`Section4Coalescing.lean`) | `AnalyticAt.analyticAt_localInverse`, `HasStrictDerivAt.to_localInverse`, `Set.InjOn.leftInvOn_invFunOn`, `intervalIntegral.integral_congr` |
| 2.4.18 (existence) | The Chester–Friedman–Ursell existence theorem for one value of `α`: `exists_cfuTransform_confluence` (`p = p(t̂) + (t − t̂)³P`, `P(t̂) ≠ 0`: `w = (3P)^{1/3}(t − t̂)` is a change of variable 2.4.18 with `a = b = 0`), `exists_cfuTransform_saddle` (simple saddle point `p = p(t₀) + (t − t₀)²P`, any prescribed critical point `w₀ ≠ 0`: `W = Φ⁻¹∘Ψ`, `Ψ = (t − t₀)P^{1/2}`, `Φ = (w − w₀)((w + 2w₀)/3)^{1/2}`, gives `p = ⅓W³ − w₀²W + p(t₀) + ⅔w₀³`), `exists_cfuTransform_pair` (two separated simple saddle points with `p(t₁) ≠ p(t₂)`: one cubic `⅓w³ − w₁²w + (p(t₁)+p(t₂))/2`, `w₁³ = ¾(p(t₂) − p(t₁))`, with local changes of variable at both onto `w₁`, `−w₁`); `exists_ball_injOn_of_analyticAt`, `unif_two_sq`, `unif_three_cube`, `UnifSetup.const_mul` (`Section4CoalescingExists.lean`). Not done: gluing the two local transformations along the path, and the analytic dependence on `α` through the confluence | `unifInv` (analytic local inverse), `Complex.cpow_nat_inv_pow`, `Complex.norm_mul_exp_arg_mul_I` |
| 2.4.18 (Chester–Friedman–Ursell) | `chester_friedman_ursell`: for `p(α,t)` analytic in `t` on `\|t − t̂\| < R`, continuous in `(α,t)` (DLMF's hypotheses), with `∂ₜp = ∂ₜ²p = 0 ≠ ∂ₜ³p` at `(α̂, t̂)`, there are `N ∈ 𝓝 α̂`, `ρ > 0`, continuous `b`, `c` on `N`, and `w(α,t)` continuous in `(α,t)` with `CFUTransform (p α) (ball t̂ ρ) (w α) 0 (b α) (c α)` for all `α ∈ N` (`p = ⅓w³ + bw + c`, `w` analytic one-to-one with `∂ₜw ≠ 0` on one fixed disc), `b(α̂) = 0`, `w(α̂, t̂) = 0`. Proof: prepared form `p(α, t̂+s) = p(α,t̂) + ε₁s + ε₂s² + s³V(α,s)` by three `dslope` divisions, jointly continuous via Cauchy's formula for `dslope` (`dslope_eq_circleIntegral`, `continuousOn_dslope_param`, `cfu_prep`, `cfuV_self`, `exists_cfuV_ne_zero`, `Section4CoalescingPrep.lean`); the fixed coordinate `u = (s − t̂)(3V(α̂,s))^{1/3}` with `p(α̂,·) − p(α̂,t̂) = ⅓u³`; the disc algebra `discAlg r` (continuous on the closed disc, analytic inside; closed subalgebra of `C(closedBall 0 r, ℂ)`, Banach: `Section4CoalescingDisc.lean`); the linear map `(b,c,h) ↦ c + bz + z²h`, a continuous linear equivalence `cfuLE` (`Section4CoalescingLinear.lean`); `Φ(b,c,h) = ⅓(z+h)³ + b(z+h) + c` with strict derivative `cfuLE` at `0`, hence a local homeomorphism `cfuPH` by the Banach inverse function theorem, Cauchy estimate `norm_deriv_discExt_le`, `injOn_add_discExt` (`Section4CoalescingIFT.lean`); assembly with `g_α(W) = p(α, u⁻¹(W)) − p(α,t̂)`, `g_α̂ = ⅓W³`, `(b,c,h)(α) = cfuPH⁻¹(g_α)`, `w(α,s) = u(s) + h_α(u(s))` (`Section4CoalescingTheorem.lean`) | `HasStrictFDerivAt.toOpenPartialHomeomorph`, `ContinuousLinearEquiv.ofBijective`, `TendstoLocallyUniformlyOn.differentiableOn`, `Complex.differentiableOn_dslope`, `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `Convex.norm_image_sub_le_of_norm_deriv_le`, `ContinuousMap.continuous_of_continuous_uncurry`, `ContinuousEval.continuous_eval` |

### §2.5 Mellin Transform Methods

| DLMF | Lean | Mathlib |
| --- | --- | --- |
| 2.5.1–2.5.2 | `dlmf_2_5_1` (`𝓜f(z) = ∫₀^∞ t^{z−1}f(t) dt`, Mathlib's `mellin`), `LocallyIntegrableDLMF` (DLMF's local integrability; `LocallyIntegrableDLMF.of_mellinConvergent`), `dlmf_2_5_1_analytic` (strip of analyticity, from 1.14), `dlmf_2_5_2` (inversion at a point of continuity, 1.14.35), `dlmf_2_5_2_bv` (symmetric limit at a point of bounded variation, 1.14.34) (`Section5.lean`) | `mellin`, `MellinConvergent`, `VerticalIntegrable` |
| 2.5.3–2.5.5 | `mellinConvInt` (`I(x) = ∫₀^∞ f(t)h(xt) dt`), `dlmf_2_5_4` (`𝓜I(z) = 𝓜f(1−z)𝓜h(z)` for `ℜz = σ` with `t^{−σ}f`, `t^{σ−1}h` integrable: `t ↦ 1/t` makes `I` the Mellin convolution 1.14.39 of `f(1/t)/t` and `h`, `mellinConvInt_eq_mellinConv`, `mellin_inv_smul`, `mellinConvergent_inv_smul`, then 1.14.40), `dlmf_2_5_5` (1.14.36), `dlmf_2_5_5_parseval` (`x = 1`, 1.14.37) (`Section5.lean`) | `integral_comp_rpow_Ioi`, `mellin_comp_inv`, `mellin_cpow_smul`, `MellinConvergent.comp_rpow` |
| residues on rectangles | `contourIntegral_eq_sum_residues_winding` (residue theorem for any closed piecewise-`C¹` curve in an open set containing its winding support: `∮_P f = 2πi ∑ res_s(f) W_P(s)`), `rectSide`/`rectCurve`/`rectPath` (the rectangle as a `ClosedPiecewiseC1`), `rectPath_contourIntegral` (`= rectBoundary`), `integral_inv_sub_horizontal`/`vertical_right`/`vertical_left` (logarithmic primitives on the edges), `rectBoundary_inv_sub` (`∮ (z − w)⁻¹ = 2πi`), `rectPath_windingNumber_eq_one`/`eq_zero`, `rectPath_windingSupport_subset`, `rectBoundary_eq_sum_residues` (`Section5Rectangle.lean`) | `integral_boundary_rect_*` (none used: the winding-support Cauchy theorem of §1.9 replaces them), `HasDerivAt.clog`, `arg_neg_eq_arg_sub_pi_of_im_pos`, `intervalIntegral.integral_comp_mul_add` |
| 2.5.6–2.5.7 | `dlmf_2_5_6` (`I(x) = ∑_{d<ℜz<c} res[x^{−z}𝓜f(1−z)𝓜h(z)] + E(x)`, `E(x) = (2π)⁻¹ lim_T ∫_{−T}^{T} F(d + iy) dy`, for `F` the continuation to a neighbourhood of `d ≤ ℜz ≤ c` with finitely many poles, horizontal integrals `→ 0` and the line integral on `ℜz = d` convergent; residue theorem on `[d, c] × [−T, T]` and `T → ∞`), `rectBoundary_strip` (`Section5Residues.lean`) | `intervalIntegral_tendsto_integral`, `tendsto_nhds_unique` |
| 2.5.8–2.5.16 (Example) | PARTIAL: `dlmf_2_5_9` (`𝓜f(1−z) = π/sin(πz)` for `f = 1/(1+t)`, from Table 1.14.5), `residue_cpow_mul_double_pole` (2.5.11: `res_{z=n}[x^{−z}G(z)] = (−a ln x + b)x^{−n}` for `G = a/(z−n)² + b/(z−n) + analytic`; Cauchy's formulas for `x^{−z}` and its derivative on a small circle), `sum_range_odd_of_even_zero` (2.5.15 → 2.5.16 reindexing when even coefficients vanish) (`Section5Example.lean`). DEFERRED: `J_ν` and `𝓜(J_ν²)` 2.5.10 (Bessel functions absent from Mathlib), hence the explicit coefficients 2.5.12–2.5.13 and expansions 2.5.15–2.5.16; 2.5.14 (`|Γ(x+iy)|` as `y → ±∞`, complex Stirling). | `dlmf_table_1_14_5_r4`, `residue_eq`, `DifferentiableOn.deriv_eq_smul_circleIntegral`, `DifferentiableOn.circleIntegral_sub_inv_smul` |
| 2.5.17–2.5.24 | `HandelsmanLewSetup` (hypotheses 2.5.17–2.5.20: expansions at `0+` and `+∞` with `ℜαₛ`, `ℜβₛ` strictly increasing to `+∞`, `f = O(t^{−b})`, `b + ℜβ₀ > 1`, `h = O(t^c)`, `c + ℜα₀ > −1`), `trunc₁`/`trunc₂` (2.5.21–2.5.24) (`Section5Truncation.lean`) | `IsGenAsympExpansionDLMF`, `Set.indicator` |
| Table 2.5.1 | `mellinConvergent_trunc₁/₂`, `differentiableAt_mellin_trunc₁/₂` and `HandelsmanLewSetup.mellinConvergent_f₁/f₂/h₁/h₂` (`𝓜f₁`: `ℜz > −ℜα₀`; `𝓜f₂`: `ℜz < b`; `𝓜h₁`: `ℜz > −c`; `𝓜h₂`: `ℜz < ℜβ₀`) | `mellinConvergent_of_isBigO_rpow`, `mellin_differentiableAt_of_isBigO_rpow` |
| Table 2.5.2 | `HandelsmanLewSetup.dlmf_table_2_5_2_11/12/21/22` (`G_{jk}` analytic on `D_{jk}`) | Table 2.5.1 |
| 2.5.25 | `dlmf_2_5_25` (`𝓜f₁` continues to a meromorphic function on `ℂ` with simple poles at `−αₛ` and principal parts `aₛ/(z + αₛ)`): explicit continuation `mellinTrunc₁Ext` on `ℜz > −ℜα_N`, one step `mellin_truncRem_succ` via `𝓜(t^{αₛ} 1_{(0,1]})(z) = 1/(z + αₛ)`, glued by `glue` into `mellinTrunc₁Cont` (`Section5Continuation.lean`) | `hasMellin_cpow_Ioc`, `hasMellin_add` |
| 2.5.26 | `dlmf_2_5_26` (`𝓜f := 𝓜f₁ + 𝓜f₂` on `ℜz < b`: equals `𝓜f` on the strip, meromorphic with the poles of `𝓜f₁`) | 2.5.25, Table 2.5.1 |
| 2.5.27 | `κ = 0`: `dlmf_2_5_27_zero` (`𝓜h₂` meromorphic with simple poles at `βₛ`, principal parts `−bₛ/(z − βₛ)`; by `t ↦ 1/t` from 2.5.25, `mellin_trunc₂_eq_inv`, `isGenAsympExpansion_inv`, `locallyIntegrableOn_comp_inv`). `κ ≠ 0`: `dlmf_2_5_27_ne` (`𝓜h₂` continues to an ENTIRE function `mellinTrunc₂Cont`): integration by parts `oscInt_eq_succ` on `∫₁^∞ t^w e^{iκt^p} dt`, iterated (`oscExt`) and glued (`oscEntire`), plus the remainder's transform on `ℜz < ℜβ_N` (`Section5Oscillatory.lean`). Both: `HandelsmanLewSetup.exists_mellinTrunc₂_cont` | `mellin_comp_inv`, `integral_Ioi_mul_deriv_eq_deriv_mul`, `hasDerivAt_ofReal_cpow_const` |
| 2.5.28 | `dlmf_2_5_28` (`𝓜h := 𝓜h₁ + 𝓜h₂` with any continuation `G` of `𝓜h₂`: equals `𝓜h` on `−c < ℜz < ℜβ₀`, analytic on `ℜz > −c` where `G` is) | Table 2.5.1 |
| 2.5.29–2.5.31 | `dlmf_2_5_29` (`I = I₁₁ + I₁₂ + I₂₁ + I₂₂` for `x > 0` when `f(t)h(xt)` is integrable), `dlmf_2_5_30`, `dlmf_2_5_31` (`I₂₁(x) = 0` for `x ≥ 1`) (`Section5Truncation.lean`) | `integral_add`, indicators |
| 2.5.32–2.5.33 | `mellinG`, `dlmf_2_5_33` (Parseval representation of `I_{jk}` on `ℜz = p ∈ D_{jk}`) (`Section5Expansion.lean`) | `dlmf_2_5_5` |
| 2.5.34–2.5.35 | `dlmf_2_5_35`: with `G` the continuation of `G_{jk}` to a neighbourhood of `p ≤ ℜz ≤ q` minus finitely many poles, 2.5.34 as `∀ ε > 0, eventually in cocompact ℝ, ∀ σ ∈ [p, q], |G(σ + iy)| ≤ ε` (which PROVES the vanishing of the horizontal integrals, `tendsto_horizontal_of_sup`), and `G` integrable on the two lines: `I_{jk}(x) = ∑_{p<ℜz<q} res[−x^{−z}G] + E_{jk}(x)`; generic `lineIntegral_shift` (rightward shift, residues with sign) | `rectBoundary_eq_sum_residues`, `rectBoundary_strip`, `residue_neg` |
| 2.5.36 | `dlmf_2_5_36`: `E_{jk}(x) = (2πi)⁻¹ ∫_{q−i∞}^{q+i∞} x^{−z}G(z) dz = o(x^{−q})` as `x → +∞` (Riemann–Lebesgue, `x^{−(q+iy)} = x^{−q} e^{−iy ln x}`, `cpow_neg_add_mul_I`); holds with no hypothesis on `G` (Bochner convention) | `dlmf_1_14_i_tendsto_zero` |

### §2.5(iii) Laplace Transforms with Small Parameters

| DLMF | Azurite | Mathlib |
|---|---|---|
| 2.5.37–2.5.39 | `LaplaceSmallSetup` (2.5.18 + 2.5.20 with `c > −1`), `dlmf_2_5_37`, `dlmf_2_5_38` (`ζ ℒh(ζ) = I₁(1/ζ) + I₂(1/ζ)` via `t ↦ t/ζ` and 2.5.29; integrability of `e^{−t} h(xt)` from the growth hypotheses) (`Section5Laplace.lean`) | `integral_comp_mul_left_Ioi`, `isLittleO_exp_neg_mul_rpow_atTop` |
| 2.5.40 | `dlmf_2_5_40_one` (`−c < p₁ < 1`), `dlmf_2_5_40_two` (`p₂ < min(1, ℜβ₀)`): Parseval with `𝓜e^{−t}(z) = Γ(z)` (`mellin_expNeg`); the line integrability of `Γ(1 − z)` comes from `\|Γ(s)\| ≤ Γ(ℜs + k)/\|ℑs\|^k` (`norm_Gamma_le_div_pow_im`, `integrable_Gamma_vertical`) | `Gamma_eq_integral`, `GammaIntegral_eq_mellin`, `Gamma_add_one` |
| 2.5.41 | `dlmf_2_5_41` (`I₁(x) = 𝓜h₁(1) x^{−1} + (2πi)⁻¹ ∫_{ρ} …`, `1 < ρ < 2`): `dlmf_2_5_35` with the residue of `−x^{−z}Γ(1−z)𝓜h₁(z)` at `1` computed via `Γ(w) = GammaNum 0 w / w` (`residue_eq_of_eq_div_add`); DLMF's "by (2.5.14)" is the uniform strip bound `exists_Gamma_strip_bound` (`Section5LaplaceShift.lean`) | `differentiableAt_Gamma`, `Real.differentiableAt_Gamma` |
| contour shifts | `StripData` (analytic off poles, finitely many per strip, polynomial growth for `\|ℑz\|` large), `shift_Gamma_mul` (`Section5LaplaceStrip.lean`); instances `stripData_h₁`, `stripData_mellinTrunc₂Cont` (`κ ≠ 0`, from `exists_norm_oscExt_le`: `k` integrations by parts give `O((1 + \|w\|)^k)`), `stripData_mellinTrunc₂ContZero` (`κ = 0`) (`Section5LaplaceGrowth.lean`) | `lineIntegral_shift`, `integrable_inv_one_add_sq` |
| 2.5.42 | `dlmf_2_5_42` (`I₂(x) = ∑_{p₂<ℜz≤1} res[−x^{−z}Γ(1−z)𝓜h₂(z)] + (2πi)⁻¹ ∫_{ρ} …` with `ρ ∈ (1, 2)` such that `𝓜h₂` has no poles in `1 < ℜz ≤ ρ`), for any continuation `MellinH₂Cont` (`mellinH₂Cont_ne`, `mellinH₂Cont_zero`) (`Section5LaplaceExpansion.lean`) | — |
| 2.5.43 | `dlmf_2_5_43` (`L = l − δ`; split form: residues of `−ζ^{z−1}Γ(1−z)𝓜h₁` at `1 ≤ n+1 < L`, of `−ζ^{z−1}Γ(1−z)𝓜h₂` at the singularities in `p₂ < ℜz < L`, plus `(2πi)⁻¹∫_{L} ζ^{z−1}Γ(1−z)𝓜h(z)dz`; DLMF's grouping follows by additivity of residues), `dlmf_2_5_43_remainder` (`O(ζ^{L−1})`, `ζ → 0+`) | `integral_const_mul` |
| 2.5.44 | `dlmf_2_5_44` (`κ = 0`, no `βₙ` a positive integer; for every admissible `L`: `ℒh(ζ) = ∑_{ℜβₙ<L} bₙΓ(1−βₙ)ζ^{βₙ−1} + ∑_{n+1<L} ((−ζ)^n/n!) 𝓜h(n+1) + O(ζ^{L−1})`, `𝓜h = 𝓜h₁ + 𝓜h₂` continued), via `residue_neg_cpow_Gamma_mul` (poles of `Γ(1−z)`: `GammaNum_neg_nat`) and `residue_neg_cpow_Gamma_mul_pole` (poles `βₙ`) (`Section5LaplaceResidues.lean`) | `Finset.sum_image`, `Finset.sum_union` |
| 2.5.45–2.5.49 (Example) | `oneDivOneAdd` with `laplaceSmallSetup_oneDivOneAdd` (`κ = 0`, `βₛ = s+1`, `bₛ = (−1)^s`, `c = 0`; geometric remainders at `0+` and `+∞`), `dlmf_2_5_45`; `cont_add_cont_eq` (`𝓜h₁ + 𝓜h₂ = π csc(πz)` on `ℂ ∖ ℤ`, identity theorem on the connected complement of `ℤ`, from Table 1.14.5 on `0 < ℜz < 1`); `dlmf_2_5_46` (double-pole residue via `residue_eq_deriv_of_eq_div_sq`, `Gamma_mul_Gamma_one_sub`, `hasDerivAt_GammaNum_neg_nat` = value × `ψ(m+1)` by `logDeriv` of `Γ(w+m+1)/∏(w+j)` and `digamma_apply_add_nat`), `dlmf_2_5_47` (= 2.5.46 at `k = 1` minus 2.5.41's residue, `ψ(1) = −γ`), `dlmf_2_5_48` (for every `K`: `∑_{k≤K} (−ln ζ + ψ(k+1))ζ^k/k! + O(ζ^{K+1/2})`, from `dlmf_2_5_43` with `L = K + 3/2` and the combined residues), `expIntegralE₁` (6.2.2) + `dlmf_2_5_49` (`ℒh(ζ) = e^ζ E₁(ζ)` by `t ↦ t+1`, `u ↦ ζu`). DEFERRED: the verification of 2.5.48 through the series 6.6.3 of `E₁` (Chapter 6) (`Section5LaplaceExample*.lean`) | `Complex.digamma`, `digamma_one`, `digamma_apply_add_nat`, `Set.Countable.isConnected_compl_of_one_lt_rank`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `logDeriv_div`, `logDeriv_prod` |

### §2.6 Distributional Methods

| DLMF | Azurite | Mathlib |
|---|---|---|
| 2.6.1 | `dlmfS` (`S(x) = ∫₀^∞ dt/((1+t)^{1/3}(x+t))`), `integrableOn_dlmfS` (convergent for `x > 0`: continuous on `(0, 1]`, `≤ t^{−4/3}/min(x,1)` on `(1, ∞)`) (`Section6.lean`) | `integrableOn_Ioi_rpow_iff` |
| 2.6.2 | `hasSum_one_add_rpow` (`(1+y)^a = ∑ binom(a,s) y^s`, `\|y\| < 1`), `dlmf_2_6_2` (`(1+t)^{−1/3} = ∑ binom(−1/3,s) t^{−s−1/3}` for `t > 1`, via `y = 1/t`) | `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`, `Ring.choose` |
| 2.6.3 | `dlmf_2_6_3`: `∫₀^∞ t^{−s−1/3}/(x+t) dt` diverges for `s ≥ 1` (not integrable on `(0,1]`: the integrand dominates `(t^{−1/3})'`) | `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton` |
| 2.6.4 | `dlmf_2_6_4` (`∫₀^∞ t^{α−1}/(x+t)^{α+β} dt = Γ(α)Γ(β)/Γ(α+β) x^{−β}`, `ℜα, ℜβ > 0`, `x > 0`): `t = xu`, then the beta integral by `u = v/(1−v)` (`integral_cpow_mul_one_add_cpow`) | `betaIntegral_eq_Gamma_mul_div`, `integral_image_eq_integral_abs_deriv_smul`, `integral_comp_mul_left_Ioi` |
| 2.6.5 | `genBetaIntegral` (the right side of 2.6.4 as the generalized value; `genBetaIntegral_eq` where convergent), `dlmf_2_6_5` (`= (2π/√3)(−1)^s x^{−s−1/3}` via `Γ(2/3−s)Γ(1/3+s) = (−1)^s 2π/√3`, `Gamma_two_thirds_sub_mul`), `dlmf_2_6_5_zero` (the honest value for `s = 0`) | `Gamma_mul_Gamma_one_sub`, `Real.sin_add_nat_mul_pi` |
| 2.6.6 | `dlmf_2_6_6_formal`: the termwise replacement of the divergent integrals by their generalized values gives `(2π/√3) ∑ (−1)^s binom(−1/3,s) x^{−s−1/3}` (partial sums). DLMF: this expansion is incorrect | — |
| 2.6.7 | `dlmf_2_6_7_remainder` (for every `n`: `S(x) = (2π/√3) ∑_{s<n} (−1)^s binom(−1/3,s) x^{−s−1/3} − ∑_{s<n} dlmfB s x^{−s−1} + O(x^{−n−1/3})`, `x → +∞`, from 2.6.27 with `f = (1+t)^{−1/3}`, `𝓢f(x) = S(x)`), `dlmf_2_6_7` (as `IsGenAsympExpansionDLMF` with the interleaved scale `dlmfScale`: `x^{−1/3}, x^{−1}, x^{−4/3}, …`, terms `dlmfTerms`), `dlmfB s = 3^{s+1} s!/(2·5⋯(3s+2))` (DLMF's `3^s(s−1)!/(2·5⋯(3s−1))` at index `s+1`) via `mellinCont_cbrtInv_succ` (`𝓜f(n+1) = n!(−1)^{n+1}3^{n+1}/∏(3k+2)` from `Γ(w)Γ(1/3−w)/Γ(1/3)`: `mellin_cbrtInv` on the strip, `cbrtCont_eq` by the identity theorem on `ℂ∖(ℤ∪(ℤ+1/3))`, `cbrtCont_eq_of_ne` by density at the integers). The failure of 2.6.6: `dlmf_2_6_6_false` (remainder after one term is `−(3/2)x^{−1} + O(x^{−4/3})`). DEFERRED: validity in `\|ph x\| ≤ π − δ` (only real `x`) (`Section6StieltjesExample.lean`) | `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`, `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`, `Set.Countable.dense_compl`, `Real.sin_pi_div_three`, `Finset.prod_range_reflect`, `neg_one_pow_eq_or` |
| 2.6.8 | `stieltjesT` (`𝓢f(z) = ∫₀^∞ f(t)/(t+z) dt`), `StieltjesSetup.integrableOn_stieltjesT` (absolutely convergent for `\|ph z\| < π` under 2.6.9: `‖t + z‖ ≥ c(1+t)`, `exists_mul_one_add_le_norm_add`) (`Section6Stieltjes.lean`) | `mellinConvergent_of_isBigO_rpow` |
| 2.6.9 | `StieltjesSetup` (`f` locally integrable on `[0,∞)`, `f ∼ ∑ aₛ t^{−s−α}` as `IsGenAsympExpansionDLMF`, `0 < α ≤ 1`); consequences `rem_isBigO`, `f_isBigO`, `locallyIntegrableOn_rem` | — |
| 2.6.10 | `stieltjesRem` (`fₙ = f − ∑_{s<n} aₛ t^{−s−α}`), `rem_eq_add_succ` | — |
| 2.6.11–2.6.14 | `pairing` (2.6.11), `powPairing` (2.6.12–2.6.13 with `(α)ₛ = ∏_{j<s}(α+j)`), `logPairing` (2.6.14) as definitions; DEFERRED: their distributional properties | `iteratedDeriv` |
| 2.6.15–2.6.16 | `repeatedIntegralTail` (`g_{n,n}(t) = ((−1)ⁿ/(n−1)!) ∫_t^∞ (τ−t)^{n−1} g(τ) dτ`), `remPairing` as definitions; DEFERRED: boundedness/`O` properties of `f_{n,n}` and `f_{n,n}^{(n)} = fₙ` | — |
| 2.6.17, 2.6.20–2.6.21 | DEFERRED: the distributional identities `f = ∑ aₛ t^{−s−α} − ∑ cₛ δ^{(s−1)} + fₙ` (and the `α = 1` form with `dₛ`); the expansions 2.6.27–2.6.28 are proven directly instead (see below) | — |
| 2.6.18 | `stieltjesC` (`cₛ = (−1)^s/(s−1)! 𝓜f(s)`), with `𝓜f` the continued transform `mellinCont = 𝓜f₁ + [𝓜f₂]_cont` (2.5.25/2.5.27 machinery); `mellinCont_eq_mellin` (agrees with `𝓜f` where it converges), `mellinCont_eq_mellin_rem` (`𝓜f(z) = ∫₀^∞ t^{z−1} f_{n+1}(t) dt` for `n+α < ℜz < n+1+α`, `ℜz ≥ 1`), `mellinCont_succ_eq` (`𝓜f(n+1) = ∫₀^∞ τⁿ f_{n+1}`, `0 < α < 1`). Errata: for `f` merely locally integrable the Mellin integral may converge nowhere | `hasMellin_cpow_Ioc`, `hasMellin_sub`, `Integrable.bdd_mul` |
| 2.6.19 | `deltaPairing` (`⟨δ^{(s)}, φ⟩ = (−1)^s φ^{(s)}(0)`) as a definition | — |
| 2.6.22 | `stieltjesTest` (`φ_ε(t) = e^{−εt}/(t+z)`); errata: `φ_ε ∉ 𝒯` (not rapidly decreasing on `ℝ`), the pairings are integrals over `(0,∞)` | — |
| 2.6.23 | `integral_cpow_neg_div_add` (the `s = 0` case: `∫₀^∞ τ^{−α}/(τ+z) dτ = (π/sin πα) z^{−α}`, `0 < α < 1`, `\|ph z\| < π`, from Table 1.14.5 for `1/(1+z⁻¹t)`), `integral_rpow_neg_div_add` (real form), `integrableOn_cpow_neg_div_add` (`Section6StieltjesExpansion.lean`). DEFERRED: `s ≥ 1` (needs `φ_ε^{(s)}` and dominated convergence) | `mellin_one_div_one_add_mul`, `inv_cpow`, `Complex.sin_pi_sub` |
| 2.6.24 | DEFERRED (the `α = 1` limit with `ln z`; its content enters 2.6.28 through `integral_Ioc_inv_ofReal_add`, `integral_Ioi_one_inv_mul_add`) | — |
| 2.6.25 | `StieltjesSetup.dlmf_2_6_25` (`⟨f, φ_ε⟩ → 𝓢f(z)` as `ε → 0+`, dominated convergence) | `tendsto_integral_filter_of_dominated_convergence` |
| 2.6.26 | DEFERRED (`⟨fₙ, φ_ε⟩ → n! ∫₀^∞ f_{n,n}/(t+z)^{n+1} = ((−1)ⁿ/zⁿ) ∫₀^∞ τⁿ fₙ/(τ+z)`; the second expression is 2.6.30, used directly) | — |
| 2.6.27 | `StieltjesSetup.dlmf_2_6_27`, `dlmf_2_6_27_Icc` (`0 < α < 1`, `\|ph z\| < π`, every `n`: `𝓢f(z) = (π/sin πα) ∑_{s<n} (−1)^s aₛ z^{−s−α} − ∑_{s=1}^n (s−1)! cₛ z^{−s} + Rₙ(z)`), by induction via `stieltjesR_succ` (`fₙ = aₙ τ^{−n−α} + f_{n+1}` and `1/(τ+z) = 1/z − τ/(z(τ+z))`), without the distribution theory; `stieltjesR_isBigO` (`Rₙ(x) = O(x^{−n−α})`, real `x → +∞`) | `integral_const_mul`, `setIntegral_union`, `setIntegral_mono_set` |
| 2.6.28 | `StieltjesSetup.dlmf_2_6_28` (`α = 1`: `𝓢f(z) = ln z ∑_{s<n} (−1)^s aₛ z^{−s−1} + ∑_{s<n} (−1)^s d̃ₛ z^{−s−1} + Rₙ(z)`), by induction via `stieltjesR_succ_one` (split at `τ = 1`; `∫₁^∞ dτ/(τ(τ+z)) − z⁻¹∫₀¹ dτ/(τ+z) = (ln z)/z`) (`Section6StieltjesOne.lean`) | `HasDerivAt.clog_real`, `integral_Ioi_of_hasDerivAt_of_tendsto`, `intervalIntegral.integral_eq_sub_of_hasDerivAt` |
| 2.6.29 | `stieltjesDTilde` (`d̃ₙ = ∫₀¹ τⁿ fₙ + ∫₁^∞ τⁿ f_{n+1}`, the finite part), `StieltjesSetup.dlmf_2_6_29` (`d̃ₙ = lim_{z→n+1} (𝓜f(z) + aₙ/(z−n−1))`, under `f = O(t^c)`, `c > −1`, at `0+`; errata: without such a hypothesis the limit need not exist for `n = 0`) | `differentiableAt_mellin_trunc₁/₂` (repo), `Tendsto.congr'` |
| 2.6.30 | `stieltjesR` (`Rₙ(z) = ((−1)ⁿ/zⁿ) ∫₀^∞ τⁿ fₙ(τ)/(τ+z) dτ`), `StieltjesSetup.integrableOn_pow_mul_rem_div` (absolutely convergent) | — |
| 2.6.31–2.6.32 | Not formalized (remarks: oscillatory factor `e^{ict}`, generalized Stieltjes transform `∫₀^∞ f(t)/(t+z)^ρ dt`; references only) | — |
| 2.6.33 | `fracIntegral` of §1.15(vi) (`dlmf_1_15_47`), here with real order `μ > 0`; `f` as in 2.6.9 (`StieltjesSetup`) | — |
| 2.6.34–2.6.35 | `convProd` (`(f ∗ g)(x) = ∫₀^x f(x−t) g(t) dt`), `dlmf_2_6_35` (`I^μ f = (1/Γ(μ)) (t^{μ−1} ∗ f)`) (`Section6Fractional.lean`) | — |
| 2.6.36 | `dlmf_2_6_36_zero` (`s = 0`, `α < 1`: `= Γ(μ)Γ(1−α)/Γ(μ+1−α) x^{μ−α}`), `dlmf_2_6_36_diverges` (not interval-integrable when `s + α ≥ 1`; test function `ln t`) | `integral_beta_shift` (repo), `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton` |
| 2.6.37 | NOT formalized: the distribution algebra `K⁺` (`F = Dⁿ f`, `F ∗ G = D^{n+m}(f ∗ g)`); the expansions below are proved without it | — |
| 2.6.38 | DEFERRED (distributional `t^{μ−1} ∗ δ^{(s−1)}`); the function-level content is the coefficient identity `binom(μ−1,i)/Γ(μ) = 1/(i! Γ(μ−i))` (`choose_div_Gamma`, valid for all `μ > 0` with `1/Γ = 0` at the poles) | `Ring.descPochhammer_eq_factorial_smul_choose` (via `dlmf_1_2_6`), `Gamma_add_nat_eq_prod_mul` (repo) |
| 2.6.39 | `dlmf_2_6_39_reg`: the regularized identity `∑_{i<n} binom(μ−1,i)(−1)^i x^{μ−s−α}/(i−s−α+1) + ∫₀^x Kₙ(x,t) t^{n−s−α} dt = Γ(μ)Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α}` (`0 < α < 1`, `s < n`, all real `μ > 0`), where `Kₙ` is the Taylor remainder of `(x−t)^{μ−1}` (`fracKer`, `fracKer_expansion`, scaling `fracKer_eq_scale`, bounds `fracKerUnit_bound`). Proof: identity theorem on `ℂ ∖ ℤ` in the exponent (`fracKerCont_eq`), `kₙ` continued by `mellinTrunc₁Cont` from its binomial expansion at `0+` (`fracKerUnit_exp_zero`); the honest case `ℜλ > −1` is the beta integral (`fracKerCont_eq_fracBeta_of_re`). Errata: DLMF's exclusion of `μ − α ∈ ℕ` is unnecessary | `betaIntegral_eq_Gamma_mul_div`, `betaIntegral_convergent`, `integral_cpow`, `intervalIntegral.integral_comp_div`, `differentiable_one_div_Gamma` |
| 2.6.40 | DEFERRED (`α = 1`: `t^{μ−1} ∗ t^{−s−1}` with `ln t − γ − ψ(μ+1)`; Chapter 5 digamma) | — |
| 2.6.41–2.6.44 | DEFERRED (distributional forms of 2.6.17/2.6.20 and their convolutions with `t^{μ−1}`) | — |
| 2.6.45 | `StieltjesSetup.dlmf_2_6_45` (`0 < α < 1`, real `μ > 0`, `∀ᶠ x` at `+∞`: `I^μ f(x) = ∑_{s<n} aₛ Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α} − ∑_{s=1}^n cₛ/Γ(μ+1−s) x^{μ−s} + x^{−n} δₙ(x)`), from the moment form `dlmf_2_6_45_moments` by induction on `n` (`fracRem_succ`: kernel recursion `fracKer_succ` + `fₙ = aₙ t^{−n−α} + f_{n+1}` + `𝓜f(n+1) = ∫₀^∞ tⁿ f_{n+1}` + 2.6.39 regularized), without the distribution theory; `fracRem_isBigO`/`fracRemDelta_isBigO`: `x^{−n} δₙ(x) = O(x^{μ−n−α})` (`Section6FractionalExpansion.lean`) | `integrableOn_sub_rpow` (repo), `IntervalIntegrable.comp_mul_left`, `integral_Ioi_rpow_of_lt` |
| 2.6.46 | DEFERRED (`α = 1` expansion of `I^μ f`, with 2.6.40) | — |
| 2.6.47 | `fracRemDelta` (`δₙ(x) := xⁿ fracRem n x/Γ(μ)`, with `fracRem n x = ∫₀^x Kₙ(x,t) tⁿ fₙ(t) dt − ∑_{i<n} binom(μ−1,i)(−1)^i x^{μ−1−i} ∫_x^∞ tⁱ fₙ(t) dt`). DEFERRED: DLMF's representation `δₙ = ∑_j C(n,j) Γ(μ+1)/Γ(μ+1−j) I^μ(t^{n−j} f_{n,j})` through the repeated integrals `f_{n,j}` | — |
| 2.6.48 | `fracExF` (`f(t) = t^{1−α}/(1+t)`), `dlmf_2_6_48` (`Section6FractionalExample.lean`) | — |
| 2.6.49–2.6.50 | `dlmf_2_6_49`, `dlmf_2_6_50` (`fₙ(t) = (−1)ⁿ t^{1−n−α}/(1+t)`, by induction), `fracEx_setup` (the hypotheses 2.6.9 with `aₛ = (−1)^s`) | — |
| 2.6.51 | `dlmf_2_6_51` (`𝓜f(n+1) = (−1)^{n+1} π/sin(πα)`, the continued transform, via `∫₀^∞ t^{−α}/(1+t) dt = π/sin πα`), `stieltjesC_fracEx` (`cₛ = (π/sin πα)/(s−1)!`) | `integral_cpow_neg_div_add` (repo) |
| 2.6.52 | `dlmf_2_6_52` (from 2.6.45 and 2.6.51) | — |
| 2.6.53 | DEFERRED (the bound on `δₙ(x)` rests on the representation 2.6.47); the `₂F₁` remark not formalized | — |
| 2.6.54 | `mellinConvInt f h x = ∫₀^∞ f(t) h(xt) dt` (§2.5) | — |
| 2.6.55–2.6.56 | `MellinZeroSetup` (`f ∼ ∑ aₛ t^{s+α−1}` at `0+`, `0 < α ≤ 1`, plus `f = O(t^{−b})` at `∞` from 2.5.19), `MellinInfSetup` (`h ∼ ∑ bₛ t^{−s−β}` at `∞`, `0 < β ≤ 1`, plus `h = O(t^c)` at `0+` from 2.5.20); remainders `zeroRem`, `stieltjesRem` (`Section6Regularization.lean`) | — |
| 2.6.57 | `dlmf_2_6_57` (the algebraic identity for `f(t) h(xt)`, `x, t > 0`) | `mul_cpow_ofReal_nonneg`, `Finset.sum_mul_sum` |
| 2.6.58 | `dlmf_2_6_58` (`∫₀^∞ t^λ dt` diverges for every real `λ`) | `integrableOn_Ioi_rpow_iff` |
| 2.6.59 | `dlmf_2_6_59`: `𝓜(t^λ 1_{(0,1]})(z) = 1/(z+λ)` for `ℜz > −ℜλ`, `𝓜(t^λ 1_{(1,∞)})(z) = −1/(z+λ)` for `ℜz < −ℜλ` (`mellin_trunc₁_cpow`, `mellin_trunc₂_cpow`), and the continuations cancel identically — the precise sense of "`∫₀^∞ t^λ dt = 0`". Errata: `λ = −1` must be excluded (pole at `z = 1`) | `hasMellin_cpow_Ioc` |
| 2.6.60 | `MellinZeroSetup.dlmf_2_6_60`: the continued `𝓜f = mellinTrunc₁Cont f a α' + 𝓜f₂` (`mellinContZero`) equals `𝓜fₙ(z)` on `−(n+α−1) < ℜz < min(b, 2−n−α)` (via `mellin_trunc₂_sub_sum`); `MellinInfSetup.mellinCont_eq_mellin_rem`: the continued `𝓜h` of 2.6.18 equals `𝓜hₘ(z)` for `m−1+β < ℜz < m+β`, `ℜz > −c` | `hasMellin_sub` |
| 2.6.61 | `MellinInfSetup.dlmf_2_6_61` (`𝓜h_x(j+α) = x^{−j−α} 𝓜h(j+α)` for the continued transforms, `α ≠ β`, `j + α > −c`), via `MellinInfSetup.comp_mul_left` (`h_x` satisfies 2.6.56 with `bₛ x^{−s−β}`) and `mellin_comp_mul_left` | `mellin_comp_mul_left` |
| 2.6.62 | `dlmf_2_6_62` (`α ≠ β`, `x > 0`): `I(x) = ∑_{j<n} a_j 𝓜h(j+α) x^{−j−α} + ∑_{k<n} b_k 𝓜f(1−k−β) x^{−k−β} + δₙ(x)`, `δₙ(x) = ∫₀^∞ fₙ(t) hₙ(xt) dt` (`regDelta`), derived rigorously from §2.5(ii): Parseval at `ℜz = p` (`max(1−b,−c) < p < min(α,β)`), the shift 2.5.35 to `ℜz = q` (`n−1+max(α,β) < q < n+min(α,β)`) with the residues `residue_at_zero_pole`, `residue_at_inf_pole` of `−x^{−z} 𝓜f(1−z) 𝓜h(z)` (`regG`), and Parseval for `(fₙ, hₙ)` at `q` via 2.6.60. Hypotheses as in 2.5.35: decay 2.5.34 of `G` on the strip and line integrability (DLMF: "see Wong"). `dlmf_2_6_62_remainder`: `δₙ(x) = o(x^{−q})` (2.5.36). DEFERRED: the logarithmic case `α = β` (`Section6RegularizationExpansion.lean`) | `AnalyticAt.eventually_analyticAt`, `Metric.eventually_nhds_iff`, `Finset.sum_union`, `Finset.sum_image` |

### §2.7 Differential Equations

| DLMF | Azurite | Mathlib |
|---|---|---|
| §2.7(i) classification | `IsOrdinaryPoint` (`f`, `g` analytic at `z₀`), `HasRegularCoefficients` (`(z−z₀)f`, `(z−z₀)²g` extend analytically), `IsRegularSingularity`, `IsIrregularSingularity`, `classify_point` (trichotomy); `IsOrdinaryPoint.analyticAt_solution` (every solution of 2.7.1 is analytic at an ordinary point, from §1.13) (`Section7.lean`) | `AnalyticAt`, `DifferentiableOn.analyticOnNhd` |
| 2.7.1 | `IsODESolution D f g w` (§1.13) | |
| 2.7.2 | `FrobeniusData f g z₀ R fc gc` (`f = (∑ fₛ (z−z₀)^s)/(z−z₀)`, `g = (∑ gₛ (z−z₀)^s)/(z−z₀)²` on the punctured ball `0 < \|z−z₀\| < R`, both series absolutely convergent on the ball), `FrobeniusData.dlmf_2_7_2` (the `(z−z₀)^{s−1}`, `(z−z₀)^{s−2}` form), `HasRegularCoefficients.exists_frobeniusData` / `IsRegularSingularity.exists_frobeniusData` (existence of such data, via `exists_summable_tsum_of_analyticAt`), `FrobeniusData.mono`; the side condition "at least one of `f₀, g₀, g₁` nonzero" (i.e. `z₀` not ordinary) is not recorded in the data, which also exist at an ordinary point (`IsOrdinaryPoint.hasRegularCoefficients`) (`Section7.lean`) | `HasFPowerSeriesOnBall.hasSum_sub`, `FormalMultilinearSeries.summable_norm_apply`, `FormalMultilinearSeries.apply_eq_pow_smul_coeff` |
| 2.7.3 | `indicial fc gc α = α(α−1) + f₀ α + g₀`, `exists_indices` (`Q(α) = (α−α₁)(α−α₂)`), `indicial_eq_zero_iff`, `indicial_add_ne_zero_iff` (`Q(α₁+s) ≠ 0` for all `s ≥ 1` iff `α₁ − α₂ ∉ {−1, −2, …}`), `indicial_add_ne_zero_of_sub_not_int` (`Section7.lean`, `Section7Frobenius.lean`) | `Complex.cpow_nat_inv_pow` |
| 2.7.4 | `frobSolution fc gc α z₀ z = (z−z₀)^α ∑ aₛ (z−z₀)^s` (principal branch); `FrobeniusData.dlmf_2_7_4`: for any index `α` with `Q(α) = 0`, `Q(α+s) ≠ 0` (`s ≥ 1`) it solves 2.7.1 on the slit ball `slitBall z₀ R = {\|z−z₀\| < R, z−z₀ ∉ (−∞,0]}`; `FrobeniusData.dlmf_2_7_4_independent` (linear independence of `w₁, w₂` on the slit ball when `α₁ − α₂ ∉ ℤ`, via the Wronskian `w₁w₂′ − w₂w₁′ = (z−z₀)^{α₁+α₂−1} V(z)`, `V(z₀) = α₂ − α₁`); `FrobeniusData.dlmf_2_7_4_pair` (both solutions + independence). Convergence: `FrobeniusData.frobCoeff_bound` (`‖aₛ‖ ρ^s ≤ K` for every `ρ < R`, by strong induction with the majorant `\|Q(α+s)\| ≥ s² − C₁ s − C₂` (`norm_indicial_add_ge`) and a geometric tail), `FrobeniusData.hasRadiusGE_frobCoeff`, `FrobeniusData.summable_frobCoeff` (radius of convergence at least the distance `R` to the next singularity). Power-series toolkit `HasRadiusGE`, `shiftDeriv`, `powerSeriesSum`, `HasRadiusGE.hasDerivAt` (termwise derivative), `HasRadiusGE.hasSum_natCast_mul(_sub_one)` (`(z−z₀)u′`, `(z−z₀)²u″`), `hasSum_mul_powerSeriesSum` (Cauchy product) (`Section7Series.lean`, `Section7Frobenius.lean`) | `hasDerivAt_tsum_of_isPreconnected`, `HasDerivAt.cpow_const`, `Complex.cpow_sub`, `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`, `summable_norm_pow_mul_geometric_of_norm_lt_one`, `geom_sum_Ico_le_of_lt_one`, `Finset.sum_range_reflect`, `HasDerivAt.unique` |
| 2.7.5 | `frobCoeff fc gc α` (`a₀ = 1`, well-founded recursion over `Fin (s+1)`), `frobCoeff_zero`, `frobCoeff_succ` (`Q(α+s) aₛ = −∑_{r<s} ((α+r) f_{s−r} + g_{s−r}) aᵣ`, `s ≥ 1`); as a power-series identity: `FrobeniusData.series_ode` / `FrobeniusData.frobU_ode` (`(z−z₀)² u″ + (2α + F)(z−z₀) u′ + (α(α−1) + αF + G) u = 0` for `u = ∑ aₛ (z−z₀)^s`, `F = ∑ fₛ (z−z₀)^s`, `G = ∑ gₛ (z−z₀)^s`, by comparing coefficients of the Cauchy products) (`Section7.lean`, `Section7Frobenius.lean`) | `Finset.sum_range_succ`, `hasSum_nat_add_iff'`, `HasSum.unique` |
| 2.7.6 | DEFERRED: the second solution `w₂ = (z−z₀)^{α₂} ∑_{s ≠ α₁−α₂} bₛ (z−z₀)^s + c w₁ ln(z−z₀)` when `α₁ − α₂ ∈ ℕ` | |
| §2.7(i) point at infinity | `infinityF f ζ = 2/ζ − f(1/ζ)/ζ²`, `infinityG g ζ = g(1/ζ)/ζ⁴`, `isODESolution_comp_inv` (`W(ζ) = w(1/ζ)` solves `W″ + infinityF W′ + infinityG W = 0` on `{ζ ≠ 0, 1/ζ ∈ D}`; `z = ∞` is classified as `ζ = 0` for this equation) (`Section7.lean`) | `hasDerivAt_inv`, `HasDerivAt.inv`, `continuousOn_inv₀` |
| §2.7(ii) rank | `PoleOrderCond f g z₀ ℓ` (`(z−z₀)^ℓ f`, `(z−z₀)^{2ℓ} g` extend analytically to `z₀`), `PoleOrderCond.mono`, `HasRank f g z₀ r` (`ℓ = r + 1` least), `HasRank.least`, `HasRank.unique`, `HasRank.not_ordinary`, `HasRank.isRegularSingularity` (rank 0 ⇒ regular singularity), `HasRank.isIrregularSingularity` (rank ≥ 1 ⇒ irregular), `IsRegularSingularity.hasRank_zero_or` ("a regular singularity has rank 0", up to removable singularities of both `f` and `g`), `PoleOrderCond.isOrdinaryPoint` (`Section7Rank.lean`) | `AnalyticAt.congr`, `nhdsNE_sup_pure`, `tendsto_nhds_unique` |
| 2.7.7 | `RankOneData f g a fc gc` (`a > 0`; `f(z) = ∑ fₛ z^{−s}`, `g(z) = ∑ gₛ z^{−s}` for `\|z\| > a`, the power series in `1/z` having radius of convergence at least `1/a`), `RankOneData.dlmf_2_7_7` (absolutely convergent series form); the point at infinity has rank 1 iff one of `f₀, g₀, g₁` is nonzero (`RankOneData.hasRank_one_iff`, via `poleOrderCond_two` and `hasRegularCoefficients_iff`: `∞` satisfies the regular-singularity condition iff `f₀ = g₀ = g₁ = 0`), `RankOneData.isIrregularSingularity` (`Section7Rank.lean`) | `DifferentiableOn.analyticAt`, `Summable.tsum_eq_zero_add` |
| 2.7.8 | `rankOneTrunc fc gc λ N` (`= e^{λz} z^μ ∑_{s≤N} aₛ/z^s`, `rankOneTrunc_eq`, principal branch); `RankOneData.dlmf_2_7_8`: the series is a formal solution — for `\|z\| > a` off `(−∞, 0]`, `w_N″ + f w_N′ + g w_N = e^{λz} z^μ B_N(z)` with `B_N(z) = O(z^{−N−2})` as `z → ∞`; via the derivative operator `frobT` (`HasRadiusGE.hasDerivAt_frobW`), the bracket coefficients `bracketSeq` (`T(Tb) + f ⋆ Tb + g ⋆ b`, `bracketSeq_zero/one/add_two`), `bracketSeq_truncSeq_eq_zero` (first `N+2` coefficients vanish) and `HasRadiusGE.isBigO_pow` (`Section7Formal.lean`) | `hasSum_nat_add_iff'`, `summable_norm_sum_mul_antidiagonal_of_summable_norm`, `tendsto_inv₀_cobounded`, `Asymptotics.IsBigO.comp_tendsto` |
| 2.7.9 | `rankOneChar fc gc λ = λ² + f₀λ + g₀`, `exists_charRoots` (`Section7Rank.lean`) | `Complex.cpow_nat_inv_pow` |
| 2.7.10 | `rankOneMu fc gc λ = −(f₁λ + g₁)/(f₀ + 2λ)`, `rankOneMu_mul`; "the construction fails iff `λ₁ = λ₂`, that is, when `f₀² = 4g₀`": `fc0_add_two_mul_eq` (`f₀ + 2λ₁ = λ₁ − λ₂`), `fc0_add_two_mul_eq_zero_iff`, `charRoots_eq_iff` (`Section7Rank.lean`) | |
| 2.7.11 | `rankOneCoeff fc gc λ μ` (`a₀ = 1`, well-founded recursion over `Fin`), `rankOneCoeff_succ` (reflected form), `dlmf_2_7_11` (DLMF's form with `∑_{r=1}^{s}`, `s ≥ 1`, `f₀ + 2λ ≠ 0`) (`Section7Formal.lean`) | `Finset.sum_range_reflect`, `Finset.sum_Icc_succ_top` |
| 2.7.12–2.7.13 | DEFERRED: the late-coefficient asymptotics `a_{s,1} ∼ Λ₁ (λ₁−λ₂)^{−s} ∑ a_{j,2} (λ₁−λ₂)^j Γ(s+μ₂−μ₁−j)` (Olver 1994a) and the consequent divergence of 2.7.8; they presuppose the solutions 2.7.14 and the Stokes multipliers 2.7.18 | |
| 2.7.14–2.7.16 | DEFERRED: existence, uniqueness and independence of solutions `w_j ∼ e^{λ_j z} ((λ₂−λ₁)z)^{μ_j} ∑ a_{s,j} z^{−s}` in the sectors 2.7.15/2.7.16 (Olver 1997b, Ch. 7: Volterra integral equations along progressive paths in the complex plane, with error bounds) | |
| 2.7.17–2.7.18 | DEFERRED: connection formulas with Stokes multipliers `C₁, C₂` and `Λ₁ = −i e^{(μ₂−μ₁)πi} C₁/(2π)`, `Λ₂ = i C₂/(2π)` (depend on 2.7.14) | |
| 2.7.19 | Fabry's transformation: `fabryF`, `fabryG`, `isODESolution_fabry` (`W(t) = e^{f₀t²/2} w(t²)` solves the transformed equation on `{t ≠ 0, t² ∈ D}`), `fabry_inverse` (`w(z) = e^{−f₀z/2} W(z^{1/2})`); `RankOneData.fabry` (for `f₀² = 4g₀` the transformed coefficients satisfy 2.7.7 for `\|t\| > √a`, `fabryFc`/`fabryGc` with `F̃₀ = 0`, `F̃₁ = 2f₁−1`, `G̃₀ = 4(g₁ − f₀f₁/2)`, `G̃₁ = 0`, via `evenSpread`/`oddSpread`); `RankOneData.fabry_dichotomy` (regular-singularity condition at `t = ∞`, or rank 1 with unequal characteristic roots); `fabry_example_ordinary` (the first case can be an ordinary point) (`Section7Fabry.lean`) | `HasSum.even_add_odd`, `Real.sqrt_lt'`, `Nat.even_or_odd'` |
| 2.7.20 | `IsLGSolution I f g w` (`w` of class `C²` on the open interval `I`, `w″ = (f + g) w`), `IsLGSolution.of_hasDerivAt`, `contDiffOn_two_of_hasDerivAt`; hypotheses `LGSetup I f g ξ` (`I` open, order-connected, nonempty; `f > 0` of class `C²`; `g` continuous; `ξ′ = f^{1/2}`, DLMF's `∫ f^{1/2} dx`). Interval ends: `ioLowerEnd I` / `ioUpperEnd I` (`atBot` / `atTop` on the subtype `I`, finite or infinite ends) (`Section7LG.lean`, `Section7LGVolterra.lean`) | `contDiffOn_succ_iff_deriv_of_isOpen`, `Filter.EventuallyEq.deriv_eq` |
| 2.7.21–2.7.23 | `LGSetup.dlmf_2_7_21` (`w₁ = f^{−1/4} e^{ξ}(1 + ε₁)`, `\|ε₁\|, ½ f^{−1/2} \|ε₁′\| ≤ exp(½ 𝒱_{a₁,x}(F)) − 1`, given `𝒱_{a₁,x}(F) < ∞`), `LGSetup.dlmf_2_7_22` (`w₂ = f^{−1/4} e^{−ξ}(1 + ε₂)`, bounds with `𝒱_{a₂,x}(F)`, by reflection `x ↦ −x`: `LGSetup.reflect`, `lgControl_reflect`, `lgVarUpper_eq`). Proof: Liouville's substitution `w = f^{−1/4} e^{ξ} u` and the Volterra equation `u(x) = 1 − ½ ∫_{a₁}^{x} (1 − e^{2ξ(v)−2ξ(x)}) F′(v) u(v) dv`, solved by Picard iteration (`lgIter`, `\|hₙ\| ≤ (V/2)ⁿ/n!` via `∫_{a₁}^{x} \|F′\| Φ′(V) = Φ(V(x)) − Φ(0)`), `VolterraLG.exists_solution` (`u′ = −f^{1/2} P`, `P′ = −2f^{1/2}P + F′u`, `\|P\| ≤ 2(e^{V/2} − 1)`); relations `phi_sq_mul_sqrt` (`φ² f^{1/2} = 1`), `phi_deriv_rel` (`Section7LGVolterra.lean`, `Section7LG.lean`) | `MeasureTheory.integral_tsum_of_summable_integral_norm`, `continuousOn_tsum`, `tendsto_setIntegral_of_antitone`, `intervalIntegral.integral_hasDerivAt_right`, `exists_hasDerivAt_eq_slope`, `NormedSpace.exp_eq_tsum_div`, `MeasurableEmbedding.setIntegral_map`, `Measure.map_neg_eq_self` |
| 2.7.24 | `lgControl f g = f^{−1/4} (f^{−1/4})″ − g f^{−1/2}` (the integrand `F′` of the error-control function; `lgPhi f = f^{−1/4}`) (`Section7LG.lean`) | |
| 2.7.25 | `volterraV I (lgControl f g) x = ∫_{a₁}^{x} \|F′\|` (`𝒱_{a₁,x}(F)`), `lgVarUpper I f g x = ∫_{x}^{a₂} \|F′\|` (`𝒱_{a₂,x}(F)`); `LGSetup.dlmf_2_7_25`: for any `F` with `F′ = lgControl`, `𝒱_{a₁,x}(F) − 𝒱_{a₁,a}(F)` is the total variation of `F` on `[a, x]` (§2.3(i), via `variationIntegral_eq_toReal` of §1.4(v)) (`Section7LG.lean`) | `eVariationOn` |
| 2.7.26–2.7.27 | `LGSetup.dlmf_2_7_26` (`w₁ ∼ f^{−1/4} e^{ξ}` as `x → a₁+`), `LGSetup.dlmf_2_7_27` (`w₂ ∼ f^{−1/4} e^{−ξ}` as `x → a₂−`), from `𝒱 → 0` at the ends (`VolterraLG.V_tendsto`, `tendsto_setIntegral_ioLowerEnd`, `LGSetup.tendsto_neg_ioUpperEnd`). Uniqueness: DLMF's claim is false as stated (`dlmf_2_7_26_not_unique`: `eˣ` and `cosh x` on `(0, 1)`); DEFERRED: uniqueness under `\|∫ f^{1/2}\| → ∞` (needs IVP uniqueness for linear second-order ODEs) (`Section7LG.lean`) | `squeeze_zero_norm'` |
| 2.7.28–2.7.29 | DEFERRED: the dominant solutions `w₃ ∼ f^{−1/4} e^{ξ}` as `x → a₂−`, `w₄ ∼ f^{−1/4} e^{−ξ}` as `x → a₁+` (need a global existence theorem for linear second-order ODEs on `I`, or a Volterra construction from an interior base point) | |
| 2.7.30 | `dlmf_2_7_30`: if `w₁ ∼ φ e^{ξ}`, `w₄ ∼ φ e^{−ξ}` and `ξ → −∞`, then `w₁/w₄ → 0` (recessive/dominant) (`Section7LG.lean`) | `Real.tendsto_exp_atBot` |
| 2.7.31 | Example `w″ = (x + ln x) w`, treated on `(1, ∞)` with `f = x + ln x` (`exF`), `g = 0`: `exSetup`, `exControl_bound` (`\|F′(x)\| ≤ (3/2) x^{−5/2}`), `exControl_integrableOn`; `dlmf_2_7_31_remark` (`f = x`, `g = ln x` is not admissible: `𝒱_{x,∞}(F) = ∞`) (`Section7LGExample.lean`) | `HasDerivAt.rpow_const`, `Real.hasDerivAt_rpow_const`, `integrableOn_Ioi_rpow_iff` |
| 2.7.32 | `dlmf_2_7_32` (`f^{1/2} = x^{1/2} + ½ x^{−1/2} ln x + O(x^{−3/2} (ln x)²)`), with the explicit `abs_exR_le` (`\|exR\| ≤ (ln x)²/(8 x^{3/2})`) and `abs_exR_le_rpow` (`≤ 8 x^{−5/4}`) (`Section7LGExample.lean`) | `Real.log_le_rpow_div` |
| 2.7.33 | `dlmf_2_7_33`: a solution `w₂ ∼ x^{−1/4−√x} exp(2x^{1/2} − ⅔ x^{3/2})` as `x → +∞`, with `∫ f^{1/2}` normalized (`exXi = exMain − ∫_x^∞ exR`, `exXi_hasDerivAt`, `exXi_sub_exMain_tendsto`) (`Section7LGExample.lean`) | `intervalIntegral_tendsto_integral_Ioi`, `Real.isLittleO_log_id_atTop`, `Real.div_rpow` |
| 2.7.34 | DEFERRED with 2.7.28 (`w₃` dominant) | |
| 2.7.35 | `IsSolW` (`w″ = w` on `ℂ`, as `IsODESolution univ 0 (−1)`), `isODESolution_exp`, `isODESolution_exp_neg`, `isODESolution_cosh`, `isODESolution_sinh`; Wronskians `wronskian_exp_pair` (`= −2`), `wronskian_cosh_sinh` (`= 1`) (`Section7NumSat.lean`) | `Complex.hasDerivAt_exp`, `Complex.hasDerivAt_cosh`, `Complex.cosh_sq_sub_sinh_sq` |
| 2.7.36–2.7.37 | `dlmf_2_7_36`, `dlmf_2_7_37` (`IsFundamentalPair`: every solution is `A e^z + B e^{−z}`, resp. `C cosh z + D sinh z`), via §1.13 `isFundamentalPair_of_wronskian_ne_zero` and `isSCDomain_univ` (`ℂ` is simply connected in DLMF's sense: its complement in `ℂ ∪ {∞}` is `{∞}`); `exp_pair_eq_cosh_sinh` (`C = A + B`, `D = A − B`) (`Section7NumSat.lean`) | `OnePoint.compl_range_coe` |
| §2.7(iv) cancellation, recessive/dominant | `cancelRatio u v = \|u + v\|/(\|u\| + \|v\|)`; `cosh_sinh_cancel` (`C = D ≠ 0`: ratio `→ 0` as `ℜz → −∞`, severe cancellation), `exp_pair_no_cancel_atBot`/`atTop` (ratio `→ 1` as `ℜz → ∓∞` for every `(A, B) ≠ (0, 0)`: the numerically satisfactory pair), `exp_recessive_atBot`, `exp_neg_recessive_atTop` (`e^z/e^{−z} → 0` as `ℜz → −∞`, `e^{−z}/e^z → 0` as `ℜz → +∞`). Not formalized (descriptive): "one member has to be recessive" near a singularity; the oscillatory definition "same amplitude, ½π out of phase" (`Section7NumSat.lean`) | `Complex.norm_exp`, `squeeze_zero'`, `tendsto_of_tendsto_of_tendsto_of_le_of_le` |

### §2.8 Differential Equations with a Parameter

| DLMF | Azurite | Mathlib |
|---|---|---|
| 2.8.1 | `IsParamSolution D u f g w` (`w″ = (u² f + g) w` in `D`) (`Section8.lean`) | |
| §2.8(i) cases | `IsTransitionPoint` (zero or singularity of `f`), `IsCaseI` (no transition points in `D`, `g` analytic), `IsCaseII` (simple zero of `f`, `g` analytic), `IsCaseIII` (simple pole of `f`, `(z−z₀)² g` analytic); `IsCaseI.analyticAt_ne_zero`, `IsCaseII.isTransitionPoint`, `IsCaseIII.isTransitionPoint` (`Section8.lean`) | |
| 2.8.2–2.8.4 | `dlmf_2_8_3` (`W = ż^{−1/2} w`, via `q` with `q² ż = 1`; `d²W/dξ² = (u² ż² f + ψ) W`), `liouvillePsi` (`ψ = ż² g + ż^{1/2} d²(ż^{−1/2})/dξ²`), from §1.13(iv) `dlmf_1_13_19`, `dlmf_1_13_20` (`Section8.lean`) | |
| 2.8.5–2.8.7 | `liouville_choice` (`F′ = s`, `s² = f`, `F(z(ξ)) = H(ξ)`, `H′ = k` ⇒ `ż² f = k²`), `dlmf_2_8_5` (`ż² f = 1`), `dlmf_2_8_6` (`⅔ ξ^{3/2} = ∫ f^{1/2}` ⇒ `ż² f = ξ`), `dlmf_2_8_7` (`2 ξ^{1/2} = ∫ f^{1/2}` ⇒ `ż² f = 1/ξ`); property (a), `ξ` and `z` analytic functions of each other at the transition point: `dlmf_2_8_i_caseI`, `dlmf_2_8_i_caseII`, `dlmf_2_8_i_caseIII` (explicit construction via `exists_analytic_root`, power-series solutions of `(z − z₀)K′ + aK = k` (`exists_euler_ode`), `exists_factor_of_zero`; inverse by `exists_analytic_inverse`) (`Section8.lean`, `Section8Transition.lean`) | `HasDerivAt.cpow_const`, `AnalyticAt.analyticAt_localInverse`, `HasStrictDerivAt.eventually_left_inverse`, `dslope`, `AnalyticAt.cpow` |
| 2.8.8 | `dlmf_2_8_8` (`d²W/dξ² = (u² ξ^m + ψ) W` when `ż² f = ξ^m`) (`Section8.lean`) | |
| §2.8(i) approximating equations | Case I: `caseI_exp` (`e^{±uξ}` solve `W″ = u² W`); Case II: `caseII_airy` (`A(cξ)`, `c³ = u²`, solves `W″ = u² ξ W` when `A″(t) = t A(t)`, the Airy equation of §9.2) (`Section8.lean`) | |
| 2.8.9 | `dlmf_2_8_9`: if `t² y″ + t y′ − (σt² + ν²) y = 0` (`σ = 1` modified Bessel, `σ = −1` Bessel), `W = ξ^{1/2} y(2uξ^{1/2})` solves `W″ = (σu²/ξ + ρ/ξ²) W`, `ρ = (ν² − 1)/4` (order `±(1 + 4ρ)^{1/2}`); `hasDerivAt_cpow_half`. Not formalized: the existence of `ρ = lim ξ² ψ(ξ)` (`Section8.lean`) | |
| 2.8.10 | `IsLGSolution I (fun _ => u²) ψ W` (`d²W/dξ² = (u² + ψ) W`, `C²`), for real `u > 0` and `ξ` in an open interval `I = (α₁, α₂)` (the real-variable case; DLMF's `𝚫` may be a complex domain, with paths along which `ℜv` is monotone) (`Section8CaseI.lean`) | |
| 2.8.11 | `CaseIData.dlmf_2_8_11`: for `n ≥ 1` there is `C` with, for every `u ≥ 1`, a solution `W_{n,1} = e^{uξ}(∑_{s<n} A_s/u^s + η)`, `\|η\| ≤ C/uⁿ`, `\|∂η/∂ξ\| ≤ C/u^{n−1}` on `I` (uniform and differentiable; reference point `α₁`, `𝚫₁(α₁) = I`). Hypotheses `CaseIData` (2.8.13 in derivative form, `𝒱(A₁) = ½∫\|ψ\| < ∞`, `𝒱(Aₙ) = ∫\|Aₙ′\| < ∞`). Proof: the residual of the truncated sum is `−2u^{1−n}Aₙ′e^{uξ}` (`CaseIData.sum_identity`), and `η″ + 2uη′ − ψη = 2u^{1−n}Aₙ′` is solved by `exists_forced_caseI` (forced Volterra equation with kernel `(1 − e^{−2u(ξ−v)})/(2u)`, `Section8Volterra.lean`: `forcedIter`, `VolterraLG.exists_forced_solution`) (`Section8CaseI.lean`) | `HasDerivAt.fun_sum` |
| 2.8.12 | `CaseIData.dlmf_2_8_12`: `W_{n,2} = e^{−uξ}(∑_{s<n} (−1)^s A_s/u^s + η)` with the same bounds (reference point `α₂`), by reflection (`CaseIData.reflect`: `ψ(−ξ)`, `(−1)^s A_s(−ξ)`) (`Section8CaseI.lean`) | |
| 2.8.13 | `dlmfA ψ x₀ c` (`A₀ = 1`, `A_{s+1} = −½A_s′ + ½∫_{x₀}^{ξ} ψA_s + c_s`, constants of integration arbitrary), `dlmf_2_8_13` (for `ψ ∈ C^∞`: every `A_s` is `C^∞` and `2A_{s+1}′ = −A_s″ + ψA_s`), `CaseIData.of_dlmfA` (`Section8CaseI.lean`) | `contDiffOn_infty_iff_deriv_of_isOpen`, `ContDiffOn.deriv_of_isOpen` |
| §2.8(ii) remarks | Not formalized: error bounds, pure imaginary or complex `u`, inhomogeneous equations, independence of `n` (DLMF refers to Olver 1997b, Ch. 10); the complex-domain regions `𝚫_j(α_j)` | |
| 2.8.14 | The equation `d²W/dξ² = (u²ξ + ψ(ξ)) W` on `(α₁, α₂) ∋ 0` (in the residual form of `CaseIIData.dlmf_2_8_15_formal`) (`Section8CaseII.lean`) | |
| 2.8.15–2.8.16 | `CaseIIData.dlmf_2_8_15_formal`: for any solution `(𝒜, 𝒜′)` of Airy's equation (`Ai` or `Bi`), the truncated expansion `𝒜(u^{2/3}ξ)∑_{s<n}A_s/u^{2s} + 𝒜′(u^{2/3}ξ)∑_{s<n−1}B_s/u^{2s+4/3}` satisfies 2.8.14 up to the single residual `u^{2−2n}(A″_{n−1} − ψA_{n−1})𝒜(u^{2/3}ξ)` (coefficient identities `CaseIIData.coeff_Ai`, `coeff_Ai'`); hypotheses `CaseIIData`. DEFERRED: the existence of solutions `W_{n,j}` with the error terms `O(u^{1−2n})` (Olver 1997b, Ch. 11), which need DLMF Ch. 9 Airy theory (Wronskian, asymptotics, modulus and weight-function bounds; Azurite has only the Maclaurin series in `Azurite/Airy/Series.lean`) (`Section8CaseII.lean`) | |
| 2.8.17 | `regB g ξ = ∫_0^1 g(ξσ²) dσ` (`regPhi`), `dlmf_2_8_17_pos` / `dlmf_2_8_17_neg` (DLMF's two one-sided formulas, via equal derivatives and `O(√ξ)` at `0`), `regB_ode` (`B + 2ξB′ = g`), `regPhi_hasDerivAt`, `regPhi_smooth` (`C^∞` through the turning point) (`Section8CaseII.lean`) | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `integral_rpow`, `intervalIntegral.integral_comp_neg`, `contDiffOn_infty` |
| 2.8.18 | `caseIIA`, `caseIIB`, `caseIIBOf`, `dlmf_2_8_18` (all `A_s`, `B_s` are `C^∞`; `B_s + 2ξB_s′ = ψA_s − A_s″`; `2A_{s+1}′ = −B_s″ + ψB_s`; constants of integration arbitrary) (`Section8CaseII.lean`) | |
| 2.8.19 | DEFERRED: `c = −0.36604…`, the root of `Ai(x) = Bi(x)` of smallest absolute value (needs Airy functions); used as a hypothesis | |
| 2.8.20–2.8.21 | `envAi`, `envBi`, `envAi_envBi_continuous` ("these envelopes are continuous", given `Ai(c) = Bi(c) ≥ 0`), `abs_le_envAi` (`\|Ai\| ≤ envAi`, `\|Bi\| ≤ envBi` for `x ≤ c`) (`Section8CaseII.lean`) | `Continuous.if_le` |
| 2.8.22–2.8.23 | DEFERRED with 2.8.15–2.8.16 | |
| 2.8.24 | The equation `d²W/dξ² = (u²/(4ξ) + (ν² − 1)/(4ξ²) + ψ(ξ)/ξ) W` on `(α₁, α₂) ∋ 0` (in the residual form of `CaseIIIData.dlmf_2_8_25_formal`) (`Section8CaseIII.lean`) | |
| 2.8.25–2.8.26, 2.8.29–2.8.30 | `IsCaseIIIPair` (`a′ = ((ν+1)/(2ξ))a + (u/(2ξ))b`, `b′ = (u/2)a + ((1−ν)/(2ξ))b`); `besselPair_pos` (`ξ^{1/2}𝓕_ν(uξ^{1/2})`, `ξ𝓕_{ν+1}(uξ^{1/2})` for `(I_ν, I_{ν+1})`, `(K_ν, −K_{ν+1})`, from the recurrences 10.29.2), `besselPair_neg` (`\|ξ\|^{1/2}𝓕_ν(u\|ξ\|^{1/2})`, `−\|ξ\|𝓕_{ν+1}(u\|ξ\|^{1/2})` for `(J_ν, J_{ν+1})`, `(Y_ν, Y_{ν+1})`, from 10.6.2); `CaseIIIData.dlmf_2_8_25_formal`: the truncated expansion `a∑_{s<n}A_s/u^{2s} + b∑_{s<n−1}B_s/u^{2s+1}` satisfies 2.8.24 up to the single residual `a·u^{2−2n}(A″_{n−1} + (ν+1)A′_{n−1}/ξ − ψA_{n−1}/ξ)` (coefficient identities `CaseIIIData.coeff_a`, `coeff_b`); hypotheses `CaseIIIData`. DEFERRED: the existence of solutions `W_{n,j}` with the error terms (Olver 1997b, Ch. 12), which need DLMF Ch. 10 Bessel theory (Azurite has no Bessel functions) (`Section8CaseIII.lean`) | |
| 2.8.27, 2.8.31 | `caseIIIBOf` (`B = −A′ + 2∫_0^1 g(ξσ²) dσ`, `g = ψA − (ν + ½)A′`, `C^∞` through the pole), `dlmf_2_8_27` (`ξ > 0`), `dlmf_2_8_31` (`ξ < 0`), both from `dlmf_2_8_17_pos` / `dlmf_2_8_17_neg` (`Section8CaseIII.lean`) | |
| 2.8.28 | `caseIIIA`, `caseIIIB`, `dlmf_2_8_28` (all `A_s`, `B_s` are `C^∞`; `ξB_s′ + ½B_s = ψA_s − (ν+1)A_s′ − ξA_s″`; `A_{s+1}′ = (ν−1)B_s′ − ξB_s″ + ψB_s`; constants of integration arbitrary) (`Section8CaseIII.lean`) | |
| 2.8.32 | DEFERRED: `X_ν`, the smallest positive root of `J_ν(x) + Y_ν(x) = 0` (needs Bessel functions); used as a hypothesis | |
| 2.8.33–2.8.34 | `envJ`, `envY`, `envJ_envY_continuous` (continuous given `J(X) + Y(X) = 0`, `J(X) ≥ 0`) (`Section8CaseIII.lean`) | `Continuous.if_le` |
| 2.8.35–2.8.36 | DEFERRED with 2.8.25–2.8.30 | |
| §2.8(v) Multiple and Fractional Turning Points | Not formalized: no numbered equations. Descriptive survey (multiple turning point: `f` has a zero of multiplicity `λ = 2, 3, 4, …`, `g` analytic; fractional: `(z−z₀)^{−λ} f` and `g` analytic, `λ > −2`); uniform approximations by Bessel functions of order `1/(λ+2)`, approximations but not expansions for `λ ≠ 0, ±1`; results and error bounds in Olver (1977c), connection formulas in Olver (1977a, 1977b, 1978) | |
| §2.8(vi) Coalescing Transition Points | Not formalized: no numbered equations. Bibliographic survey (coalescing turning points: parabolic cylinder functions; turning point and double pole: Bessel functions of variable order; turning point and simple pole: Whittaker functions) with cross-references to later chapters | |

### §2.9 Difference Equations

| DLMF | Azurite | Mathlib |
|---|---|---|
| 2.9.1 | `IsDiffSolution f g w` (`Section9.lean`) | |
| 2.9.2 | `dlmf_2_9_2`, `dlmf_2_9_1_iff_2_9_2` (`Section9.lean`) | `fwdDiff` |
| 2.9.3 | `IsAsympSeqDLMF` (Poincaré along the integers), `isAsympSeqDLMF_iff`; calculus `HasAsympSeries` (`add`, `const_mul`, `sum`, `mul` via `seqConv`, `pow_mul`, `hasAsympSeries_one_add_cpow`) (`Section9.lean`) | `Complex.one_add_cpow_hasFPowerSeriesAt_zero`, `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` |
| 2.9.4 | `dlmf_2_9_4`: each truncation `diffTrunc` of `ρⁿ n^α ∑ aₛ/nˢ` satisfies 2.9.1 up to `ρⁿ n^α B_N(n)`, `B_N = O(n^{−N−2})`; residual identity `formalTrunc_residual`, coefficient identities `diffCoeff_vanish` (`Section9Formal.lean`) | |
| 2.9.5 | `dlmf_2_9_5` (roots, `ρ₁ = ρ₂ ↔ f₀² = 4g₀`), `dlmf_2_9_construction_fails` (`f₀ + 2ρ = 0 ↔ f₀² = 4g₀`), `charRoot_ne_zero` (`Section9Formal.lean`) | `IsAlgClosed.exists_eq_mul_self` |
| 2.9.6 | `diffAlpha`, `diffT_one` (`T(s, 1) = −sρ(f₀ + 2ρ)`) (`Section9Formal.lean`) | |
| 2.9.7 | `diffCoeff`, `diffCoeff_succ`, `dlmf_2_9_7` (DLMF's form) (`Section9Formal.lean`) | `Ring.choose` |
| 2.9.8 | `IsDiffAsympDLMF`, `HasLeading` (`IsDiffAsympDLMF.hasLeading`); consequences for any solutions with these behaviours: `dlmf_2_9_8_independent`, `HasLeading.tendsto_ratio`. DEFERRED: the existence of the solutions `w_j` (Wong and Li 1992b) and error bounds (Zhang et al. 1996) (`Section9Recessive.lean`) | |
| §2.9(i) recessive/dominant | `dlmf_2_9_8_recessive` (`\|ρ₂\| > \|ρ₁\|`, or equal and `ℜα₂ > ℜα₁` ⇒ `w₁/w₂ → 0`), `dlmf_2_9_8_neither` (equal moduli and real parts ⇒ `\|w₁/w₂\| → 1`), `dlmf_2_9_8_recessive_unique` (via `casoratian`, `IsDiffSolution.eq_comb`, `exists_casoratian_ne_zero`), `dlmf_2_9_8_dominant_not_unique`. Not formalized: the informal remark on numerically satisfactory pairs; inverse factorial series (Olde Daalhuis 2004a) (`Section9Recessive.lean`) | |
| 2.9.9 | `dlmf_2_9_9` (each truncation `sqrtTrunc` of `ρⁿ e^{κ√n} n^α ∑ cₛ/n^{s/2}` satisfies 2.9.1 up to `ρⁿ e^{κ√n} n^α O(n^{−(N+4)/2})`), `dlmf_2_9_9_pair` (`κⱼ = (−1)ʲκ`, coefficients `(−1)^{js}cₛ` via `sqCoeff_neg`); residual `sqrtTrunc_residual`, bracket series `sqBracket_series`, coefficients `sqCoeff` ("determined by formal substitution"), `sqCoeff_vanish`. DEFERRED: the existence of the solutions `w_j` (Wong and Li 1992b) (`Section9Sqrt.lean`) | `Complex.exp_bound`, `Complex.one_add_cpow_hasFPowerSeriesAt_zero` |
| 2.9.10 | `dlmf_2_9_10`: `T(s, 0) = T(s, 1) = 0`; `T(s, 2) = 0 ↔ g₀κ² = 2f₀f₁ − 4g₁`; then (`κ ≠ 0`) `T(0, 3) = 0 ↔ 4g₀α = g₀ + 2g₁`; `sqT_three_eq` (`T(s, 3) = −κg₀s/2`), `kappa_ne_zero` (`Section9Sqrt.lean`) | |
| 2.9.11 | `coincPoly`, `dlmf_2_9_11` (factorization `2g₀(α − α₁)(α − α₂)`), `coinc_T_one`, `coinc_T_two` (`T(s, 2) = P(α − s)/2`) (`Section9Coincident.lean`) | `IsAlgClosed.exists_eq_mul_self` |
| 2.9.12 | `coincCoeff`, `dlmf_2_9_12` (formal solutions for a root `α` with `P(α − m) ≠ 0`, `m ≥ 1`), `dlmf_2_9_12_coeff` (the coefficients satisfy 2.9.7), `dlmf_2_9_12_pair` (`α₂ − α₁ ∉ ℤ`: both roots), `dlmf_2_9_12_first` (`α₂ − α₁ ∈ ℕ`: `j = 1`); the parenthetical remark corrected in `dlmf_2_9_ii_coeff` (errata). DEFERRED: existence of `w_j` (`Section9Coincident.lean`) | |
| 2.9.13 | DEFERRED: logarithmic solutions when `α₂ − α₁ = 0, 1, 2, …` (compare the deferred 2.7.6) | |
| 2.9.14 | Not formalized: pointer to Wong and Li (1992a) for `w(n+2) + n^P f(n) w(n+1) + n^Q g(n) w(n) = 0` | |
| §2.9(iii) Other Approximations | Not formalized: no numbered equations. Bibliographic survey (Liouville–Green analogues with error bounds: Spigler and Vianello 1992, 1997, Spigler et al. 1999; turning points and uniform expansions: Wang and Wong 2003, 2005; arbitrary order: Wimp 1984; orthogonal polynomials: Wang and Wong 2012, Wong 2014, Dai et al. 2014) | |

### §2.10 Sums and Sequences

| DLMF | Azurite | Mathlib |
|---|---|---|
| §2.10(i) `B̃ₙ` | `periodicBernoulli` (`B̃ₙ(x) = Bₙ(x − ⌊x⌋)`), `periodicBernoulli_bound` (`Section10.lean`) | `bernoulliFun`, `bernoulli` |
| 2.10.1 | `dlmf_2_10_1` (Euler–Maclaurin for integers `a < n`, `m > 0`, derivatives up to `f^{(2m)}`, `f^{(2m)}` absolutely integrable); `em_sum` (any real start `t`), `em_unit`, `em_iter`, `em_alt_sum` (`Section10.lean`) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `hasDerivAt_bernoulliFun`, `bernoulli_eq_zero_of_odd` |
| 2.10.2 | DEFERRED: the Abel–Plana formula (contour integration on the strip `a ≤ ℜz ≤ n`, the mean-value parameter `ϑₙ`) | |
| 2.10.3 | `exS` (`Section10Example.lean`) | |
| 2.10.4 | `dlmf_2_10_4` (one constant `C` for all `m ≥ 2`, via `exC_succ` and `const_eq_of_tendsto`); `exS_eq`, `exTerm` (`Section10Example.lean`) | `Real.hasDerivAt_mul_log` |
| 2.10.5 | `jlogR`; `dlmf_2_10_5_bound` (sign `(−1)^m`, `R_m − R_{m+1}` is the term `s = m`, `\|R_m\| ≤` that term, same sign); `periodicBernoulli_sub_sign` ("`B̃_{2m}(x) − B_{2m}` is of constant sign `(−1)^m`", from the Fourier series), `em_tail`, `emRem_sign`, `remainder_bound` (`Section10Tail.lean`, `Section10Example.lean`) | `hasSum_one_div_nat_pow_mul_cos`, `intervalIntegral_tendsto_integral_Ioi` |
| 2.10.6 | DEFERRED: `C = (γ + ln 2π)/12 − ζ′(2)/(2π²) = 1/12 − ζ′(−1)` (DLMF derives it from 2.10.2; needs `ζ′`, §25.2) | |
| 2.10.7 | DEFERRED: `∑_{j<n} j^α ∼ ζ(−α) + …`; the Euler–Maclaurin machinery applies, but identifying the constant with `ζ(−α)` for `α > −1` needs the analytic continuation of the constant in `α` | |
| 2.10.8 | `dlmf_2_10_8` (constant `γ`: `emConst_inv_eq_gamma` from `Real.tendsto_harmonic_sub_log`), `dlmf_2_10_8_bound` (remainder bounded by the first neglected term, same sign) (`Section10Example.lean`) | `Real.tendsto_harmonic_sub_log`, `harmonic_eq_sum_Icc` |
| §2.10(i) closing remarks | Not formalized: pointers to Sidi (2004, 2012a, 2012b), Weniger (2007), Elliott (1998) | |
| 2.10.9–2.10.10 | `dlmf_2_10_9` (summation by parts), `partialSumU` (`Section10Parts.lean`) | |
| 2.10.11 | `sumOsc` (`Section10Parts.lean`) | |
| 2.10.12 | `dlmf_2_10_12` (`\|S\| ≤ ∑ j^α`; `∑ j^α` bounded for `α < −1`, `≤ 1 + ln n` for `α = −1`, `≤ (1 + 1/(α+1)) n^{α+1}` for `α > −1`); `sum_rpow_le` (`≤ K(n^{γ+1} + 1)` for `γ ≠ −1`) (`Section10Parts.lean`) | `Real.summable_nat_rpow`, `harmonic_le_one_add_log`, `exists_hasDerivAt_eq_slope` |
| 2.10.13 | `dlmf_2_10_13` (`Section10Parts.lean`) | |
| 2.10.14 | `dlmf_2_10_14` (`Section10Parts.lean`) | |
| 2.10.15 | `dlmf_2_10_15` (`\|j^α − (j+1)^α + αj^{α−1}\| ≤ \|α(α−1)\| C j^{α−2}`, `C = max(1, 2^{α−2})`, all `j ≥ 1`) (`Section10Parts.lean`) | `norm_image_sub_le_of_norm_deriv_le_segment'` |
| 2.10.16 | `dlmf_2_10_16` (remainder `sumOscRem` with `\|e\| ≤ K(n^{α−1} + 1)`, all `n ≥ 1`); `sumOsc_decomp` (`Section10Parts.lean`) | |
| 2.10.17 | `dlmf_2_10_17` (`\|S\| ≤ K(n^α + 1)`) (`Section10Parts.lean`) | |
| 2.10.18 | `dlmf_2_10_18` (`\|S − e^{inβ}n^α/(e^{iβ} − 1)\| ≤ K(n^{α−1} + 1)`); extensions (Olver 1997b, Ch. 8) not formalized (`Section10Parts.lean`) | |
| 2.10.19 | `hyp0F2` (`₀F₂(−; 1, 1; x) = ∑ xʲ/(j!)³`), `summable_hyp0F2`, `summable_hyp0F2_complex` (entire) (`Section10Entire.lean`) | `Real.summable_pow_div_factorial` |
| 2.10.20 | DEFERRED: the contour representation `∑_{j<n} xʲ/(j!)³ = (1/2i)∫_𝒞 x^t cot(πt)/Γ(t+1)³ dt` (residue theorem on the contour of Figure 2.10.1) | |
| 2.10.21 | `dlmf_2_10_21` (`cot(πt)/(2i) = −½ − 1/(e^{−2πit} − 1) = ½ + 1/(e^{2πit} − 1)`, `t ∉ ℤ`) (`Section10Entire.lean`) | `Complex.cot_pi_eq_exp_ratio` |
| 2.10.22–2.10.23 | DEFERRED: Cauchy deformation and the vanishing of the quarter-circle integrals, which need the complex Stirling bounds 5.11.7 for `1/Γ(t+1)³` | |
| 2.10.24 | `dlmf_2_10_24` (`AsympEqDLMF`): proved by a real-variable route (DLMF's route goes through 2.10.23 and Laplace's method): `₀F₂(v¹⁵) = e^{3v⁵}∑ bⱼ³` (`hyp0F2_eq`), Stirling form `poissonW_eq`, Taylor bound `entPhi_taylor`, tails `poissonW_tail` via `entPhi_tangent`, window terms `window_term`, Gaussian Riemann sum `tendsto_gaussSum`, squeeze `tendsto_main` (`Section10Entire.lean`) | `Stirling.tendsto_stirlingSeq_sqrt_pi`, `Stirling.stirlingSeq'_antitone`, `integral_gaussian`, `Real.abs_log_sub_add_sum_range_le` |
| §2.10(iii) closing remarks | Not formalized: pointers to Olver (1997b, Ch. 8), Ford (1960), Berndt and Evans (1984), Paris and Kaminski (2001, Ch. 5), §16.11 | |
| 2.10.25 | `dlmf_2_10_25` (from §1.10's `dlmf_1_10_6`) (`Section10Darboux.lean`) | |
| 2.10.26 | `dlmf_2_10_26` (positively oriented Jordan curve in the annulus enclosing `0`, via the residue theorem `dlmf_1_10_8`); `laurentCoeff_fourier` (circle form `fₙ = (2πρⁿ)⁻¹∫_0^{2π} f(ρe^{iθ})e^{−inθ}dθ`) (`Section10Darboux.lean`) | |
| §2.10(iv) conditions (a)–(c), (b´), 2.10.27, 2.10.30 | `DarbouxCond` (finitely many singular points on `\|z\| = r` with `O((z − zⱼ)^{σⱼ−1})`, `σⱼ > 0`, continuity elsewhere; (b) via `darbouxCond_of_continuousOn`); `DarbouxCond.tendsto` (radial limit by dominated convergence), `integrable_norm_exp_sub_rpow`, `norm_exp_sub_exp_ge` (Jordan's inequality), `norm_sub_ge_of_circle`; 2.10.27 (`g`'s coefficients) is `laurentCoeff g` (`Section10Darboux.lean`) | `Real.mul_le_sin`, `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`, `Function.Periodic.intervalIntegrable` |
| 2.10.28 | `dlmf_2_10_28` (both forms; `h` is `f − g` extended to `\|z\| = r`) (`Section10Darboux.lean`) | |
| 2.10.29 | `dlmf_2_10_29` (`rⁿ(fₙ − gₙ) → 0` as `n → ±∞`, under (b´)) (`Section10Darboux.lean`) | Riemann–Lebesgue `tendsto_intervalIntegral_mul_exp_cocompact` (§1.8) |
| 2.10.31–2.10.32 | `dlmf_2_10_31` (`rⁿ\|n\|^m\|fₙ − gₙ\| → 0` when `f^{(m)} − g^{(m)}` satisfies (b) or (b´)); proved from 2.10.29 for the derivatives and `laurentCoeff_iterate_deriv`, not by integrating by parts (`Section10Darboux.lean`) | `circleIntegral.integral_eq_zero_of_hasDerivWithinAt` |
| §2.10(iv) Example setup | `legendreP` (Bonnet recurrence, 18.9.1); `α ∈ (0, π)`, not `(0, 2π)` (erratum, `dlmf_2_10_36_false`); coefficient calculus `laurentCoeff_add'`/`_const_mul`/`_mul_id`/`_zero'`, `hasSum_taylor` (Taylor series from `laurentCoeff`), `laurentCoeff_ode` (coefficient recurrence of `(p₀ + p₁z + p₂z²)G′ = (q₀ + q₁z)G`) (`Section10Legendre.lean`) | `DifferentiableOn.hasFPowerSeriesOnBall`, `cauchyPowerSeries_apply`, `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` |
| 2.10.33 | `dlmf_2_10_33` (`HasSum`, `\|z\| < 1`) for `legendreGen = (1 − ze^{iα})^{−1/2}(1 − ze^{−iα})^{−1/2}` (principal powers; `legendreGen_sq`, `legendreGen_zero` fix the branch); coefficients via the ODE `(1 − 2z cos α + z²)f′ = (cos α − z)f` (`legendreGen_ode`, `laurentCoeff_legendreGen`) | `HasDerivAt.cpow_const` |
| 2.10.34 | `legendreCmp` (`A₊(1 − ze^{iα})^{−1/2} + A₋(1 − ze^{−iα})^{−1/2}`; DLMF's grouping `legendreCmp_comb`, branch `legendreBranch_sq`) | |
| 2.10.35 | `dlmf_2_10_35` (`laurentCoeff_hsq`: `(1 − βz)^{−1/2}` has coefficients `βⁿΓ(n+½)/(√π n!)`, from its ODE) | `Real.Gamma_one_half_eq` |
| (b´) for the example | `legendre_darbouxCond` (`f′ − g′`, `σ = ½` at `e^{±iα}`; `legendreAP_eq`/`legendreAM_eq`: `A₊ = (1 − e^{−2iα})^{−1/2}`, `A₋ = (1 − e^{2iα})^{−1/2}`; local estimate `sing_bound`) | `HasDerivAt.isBigO_sub`, `Complex.norm_cpow_real`, `Complex.log_exp` |
| 2.10.36 | `dlmf_2_10_36` (`n\|Pₙ(cos α) − (2/(πn sin α))^{1/2} cos(nα + ½α − ¼π)\| → 0`, `0 < α < π`), from `dlmf_2_10_31` (`m = 1`, `r = 1`) and `halfGamma_bounds` (`(n+½)^{−1/2} ≤ Γ(n+½)/n! ≤ n^{−1/2}` by log-convexity, in place of 5.11.7); `dlmf_2_10_36_false` (fails for `π < α < 2π`) | `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma` |

### §2.11 Remainder Terms; Stokes Phenomenon

Numerical claims are computed by `AzFloat` (interval evaluation with directed rounding, `AzFloat/Interval.lean`), checked in the kernel (`decide +kernel`), and turned into real bounds by `AzFloat/Equiv/Interval.lean`.

| DLMF | Azurite | Mathlib |
|---|---|---|
| §2.11(i) advice (judging accuracy by the size of terms, comparison with a nonasymptotic method, sectors of validity and Stokes lines) | Not formalized (no mathematical content) | |
| `φ = 1/(t² + 1)` and its derivatives | `cauchyD k = (−1)^k k! ℑ((t − i)^{−k−1})` (`hasDerivAt_cauchyD`, `cauchyD_zero`, `cauchyD_eq`, `cauchyD_odd_zero`, bounds `abs_cauchyD_le`, `abs_cauchyD_odd_le`, `abs_cauchyD_le_pow`, `abs_cauchyD_le_inv`) (`Section11.lean`) | `hasDerivAt_zpow`, `HasDerivAt.comp_ofReal` |
| 2.11.1 | `cosIntI` | |
| 2.11.2 | `dlmf_2_11_2` (remainder after `n` terms `≤ (\|q_{n+1}(π)\| + ∫_0^π \|φ^{(2n+2)}\|)/m^{2n+2}` for every integer `m ≥ 1`), from the exact form `dlmf_2_11_2_exact` (`ibp_two`, two integrations by parts per step); `q_s = (−1)^{s−1}φ^{(2s−1)}` (`cosIntQ`) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` |
| 2.11.3 | `dlmf_2_11_3` | |
| "On rounding to 5D, `q₁(π) = −0.05318`, …" | `dlmf_2_11_i_q_decimals` (AzFloat decimal rendering of both ends of each enclosure), `dlmf_2_11_i_q_values` (`\|q_s(π) − v_s\| < 5·10^{−6}`) (`Section11Numerics.lean`) | |
| 2.11.4 | `dlmf_2_11_4_term_decimals`, `dlmf_2_11_4_decimals` (the terms and the sum to 7D), `dlmf_2_11_4` (`\|S₃ + 0.0005271\| < 5·10^{−8}`) | |
| "to 7D `I(10) = −0.0004558`" | `dlmf_2_11_i_I10_decimal`, `dlmf_2_11_i_I10`, via `cosIntI_add_tail` (`I(m) + ∫_π^∞ = ½πe^{−m}`, from §1.14 `integral_poisson_kernel_cos`) and `dlmf_2_11_i_shifted` with `n = 3` | `integral_Ioi_mul_deriv_eq_deriv_mul` |
| "approximately 700 times the last term" | `dlmf_2_11_i_ratio` (`713 < (I(10) + 0.0005271)/10^{−7} < 714`) | |
| "(2.11.2) is a more accurate expansion for `I(m) − ½πe^{−m}`" | `dlmf_2_11_i_shifted` (remainder involves only `[π, ∞)`: `≤ ((2n+1)!/(π² + 1)^{n+1} + (2n+1)!/π^{2n+2})/m^{2n+2}`; tail expansion `cosIntTail_exact`, `ibp_two_tail`, `integral_abs_cauchyD_tail_le`) | `integral_Ioi_rpow_of_lt` |
| "the asymptotic series represents an infinite class of functions" | `dlmf_2_11_i_same_expansion` (`I(m)` and `I(m) − ½πe^{−m}` have the same expansion) | |
| §2.11(ii) `E_p` on the Riemann surface of `ln` | `genExpInt p w = e^{(p−1)w} ∫_z^∞ e^{−t}t^{−p} dt`, `z = e^w`, `ph z = ℑw` (DLMF 8.19.1–8.19.3; the second factor `eiP` = `∫_1^∞ − ∫_0^w` of the entire `exp(−e^v)e^{(1−p)v}` by `Complex.wedgeIntegral`), all `p ∈ ℂ`, entire in `w` (`differentiable_genExpInt`); 8.19.12 on the Riemann surface `eiP_succ`; decay `eiP_small` (`Section11Expint.lean`). The analytic continuation in `p` for `ℜp ≤ 0` is the definition (8.19.1), not proved from 2.11.5 | `Complex.wedgeIntegral`, `Differentiable.isExactOn_univ` |
| 2.11.5 | `dlmf_2_11_5` (`ℜp > 0`, `\|ph z\| < π/2`, principal `z^{p−1}`): the ray `t = z + σ` and Fubini (`gamma_mul_integral_eq`) (`Section11ExpintLaplace.lean`) | `MeasureTheory.integral_integral_swap` |
| 2.11.6 | `dlmf_2_11_6` (remainder after `n` terms `≤ C\|e^{−z}\|/\|z\|^{n+1}` for `\|z\| ≥ 1`, `\|ph z\| ≤ 3π/2 − δ`), from the exact `genExpInt_expansion` (repeated integration by parts in place of Watson's lemma) and the ray bound `norm_eiP_le_sector` (`eiP_eq_ray`: path `t = z(1 + σe^{iθ})`, `θ = rayAngle`, ending on the principal sheet) (`Section11ExpintAsymp.lean`) | |
| "poor accuracy … as ph z approaches ±3π/2" | Not formalized (qualitative) | |
| 8.19.18 (`m = 1`) | `dlmf_8_19_18`: `E_p(ze^{2πi}) = (2πi e^{pπi}/Γ(p)) z^{p−1} + E_p(z)` for all `p`; constant `eiC` = `(e^{2πip} − 1)Γ(1 − p)` for `ℜp < 1` (`eiC_of_re_lt_one`, loop shrunk to `0`, `integral_eiF_eq_Gamma`), `= 2πi e^{pπi}/Γ(p)` by reflection (`reflection_connConst`), all `p` by `eiC_succ` and continuity in `p` (`eiC_eq_connConst`) | `Complex.Gamma_mul_Gamma_one_sub`, `integral_comp_exp`, `Complex.differentiable_one_div_Gamma` |
| 2.11.7 | `dlmf_2_11_7` (`π/2 + δ ≤ ph z ≤ 7π/2 − δ`, `z^{p−1} = e^{(p−1)w}`) | |
| "relatively exponentially small … near ph z = π … dominant after 3π/2" | `dlmf_2_11_ii_small` (`cos(ph z) < 0`: `\|z^{p−1}\|/\|e^{−z}/z\| → 0`), `dlmf_2_11_ii_dominant` (`cos(ph z) > 0`: `→ ∞`); "increasingly significant" between not formalized | `Filter.Tendsto.atTop_mul_neg` |
| §2.11(iii) "optimum truncation … `|p + n − 1| = |z|`" | Not formalized (heuristic); 2.11.8 is a choice of `n`, used as the hypothesis `|n + p − ρ| ≤ A` | |
| 2.11.9 | `dlmf_2_11_9` (`Section11Terminant.lean`) | |
| 2.11.10 | `dlmf_2_11_10` (exact for every `n`, `p` not a nonpositive integer), from `genExpInt_expansion` and `ascPochhammer_eval_eq_Gamma` | |
| 2.11.11 | `terminant q w = Γ(q)/(2π) · E_q(z)/z^{q−1}` (second form, the definition); first form `dlmf_2_11_11` (`ℜq > 0`, `\|ph z\| < π/2`, from `dlmf_2_11_5`) | |
| 2.11.12 | `dlmf_2_11_12` (`q = ρ + α`, `\|θ\| < π/2`) | |
| "rotate the integration path through an angle −θ … valid by analytic continuation when −π < θ < π" | `gamma_mul_eiP_rotated`, `terminant_rotated` (proved by Fubini from the ray representation `eiP_eq_ray`, not by continuation) | `MeasureTheory.integral_integral_swap`, `integral_comp_mul_left_Ioi` |
| 2.11.13 | `dlmf_2_11_13`: all orders, uniformly for `\|θ\| ≤ π − δ`, `\|α\| ≤ A`, with the prefactor `Γ(ρ)ρ^{−ρ}/(2π)` in place of `e^{−ρ}/(2πρ)^{1/2}` and coefficients `ahat` (`Section11TerminantAsymp.lean`; Laplace's method by moments: `gMom`, `gMom_rec`, `gMom_bound`, `mPoly`, binomial remainder `binomRem_bound`, `J_expansion`). DEFERRED: DLMF's normalization needs Stirling's series 5.11.3 for real `Γ` (`a_{2s}` = Cauchy product of `â_{2s}` with the Stirling coefficients) | `integral_Ioi_of_hasDerivAt_of_tendsto`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` |
| 2.11.14 | `ahat_zero` (`a_0 = 1`), `ahat_one`, `dlmf_2_11_14` (`a_2 = â_2 + 1/12`, `1/12` the first Stirling coefficient) | |
| "exponentially improved" | `dlmf_2_11_iii_exp_improved` (remainder of 2.11.10 is `O(ρ^{ℜp−1}e^{−ρ}\|e^{−z}\|)` uniformly in `\|ph z\| ≤ π − δ`; `gMom_zero_le_exp`: `Γ(ρ)ρ^{−ρ} ≤ e^{1−ρ}`) | |
| 2.11.15–2.11.18 | DEFERRED: the erfc re-expansion needs the complementary error function (§7.2(i)) and uniform asymptotics for a saddle point coalescing with a pole (Olver 1991a); `c(θ)` (2.11.16) and `h_{2s}` (2.11.17, 2.11.18) not defined yet | |
| "For the sector −3π + δ ≤ ph z ≤ π − δ the conjugate result applies" | DEFERRED with 2.11.15 | |
| §2.11(iv) two expansions in `π/2 < ph z < 3π/2` | `dlmf_2_11_iv_two_expansions` (2.11.6 and 2.11.7 both hold in closed subsectors; `E_p` entire in `w`, `differentiable_genExpInt`) (`Section11Stokes.lean`) | |
| 2.11.16 `c(θ)` | `stokesC = (π − θ)(c²/(θ − π)²)^{1/2}` (principal root), `stokesC_sq` (`c² = 2(1 + e^{iθ} + i(θ − π))`), `continuousOn_stokesC` (on `(−π, 3π)`), `tendsto_stokesC_div` (`c(θ) ∼ π − θ`), `stokesC_unique` (the only continuous branch with that behaviour) | `Complex.exp_bound`, `Complex.cpow_ofNat_inv_pow`, `intermediate_value_uIcc` |
| "`c(θ)` lies in the right half-plane" / "in the left half-plane" | `stokesC_re_pos` (all `−π < θ < π`; DLMF `0 ≤ θ ≤ π − δ`), `stokesC_re_neg` (all `π < θ < 3π`; DLMF `π + δ ≤ θ ≤ 3π − δ`) | |
| "of the same exponentially-small order of magnitude as the contribution from the other terms in (2.11.15)" | `dlmf_2_11_iv_same_order` (the Gaussian factor `\|exp(−(√(ρ/2) c(θ))²)\| = \|e^{−ρ−z}\|`), `norm_exp_neg_stokes_le` (`= e^{−ρ(1+cos θ)}`). DEFERRED: the asymptotics of `erfc` itself (7.12.1), hence "differs from 2 by an exponentially-small quantity" and the smooth switching | |
| Stokes lines | `stokes_line_max_dominance` (`\|e^{−z}\| ≤ e^{\|z\|}`, equality iff `ph z = π + 2πk`) | `Real.cos_eq_neg_one_iff` |
| accuracy on `θ = π` (averaging 2.11.6 and 2.11.7, the `h_{2s}` terms), Figure 2.11.1, higher-order Stokes phenomena | DEFERRED with 2.11.15 / not formalized (heuristic, figure, references) | |
| §2.11(v) "expansions in terms of the F-functions … called terminants" (prose, Dingle) | Not formalized (no mathematical content) | |
| 2.11.19 | `odeRem λ μ a W n w` (`R_n(z) = w(z) − e^{λz}z^μ ∑_{s<n} aₛ/z^s` on the Riemann surface, `z = e^w`, `z^μ = e^{μw}`) (`Section11Resurgence.lean`); "optimum `n ≈ \|z\|`" is the hypothesis `\|n − \|z\|\| ≤ B` | |
| 2.11.20, 2.11.21 | Definitions of `R^{(1)}_{m,n}`, `R^{(2)}_{m,n}`: `reexpRem₁`, `reexpRem₂` (prefactors `reexpPref₁`, `reexpPref₂`; `(−1)^{n−1}` written `(−1)^{n+1}`; `F_p(ze^{−πi})` = `terminant p (w − πi)`), `dlmf_2_11_20`, `dlmf_2_11_21` | |
| 2.11.22, 2.11.23 (general rank-one equation) | DEFERRED: need the solutions `w_j` (2.7.14–2.7.16) and the Stokes multipliers `C₁`, `C₂` (2.7.17), deferred in §2.7(ii) (Olde Daalhuis and Olver 1994). Analytic core done: `terminant_uniform` (`F_{ρ+α}(ρe^{iθ}) = O(e^{−\|z\|−z})` uniformly for `\|θ\| ≤ π`, `\|α\| ≤ A`, including the Stokes lines; `norm_Jint_le` by splitting at `\|u − 1\| = ρ^{−1/2}`, `norm_integral_inv_cexp_add_le`, `abs_sub_one_le_norm_cexp_add`, `gMom_zero_le_sqrt` (`Γ(ρ+m)ρ^{−ρ−m} = O(e^{−ρ}ρ^{−1/2})`, Chebyshev)), `terminant_bounded_beyond` (`O(1)` for `π ≤ \|θ\| ≤ 3π`, via `terminant_add_two_pi_I`, `terminant_sub_two_pi_I`) | `integral_inter_add_sdiff`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, `HasDerivAt.clog_real`, `closure_Ioo` |
| 2.11.20–2.11.23, example `w″ + (1 + p/z)w′ = 0` | `incGammaFc`; `incGamma_charRoots` (`λ₁ = −1`, `λ₂ = 0`), `incGamma_mu` (`μ₁ = −p`, `μ₂ = 0`), `incGamma_coeff₁` (`a_{s,1} = (−1)^s(p)_s`), `incGamma_coeff₂` (`a_{s,2} = δ_{s0}`), `incGamma_isODESolution` (`w₁ = Γ(1−p, z)`), `incGamma_dlmf_2_7_14` (sector 2.7.15), `incGamma_dlmf_2_7_17` (`C₁ = 2πie^{−πip}/Γ(p)`, `C₂ = 0`), `incGamma_odeRem` (`R^{(1)}_n = (−1)^n(2π/Γ(p))F_{n+p}`), `incGamma_reexpRem₁` (`R^{(1)}_{m,n} = 0` for `m ≥ 1`: checks the constants of 2.11.20), `incGamma_dlmf_2_11_22` (both cases; second for `π ≤ \|ph z\| ≤ 3π`), `incGamma_dlmf_2_11_23` | |
| "the re-expansions are resurgent", hyperasymptotics, Borel transform, references | Not formalized (prose / references) | |
| §2.11(vi) "the transformations in §3.9 … can also be very effective when applied to divergent asymptotic series" | Not formalized (no mathematical content) | |
| 2.11.24 | `expIntE1` (6.2.1, real `x > 0`); `dlmf_2_11_24` (remainder after `n` terms has sign `(−1)^n` and modulus `≤ n!/x^{n+1}`), from the exact `expIntE1_expansion` (`expIntJ`, integration by parts `expIntJ_succ`) (`Section11Euler.lean`) | `integral_Ioi_of_hasDerivAt_of_tendsto`, `integral_exp_neg_Ioi` |
| 2.11.25 | `dlmf_2_11_25_decimals` (the eleven terms at `x = 5` to 5D, `AzRat.toSci`, kernel); `dlmf_2_11_vi_smallest` (5th and 6th terms smallest); `dlmf_2_11_vi_trunc5` (truncation after 5 terms `= 0.17408`) | |
| 2.11.26 | `dlmf_2_11_26` (`0.17042 21463 ≤ e⁵E₁(5) ≤ 0.17042 21770`, AzFloat: `E₁(5) = E₁(20) + ln 4 + ∑_{k=1}^{80} (−1)^k(20^k − 5^k)/(k·k!) + E`, `integral_exp_neg_div_approx` via the Taylor bound `abs_exp_neg_sub_taylor_le`, `ln2Bracket`, `Encl.exp`, exact `ℚ` sum in the kernel; `e1Scaled_decimals`) | `integral_inv_of_pos`, `integral_pow`, `monotoneOn_of_deriv_nonneg` |
| 2.11.27 | `dlmf_2_11_27_decimals` (kernel), `dlmf_2_11_27` (exact) | |
| 2.11.28 | `dlmf_2_11_28_decimals` (rounded to 5D, ties to even: `−0.000385 → −0.00038`), `dlmf_2_11_28` (exact products; rounded sum `0.00363`, unrounded `0.00362 21875`); "yields 0.17045, which is much closer": `dlmf_2_11_vi_euler_estimate` | |
| "equivalent to re-expanding the remainder … in powers of `1/(x+5)`", second application, Aitken / Wynn, Weniger survey | Not formalized (description / references) | |
| 2.11.29 | DEFERRED: the expansion of `W_{κ,μ}(z)` (§13.19) needs the Whittaker functions of Chapter 13. Plan: define `W_{κ,μ}` (13.14.3 via Kummer `U`), prove 13.19.3 | |
| 2.11.30 | `whitA` (`Section11Levin.lean`); `whitA_example` (`a_n = e^{−1/2} r_n`, `whitR` exact rationals at `z = 1`, `κ = 2.3`, `μ = 0.5`) | |
| Table 2.11.1 | `dlmf_table_2_11_1_a`, `dlmf_table_2_11_1_s`, `dlmf_table_2_11_1_d` (all 33 entries to 8D, both ends of 64-bit AzFloat enclosures `halfEncl`, sound by `isEncl_halfEncl`); "optimum truncation … at `s₄`": `dlmf_2_11_vi_smallest_a` | |
| 2.11.31 | DEFERRED: the value of `W_{2.3,0.5}(1.0)` needs the Whittaker function (plan: AzFloat evaluation from a convergent representation once Chapter 13 exists). The claims comparing with the quoted value are proved: `dlmf_2_11_vi_s4` ("correct to almost 3D": error in `(0.0029, 0.003)`), `dlmf_2_11_vi_d10` (8D), `dlmf_2_11_vi_d20` (13D; `d₂₀ = −0.83299 50268 27501 4`, `levin_d20_decimals`) | |
| 2.11.32 | `levinD` (over any field; `levinW` weights `(−1)^j C(n,j)(j+1)^{n−1}`, `zpow`), `levinD_const_mul` (homogeneity), `levinD_cast` | |
| "extrapolated values may converge to an accurate value on one side of a Stokes line …" | Not formalized (cautionary remark) | |

## Chapter 3: Numerical Methods

### §3.1 Arithmetics and Error Measures (`Azurite/DLMF/Chapter3/Section1*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| §3.1(i) binary/hexadecimal systems, historical remarks | Not formalized (no mathematical content) | |
| 3.1.1, 3.1.2 | `machineNum` (`ℝ_fl` with `p` bits, `E_min ≤ E ≤ E_max`, the bit sum of 3.1.2); `mem_machineNum_iff` (`±M 2^E/2^{p−1}`, `2^{p−1} ≤ M < 2^p`, via `binDigit`/`bitsVal`); `machine_abs_bounds` (`2^E ≤ \|x\| < 2^{E+1}`) (`Section1.lean`) | `Nat.mod_pow_succ`, `Finset.sum_range_reflect` |
| format width `N` | `BinaryFormat` (sign, `p − 1` fraction bits, `N − p` exponent bits) | |
| `ε_M`, machine precision | `machineEps` (`2^{1−p}`), `machineEps_isLeast` (`1 + ε_M` least machine number `> 1`), `machineEps_half` (`½ε_M = 2^{−p}`) | |
| 3.1.3 | `dlmf_3_1_3`, `machineNmin_mem` (both bounds attained); underflow/overflow are the definitions `\|x\| < N_min`, `\|x\| > N_max` (not separately formalized) | |
| IEEE 754-2019 formats, Figure 3.1.1 | `binary32`, `binary64`, `binary128`, `dlmf_figure_3_1_1` (8/11/15 exponent bits, `E_max = 2^{N−p−1} − 1`, `E_min = 1 − E_max`) | |
| machine precisions `0.596 × 10^{−7}`, `0.111 × 10^{−15}`, `0.963 × 10^{−34}` | `dlmf_3_1_ii_precision_decimals` (`AzRat.toSci`, kernel), `dlmf_3_1_ii_precisions` | |
| 3.1.4, 3.1.5 | `roundChop` (`x₋`), `roundChopUp` (`x₊`), `roundChop_bounds`, `roundChop_mem` (machine numbers when `N_min ≤ x ≤ N_max`, `x₊` when `x < N_max`); `roundFloor_eq_roundChop` (Azurite's `round (precisionSet 2 p) .Floor` is chopping), `roundNearest_spec` (`.Nearest` gives the nearer of `x₋`, `x₊`; ties to even), `roundNearest_neg` | `Int.log`, `Int.zpow_log_le_self` |
| "maximum relative error `ε_M`" (chopping) | `roundChop_rel_err` (`< ε_M/(1+ε_M)`), `roundChop_rel_err_lt` (`< ε_M`), `roundChop_rel_err_sharp` (supremum `ε_M/(1+ε_M)`, not attained); see errata | |
| "maximum relative error equal to the machine precision `2^{−p}`" (nearest) | `roundNearest_rel_err` (`≤ 2^{−p}/(1+2^{−p})`), `roundNearest_rel_err_attained` (at `1 + 2^{−p}`); see errata | |
| 3.1.6 | `intervalOp`; `intervalOp_add`, `intervalOp_sub`, `intervalOp_mul` (`min4`/`max4`), `intervalOp_div` (`image_inv_Icc`), `intervalOp_div_unbounded` ("only if the divisor interval does not contain zero"), `encl_intervalOp_add_sub` (rounded end points: `AzFloat.Encl`) (`Section1Interval.lean`) | `Set.image_uncurry_prod`, `IsPreconnected.Icc_subset` |
| §3.1(iii) exact rational arithmetic | Realized by `AzRat` (lowest terms over `AzNat`, `AzRat.toSci`); nothing further to formalize | |
| 3.1.7 | `genLog`, `existsUnique_level` (with `ln_k x ≥ 1` for `k < ℓ`), `levelIndex`, `levelIndexInv_levelIndex` (`Section1LevelIndex.lean`); generalized precision is undefined in the text (not formalized) | `Real.log_le_sub_one_of_pos` |
| 3.1.8–3.1.11 | `absErr`, `relErr`, `relPrec`, `mollErr`; `dlmf_3_1_9`, `mollErr_eq`, `relPrec_ofReal`, `relPrec_symm`, `relErr_relPrec` | |
| references (Goldberg, Overton, Moore, IEEE 1788, Olver 1983, …) | Not formalized | |

### §3.2(i) Gaussian Elimination (`Azurite/DLMF/Chapter3/Section2*.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.2.1, 3.2.2 | The system `Ax = b` for `A : AzMatrix K n n` (any field); the augmented matrix is not formed (the right side is carried by forward elimination) | |
| 3.2.3 | `luU` = `AzMatrix.gaussSteps M n` (BPR Algorithm 8.15 without pivoting), `luU_upper` (`Section2.lean`) | |
| 3.2.4 | `luL` (unit lower triangular), multipliers `luMult` (`ℓ_{ik} = g^{(k)}_{ik}/g^{(k)}_{kk}`) | |
| 3.2.5 | `dlmf_3_2_5` (`A = LU` when `u_{11}, …, u_{n−1,n−1} ≠ 0`), via `gaussSteps_succ_row` and `gaussSteps_invariant` | |
| forward elimination, back substitution | `forwardSubst`/`forwardSubst_spec` (`Ly = b`), `backSubst`/`backSubst_spec` (`Ux = y`), `gauss_solve` (`Ax = b`), `mulVec_mul` | |
| 3.2.6 and the Example | `gaussExampleA`, `dlmf_3_2_6` (`L`, `U`, `LU = A`, kernel), `dlmf_3_2_i_example_solve` (`y = [1, −1, 3]ᵀ`, `x = [1/6, 1/6, 1/6]ᵀ`) | |
| "unduly large multipliers … unstable" | Not formalized (stability heuristic) | |
| partial pivoting, "`\|ℓ_{jk}\| ≤ 1` in all cases" | `pivotRow`, `ppSwap`, `ppElim`, `ppRun`, `gaussPP`, `ppL`, `ppU`, `ppPA`; `gaussPP_factorization` (`PA = LU` for every square matrix), `ppRun_invariant`, `ppR_swap`, `ppR_elim`; `ppRun_mult_le_one`, `ppL_le_one` (`Section2Pivot.lean`) | |
| iterative refinement | `iterative_refinement_lu` (residual `r = b − Ax`, correction from the existing `L`, `U` by forward elimination and back substitution, `x + δx` solves `Ax = b`), `iterative_refinement` (the identity `A(x + δx) = b`); the effect of rounding errors is not formalized | `Matrix.mulVec_add`, `dotProduct_add` |

### §3.2(ii) Gaussian Elimination for a Tridiagonal Matrix (`Azurite/DLMF/Chapter3/Section2Tridiag.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.2.7 | `tridiag`, `triEntry` (sequences indexed from `1`) | |
| "Assume that `A` can be factored as in (3.2.5), but without partial pivoting" | `gaussSteps_tridiag` (the general elimination keeps the closed form `triG` at every step, no pivot hypothesis); `tridiag_LU` (`A = LU` for `d₁, …, d_{n−1} ≠ 0`) | |
| 3.2.8 | `dlmf_3_2_8` (`luL` unit lower bidiagonal with `ℓ_j`) | |
| 3.2.9 | `dlmf_3_2_9` (`luU` upper bidiagonal, `d_j`, `u_j = c_j`) | |
| 3.2.10 | `triD`, `triL`, `dlmf_3_2_10` | |
| 3.2.11 | `triY`, `dlmf_3_2_11` | |
| 3.2.12 | `triX`, `dlmf_3_2_12`; `tridiag_solve` (`Ax = f` for `d₁, …, d_n ≠ 0`), `sum_lower_bidiag`, `sum_upper_bidiag` | `Finset.sum_eq_add`, `Finset.sum_eq_single` |

### §3.2(iii) Condition of Linear Systems (`Azurite/DLMF/Chapter3/Section2Cond.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.2.13 | `dlmf_3_2_13` (`p = 1, 2, …`), `dlmf_3_2_13_inf`, `dlmf_3_2_13_euclidean` (vector norms are Mathlib's `ℓ^p` norms on `WithLp p (Fin n → 𝕜)`) | `PiLp.norm_eq_sum`, `PiLp.norm_eq_ciSup`, `EuclideanSpace.norm_eq` |
| 3.2.14 | `matNorm` (the supremum of the ratios, literally), `matNorm_eq` (= operator norm of `lpCLM`), `matNorm_mulVec_le`, `matNorm_mul_le`, `matNorm_one`. The "max" (attainment) is not separately proved | `Matrix.toLpLin`, `ContinuousLinearMap.opNorm_le_bound` |
| 3.2.15 | `dlmf_3_2_15_one` (largest column sum), `dlmf_3_2_15_inf` (largest row sum, sign vector), `dlmf_3_2_15_two` (`√ρ(AAᴴ)`), `dlmf_3_2_15_two_real` (`√ρ(AAᵀ)`); `eigRadius`, `mem_spectrum_iff_eigen` | `Matrix.l2_opNorm_conjTranspose_mul_self`, `ContinuousLinearMap.spectralRadius_eq_nnnorm`, `Matrix.toEuclideanCLM` |
| 3.2.16 | `condNum`; "`κ(A) ≥ 1`": `one_le_condNum` | |
| 3.2.17 | `dlmf_3_2_17` | `Matrix.nonsing_inv_mul` |
| "the larger the value `κ(A)`, the more ill-conditioned the system" | Not formalized (interpretation of 3.2.17) | |

### §3.2(iv) Eigenvalues and Eigenvectors, §3.2(v) Condition of Eigenvalues (`Azurite/DLMF/Chapter3/Section2Eigen.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.2.18 | `IsRightEigen`, `IsLeftEigen`, `isLeftEigen_iff` (`yᵀA = λyᵀ ↔ Aᵀy = λy`), `IsEigenvalue`; normalized eigenvectors `IsRightEigen.normalize` | `Matrix.mulVec_transpose` |
| 3.2.19 | `dlmf_3_2_19` (`p_n(λ) = det[λI − A]`), `charpoly_isRoot_iff` (zeros = eigenvalues), `isEigenvalue_transpose` | `Matrix.eval_charpoly`, `Matrix.exists_mulVec_eq_zero_iff`, `Matrix.charpoly_transpose` |
| multiplicity, nondefective, "`m` linearly independent eigenvectors" | `IsNondefective`, `charpoly_eq_prod_of_nondefective`, `dlmf_3_2_iv_multiplicity` | `Matrix.charpoly_units_conj`, `Matrix.charpoly_diagonal`, `Polynomial.roots_multiset_prod_X_sub_C`, `Matrix.linearIndependent_cols_iff_isUnit` |
| 3.2.20 | `eigCond`; `eigvec_eq_smul_of_simple`, `dotProduct_ne_zero_of_simple` (`yᵀx ≠ 0`), `one_le_eigCond` ("`κ(λ) ≥ 1`"), `abs_dotProduct_eq_abs_cos` ("`\|yᵀx\| = \|cos θ\|`"), `eigCond_eq_one_of_symm` (symmetric `A`: `κ(λ) = 1`) | `basisOfLinearIndependentOfCardEqFinrank`, `InnerProductGeometry.cos_angle_mul_norm_mul_norm`, `Real.sum_mul_le_sqrt_mul_sqrt` |
| "the calculation of its eigenvalues is a well-conditioned problem" | Not formalized (interpretation) | |

### §3.2(vi) Lanczos Tridiagonalization of a Symmetric Matrix (`Azurite/DLMF/Chapter3/Section2Lanczos.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.2.21 | `lzStep`, `lzState`, `lzV`, `lzα`, `lzβ` with `S = I`, `L = I`; `lzV_one`, `lzα_one`, `lzβ_one`; "`v_jᵀv_k = δ_{j,k}`": `dlmf_3_2_21_orthonormal` (no-breakdown hypothesis, see errata), via `lanczos_orthonormal_aux` | `Matrix.dotProduct_mulVec` |
| 3.2.22 | `lanczosB`, `lanczosV`, `lz_entry` (`v_aᵀAv_b = B_{ab}`), `lanczosV_spec` (`VᵀV = I`, `VᵀAV = B`), `dlmf_3_2_22` (same characteristic polynomial and eigenvalues) | `Matrix.charpoly_units_conj`, `Matrix.inv_eq_left_inv` |
| 3.2.23 | `lanczosP`, `dlmf_3_2_23` (`p₀ = 1`, `p₁ = λ − α₁`, the recurrence), `det_tridiag` (tridiagonal determinant recurrence), `charmatrix_lanczosB` | `Matrix.det_succ_row`, `Matrix.det_succ_column`, `Matrix.det_unique` |
| 3.2.24 (`S`-orthogonality, `S = LᵀL`) | `dlmf_3_2_24` (the recursion), `lanczosS_orthonormal`, `dlmf_3_2_24_orthonormal` (`v_jᵀSv_k = δ_{j,k}`) | `Matrix.transpose_nonsing_inv`, `Matrix.mul_nonsing_inv` |
| relation to Gauss quadrature (§3.5(v)), numerical remarks | Not formalized (§3.5 not yet available; references) | |

### §3.3(i) Lagrange Interpolation (`Azurite/DLMF/Chapter3/Section3.lean`, `Section3Contour.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "the unique polynomial `P_n(z)` of degree not exceeding `n` such that `P_n(z_k) = f_k`" | `lagrange_unique` | `Lagrange.eval_interpolate_at_node`, `Lagrange.degree_interpolate_lt`, `Lagrange.eq_interpolate_of_eval_eq` |
| 3.3.1 | `dlmf_3_3_1`, `dlmf_3_3_1_nodal`, `dlmf_3_3_1_barycentric` (`z` not a node in the last two) | `Lagrange.eval_interpolate_not_at_node`, `Lagrange.eval_interpolate_not_at_node'` |
| 3.3.2 | `dlmf_3_3_2`, `dlmf_3_3_2_delta` | `Lagrange.eval_basis_self`, `Lagrange.eval_basis_of_ne` |
| 3.3.3 | `dlmf_3_3_3` | `Lagrange.eval_nodal` |
| 3.3.3_1 | `dlmf_3_3_3_1` | `Lagrange.nodalWeight_eq_eval_derivative_nodal` |
| 3.3.3_2 | `dlmf_3_3_3_2` | `Lagrange.sum_basis`, `Lagrange.interpolate_one` |
| "most efficient representation" (Berrut–Trefethen) | Not formalized (complexity remark) | |
| 3.3.4 | `lagrangeRem` (definition of `R_n`) | |
| 3.3.5 | `dlmf_3_3_5` (`f` `n + 1` times differentiable on an open set containing `I`; continuity of `f^{(n+1)}` not needed); generalized Rolle `exists_iteratedDeriv_eq_zero` | `exists_deriv_eq_zero`, `Finset.orderEmbOfFin`, `Polynomial.coeff_iterate_derivative` |
| 3.3.6 | `dlmf_3_3_6` (Jordan contour, `f` continuous on the closed region and analytic inside; all nodes `z₀, …, z_n` enclosed, see errata); `nodal_partialFraction`, `ClosedPiecewiseC1.contourIntegral_finsetSum` | `Polynomial.mul_divByMonic_eq_iff_isRoot` |

### §3.3(ii) Lagrange Interpolation with Equally-Spaced Nodes, through Linear Interpolation (`Azurite/DLMF/Chapter3/Section3Equal.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.3.7 | `dlmf_3_3_7` (DLMF's `A_k^n`, `t` not a node), `dlmf_3_3_7'` (cancelled `A_k^n`, every real `t`); `R_{n,t}` = `lagrangeRem (eqNode x₀ h n) f (x₀ + th)`; nodes `eqNode`, `eqNode_injective` | |
| 3.3.8 | `eqN0`, `eqN1`; `eqN0_eq` (`n₀ = −⌊n/2⌋`), `eqN1_eq` (`n₁ = n₀ + n`) | |
| 3.3.9 | `eqSigma`, `eqSigma_eq` (`σ = n mod 2`) | |
| 3.3.10 | `lagCoeff`; `lagCoeff'` (factor `t − k` cancelled), `lagCoeff_eq`; `eqNode_basis_eval` (`A_k^n(t) = ℓ_k(x₀ + th)`), `prod_fin_erase_sub`. At an integer `t = k` with `n₀ < t < n₁` the formula is `0/0` and is read with `t − k` cancelled | `Lagrange.basis`, `Finset.mul_prod_erase` |
| 3.3.11 | `dlmf_3_3_11` (every real `t`; `ξ` in the smallest interval containing `x₀ + th` and the nodes), `eqNode_nodal_eval` | |
| 3.3.12 | `eqBoundCoeff` (max as `sSup` over a `t`-set) | |
| 3.3.13 | `dlmf_3_3_13` (bounded `t`-set) | `IsCompact.bddAbove_image`, `le_csSup` |
| 3.3.14 | `dlmf_3_3_14` (every real `t`), `lagCoeff'_one` | |
| 3.3.15 | `dlmf_3_3_15` (`c₁ = 1/8` on `(0, 1)`, maximum attained at `t = ½`), `dlmf_3_3_15_bound` (`\|R_{1,t}\| ≤ h²\|f''(ξ)\|/8`, `ξ ∈ [x₀, x₀ + h]`) | `IsGreatest.csSup_eq` |

### §3.3(ii) Three-Point and Four-Point Formulas (`Azurite/DLMF/Chapter3/Section3Points.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.3.13 for `t ∈ (n₀, n₁)` | `dlmf_3_3_13_Ioo` (`ξ ∈ [x_{n₀}, x_{n₁}]`) | |
| 3.3.16 | `dlmf_3_3_16` (sum form and written-out form; every real `t`, DLMF: `\|t\| < 1`) | |
| 3.3.17 | `dlmf_3_3_17` | |
| 3.3.18 | `dlmf_3_3_18` (`c₂ = 1/(9√3)` on `(−1, 1)`, attained at `t = 1/√3`), `dlmf_3_3_18_decimal` (`0.0641 ≤ c₂ < 0.0642`), `dlmf_3_3_18_bound` | `Real.lt_sqrt`, `Real.sqrt_lt'`, `abs_le_of_sq_le_sq'` |
| 3.3.19 | `dlmf_3_3_19` (sum form and written-out form; every real `t`, DLMF: `−1 < t < 2`) | |
| 3.3.20 | `dlmf_3_3_20` | |
| 3.3.21 | `dlmf_3_3_21_inner` (`3/128` on `(0, 1)`, attained at `t = ½`), `dlmf_3_3_21_outer` (`1/24` on `(−1, 0) ∪ (1, 2)`, attained at `t = (1 − √5)/2`), `dlmf_3_3_21_decimal`, `dlmf_3_3_21_bound_inner`, `dlmf_3_3_21_bound_outer` | `IsGreatest.csSup_eq` |

### §3.3(ii) Five-Point and Six-Point Formulas (`Azurite/DLMF/Chapter3/Section3PointsFiveSix.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.3.12 bounds | `eqBoundCoeff_bounds` (witness + uniform bound), `eqRem_le_of_coeff_le` | `le_csSup_of_le`, `csSup_le` |
| 3.3.22 | `dlmf_3_3_22` (sum form and written-out form; every real `t`, DLMF: `\|t\| < 2`) | |
| 3.3.23 | `dlmf_3_3_23` | |
| 3.3.24 | `dlmf_3_3_24_inner` (`0.0118 ≤ c₄ < 0.0119` on `(−1, 1)`), `dlmf_3_3_24_outer` (`0.0302 ≤ c₄ < 0.0303` on `(−2, −1) ∪ (1, 2)`); certificates `quintic_le_inner`, `quintic_le_outer`; `dlmf_3_3_24_bound_inner`, `dlmf_3_3_24_bound_outer` (with the upper decimals) | |
| 3.3.25 | `dlmf_3_3_25` (sum form and written-out form; every real `t`, DLMF: `−2 < t < 3`) | |
| 3.3.26 | `dlmf_3_3_26` | |
| 3.3.27 | `dlmf_3_3_27_inner` (`c₅ = 5/1024` exactly on `(0, 1)`), `dlmf_3_3_27_inner_decimal` (`0.00488…`), `dlmf_3_3_27_mid` (`0.00701 ≤ c₅ < 0.00702` on `(−1, 0) ∪ (1, 2)`), `dlmf_3_3_27_outer` (`0.0234 ≤ c₅ < 0.0235` on `(−2, −1) ∪ (2, 3)`); certificates `cubic_le_inner`, `cubic_le_mid`, `cubic_le_outer`; remainder bounds `dlmf_3_3_27_bound_inner`, `_mid`, `_outer` | |

### §3.3(ii) Seven-Point and Eight-Point Formulas (`Azurite/DLMF/Chapter3/Section3PointsSevenEight.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.3.28 | `dlmf_3_3_28` (sum form and written-out form; every real `t`, DLMF: `\|t\| < 3`) | |
| 3.3.29 | `dlmf_3_3_29` | |
| 3.3.30 | `dlmf_3_3_30_inner` (`0.00245 ≤ c₆ < 0.00246`), `dlmf_3_3_30_mid` (`0.00459 ≤ c₆ < 0.00460`), `dlmf_3_3_30_outer` (`0.0190 ≤ c₆ < 0.0191`); certificates `septic_le_inner`, `septic_le_mid`, `septic_le_outer`; `dlmf_3_3_30_bound` (all three `t`-sets) | |
| 3.3.31 | `dlmf_3_3_31` (sum form and written-out form; every real `t`, DLMF: `−3 < t < 4`) | |
| 3.3.32 | `dlmf_3_3_32` | |
| 3.3.33 | `dlmf_3_3_33_inner` (`c₇ = 35/32768` exactly), `dlmf_3_3_33_inner_decimal` (`0.00106…`), `dlmf_3_3_33_mid` (`0.00139 ≤ c₇ < 0.00140`), `dlmf_3_3_33_third` (`0.00321 ≤ c₇ < 0.00322`), `dlmf_3_3_33_outer` (`0.0158 ≤ c₇ < 0.0159`); certificates `quartic_le_inner`, `quartic_le_mid`, `quartic_le_third`, `quartic_le_outer`; `dlmf_3_3_33_bound` (all four `t`-sets) | |

### §3.3(iii) Divided Differences (`Azurite/DLMF/Chapter3/Section3Divided.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.3.34 | `divDiff` (the recursion), `divDiff_succ_seq` (general step for a sequence), `dlmf_3_3_34` (the three displayed cases) | |
| "the divided difference of order `n`" = leading coefficient of `P_n` | `divDiff_eq_coeff`, `interpolate_neville`, `coeff_interpolate`, `coeff_basis_eq_nodalWeight` | `Lagrange.basis_eq_prod_sub_inv_mul_nodal_div`, `Lagrange.nodal_erase_eq_nodal_div`, `Polynomial.coeff_X_sub_C_mul` |
| 3.3.35 | `dlmf_3_3_35` (distinct nodes) | `Lagrange.nodalWeight` |
| 3.3.36 | `dlmf_3_3_36` (`f` `n` times differentiable on an open set containing the smallest interval containing the nodes; `ξ` in that interval), `iterate_derivative_of_natDegree_le` | `Polynomial.coeff_iterate_derivative` |
| 3.3.37 | `dlmf_3_3_37` (Jordan contour, `f` continuous on the closed region and analytic inside; vacuous "for `z ∈ D`", see errata) | |

### §3.3(iv) Newton's Interpolation Formula (`Azurite/DLMF/Chapter3/Section3Newton.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.3.38 | `newton_interpolate` (`P_n` in Newton form), `dlmf_3_3_38` (with `R_n` of §3.3(i)); nodes a sequence distinct on `{0, …, n}` | `Polynomial.natDegree_le_iff_coeff_eq_zero`, `Fin.prod_univ_eq_prod_range` |
| "easy updating" | `newton_update` | |
| "robustness with respect to confluence" | Not formalized (qualitative remark) | |
| `[z₀, z₀, …, z₀] f = f^{(k)}(z₀)/k!` (limiting form) | `divDiff_confluent` (real nodes: ε–δ limit as `k + 1` distinct points tend to `z₀`; `f` `k` times differentiable near `z₀`, `f^{(k)}` continuous at `z₀`). Complex nodes (analytic `f`) deferred: needs the limit under the 3.3.37 contour integral | `Metric.isOpen_iff`, `Metric.continuousAt_iff` |

### §3.3(v) Inverse Interpolation (`Azurite/DLMF/Chapter3/Section3Inverse.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "interchange the roles of the points `z_k` and the function values `f_k`" | `inverse_interpolation` (general `n`), `divDiff_congr` | |
| "solving a nonlinear scalar equation `f(z) = 0`" | `inverse_interpolation_zero` (error of `x(0)` via 3.3.5 for the inverse function) | |
| "combine the methods of §3.8 with direct interpolation and §3.4" | Not formalized (pointer; §3.4, §3.8 not yet available) | |
| 3.3.39 | `dlmf_3_3_39` | |
| Example: `a₁ = −2.33810 7410…`, `f_k = Ai(x_k)` | **Deferred**: needs certified AzFloat `Ai` (Airy arc T3–T8; blocked on `Γ(1/3)` for `c₁ = Ai(0)`, `c₂ = −Ai′(0)`). Python 60-digit series check: `Ai(−2.2) = 0.09614 53780 08`, `Ai(−2.3) = 0.02670 63330 57`, `Ai(−2.4) = −0.04333 41404 4`, `a₁ = −2.33810 74104 6` | |
| 3.3.40 | `dlmf_3_3_40_zero` (`x = −2.33823 2462` from the printed polynomial). **Deferred**: the coefficients `1.44011 1973`, `0.08865 85832` as divided differences of the `Ai` data (they need the unrounded `Ai` values; the 10-digit rounded values give `…3659`, `…5910`) | |
| second inverse step (`[f₀, …, f₃] x = 1.12388 6190`, `x = −2.33810 7409`) | **Deferred** (needs `Ai(x₃)`); correct-digit count proved in `dlmf_3_3_v_correct_digits` | |
| 3.3.41 | `airyNewton2`, `dlmf_3_3_41` (corrected first factor `x + 2.2`, see errata) | |
| 3.3.42 | `dlmf_3_3_42` (`HasDerivAt`; exact constant `0.55906 902575`) | `HasDerivAt.mul`, `HasDerivAt.const_mul` |
| Newton's rule from `−2.5`, `x₃ = −2.33934 0514` | `dlmf_3_3_v_newton_x3` | |
| `[x₀, …, x₃] f = −0.26608 28233`, `x = −2.33810 7373` | `airyNewton3`, `airyNewton3_hasDerivAt`, `dlmf_3_3_v_newton_final` (from the printed divided difference; sign erratum); the divided difference itself deferred (needs `Ai`; numerical drift in the 8th digit, see errata) | |
| "4 / 9 / 8 correct digits" | `dlmf_3_3_v_correct_digits` (given `−2.33810 7411 < a₁ ≤ −2.33810 7410`) | |

### §3.3(vi) Other Interpolation Methods (`Azurite/DLMF/Chapter3/Section3Cardinal.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Hermite, trigonometric, spline, rational, Chebyshev-point and bivariate interpolation; convergence properties | Not formalized (references only) | |
| 3.3.43 | `cardinalFn` (`tsum`), `cardinal_node` (interpolation at `kh`), `cardinal_summable` (absolute convergence under `∑ \|f(kh)\|/(1 + \|k\|) < ∞`); erratum: `cardinalCounter`, `cardinalCounter_term`, `cardinal_not_summable`, `cardinal_partial_sums_atBot` (bounded `f` with divergent series) | `tsum_eq_single`, `Summable.of_norm_bounded`, `Real.not_summable_one_div_natCast`, `Real.tendsto_sum_range_one_div_nat_succ_atTop` |
| 3.3.44 | `sincS` (removable singularity filled with `1`), `dlmf_3_3_44`, `sincS_node`, `abs_sincS_le` | `Real.sinc`, `Real.abs_sinc_le_one`, `Real.sin_int_mul_pi` |
| "For theory and applications see Stenger (1993, Chapter 3)" | Not formalized (reference) | |

## Section 3.4

### §3.4(i) Equally-Spaced Nodes, through 3.4.4 (`Azurite/DLMF/Chapter3/Section4.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.4.1 | `dlmf_3_4_1` (every real `t`; DLMF: `n₀ < t < n₁`) | `Polynomial.hasDerivAt`, `HasDerivAt.fun_sum`, `HasDerivAt.unique` |
| 3.4.2 | `lagCoeffD` (derivative of the cancelled `A_k^n`), `differentiable_lagCoeff'`, `dlmf_3_4_2` (= derivative of DLMF's `A_k^n` off `t = k`) | `Filter.EventuallyEq.deriv_eq` |
| 3.4.3 | `dlmf_3_4_3` (corrected: second term `h^{n+2}/(n+2)!`), general nodes `hasDerivAt_lagrangeRem_mean`, `remG`, `lagrangeRem_eq_nodal_mul_remG`, `remG_slope`, `eq_C_mul_nodal`, `divDiff_mem_image`, `eqNode_nodal_deriv`; erratum `dlmf_3_4_3_erratum` | `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `hasDerivAt_iff_tendsto_slope`, `Lagrange.eval_nodal_derivative_eval_node_eq`, `IsCompact.image_of_continuousOn` |
| 3.4.4 | `dlmf_3_4_4` (corrected: `c_n h \|f^{(n+2)}(ξ₁)\|`); `abs_deriv_prod_Icc_eqN_le` (`\|(d/dt) ∏_{k=n₀}^{n₁} (t − k)\| ≤ n!` on `[n₀, n₁]`, all `n`, by induction via `fallProd`, `abs_fallProd_le`, `abs_deriv_fallProd_le`, `prod_Icc_eqN_eq_fallProd`) | `Finset.prod_range_succ'`, `HasDerivAt.fun_mul`, `Fin.prod_univ_eq_prod_range` |

### §3.4(i) Two-Point through Eight-Point Formulas (`Azurite/DLMF/Chapter3/Section4Points.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| `B_k^n` for explicit `n` | `lagCoeffD_eq` (`B_k^n = c ω_E′`) | `Lagrange.eval_nodal`, `Polynomial.derivative_mul` |
| 3.4.5 | `dlmf_3_4_5`, `lagCoeffD_one`; bound `dlmf_3_4_5_bound` (`c₁ = 1/8`) | |
| 3.4.6 | `dlmf_3_4_6`, `lagCoeffD_two`; bound `dlmf_3_4_6_bound` (`c₂ = 1/(9√3)`) | |
| 3.4.7, 3.4.8 | `dlmf_3_4_7`, `dlmf_3_4_8` | |
| 3.4.9, 3.4.10 | `dlmf_3_4_9`, `dlmf_3_4_10` | |
| 3.4.11, 3.4.12 | `dlmf_3_4_11`, `dlmf_3_4_12` | |
| 3.4.13, 3.4.14 | `dlmf_3_4_13`, `dlmf_3_4_14` | |
| 3.4.15, 3.4.16 | `dlmf_3_4_15`, `dlmf_3_4_16` | |
| bounds for `n = 3, …, 7` | Not stated separately: `dlmf_3_4_4` with the `t`-sets and `c_n` bounds of §3.3(ii) (`dlmf_3_3_21_*`, `dlmf_3_3_24_*`, `dlmf_3_3_27_*`, `dlmf_3_3_30_*`, `dlmf_3_3_33_*`) | |
| higher derivatives (Collatz), Sinc-based formulas (Stenger) | Not formalized (references) | |

### §3.4(ii) Analytic Functions (`Azurite/DLMF/Chapter3/Section4Analytic.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.4.17 | `dlmf_3_4_17` (analytic `F`, any interior `x₀`), `dlmf_3_4_17_real` (real `f` extending analytically), `ofReal_iteratedDeriv_eq` | `DifferentiableOn.analyticOnNhd`, `AnalyticOnNhd.iterated_deriv`, `HasDerivAt.real_of_complex`, `HasDerivAt.ofReal_comp` |
| 3.4.18 | `dlmf_3_4_18` (`F` analytic on the closed disk) | `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`, `deriv_circleMap` |
| "approximated by the composite trapezoidal rule (3.5.2)" | Not formalized (§3.5 not yet available) | |
| 3.4.19 | `dlmf_3_4_19` (every `r > 0`) | `Complex.iter_deriv_exp`, `intervalIntegral.intervalIntegral_re` |
| "`r = k` … the integrand equals `e^k` at the dominant points `θ = 0, 2π`" | `dlmf_3_4_19_dominant` | `Real.cos_nat_mul_two_pi` |
| "with the factor `k^{−k}` … a rough approximation to `1/k!`" | `dlmf_3_4_19_bound` (`1/k! ≤ e^k/k^k`) | `intervalIntegral.integral_mono_on` |
| saddle-point motivation, efficiency of the trapezoidal rule | Not formalized (pointers to §2.4(iv), §3.5(i), §3.5(ix)) | |

### §3.4(iii) Partial Derivatives (`Azurite/DLMF/Chapter3/Section4Partial.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| `u_{t,s} = u(x₀ + th, y₀ + sh)`, partial derivatives | `iterPartialY`, `iterPartialXY` (`y` first; no higher symmetry used), `contDiff_iterPartialY` | `ContDiff.fderiv_right`, `ContDiff.clm_apply`, `HasFDerivAt.comp_hasDerivAt` |
| `O(hᵖ)` machinery | `taylor_lagrange_iteratedDeriv`, `taylor2`, `stencilTarget`, `stencil_isBigO` | `taylor_mean_remainder_lagrange_iteratedDeriv`, `iteratedDerivWithin_eq_iteratedDeriv`, `IsCompact.exists_bound_of_continuousOn`, `Asymptotics.IsBigO.of_bound` |
| 3.4.20, 3.4.21 | `dlmf_3_4_20`, `dlmf_3_4_21` (`u ∈ C³`) | |
| 3.4.22–3.4.24 | `dlmf_3_4_22` (`C⁴`), `dlmf_3_4_23` (`C⁶`), `dlmf_3_4_24` (`C⁴`) | |
| 3.4.25, 3.4.26 | `dlmf_3_4_25`, `dlmf_3_4_26` (`C⁴`) | |
| 3.4.27 | `laplacian` | |
| 3.4.28, 3.4.29 | `dlmf_3_4_28` (`C⁴`), `dlmf_3_4_29` (`C⁶`) | |
| 3.4.30, 3.4.31 | `dlmf_3_4_30`, `dlmf_3_4_31` (`C⁶`) | |
| 3.4.32 | `biharmonic` | |
| 3.4.33, 3.4.34 | `dlmf_3_4_33` (`C⁶`), `dlmf_3_4_34` (`C⁸`) | |
| Hypotheses | `u` is `C^{d+p}` on all of `ℝ²` (DLMF states none); a local version (smoothness near `(x₀, y₀)`) is not formalized | |
| sources (Panow), formulas on other grids (Collatz) | Not formalized (references) | |

## Section 3.5

### §3.5(i) Trapezoidal Rules (`Azurite/DLMF/Chapter3/Section5.lean`, `Section5Smooth.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.1 | `dlmf_3_5_1` (`f ∈ C²` on an open set containing `[a, b]`; `a < ξ < b`), `exists_mem_Ioo_integral_mul_eq` | `exists_eq_const_mul_intervalIntegral_of_nonneg`, `intervalIntegral_pos_of_pos_on`, `intermediate_value_uIcc`, `ContDiffOn.deriv_of_isOpen` |
| 3.5.2 | `trapezoidSum`, `trapError`, `dlmf_3_5_2` | |
| 3.5.3 | `dlmf_3_5_3`, `exists_sum_eq_card_mul` | `sum_integral_adjacent_intervals` |
| 3.5.4 | `dlmf_3_5_4` (explicit constant, all `k ≥ 1`), `dlmf_3_5_4_isBigO`, `periodic_iteratedDeriv` | `em_iter` (§2.10(i)), `continuous_bernoulliFun`, `intervalIntegral.integral_comp_mul_add` |
| "when `k = ∞` the error term is an exponentially-small function of `1/h`" | Erratum (needs analyticity): `smoothPeriodic_not_exponentially_small` and the rest of `Section5Smooth` | `contDiff_tsum`, `integral_tsum_of_summable_integral_norm`, `Summable.tsum_finsetSum`, `geom_sum_eq`, `Complex.exp_eq_one_iff` |
| 3.5.5 ("Similar results hold … analytic in a strip") | Deferred: no precise statement; the natural route is Poisson summation with decay of the Fourier transform (Mathlib's `Real.tsum_eq_tsum_fourier`) | |
| improvement by Euler–Maclaurin (§2.10(i)); Goodwin, Stenger | Not formalized (pointers) | |

### §3.5(ii) Simpson's Rule (`Azurite/DLMF/Chapter3/Section5Simpson.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.6 | `dlmf_3_5_6` (`f ∈ C⁴` on an open set containing `[a, b]`; `a < ξ < b`), `peano4`, `C4Data`, `simpsonKernel_derivs`, `simpsonKernel_derivs'`, `iteratedDeriv_four_eq` | `integral_eq_sub_of_hasDerivAt`, `integral_add_adjacent_intervals`, `ContDiffOn.deriv_of_isOpen` |
| 3.5.7 | `simpsonWeight`, `simpsonSum`, `simpsonError`, `dlmf_3_5_7`, `sum_simpsonWeight` | |
| 3.5.8 | `dlmf_3_5_8` (`n = 2N`) | `sum_integral_adjacent_intervals` |
| "a combination of two trapezoidal rules, one with step size `h` and one with step size `h/2`" | `simpsonSum_eq_trapezoid` (`S_{2N} = (4T_{2N} − T_N)/3`); the refinement of the error term itself is not formalized | |

### §3.5(iii) Romberg Integration (`Azurite/DLMF/Chapter3/Section5Romberg.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.9 | `rombergCoeff` (`c_s = −B_{2s}/(2s)! (f^{(2s−1)}(b) − f^{(2s−1)}(a))`), `dlmf_3_5_9` (`f ∈ C^{2m+2}` on an open set containing `[a, b]`; `O` uniform in `n ≥ 1`, explicit constant), `contDiffOn_iterate_deriv` | `em_sum` (§2.10(i)), `periodicBernoulli_bound` (§2.10(i)) |
| "by combining the rule for `h` with that for `h/2`, the first error term `c₁h²` … can be eliminated" | `romberg_expansion` with `k = 1` (`λ_{1,1} = 0`); Simpson form `simpsonSum_eq_trapezoid` (§3.5(ii)) | |
| 3.5.10 | Erratum (left side must be `G_k(h)`): `rombergG`, `dlmf_3_5_10` (corrected), `dlmf_3_5_10_erratum` | |
| "successive terms `c₁h², c₂h⁴, …` … are eliminated" | `rombergLambda`, `rombergLambda_succ`, `rombergLambda_eq_zero`, `romberg_expansion` | `Finset.prod_Icc_succ_top` |
| 3.5.11, elementary start `G₀(h) = ½h(f(a) + f(b))`, `h = b − a` | `dlmf_3_5_11` | |
| "To generate `G_k(h)` the quantities `G₀(h), …, G₀(h/2ᵏ)` are needed" | By the definition of `rombergG` (structural recursion on `k`) | |
| 3.5.12 | `dlmf_3_5_12` (`x₀ = a`) | `sum_range_even_odd` (§3.5(ii)) |
| 3.5.13, `k = 0` | `rombergErrCoeff`, `dlmf_3_5_13_zero` (from 3.5.3) | |
| 3.5.13, `k = 1` | `dlmf_3_5_13_one` (`G₁` is Simpson's rule; from 3.5.8) | `bernoulli'_four` |
| 3.5.13, `k ≥ 2` | Deferred: needs the constant sign of the Romberg Peano kernel (Bauer, Rutishauser and Stiefel 1963), then the weighted mean value theorem `exists_mem_Ioo_integral_mul_eq` and `romberg_expansion` to identify the constant | |
| Hypothesis `f ∈ C^{2k+2}(a, b)` in 3.5.13 | Formalized with `f ∈ C^{2k+2}` on an open set containing `[a, b]` (as in §3.5(i)–(ii)) | |
| "the Romberg method affords … high accuracy … adaptive algorithm" | Not formalized (remark) | |
| Example: coefficient of `f^{(16)}(ξ)` in 3.5.13 with `j = 2`, `k = 7` is `(0.14…) × 10⁻¹³` | `dlmf_3_5_iii_example_coeff` (absolute value; the coefficient carries a minus sign), `bernoulli'_six` … `bernoulli'_sixteen`, `bernoulli_sixteen` | `bernoulli'_def`, `bernoulli_eq_bernoulli'_of_ne_one` |
| 3.5.14 (`∫₀^∞ e^{−pt} J₀(t) dt = 1/√(p² + 1)`), "`G₇(h)` with 14 correct digits" (`p = 1`, `[0, 30]`, `h = 7.5`) | Deferred: needs `J₀` (Chapter 10); the 14 digits would then be an AzFloat enclosure of `G₇(7.5)` plus a bound on the tail `∫₃₀^∞` | |
| "About `2⁹ = 512` function evaluations" | Not formalized (`G₇(30/4)` uses the `4 · 2⁷ + 1 = 513` nodes of `G₀(30/2⁹)`) | |
| 20-point Gauss–Laguerre, 15 evaluations | Deferred to Chapter 10 (needs `J₀`; the 20-point nodes and weights are certified in `dlmf_table_3_5_9`) | |
| Davis and Rabinowitz (singular `f`) | Not formalized (reference) | |

### §3.5(iv) Interpolatory Quadrature Rules (`Azurite/DLMF/Chapter3/Section5Interpolatory.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.15, definition of an interpolatory rule | `quadError`, `IsInterpolatory`, `isInterpolatory_of_pow` | `Polynomial.eval_eq_sum_range'` |
| "the weights `w_k` and error term `E_n(f)` are found by integrating the product of the Lagrange interpolation polynomial … and `w(x)`" | `interpWeight`, `dlmf_3_5_15`, `isInterpolatory_iff` (uniqueness), `integral_interpolate_mul`, `quadError_interpWeight` (`w` interval integrable, nodes distinct) | `Lagrange.basis`, `Lagrange.interpolate`, `Lagrange.eq_interpolate` |
| closed / open rules | `IsClosedRule`, `IsOpenRule` | |
| Newton–Cotes: trapezoidal rules and Simpson's rule are closed | `trapezoid_isInterpolatory`, `trapezoid_isClosedRule`, `trapezoidSum_one_eq`, `simpson_isInterpolatory`, `simpson_isClosedRule`, `simpsonSum_two_eq` (elementary rules; the composite rules are piecewise interpolatory) | `integral_pow` |
| open rules: midpoint rule | `midpoint_isInterpolatory`, `midpoint_isOpenRule` | |
| open rules: Gauss formulas | Deferred to §3.5(v) | |
| Fejér's rule: nodes are the extrema of `T_n` | `ccNode`, `fejer_nodes_isLocalExtr_iff` (`n ≥ 2`), `fejer_isOpenRule`, `fejer_isInterpolatory` (weights `∫₋₁¹ ℓₖ`; DLMF gives no formula) | `Polynomial.Chebyshev.isLocalExtr_T_real_iff` |
| "If we add `−1` and `1` … the resulting closed formula is the … Clenshaw–Curtis formula" | `range_eq_insert_fejer`, `ccNode_isClosedRule` | |
| "whose weights are positive" | `ccWeight_pos`, `sum_two_div_four_sq_sub_one` | |
| 3.5.16–3.5.17 | `ccG`, `ccB`, `ccWeight`, `dlmf_3_5_16` (`n ≥ 1`; interpolatory, weights = `∫₋₁¹ ℓₖ`), `integral_eq_sum_ccWeight`, `ccWeight_mul_cos`, `sum_ccG_mul_cos`, `sum_range_two_mul_cos`, `integral_T_real`, `integral_neg_one_one_eq`, `integral_sin_mul_zero_pi`, `ccNode_injOn` | `Polynomial.Sequence.span_degreeLT`, `Polynomial.Chebyshev.chebyshevTsequence`, `Polynomial.Chebyshev.T_real_cos`, `geom_sum_eq`, `Real.injOn_cos`, `intervalIntegral.integral_comp_mul_deriv` |
| Mason–Handscomb, Davis–Rabinowitz, Clenshaw–Curtis; comparisons with Gauss quadrature (Trefethen) | Not formalized (references) | |

### §3.5(v) Gauss Quadrature, through the paragraph before "Gauss–Legendre Formula" (`Azurite/DLMF/Chapter3/Section5Gauss.lean`, `Section5GaussError.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "monic polynomials `p_n` … orthogonal with respect to a positive weight function `w` on a finite or infinite interval `(a, b)`; compare §18.2(i)" | `IsGaussWeight` (open interval `I`, `w > 0` on `I`, all moments finite), `wInt`, `IsOrthMonic`, `exists_isOrthMonic`, `IsOrthMonic.unique`, `wInt_pos` | `Matrix.mulVecLin`, `LinearMap.injective_iff_surjective`, `setIntegral_pos_iff_support_of_nonneg_ae` |
| "nodes `x_k` the zeros of `p_n`" (implicitly: `n` real simple zeros in `(a, b)`) | `IsOrthMonic.roots_spec`, `eval_nonneg_or_nonpos_of_even`, `IsOrthMonic.eq_nodal` | `Polynomial.roots_mul`, `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` |
| 3.5.18 | `christoffel`, `christoffel_eq_wInt_basis` (= interpolatory weights `∫ ℓₖ w`, so the rule is 3.5.15) | `Lagrange.eval_basis_not_at_node`, `Lagrange.nodalWeight_eq_eval_derivative_nodal` |
| "they are all positive" | `christoffel_pos` | |
| 3.5.19 | `dlmf_3_5_19` (finite `(a, b)`, `n ≥ 1`, `f ∈ C^{2n}` on an open set containing `[a, b]`; `ξ ∈ (a, b)`), `hermite`, `hermite_eval`, `hermite_derivative_eval`, `natDegree_hermite_le`, `hermite_error`, `exists_mem_Ioo_notMem_eq_zero` | `exists_deriv_eq_zero`, `intermediate_value_Ioo`, `IsCompact.exists_isMinOn` |
| 3.5.19 on infinite intervals | Not formalized (DLMF states no conditions on `f`; needs growth conditions making `f w` integrable and `f^{(2n)}` controlled) | |
| 3.5.20 | `gaussGamma` | |
| 3.5.20_1 | `dlmf_3_5_20_1` (any interval, polynomial `f`) | `Polynomial.modByMonic_add_div`, `Lagrange.eq_interpolate` |
| 3.5.20_2 | `dlmf_3_5_20_2` (family `p_m`, `ℓ, m < n`) | |
| weight chosen to simulate asymptotics; efficiency for `C^∞`; adaptive algorithms; references (Gautschi, Gil et al., Davis–Rabinowitz, Stroud–Secrest) | Not formalized (remarks, references) | |
| "The given quantities `γ_n` follow from (18.2.5), (18.2.7), Table 18.3.1, and the relation `γ_n = h_n/k_n²`" | `gaussGamma_eq_div` (the relation); the tabulated values belong to the Gauss–Legendre … formulas (Chapter 18) | |

### §3.5(v) Gauss–Legendre Formula (`Azurite/DLMF/Chapter3/Section5GaussLegendre.lean`, `Section5GaussLegendreTables.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.21, `[a, b] = [−1, 1]`, `w(x) = 1` | `isGaussWeight_legendre`, `isOrthMonic_legendreMonic` (Rodrigues' formula, repeated integration by parts) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity` |
| 3.5.21, `γ_n` | `dlmf_3_5_21`, `wallisI_eq` | |
| "The `p_n(x)` are the monic Legendre polynomials … `P_n(x)` … scaled" | `legendrePoly`, `legendreMonic`, `legendreP_eq`, `legendreLead` | |
| (used) three-term recurrence, Bonnet 18.9.1, parity | `legendreMonic_succ_succ`, `eval_legendreP_succ_succ`, `eval_neg_legendreP` (on `legendrePoly`) | |
| (used) weights via the Christoffel function | `christoffel_mul_sum`, `christoffel_legendre` | `Matrix.mul_eq_one_comm_of_card_eq` |
| Table 3.5.1 (`n = 5`, 15D) | `dlmf_table_3_5_1` | |
| Table 3.5.2 (`n = 10`, 18D) | `dlmf_table_3_5_2` | |
| Table 3.5.3 (`n = 20`, 21D) | `dlmf_table_3_5_3` | |
| Table 3.5.4 (`n = 40`, 21D) | `dlmf_table_3_5_4`; errata `dlmf_table_3_5_4_erratum_5`, `dlmf_table_3_5_4_erratum_15` | |
| Table 3.5.5 (`n = 80`, 21D) | `dlmf_table_3_5_5`; erratum `dlmf_table_3_5_5_erratum_32` | |
| Certificate method | `glRH`, `glAC`, `glRowOK_sound`, `glZeroOK_sound`, `glTableOK_sound`, `GLTableSpec` (exact `Nat`/`Int` kernel arithmetic, `D = 10^90`; about 10 s) | `intermediate_value_Ioo` |

### §3.5(v) Gauss–Chebyshev Formula (`Azurite/DLMF/Chapter3/Section5GaussChebyshev.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.22, `w(x) = (1 − x²)^{−1/2}` | `chebWeight`, `chebWeight_eq_rpow`, `isGaussWeight_chebWeight`, `gcT`, `isOrthMonic_gcT` | `Polynomial.Chebyshev.integral_measureT_eq_integral_cos`, `Polynomial.Chebyshev.T_real_cos` |
| 3.5.22, `γ_n = π/2^{2n−1}` | `dlmf_3_5_22` (`n ≥ 1`) | |
| 3.5.23 | `gcNodesT`, `dlmf_3_5_23` (`n ≥ 1`) | `Polynomial.Chebyshev.integral_eq_sumZeroes` |
| "Chebyshev weight functions `(1 − x)^α (1 + x)^β` with `|α| = |β| = ½`" | `chebWeight_eq_rpow` | |
| 3.5.24 (nodes, weights) | `gcU`, `isOrthMonic_gcU`, `gcNodesU`, `dlmf_3_5_24` (`n ≥ 1`) | `Polynomial.Chebyshev.U_real_cos` |
| 3.5.24, `γ_n = π/2^{2n+1}` | `dlmf_3_5_24_gamma` (`n ≥ 1`) | |
| 3.5.25 (`α = ½`: nodes `+cos(2kπ/(2n+1))`) | `gcW`, `isOrthMonic_gcW`, `gcNodesW`, `dlmf_3_5_25_W`, `dlmf_3_5_25_gamma_W` | |
| 3.5.25 (`α = −½`: nodes `−cos(2kπ/(2n+1))`) | `gcV`, `isOrthMonic_gcV`, `gcNodesV`, `dlmf_3_5_25_V`, `dlmf_3_5_25_gamma_V` | |
| (tools) | `gauss_rule_eq`, `eq_zero_of_T`, `trap_exact`, `circ_exact`, `cheb_U_identity`, `cheb_W_identity`, `cheb_V_identity` | `Polynomial.Sequence.span_degreeLT` |

### §3.5(v) Gauss–Jacobi Formula (`Azurite/DLMF/Chapter3/Section5GaussJacobi.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.26, `w(x) = (1 − x)^α (1 + x)^β`, `α, β > −1` | `jacW`, `isGaussWeight_jacW`, `intervalIntegrable_jac` | `intervalIntegral.intervalIntegrable_rpow'` |
| 3.5.26, `γ_n` | `dlmf_3_5_26` (`n ≥ 1`; for `n = 0` and `α + β = −1` the printed expression is `0 · Γ(0)²` in the denominator, i.e. undefined, while `γ₀ = ∫ w` — the rule has `n ≥ 1` nodes) | `Complex.betaIntegral_eq_Gamma_mul_div`, `Real.Gamma_add_one` |
| "The `p_n(x)` are the monic Jacobi polynomials `P_n^{(α,β)}(x)` (§18.3)" | `jacobiP` (Rodrigues), `jacobiP_rodrigues` (18.5.5), `jacMonic`, `isOrthMonic_jacMonic`, `jacMonic_eq_jacobiP` | |
| (tools) | `jacR`, `jacF`, `hasDerivAt_jacF`, `iteratedDeriv_jac`, `integral_mul_jacF`, `jacR_degree`, `jacLead`, `integral_rpow_mul_one_sub_rpow`, `integral_jac_beta`, `jacGamma_add_nat` | `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` |

### §3.5(v) Gauss–Laguerre Formula (`Azurite/DLMF/Chapter3/Section5GaussLaguerre.lean`, `Section5GaussLaguerreTables.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.27, `[a, b) = [0, ∞)`, `w(x) = x^α e^{−x}`, `α > −1` | `lagW`, `isGaussWeight_lagW`, `wInt_lagW_X_pow` | `Real.GammaIntegral_convergent`, `Real.Gamma_eq_integral` |
| 3.5.27, `γ_n = n! Γ(n + α + 1)` | `dlmf_3_5_27` (all `n`) | `fwdDiff_iter_eq_sum_shift`, `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`, `Polynomial.fwdDiff_iter_degree_eq_factorial` |
| "If `α ≠ 0` … generalized Gauss–Laguerre formula" | Covered: everything above is for general `α > −1` | |
| "The `p_n` are the monic Laguerre polynomials `L_n` (§18.3)" | `lagL` (explicit sum 18.5.12), `lagMonic`, `lagMonic_monic`, `natDegree_lagMonic`, `isOrthMonic_lagMonic`, `lagMonic_eq_lagL` (`p_n = (−1)^n n! L_n^{(α)}`) | |
| (used) weights for `α = 0` | `eval_lagL_zero`, `christoffel_laguerre` (`wₖ = 1/∑_{j<n} L_j(xₖ)²`) | |
| Table 3.5.6 (`n = 5`, 18S) | `dlmf_table_3_5_6` | |
| Table 3.5.7 (`n = 10`, 18S) | `dlmf_table_3_5_7`; errata `dlmf_table_3_5_7_erratum_0`, `dlmf_table_3_5_7_erratum_3` | |
| Table 3.5.8 (`n = 15`, 18S) | `dlmf_table_3_5_8` | |
| Table 3.5.9 (`n = 20`, 18S) | `dlmf_table_3_5_9` | |
| Certificate method | `lagS`, `lagH`, `lagK_spec`, `lagRowOK_sound`, `lagTableOK_sound`, `LagTableSpec`, `lagNodes`, `lagWeight` (exact `Nat`/`Int` kernel arithmetic, `D = 10^100`, brackets in `[0, R]`) | `intermediate_value_Ioo` |

### §3.5(v) Gauss–Hermite Formula (`Azurite/DLMF/Chapter3/Section5GaussHermite.lean`, `Section5GaussHermiteTables.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.28, `(a, b) = (−∞, ∞)`, `w(x) = e^{−x²}` | `hermW`, `isGaussWeight_hermW`, `wInt_hermW_one`, `wInt_hermW_derivative` | `integrable_rpow_mul_exp_neg_mul_sq`, `integral_gaussian`, `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` |
| 3.5.28, `γ_n = √π n!/2ⁿ` | `dlmf_3_5_28` (all `n`), via `wInt_hermMonic_succ_mul`, `wInt_hermMonic_mul` | `Polynomial.iterate_derivative_eq_zero`, `Polynomial.coeff_iterate_derivative` |
| "The `p_n(x)` are the monic Hermite polynomials `H_n(x)` (§18.3)" | `hermiteH` (with Rodrigues' formula 18.5.5 `hermiteH_rodrigues`, 18.9.1 `hermiteH_succ_succ`, 18.9.25 `derivative_hermiteH_succ`), `hermMonic`, `hermMonic_eq` (`2ⁿ p_n = H_n`), `hermMonic_spec`, `isOrthMonic_hermMonic` | |
| (used) parity and weights | `eval_neg_hermiteH`, `eval_neg_hermMonic`, `christoffel_hermite` (`wₖ = √π/∑_{j<n} H_j(xₖ)²/(2^j j!)`) | |
| "for `n = 5, 10` are shown in Tables 3.5.10 and 3.5.11" | All four printed tables are certified (Tables 3.5.12, 3.5.13 give `n = 15, 20`; the Laguerre sentence is worded the same way) | |
| Table 3.5.10 (`n = 5`, 15S) | `dlmf_table_3_5_10` | |
| Table 3.5.11 (`n = 10`, 18S) | `dlmf_table_3_5_11` | |
| Table 3.5.12 (`n = 15`, 21S) | `dlmf_table_3_5_12` | |
| Table 3.5.13 (`n = 20`, 21S) | `dlmf_table_3_5_13` | |
| Certificate method | `hermRH`, `hermAC_spec`, `herm_pi_bounds` (128-bit AzFloat `Encl.pi`, `decide +kernel`), `hermWOK_sound`, `hermRowOK_sound`, `hermZeroOK_sound`, `hermTableOK_sound`, `HermTableSpec`, `hermNodes`, `hermWeight` (exact `Nat`/`Int` kernel arithmetic, `D = 10^100`) | `intermediate_value_Ioo`, `Real.le_sqrt`, `Real.sqrt_le_left` |

### §3.5(v) Gauss Formula for a Logarithmic Weight Function (`Azurite/DLMF/Chapter3/Section5GaussLog.lean`, `Section5GaussLogTables.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.29, `[a, b] = [0, 1]`, `w(x) = ln(1/x)` | `logW`, `logW_eq`, `isGaussWeight_logW` (on `(0, 1)`) | `intervalIntegral.intervalIntegrable_log'` |
| (used) moments `∫₀¹ xᵏ ln(1/x) dx = 1/(k + 1)²` | `integral_pow_mul_logW`, `wInt_logW_X_pow` | `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, `Real.continuous_mul_log`, `Real.hasDerivAt_mul_log` |
| (used) the monic orthogonal polynomials (no closed form; rational coefficients) | `logMonic`, `isOrthMonic_logMonic`, `qPoly`, `logMom`, `logOK`, `isOrthMonic_of_logOK`, `gaussGamma_of_logOK`, `logMonic_eq`, `christoffel_log`; `logData_ok` certifies `p_0, …, p_20` | |
| "for `n = 5, 10` are shown in Tables 3.5.14 and 3.5.15" | All four printed tables are certified (Tables 3.5.16, 3.5.17 give `n = 15, 20`) | |
| Table 3.5.14 (`n = 5`, 15S) | `dlmf_table_3_5_14` | |
| Table 3.5.15 (`n = 10`, 18S) | `dlmf_table_3_5_15` | |
| Table 3.5.16 (`n = 15`, 21S) | `dlmf_table_3_5_16` | |
| Table 3.5.17 (`n = 20`, 21S) | `dlmf_table_3_5_17` | |
| Certificate method | `logRowOK_sound`, `logTableOK_sound`, `LogTableSpec`, `logNodes`, `logWeight`, `logGR_lip` (exact `ℚ` kernel arithmetic, `D = 10^100`) | `intermediate_value_Ioo` |

### §3.5(vi) Eigenvalue/Eigenvector Characterization of Gauss Quadrature Formulas (`Azurite/DLMF/Chapter3/Section5Eigen.lean`, `Section5EigenClassical.lean`, `Section5EigenChebyshev.lean`, `Section5EigenJacobi.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.30, with `β_n > 0`, `p_{−1} = 0`, `p_0 = 1` | `recA`, `recB`, `prevP`, `dlmf_3_5_30`, `recB_pos`, `orth_P_zero` (any Gauss weight; `α_n = ∫ x p_n² w/h_n`, `β_n = h_n/h_{n−1}`) | |
| `h_n = h_0 β_1 β_2 ⋯ β_n` | `gaussGamma_eq_prod` | |
| 3.5.30_5, `q_n = p_n/√h_n`, `q_{−1} = 0`, `q_0 = 1/√h_0` | `orthoQ`, `orthoQ_zero`, `dlmf_3_5_30_5` | |
| "closely related to the Lanczos recursion in §3.2(vi)" | Not formalized (remark) | |
| 3.5.31 (nodes = eigenvalues of `J_n`) | `jacobiMatrix`, `jacobiMatrix_isSymm`, `dlmf_3_5_31` (`∃ v ≠ 0, J_n v = x v ↔ p_n(x) = 0`), `dlmf_3_5_31_hasEigenvalue`, `jacobiMatrix_mulVec_qvec`, `eigvec_eq_smul_qvec` | `Module.End.HasEigenvalue`, `Matrix.toLin'` |
| 3.5.32, `w_k = β_0 v_{k,1}²`, `β_0 = ∫ w` | `dlmf_3_5_32`, `recB_zero` | |
| 3.5.33, `γ_n = β_0 β_1 ⋯ β_n` | `dlmf_3_5_33` | |
| "Tables 3.5.1–3.5.13 can be verified by application of the results given in the present subsection" | Not used: the tables are certified directly (§3.5(v)) | |
| "monic version `p_n` and orthonormal version `q_n` … dividing by `k_n` respectively `√h_n`" | `legendreP_eq`, `hermMonic_eq`, `lagMonic_eq_lagL`, `jacMonic_eq_jacobiP`, `gcT`, `gcU`, `gcV`, `gcW`, `shP_gcT`; `table_3_5_17_5_laguerre_q`, `wInt_lagL_sq` | |
| 3.5.33_1 (`α_n`) | `dlmf_3_5_33_1_alpha` (whenever `2n + α + β ≠ 0`), via `coeff_jacR_succ`, `jacR_sub`, `coeff_jacMonic_sub`, `recA_eq_coeff` | |
| 3.5.33_1 (`β_n`) | `dlmf_3_5_33_1_beta` (`n ≥ 2`; for `n = 1` it holds when `α + β ≠ −1`, `dlmf_3_5_33_1_beta_one`) | |
| 3.5.33_2 ("by continuity") | `dlmf_3_5_33_2_alpha`, `dlmf_3_5_33_2_beta` (exact values, no continuity argument needed) | |
| Jacobi `h_0 = 2^{α+β+1}Γ(α+1)Γ(β+1)/Γ(α+β+2)` | `jacobi_h0` | |
| Table 3.5.17_5, `C_n^{(λ)}` | `table_3_5_17_5_ultra_alpha`, `_beta` (`λ ≠ 0`), `_h0`, `jacW_ultra` (monic `C_n^{(λ)}` = monic `P_n^{(λ−½,λ−½)}`) | `Real.Gamma_mul_Gamma_add_half` |
| Table 3.5.17_5, `T_n` | `table_3_5_17_5_T_alpha`, `_beta`, `_h0`, `gcT_rec` | `Polynomial.Chebyshev.T_add_two` |
| Table 3.5.17_5, `U_n` | `table_3_5_17_5_U_alpha`, `_beta`, `_h0`, `gcU_rec` | `Polynomial.Chebyshev.U_add_two`, `integral_cos_sq` |
| Table 3.5.17_5, `V_n` | `table_3_5_17_5_V_alpha`, `_beta`, `_h0`, `gcV_rec` | `integral_cos` |
| Table 3.5.17_5, `W_n` | `table_3_5_17_5_W_alpha`, `_beta`, `_h0`, `gcW_rec` | |
| Table 3.5.17_5, `T_n^*` | `table_3_5_17_5_Tstar_alpha`, `_beta`, `_h0`, `shW_chebWeight_one`, `shP_gcT`; general shift `shW`, `shP`, `wInt_shW`, `isGaussWeight_shW`, `isOrthMonic_shP`, `recAB_shP`, `recB_shP_zero` | `intervalIntegral.integral_comp_mul_sub`, `IntervalIntegrable.comp_mul_left` |
| Table 3.5.17_5, `P_n` | `table_3_5_17_5_legendre_alpha`, `_beta`, `_h0`, `legendreMonic_rec` | |
| Table 3.5.17_5, `L_n^{(α)}` | `table_3_5_17_5_laguerre_alpha`, `_beta`, `_h0`, `table_3_5_17_5_laguerre_q` | |
| Table 3.5.17_5, `H_n` | `table_3_5_17_5_hermite_alpha`, `_beta`, `_h0`, `hermMonic_rec`, `derivative_hermMonic_succ` | |
| (tools) | `recAB_of_rec` (uniqueness of recurrence coefficients), `recA_eq_coeff`, `eq_zero_of_wInt_mul_P` | |
| 3.5.33_3, `q_n = L_n^{(α)}/√h_n` | `lagOrtho`, `dlmf_3_5_33_3`, `wInt_lagL_sq` (`h_n = Γ(n + α + 1)/n!`) | |

### §3.5(vii) Oscillatory Integrals (`Azurite/DLMF/Chapter3/Section5Oscillatory.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.34 | `oscCos`, `oscSin` (definitions) | |
| "can be computed by Filon's rule" (Davis–Rabinowitz) | Not formalized (method not stated in DLMF; reference) | |
| Wong (Gaussian quadrature for transforms), Evans–Webster (comparison incl. extended Clenshaw–Curtis) | Not formalized (references) | |
| Longman's method: "the integral is written as an alternating series of positive and negative subintegrals" | `dlmf_3_5_vii_longman_sin`, `dlmf_3_5_vii_longman_cos`, `longman_core` (hypotheses supplied: `f` decreasing on `[0, ∞)` with limit `0`, `ω > 0`; subintegrals between consecutive zeros alternate in sign, decrease to `0`, the series converges and sums to the improper integral), `longmanI`, `longmanA`, `longmanJ`, `longmanA_antitone`, `longmanA_tendsto`, `sum_longmanI`, `longman_rem_le` | `Antitone.tendsto_alternating_series_of_tendsto_zero`, `AntitoneOn.intervalIntegrable`, `Real.sin_add_nat_mul_pi` |
| "Convergence acceleration schemes, for example Levin's transformation (§3.9(v))" | Deferred to §3.9(v) | |
| Clendenin (1966), Lyness (1985), Iserles et al. (2006) | Not formalized (references) | |

### §3.5(viii) Complex Gauss Quadrature (`Azurite/DLMF/Chapter3/Section5ComplexGauss.lean`, `Section5ComplexGaussTable.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.35, `s > 0`, `c > c₀ > 0` | `cgI` (`bromwich` of §2.4(ii) at `t = 1`: limit of the symmetric integrals), `tendsto_cgI_pow` (moments `1/Γ(s + k)`), `cgL`, `tendsto_cgI_poly`, `cgI_poly` | `Complex.Gamma_ne_zero_of_re_pos`, `Complex.cpow_add` |
| "`f(ζ)` analytic in `ℜζ > c₀` and bounded as `ζ → ∞` in `\|ph ζ\| ≤ ½π`" | Hypotheses for convergence of 3.5.35 for general `f`; not needed for the exactness statement (polynomials in `1/ζ` converge for every `c > 0`) | |
| 3.5.36, `E_n(f) = 0` for `f` a polynomial of degree `≤ 2n − 1` in `1/ζ` | `cgE`, `dlmf_3_5_36`, `cgL_eq_sum`, `cgNodes`, `cgNodesU`, `mem_cgNodes`, `cgWeight`, `cgWeight_eq` (`w_k = A(u_k)/p_n′(u_k)`), `cgA`, `cgQ`, `cgL_basis_eq` | `Lagrange.eq_interpolate`, `Lagrange.basis_eq_prod_sub_inv_mul_nodal_div`, `Polynomial.modByMonic_add_div` |
| 3.5.37 (complex orthogonal polynomials `p_n(1/ζ)`) | `cgP`, `cgc` (explicitly `₂F₀(−n, s + n − 1; ; u)`), `sum_cgc_mu`, `cgL_cgP_mul_X_pow`, `cgL_cgP_mul`, `dlmf_3_5_37` | `fwdDiff_iter_eq_sum_shift`, `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` |
| "related to Bessel polynomials (§§10.49(ii), 18.34)" | `besselYGen` (18.34.1), `cgP_eq_besselYGen` (`p_n(u) = y_n(−2u; s)`) | |
| (needed) the `n` nodes are distinct and finite | `cgP_ode`, `cgP_ode_iter`, `cgP_derivative_ne_zero` (simple zeros), `nodup_roots_cgP`, `card_cgNodesU`, `eval_zero_cgP` | `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'` |
| "The complex Gauss nodes `ζ_k` have positive real part for all `s > 0`" | Proved for `n = 5`, `s = 1` (`cgNodes_one_five_re_pos`). **Deferred** in general: a stability theorem for generalized Bessel polynomials (zeros of `y_n(x; s)` in `ℜx < 0`), not derivable from this subsection | |
| Table 3.5.18 (`n = 5`, `s = 1`, 10S) | `dlmf_table_3_5_18`, `polyPz`, `mem_cgNodes_one_five`, `cgWeight_one_five`; certificates `exists_root_within`, `cEval_lip`, `norm_div_sub_div_le`, `cgRowOK_sound`, `cgTableOK_sound` (exact Gaussian rationals, disks of radius `10^{−30}`) | `Polynomial.Splits.eval_derivative_div_eval_of_ne_zero` |
| Krylov and Skoblya (1985) | Not formalized (reference) | |
| Example: 3.5.38, 3.5.39 (from §1.14(iii)) | `laplace`, `bromwichPartial`, `dlmf_2_4_3` | |
| Example: 3.5.40 (`g = J₀`, `G = 1/√(p² + 1)`, conditions hold for `σ > 0`) | `besselJ0`, `lapG`, `laplace_besselJ0` (`ℜp > 0`), `laplace_besselJ0_real`, `tendsto_bromwich_lapG` (`σ > 0`), `abs_besselJ0_le_one`, `besselJ0_ode`, `expGrowth_besselJ0`, `choose_neg_half`, `hasSum_one_add_rpow_neg_half` | `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`, `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, `integral_tsum_of_summable_integral_norm`, `BZ.besselJNat_ode` |
| Example: "(3.5.39) has the form (3.5.35) if we set `ζ = tp`, `c = tσ`, `f(ζ) = t^{−1}ζ^s G(ζ/t)`" | `lapF`, `bromwichPartial_lapF`, `tendsto_cgI_lapF`, `cgI_lapF_besselJ0` | `intervalIntegral.integral_comp_div` |
| Example: "We choose `s = 1` so that `f(ζ) = O(1)` at infinity" | `lapF_lapG` (`f(ζ) = ζ/√(ζ² + t²)`), `norm_lapF_lapG_le` (`\|f\| ≤ 2` for `\|ζ\| ≥ 2t`) | |
| Example: 3.5.41 | `lapApprox`, `dlmf_3_5_41` (`J₀(t) = ∑ wₖζₖ/√(ζₖ² + t²) + Eₙ(f)`), `sum_cgWeight`, `lapApprox_zero` | `Complex.pow_cpow_nat_inv` |
| Table 3.5.19, column `J₀(t)` (10D) | `dlmf_table_3_5_19_J0` (all correct), `j0Rec`, `j0OK_sound`, `abs_tsum_sub_sum_le` | |
| Table 3.5.19, column `g(t)` | `dlmf_table_3_5_19_g` (`g₅(0) = 1`; certified 10D values at `t = 0.5, 1, 2, 5, 10`), `lapFt_sound`, `lapApprox_near`, `norm_cpow_half_sub_le`, `cgTable_nodes`; **errata** `dlmf_table_3_5_19_erratum` (`t = 1, 2, 5, 10`) | |
| "The results are given in the middle column … the actual 10D values in the last column" | **Erratum** (text vs the corrected headings of V1.0.7): the middle column is `J₀(t)` and the last is `g(t)`; see `docs/dlmf_errata.md` | |
| "Agreement is very good for small values of `t`, but not for larger values" | `dlmf_table_3_5_19_agreement` | |
| "the integration path may need to be deformed; see §3.5(ix)" | See §3.5(ix) (`dlmf_3_5_45_path`) | |

### §3.5(ix) Other Contour Integrals (`Azurite/DLMF/Chapter3/Section5Contour.lean`, `Section5ContourBromwich.lean`, `Section5ContourTable.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "heavy cancellation … deform the path to pass through a saddle point … steepest descent paths (§2.4(iv))" | Prose (pointer); realized in the Example below | |
| Example: `s = 1`, `f(ζ) = e^{−2λ√ζ}`, "the quadrature rule of §3.5(viii) is useless" | Prose; `erfc` is `BZ.erfc` (7.2.2 for real argument) | |
| 7.14.4 (used): `∫₀^∞ e^{−pτ} erfc(μ/√τ) dτ = e^{−2μ√p}/p`, `ℜp > 0` | `laplace_erfcLapQ`, `laplace_erfc_real` (Fubini), `integral_exp_neg_sq_sub_sq_div`, `integral_exp_neg_sub_div_sq` (`w = u − a/u`, `v = a/u`), `erfcLapQ`, `erfcLapG`, `hasDerivAt_erfc`, `erfc_nonneg`, `erfc_le_one`, `tendsto_bromwich_erfcLapG` | `integral_integral_swap`, `integral_image_eq_integral_abs_deriv_smul`, `integral_gaussian`, `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` |
| 3.5.42, `c > 0` | `dlmf_3_5_42` (limit of symmetric partial integrals), `cgI_erfc` (`I(f) = erfc λ`) | `Complex.cpow_neg_one` |
| 3.5.43 (from 7.12.1) | `dlmf_3_5_43` (`IsEquivalent`) | `Asymptotics.isEquivalent_of_tendsto_one` |
| 3.5.44 (`ζ = λ²t`), `c > 0` | `dlmf_3_5_44`, `erfcPhase` | |
| "saddle point at `t = 1`" | `erfcPhase_saddle`, `hasDerivAt_erfcPhase` | `Complex.hasStrictDerivAt_cpow_const` |
| "steepest descent path `ℑ(t − 2√t) = 0`, … `r = sec²(½θ)`" | `erfcPhase_im_eq_zero_iff` (`0 < \|θ\| < π`), `im_erfcPhase_polar`, `cpow_half_polar`, `erfcPath`, `erfcPathDeriv`, `hasDerivAt_erfcPath`, `erfcPhase_erfcPath` (`t − 2√t = −1 − tan²(θ/2)`) | `Complex.log_exp` |
| 3.5.45 | `dlmf_3_5_45` (`θ = 2 arctan s`, `integral_erfcPathIntegrand`; `integral_exp_div_one_add_sq`), `dlmf_3_5_45_path` (the integral of 3.5.44 along the steepest descent path), `erfcPathIntegrand`, `erfcPath_integrand_eq`, `abs_mul_exp_neg_sq_le`. The deformation of the vertical path by Cauchy's theorem is not formalized (both sides are proved equal to `erfc λ`) | `Real.arctan_tan`, `intervalIntegral.integral_comp_neg` |
| "extended as a periodic `C^∞` function … the trapezoidal rule is exceptionally efficient" | `erfcPathExt`, `contDiff_erfcPathExt`, `periodic_erfcPathExt`, `erfcPathExt_eq`, `erfcPathExt_pi`, `integral_erfcPathExt`, `erfcPath_trapError_isBigO` (`O(hᵏ)` for all `k`, via 3.5.4) | `expNegInvGlue.contDiff` |
| Table 3.5.20 (`λ = 10`) | `erfcTrap`, `dlmf_table_3_5_20_nodes`, `sum_Icc_even`, `dlmf_table_3_5_20` (rows `h = 0.15, 0.10` correct), **erratum** `dlmf_table_3_5_20_erratum` (rows `h = 0.25, 0.20`: last digit), `dlmf_table_3_5_20_n` (`n = 5, 6, 8, 11`), `dlmf_table_3_5_20_erfc` ("all digits … in the final row are correct"); certificates `expEncl_sound`, `cosEncl_sound`, `gEncl_sound`, `trapEncl_sound`, `count_sound`, `erfcEncl_sound` (7.12.1, 20 terms) | `Real.exp_bound`, `Complex.exp_bound`, `Real.pi_gt_d20`, `Real.pi_lt_d20` |
| Gil et al. (2001, 2003b), Scorer functions (§9.12) | Not formalized (references) | |
| "If `f` is meromorphic, with poles near the saddle point, then the foregoing method can be modified" | Not formalized (prose) | |
| 3.5.46 (Hilbert transform as principal value, §1.14(v)) | `dlmf_3_5_46` (the limits of `(1/π)(∫_{x−R}^{x−ε} + ∫_{x+ε}^{x+R}) f(t)/(t − x) dt` give `hilbert f x`) | |
| Kress and Martensen (1970) | Not formalized (reference) | |
| Hankel (§10.22(v)), Kontorovich–Lebedev (§10.43(v)), Mellin (§1.14(iv)) transforms | Not formalized (pointers) | |

### §3.5(x) Cubature Formulas (`Azurite/DLMF/Chapter3/Section5Cubature.lean`, `Section5CubatureTable.lean`, `Section5MonteCarlo.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.5.47 (disk `D`: `x² + y² ≤ h²`) | `dlmf_3_5_47`, `diskRem`, `diskSet`, `cubSum`, `cubRem`; area `volume_diskSet` (`πh²`); moments `integral_diskSet_mono` (polar coordinates), `trigMom`, `trigMom_odd_left`, `trigMom_odd_right`, `trigMom_swap`, `trigMom_eq_thetaQ` | `integral_comp_polarCoord_symm`, `setIntegral_prod_mul`, `integral_sin_pow`, `Function.Periodic.intervalIntegral_add_eq` |
| 3.5.48 (square `S`: `\|x\|, \|y\| ≤ h`) | `dlmf_3_5_48`, `squareRem`, `squareSet`, `volume_squareSet` (`4h²`), `integral_squareSet_mono` | `integral_pow` |
| Meaning of `R = O(hᵏ)` | `cubRem_le_of_exact` (exact on monomials of degree `< k` ⇒ `\|R\| ≤ Chᵏ` for `f ∈ Cᵏ`, `0 < h ≤ 1`), `multilinear_diag_eq`, `prod_coord`, `diskRem_isBigO`, `squareRem_isBigO` | `map_add_eq_sum_add_integral_iteratedFDeriv`, `ContinuousMultilinearMap.map_sum`, `ContinuousMultilinearMap.map_smul_univ` |
| Table 3.5.21 (all seven rules; last square row with the V1.0.7 corner correction) | `diskRule1`–`diskRule4`, `squareRule1`–`squareRule3`; exactness `diskRule1_exact`, …, `squareRule3_exact`; node bounds `*_nodes`; `dlmf_table_3_5_21_disk1`, `_disk2` (`O(h⁴)`), `_disk3`, `_disk4` (`O(h⁶)`), `_square1`, `_square2` (`O(h⁴)`), `_square3` (`O(h⁶)`). All entries correct | |
| Cools (2003), Stroud (1971) | Not formalized (references) | |
| "Monte Carlo … error of order `1/√N`, independently of the dimension" | `mcMean`, `integral_mcMean` (unbiased), `variance_mcMean` (`σ²/N`), `sqrt_variance_mcMean` (`σ/√N`), `dlmf_3_5_x_monteCarlo` (`P(\|mean − m\| ≥ ε) ≤ σ²/(Nε²)`, any probability space) | `ProbabilityTheory.IndepFun.variance_sum`, `ProbabilityTheory.meas_ge_le_variance_div_sq` |
| Importance sampling ("points … sampled from a probability distribution"); Davis–Rabinowitz, Schürer (2004) | Not formalized (prose, references) | |

## Section 3.6

### §3.6(i) Introduction (`Azurite/DLMF/Chapter3/Section6.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.6.1 (`n ∈ ℤ`) | `diffLHS` | |
| 3.6.2 (`Δw_{n−1} = wₙ − w_{n−1}`, `Δ²w_{n−1} = Δwₙ − Δw_{n−1}`) | `dlmf_3_6_2`, `dlmf_3_6_1_iff_3_6_2` | `fwdDiff` |
| homogeneous / inhomogeneous | `IsHomogeneousDiff` | |
| "problems of severe instability often arise" | Made precise in §3.6(ii) | |

### §3.6(ii) Homogeneous Equations (`Azurite/DLMF/Chapter3/Section6.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.6.3, "given `w₀`, `w₁` … computed recursively for `n = 2, 3, …`" (`aₙ ≠ 0`) | `IsRec3`, `fwdRec`, `fwdRecPair`, `dlmf_3_6_3_forward` (existence and uniqueness), `IsRec3.eq_of_eq` | |
| "small multiples of `wₙ` and of an independent solution `gₙ`" | `IsRec3.eq_comb` (two solutions with nonzero Casoratian span all solutions), `casoratian` (§2.9) | |
| "of little consequence if the wanted solution is growing … at least as fast" | `dlmf_3_6_ii_forward_stable` (`\|gₙ/wₙ\| ≤ M` ⇒ relative error `≤ \|ε\| M`) | |
| 3.6.4, recessive (minimal, distinguished) solutions | `IsRecessiveWrt`, `IsRecessive`, `casoratian_ne_zero_of_recessive` | |
| "unique except for a constant factor" | `dlmf_3_6_4_unique` | `tendsto_norm_inv_nhdsNE_zero_atTop` |
| "the computations are unstable" | `dlmf_3_6_ii_forward_unstable` (relative error `→ ∞`) | |
| backward recursion (`cₙ ≠ 0`) from `w_N`, `w_{N+1}` | `bwdRec`, `bwdRecPair`, `dlmf_3_6_3_backward` (existence and uniqueness of `w_{N−1}, …, w₀`) | |
| "the unwanted multiples of `gₙ` now decay in comparison with `wₙ`" | `bwdPerturbed`, `bwdPerturbed_isRec3`, `bwdPerturbed_start`, `dlmf_3_6_ii_backward_stable` | |
| starting values from asymptotic expansions (§2.9); §§3.6(iii), 3.6(v) | Not formalized (pointers) | |

### §3.6(iii) Miller's Algorithm (`Azurite/DLMF/Chapter3/Section6Miller.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| (needed) Casoratian of two solutions | `IsRec3.casoratian_succ` (`aₙCₙ = cₙC_{n−1}`), `IsRec3.casoratian_ne_zero` | |
| trial values `w_N = 1`, `w_{N+1} = 0`, backward recursion; "the original components of the unwanted solution `gₙ` die away" | `millerTrial`, `millerZ`, `millerTrial_eq` (trial solution `= zₙ/z_N`, `zₙ = wₙ − (w_{N+1}/g_{N+1})gₙ`), `tendsto_millerZ` | |
| normalizing factor `Λ` = true `w₀` / trial value | `millerNorm`, `dlmf_3_6_iii_miller` (convergence for every fixed `n`, `w₀ ≠ 0`) | |
| 3.6.5 `∑ λₙwₙ = 1` | `millerSumNorm`, `dlmf_3_6_iii_miller_sum` (convergence when `(w_{N+1}/g_{N+1})∑_{k≤N} λₖgₖ → 0`; no condition on `w₀`) | `HasSum.tendsto_sum_nat` |
| repetition with higher `N` until agreement; references (Wimp, Gautschi, Olver, Gil et al.), continued fractions | Not formalized (algorithmic loop, references) | |

### §3.6(iv) Inhomogeneous Equations (`Azurite/DLMF/Chapter3/Section6Inhom.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.6.1 with `aₙcₙ ≠ 0` | `IsRec3Inh`, `IsRec3Inh.add_hom`, `IsRec3Inh.sub` | |
| forward (backward) recursion stable if `wₙ` grows (decays) at least as fast as any complementary function | `dlmf_3_6_iv_forward_stable`, `dlmf_3_6_iv_backward_stable` | |
| 3.6.6; "computation of `wₙ` by forward recursion is unstable" | `dlmf_3_6_iv_forward_unstable` | |
| "if … `fₙ/wₙ → 0` … backward recursion is unstable as well" | `dlmf_3_6_iv_backward_unstable` | `tendsto_norm_inv_nhdsNE_zero_atTop` |
| "two independent solutions `fₙ` and `gₙ` of the corresponding inhomogeneous equation (the complementary functions)" | **Erratum**: complementary functions solve the *homogeneous* equation (`IsRec3 a b c f`); see `docs/dlmf_errata.md` | |
| 3.6.7 (tridiagonal system, §3.2(ii)) | `IsBVSol`, `dlmf_3_6_7` (equivalence with `tridiag` of 3.2.7), `tridiag_mulVec_row`, `triEntry_split` | |
| "as `N → ∞` with `n` fixed, `wₙ^{(N)} → wₙ`" | `dlmf_3_6_iv_boundary` (solvable for large `N`; convergence), `bvH`, `bvH_isRec3`, `eq_mul_bvH_of_zero`, `dlmf_3_6_iv_wanted_unique` | `Classical.epsilon_spec` |
| Olver (1967a) | Not formalized (reference) | |

### §3.6(v) Olver's Algorithm (`Azurite/DLMF/Chapter3/Section6Olver.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| `pₙ`: 3.6.3 with `p₀ = 0`, `p₁ = 1` by forward recurrence | `olverP`, `olverP_isRec3` | |
| 3.6.8 (`e₀ = w₀`); "equivalent to forward elimination" | `olverE`, `dlmf_3_6_8`, `olverE_eq` (`eₙ = p_{n+1}wₙ − pₙw_{n+1}` for every solution of 3.6.1) | |
| 3.6.9 | `dlmf_3_6_9` (the test is eventually passed when the terms `eₙ/(pₙp_{n+1})`, `1 ≤ n ≤ M`, are nonzero); its meaning: `olver_series` (`wₙ/pₙ = ∑_{k≥n} e_k/(p_kp_{k+1})`), `olver_div_sub`, `olver_error` (error `pₙ(w_N/p_N)` = `pₙ` × tail of the series) | `Finset.exists_mem_eq_inf'` |
| 3.6.10 from `w_N = 0`; "back substitution" | `olverWAux`, `olverW`, `dlmf_3_6_10`, `olverW_eq` (`wₙ − (w_N/p_N)pₙ`), `olverW_isBVSol` (solves 3.6.7) | |
| convergence; "applicable equally to the recessive solution of 3.6.3 or … 3.6.1 under §3.6(iv)" | `dlmf_3_6_v_tendsto`, `olver_tendsto_div`, `dlmf_3_6_v_inhom`, `dlmf_3_6_v_recessive` | |
| "to a prescribed relative accuracy `ε`" | Not formalized: 3.6.9 estimates the tail by its first term (heuristic; error analyses in Olver (1967a), Olver and Sookne (1972), Wimp (1984)) | |
| "to a prescribed relative accuracy `ε`" | `dlmf_3_6_9_one_step` (3.6.9 bounds the next change by `ε|pₙ| min_m |eₘ/(pₘp_{m+1})|`), `dlmf_3_6_9_relative` (relative change `≤ ε` when the terms `eₛ/(pₛp_{s+1})` are nonnegative reals); the error of `wₙ^{(N)}` itself is `pₙ ∑_{s≥N} eₛ/(pₛp_{s+1})` (`olver_5_01`), estimated by 3.6.9 through its first term (heuristic; strict bounds: `olver_10_07`) | |
| error analyses, Olver (1967a) §§4–5, 7 (`Section6OlverError.lean`) | (4.09)–(4.12) `olver_4_09`, `olver_4_10`, `olver_4_11`, `olver_4_12`; truncation error (5.01)–(5.04) `olverTrunc`, `olver_5_01`, `olver_5_03`, `olver_5_04`, `olverT`, `olver_partial_sum`; rounding errors (7.01) `olver_7_01`, `olverP_div_tendsto`, (7.02) `olver_7_02`, back-substitution factor `pᵣ/pₛ` `olver_backsub_propagation` | `Filter.Tendsto.limUnder_eq` |
| more general normalizing condition, Olver (1967a) §§9–10 (`Section6OlverGeneral.lean`) | (9.01)–(9.04) `NormSum`, `olver_9_04` (existence and uniqueness), `eq_comb_of_range`; (9.05)–(9.07) `IsGenBVSol`; (9.10)–(9.14) `genP`, `genQ`, `genE`, `olver_9_10`, `olver_9_14`; Theorem 2 `olver_theorem_2`; bounds (10.02) `olver_10_02`, (10.03)–(10.04) `IsRhoBound`, `olver_10_04`, `olver_10_03`, (10.05)–(10.06) `olver_10_06`, `olver_eta_N`, (10.07)–(10.10) `olverGenBound`, `olver_10_07`, `norm_sub_le_tsum_of_steps` | `Filter.Tendsto.div_atTop`, `not_tendsto_atTop_of_tendsto_nhds`, `Finset.prod_Ico_consecutive`, `HasSum.tendsto_sum_nat` |
| Olver (1967a) §8 (Miller/Shintani as backward elimination), §11 (alternative method, first-order error decomposition), examples; Olver and Sookne (1972), Wimp (1984) | Not formalized | |
| examples | See §3.6(vi) | |

### §3.6(vi) Examples (`Azurite/DLMF/Chapter3/Section6Examples.lean`, `Section6Weber.lean`, `Section6WeberTable.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.6.11 (satisfied by `Jₙ(1)`) | `besA`, `besB`, `besC`, `besJ1`, `dlmf_3_6_11` (from `BZ.besselJNat_recurrence`) | |
| 3.6.12 | `dlmf_3_6_12`, `abs_besselJNat_one_sub_le`, `tendsto_besselJNat_one`, `besselJNat_zero_one_pos` | `Stirling.factorial_isEquivalent_stirling` |
| 3.6.13 (`Yₙ(1)`) | **Deferred**: `Yₙ` is only defined (`BZ.besselY`); the dominance claim is proved for every solution independent of `Jₙ(1)` (`dlmf_3_6_vi_dominant`) | |
| "`Yₙ(1)` is dominant … `Jₙ(1)` is recessive"; backward recursion by Miller's or Olver's algorithm | `besP`, `besP_ge`, `olverP_bes`, `besJ1_isRecessive`, `dlmf_3_6_vi_dominant`, `dlmf_3_6_vi_miller`, `dlmf_3_6_vi_olver` | |
| 11.10.2 (used), 3.6.14 | `weberE`, `abs_weberE_le`, `weberE_rec`, `weberD`, `weberW`, `dlmf_3_6_14` | `intervalIntegral.integral_eq_sub_of_hasDerivAt` |
| 3.6.15, 3.6.16 | `weberE_expansion` (`π𝐄ₙ(1) = 1/(n−1) − (−1)ⁿ/(n+1) + O(n⁻³)`, explicit), `dlmf_3_6_15`, `dlmf_3_6_16` | |
| "intermediate … ; the conditions for Olver's algorithm are satisfied" | `dlmf_3_6_vi_weber_intermediate`, `weberE_lower`, `tendsto_weberW_div_olverP`, `dlmf_3_6_vi_weber_olver` | |
| `𝐄₀(1) = −0.56865 663` from the Maclaurin series (§11.10(iii)) | `weberE_zero_one`, `weberE0Term`, `hasSum_weberE0Term`, `integral_sin_sin_mem`, `dlmf_table_3_6_1_E0` | `intervalIntegral.hasSum_integral_of_dominated_convergence`, `integral_sin_pow_odd`, `Real.hasSum_sin` |
| "The least value of `N` that satisfies (3.6.9) is found to be 16" | `dlmf_table_3_6_1_N` | |
| Table 3.6.1 (`pₙ`, `eₙ`, `eₙ/(pₙp_{n+1})`, `wₙ`) | `table361`, `dlmf_table_3_6_1` (all 64 printed entries correctly rounded results of the computation); `besS`, `olverE_weber`, `olverW_eq_sum`, `olverW_zero_eq`, `encAB`, `encMul`, `RoundsSig`, `rsum` | `Real.pi_gt_d20`, `Real.pi_lt_d20` |
| "The values of `wₙ` for `n = 1, 2, …, 10` are the wanted values of `𝐄ₙ(1)`" | `dlmf_table_3_6_1_wanted` (`n = 2, …, 10`), `trueEnc`, `trueEnc_sound`; **erratum** `dlmf_table_3_6_1_erratum_w1` (`n = 1`) | |
| "for `n > 10` … the underlined digits are in error" | `dlmf_table_3_6_1_digits` (`n = 11–14` consistent with the half-unit criterion; **erratum** at `n = 15`) | |
| Gil et al., references | Not formalized | |

### §3.6(vii) Linear Difference Equations of Other Orders (`Azurite/DLMF/Chapter3/Section6Other.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.6.17 | `IsRec1`, `rec1H`, `rec1H_isRec1`, `rec1H_ne_zero`, `IsRec1.eq_mul_rec1H`, `IsRec1.sub` | |
| "in the inhomogeneous case it may sometimes be necessary to recur backwards to achieve stability" | `rec1Back`, `rec1Back_spec`, `rec1_eq_of_end`, `rec1Back_eq`, `dlmf_3_6_17_backward`, `dlmf_3_6_17_forward_unstable`, `dlmf_3_6_17_unique` | |
| 3.6.18 | `IsRecK`, `IsRecKUpTo`, `isRecK_two_iff` (3.6.1 is `k = 2`) | |
| "or for systems of `k` first-order inhomogeneous equations" | `companionStep`, `dlmf_3_6_18_system` | |
| "`k − ℓ` conditions … at the beginning …, and `ℓ` conditions at the end" | `IsBVk` | |
| "forward and backward recursion … the special cases `ℓ = 0` and `ℓ = k`" | `recKState`, `recKFwd`, `recKState_eq`, `dlmf_3_6_18_forward`, `recK_eq_of_init`, `dlmf_3_6_vii_ell_zero`; `revA`, `revD`, `recKBwd`, `recK_eq_of_end`, `dlmf_3_6_18_backward`, `dlmf_3_6_vii_ell_k` | |
| "`ℓ` … depends on the asymptotic behavior of the wanted solution" | Prose (see §3.6(ii), 3.6.17 above for `k = 1, 2`) | |
| Gautschi (1997b), Wimp (1984), Cash and Zahar (1994), Lozier (1980) | Not formalized | |

## Section 3.7

### §3.7(i) Introduction (`Azurite/DLMF/Chapter3/Section7.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.7.1 (`f`, `g`, `h` analytic in a domain `D`) | `IsInhomSolution` (§1.13(iii)); homogeneous case `dlmf_3_7_1_homogeneous` (= `IsODESolution`) | |
| §1.13, §2.7, Ascher–Petzold (1998), Hairer et al. (1993), Iserles (1996) | Not formalized (pointers) | |

### §3.7(ii) Taylor-Series Method: Initial-Value Problems (`Azurite/DLMF/Chapter3/Section7.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.7.2 | `dlmf_3_7_2` (for every solution in `D`) | `iteratedDeriv_succ` |
| 3.7.3, 3.7.4 | `taylorFG`, `taylorF`, `taylorG`, `taylorH`, `dlmf_3_7_3`, `dlmf_3_7_4` (also for `s = 1`); `taylorFG_differentiableOn`, `taylorH_differentiableOn`, `taylorH_zero` | |
| 3.7.6–3.7.9 | `taylorA`, `taylorB`; convergence for `\|τ\| < R` with `B(z, R)` in the domain of analyticity `dlmf_3_7_8_9` (sums are solutions with data `(1, 0)`, `(0, 1)`, `(0, 0)`), `hasSum_taylor_sol`, `isSCDomain_ball`, `infty_mem_closure_ray`, `taylorB_zero` | `Complex.hasSum_taylorSeries_on_ball` |
| 3.7.5 | `dlmf_3_7_5`, `odeState`, `odeState_succ` | |
| "`τⱼ = z_{j+1} − zⱼ`, `j = 0, 1, …, P`" | **Erratum** (`j ≤ P − 1`; `z_{P+1}` does not exist): `IsTaylorPath`, `taylorPath` | |
| Partition `z₀ = a, …, z_P = b` of the path 𝒫; successive application of 3.7.5 | `IsTaylorPath`, `IsTaylorPath.mem`, `taylorPath`, `dlmf_3_7_ii_exact` | |
| "computed in a stable manner … grows in magnitude at least as fast as all other solutions" | `taylorPath_sub` (errors propagate as homogeneous solutions), `dlmf_3_7_ii_forward_stable` (relative error `≤ C ∑` relative step errors) | |
| "decaying at least as fast … reverse the labeling … initial values `w(b)` and `w′(b)`" | `dlmf_3_7_ii_backward_stable` | |

### §3.7(iii) Taylor-Series Method: Boundary-Value Problems (`Azurite/DLMF/Chapter3/Section7BVP.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "rate of growth … intermediate to that of two other solutions. (This can happen only for inhomogeneous equations.)" | `exists_dep_three`, `dlmf_3_7_iii_hom_not_intermediate`; inhomogeneous example `dlmf_3_7_iii_inhom_intermediate` (`w″ − w = −1`, `posRealRay`, `tendsto_exp_neg_posRealRay`) | `Matrix.exists_mulVec_eq_zero_iff` |
| "solve the set of equations (3.7.5) simultaneously for `j = 0, 1, …, P`" | **Erratum** (`j ≤ P − 1`): `bandAP_mulVec_eq_iff` | |
| 3.7.10 | `stepA`, `stepB`, `bandAP` (block indices `Fin P × Fin 2`, `Fin (P + 1) × Fin 2`), `bandAP_mulVec`, `finProdFinEquiv_two` (flat order) | `finProdFinEquiv` |
| 3.7.11, 3.7.12 | `bandW`, `bandB` | |
| 3.7.13 | `dlmf_3_7_13`, `dlmf_3_7_13_flat` | `Matrix.submatrix_mulVec_equiv` |
| 3.7.14; "the remaining two equations are supplied by boundary conditions" | `IsBC`, `dlmf_3_7_13_14` (3.7.13 + 3.7.14 ⟺ values of a solution of the boundary-value problem) | |
| "`β₀ = β₁ = 0` … can readily be made tridiagonal by annihilating the elements of `𝐀_P` that lie below the main diagonal and its two adjacent diagonals" | `triState`, `triMult`, `bvpA`, `bvpB`, `bvpC`, `bvpF`, `TriRow`, `bvp_tridiagonal`, `block_iff`, `triRow_odd`, `triRow_even`, `triRows_iff`, `bvpX`, `triState_bvpX`, `dlmf_3_7_iii_tridiag_of_sol`, `dlmf_3_7_iii_sol_of_tridiag` | |
| "solved by the method of §3.2(ii), if the differential equation is homogeneous" | `dlmf_3_7_iii_solve` (any `h`; nonvanishing pivots `d_j` of 3.2.10), `three_term_of_tridiag`, `triEntry_mul_split` | |
| "or by Olver's algorithm (§3.6(v)) … especially useful if the endpoint `b` … is at `∞`" | Not formalized (the reduced system is not of the second-order form 3.6.7; see §3.6(v)) | |
| Parallelism remark; Olde Daalhuis–Olver (1998), Lozier–Olver (1993), Ascher et al. (1995) | Not formalized (prose, references) | |

### §3.7(iv) Sturm–Liouville Eigenvalue Problems (`Azurite/DLMF/Chapter3/Section7SL.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.7.15, 3.7.16 (finite `[a, b]`, `q` continuous on `[a, b]`) | `IsDirichletEigenfunction`, `IsDirichletEigenvalue`; shooting solution `slQ`, `slClamp`, `slV`, `slUL`, `slUDL`, `slU`, `slUD`, `slUL_spec`, `slUL_eq_slU`, `continuous_slU`, `isPruferData_slU`, `ode2_eq_zero_Icc` | `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` |
| Prüfer angle (proof device) | `pruferRate`, `prufer`, `IsPruferData` (`prufer_S`, `sin_prufer_eq_zero_iff`, `rate_eq`, `rate_of_zero`, `prufer_lt_of_zero`, `prufer_pos`, `prufer_add_pi_le`), comparison `prufer_compare_core`, `prufer_le_of_le`, `prufer_lt_of_lt`; `isPruferData_sin`, `prufer_sin_ge`; `eventually_lt_right_of_hasDerivAt`, `eventually_lt_left_of_hasDerivAt`, `sinc_mul_self`, `sin_add_mul_sin_sub` | `Real.sinc`, `continuous_sinc` |
| "The eigenvalues `λ_k` are simple" | `eq_mul_slU`, `isDirichletEigenvalue_iff`, `isDirichletEigenfunction_slU`, `exists_slU_ne_zero`, `dlmf_3_7_iv_simple` | |
| 3.7.17 | `dlmf_3_7_17` (`Λ 0 < Λ 1 < ⋯ → ∞` are all the eigenvalues), `slTheta`, `isDirichletEigenvalue_iff_sin`, `slTheta_strictMono`, `continuous_slTheta`, `slTheta_pos`, `exists_slTheta_lt_pi`, `exists_slTheta_ge` | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` |
| Infinite intervals ("with limits taken in 3.7.16") | **Erratum**: `dlmf_3_7_iv_infinite_no_eigenvalue` (`q = 0` on `(0, ∞)`: no eigenvalues), `eq_zero_of_tendsto_mul` | |
| `q` piecewise continuous | Not formalized (continuous `q` only) | |
| Discretization by 3.7.13: tridiagonal, entries polynomials in `λ`; compare §3.2(vi); step size; Pryce (1993) | Not formalized (method description; the entries are polynomials only after truncating 3.7.8) | |

### §3.7(v) Runge–Kutta Method (`Azurite/DLMF/Chapter3/Section7RK.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Jets (proof device) | `IsJet`, `jpoly`, `eval_isBigO_of_coeff`, `pow_isBigO_pow`, `IsJet.congr`, `.congr_fun`, `.add`, `.sub`, `.const_mul`, `.sum`, `.const`, `.id`, `.mono`, `.mul` (`jmul`), `.pow` (`jpow`), `.mul_id` (`jshift`), `.integral` (`jinteg`), `.isBigO_id`, `isJet_zero_of_continuous`, `isBigO_of_isJet_zero` | `Polynomial.X_pow_dvd_iff` |
| Taylor's formula with `O(‖v‖⁴)` remainder, in coordinates | `taylor3_isBigO`, `taylorCoeff2`, `diag_eq_sum`, `taylorCoeff2_zero`, `taylor3_coord`; three variables `coord3`, `coordVec3`, `prod_coord3`, `card_filter3`, `multilinear_diag_eq3`, `wordFiber`, `taylorCoeff3`, `diag_eq_sum3`, `taylor3_coord3` | `map_add_eq_sum_add_integral_iteratedFDeriv` |
| Composition of jets with `f` | `compJet`, `compC`, `compJet_eq`, `IsJet.comp_taylor`; `compJet3`, `compC3`, `compJet3_eq`, `IsJet.comp_taylor3` | |
| 3.7.18, 3.7.19 | `rkK1`, `rkK2`, `rkK3`, `rkK4`, `rk4Step`, `dlmf_3_7_18` (`f ∈ C⁴`) | |
| "The order estimate `O(h⁵)` holds if the solution `w(z)` has five continuous derivatives" | **Erratum**: `dlmf_3_7_v_erratum` | |
| 3.7.20, 3.7.21 | `nysK1`, `nysK2`, `nysK3`, `nysK4`, `nysW`, `nysWD`, `nystrom_isBigO`, `dlmf_3_7_20_w` (`w`-update as printed) | |
| 3.7.21 `k₃` | **Erratum** (`⅛hk₁`, not `⅛hk₂`): `dlmf_3_7_21_erratum`, `not_isBigO_pow_of_le`; corrected `nysK3'`, `dlmf_3_7_20` | |
| Method remarks; Butcher (1987), Dekker–Verwer (1984), Hairer et al. (1993), Hairer–Wanner (1996) | Not formalized (prose, references) | |

## Section 3.8

### §3.8(i) Introduction (`Azurite/DLMF/Chapter3/Section8.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.8.1; simple zeros; multiplicity `m` | `IsZeroOfMultiplicity`, `isZeroOfMultiplicity_one_iff`, `IsZeroOfMultiplicity.root` | |
| "compare §1.10(i)" | `isZeroOfMultiplicity_iff_isZeroOfOrder`, `isZeroOfMultiplicity_iff_analyticOrderAt` | `analyticOrderAt` |
| 3.8.2 (fixed points) | `dlmf_3_8_2` | `Function.IsFixedPt` |
| 3.8.3 (order `p`) | `HasConvOrder`, `convIndices`, `HasConvOrder.mono` | |
| Linear, quadratic, cubic convergence | `IsLinearConv`, `IsLinearConv.tendsto`, `IsQuadraticConv`, `IsCubicConv` | |
| Strict inequality in 3.8.3 | **Imprecision**: `not_mem_convIndices_const` | |
| "`p` is the largest of the possible set of indices" | **Imprecision**: `slowSeq`, `slowSeq_hasConvOrder`, `slowSeq_not_two`, `tendsto_slowSeq`, `dlmf_3_8_3_no_largest` | `tendsto_pow_const_div_const_pow_of_one_lt` |
| Local convergence | `ConvergesLocally`, `convergesLocally_of_contract` | |

### §3.8(ii) Newton's Rule (`Azurite/DLMF/Chapter3/Section8Newton.lean`, `Section8NewtonExample.lean`, `Section8NewtonTable.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.8.4 | `newtonStep` | |
| "If `ζ` is a simple zero, then the iteration converges locally and quadratically" | `newton_sq_estimate`, `newton_simple_zero_ball`, `dlmf_3_8_ii_simple` (`f′` Lipschitz), `dlmf_3_8_ii_simple_of_contDiffAt` (real `C²` or complex analytic), `newton_eventually_quadratic` | `ContDiffAt.exists_lipschitzOnWith`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` |
| "For multiple zeros the convergence is linear … quadratic convergence can be restored by multiplying … by `m`" | `newtonStepMul`, `deriv_eq_of_factor`, `newton_error_of_factor`, `dlmf_3_8_ii_multiple` (linear, ratio `→ (m − 1)/m`, no order `p > 1`; modified rule quadratic), `exists_factor_of_multiplicity` | |
| Real functions, condition (a) | `dlmf_3_8_ii_a`, `newton_real_step`, `newton_real_monotone`, `deriv_sign_const`, `exists_deriv_eq_div_of_zero`, `contDiffAt_two_facts` | `exists_deriv_eq_slope` |
| Condition (b) | `dlmf_3_8_ii_b` (sign conditions on the closed interval `[x₀, x₁]`) | |
| Example: 3.8.5 | `tanExF`, `exPhi`, `hasDerivAt_exF`, `deriv_exF`, `deriv2_exF`, `dlmf_3_8_5` | `Real.hasDerivAt_tan` |
| "The first positive zero of `f(x)` lies in the interval `(π, 3π/2)`" | `exF_strictAntiOn`, `exF_ne_zero_of_mem_Ioc`, `dlmf_3_8_ii_example_zero` (`ζ` to 13 decimals) | `Real.lt_tan` |
| Convergence from `x₀ = 4.65`; Table 3.8.1 | `exF_newton_converges`, `dlmf_table_3_8_1`; **erratum** `x₁ … x₅`; certificate `sinSumQ`, `cotLo`, `cotHi`, `cot_mem`, `cot_antitone`, `cotEnclX`, `phiEncl`, `phiEncl_sound`, `tabEncl`, `tab_correct_check`, `tab_wrong_check` | `Real.pi_gt_d20`, `Real.pi_lt_d20` |
| "When `x₀ ≤ 4.2875` or `x₀ ≥ 4.7125` … does not converge" | **Erratum** (`x₀ = 2.25` converges): `dlmf_3_8_ii_example_erratum`; the `x₀ ≥ 4.7125` part not formalized | |
| "faster when we use instead `f(x) = x cos x − sin x`" | `exG`, `exG_eq`, `newtonStep_exG` (Newton map `x + cot x − 1/x`); speed and interval claims not formalized | |

### §3.8(iii) Other Methods (`Azurite/DLMF/Chapter3/Section8Other.lean`, `Section8Secant.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Bisection: "If `f(a)f(b) < 0` … `[a, b]` contains one or more zeros"; bisection; slow (linear) convergence | `bisectStep`, `bisectStep_spec`, `bisect_iter`, `dlmf_3_8_iii_bisection` (error `≤ (b − a)/2ⁿ`) | `tendsto_atTop_ciSup` |
| "All zeros … can be computed to any predetermined accuracy" | **Imprecision**: `dlmf_3_8_iii_bisection_misses` | |
| Kaufman and Lenker (1986), Nievergelt (1995) | Not formalized | |
| 3.8.6; inverse linear interpolation (§3.3(v)) | `rfPoint`, `dlmf_3_8_6`, `rfPoint_interp` | |
| Regula falsi: "We continue with `x₂` and either `x₀` or `x₁` …" | `rfStep`, `rfPoint_mem`, `rfStep_bracket` | |
| "The convergence is linear" | `dlmf_3_8_iii_regula_falsi` (strictly convex `f`: fixed endpoint, ratio `→ 1 − f′(ξ)(b − ξ)/f(b) ∈ (0, 1)`, no order `p > 1`), `not_mem_convIndices_of_ge` | `StrictConvexOn.lt_slope_of_hasDerivAt`, `StrictConvexOn.slope_lt_of_hasDerivAt` |
| Secant method: "converges locally with order of convergence `p = ½(1 + √5)`" | `rolle_three`, `slopeAt`, `dd2_mvt`, `secant_error`, `secantStep`, `secX`, `secX_succ`, `secant_consts`, `secant_local`, `tendsto_of_contract_rec`, `secant_order` (order exactly `φ` for `f″(ξ) ≠ 0`), `dlmf_3_8_iii_secant` | `exists_hasDerivAt_eq_zero`, `Real.goldenRatio` |
| "its numerical efficiency is ultimately higher than that of Newton's method" | `secant_efficiency` (`√2 < φ`) | |
| "the first approximation `x₂` may be outside `[x₀, x₁]`" | `secant_outside` | |
| 3.8.7 (Steffensen); "converges locally and quadratically for both `ℝ` and `ℂ`" | `steffStep`, `lip_taylor`, `steffStep_eq`, `dlmf_3_8_7`, `dlmf_3_8_7_of_contDiffAt`; **imprecision** (`φ′(ζ) ≠ 1` needed) `dlmf_3_8_7_erratum` | |
| Le (1985) | Not formalized | |
| Eigenvalue methods (zeros of orthogonal polynomials as eigenvalues of tridiagonal matrices, §3.5(vi)); Gil et al., Grad–Zakrajšek, Ikebe, Ball | See §3.5(vi) (`Section5Eigen`); references not formalized | |

### §3.8(iv) Zeros of Polynomials (`Azurite/DLMF/Chapter3/Section8Poly.lean`, `Section8Bairstow.lean`, `Section8AbelRuffini.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.8.8: `n` zeros in `ℂ` counting multiplicity | `dlmf_3_8_8` (card of roots, `aₙ ∏ (z − ζ)`, multiplicities sum to `n`); `rootMultiplicity_eq_iff_isZeroOfMultiplicity` (§3.8(i) multiplicity), `iteratedDeriv_polyEval` | `IsAlgClosed.card_roots_eq_natDegree`, `C_leadingCoeff_mul_prod_multiset_X_sub_C`, `lt_rootMultiplicity_iff_isRoot_iterate_derivative` |
| "Explicit formulas … if `n ≤ 4`; see §§1.11(iii) and 4.43" | `dlmf_3_8_iv_radicals` (coefficients by radicals ⇒ zeros by radicals), `dlmf_3_8_iv_radicals_rat`; `quadratic_rad`, `cubic_rad`, `quartic_rad` (from 1.11.11–1.11.20), `IsRad`, `rad_mem`; §4.43 not formalized (Chapter 4) | `solvableByRad`, `solvableByRad.rad_mem` |
| "No explicit general formulas exist when `n ≥ 5`" | `dlmf_3_8_iv_abel_ruffini` (degree `n` over `ℚ` with a zero not by radicals); vendored `Section8AbelRuffini` (Mathlib Archive, `x⁵ − 4x + 2`) | `isSolvable_gal_of_irreducible` |
| Deflation via Horner (§1.11(i)); final iteration on `p` | `dlmf_3_8_iv_deflation` (`p = (z − ζ)q`, `deg q = n − 1`, roots `ζ ::ₘ roots q`, zeros of `q` are zeros of `p`) | `roots_mul` |
| Example `z⁴ − 1`: zeros `±1, ±i`; 3.8.9 | `quartEx`, `dlmf_3_8_iv_example`, `dlmf_3_8_9`, `dlmf_3_8_iv_example_converges` (monotone, quadratic from `1.5`) | |
| Table 3.8.2 | `dlmf_table_3_8_2`, `tab382`, `tab382_check` (`decide +kernel`); **erratum** `z₅` | |
| 3.8.10 (Bairstow `qⱼ`, `rⱼ`) | `bairAux`, `bairSeq`, `bairSeq_rec`, `bairSeq_rec_all`, `bairQ`, `bairR`, `bairR_rec`, `bairSeq_map`, `bair_down` | |
| "On the last iteration `q_n z^{n−2} + ⋯ + q₂` is the quotient" | `bair_telescope`, `bair_quotient_gen`, `dlmf_3_8_10_quotient`, `dlmf_3_8_10_quotient_poly`, `bairF`, `bairF_eq_zero_iff` (factor iff `F = (q₁, q₀ − sq₁) = 0`) | `eq_zero_of_dvd_of_natDegree_lt` |
| 3.8.11 | `bairStep`, `bairEll`, `bairDet`; Newton interpretation `hasFDerivAt_bairQ` (`∂qⱼ/∂s = rⱼ₊₁`, `∂qⱼ/∂t = rⱼ₊₂`), `bairJ`, `hasFDerivAt_bairF`, `bairStep_newton` | `HasFDerivAt.mul`, `HasFDerivAt.prodMk` |
| "converges locally and quadratically, except when the wanted quadratic factor is a multiple factor of `q(z)`" | `dlmf_3_8_iv_bairstow` (exact factor with `r₂² − ℓr₃ ≠ 0`); `bairDet_eq_quotient`, `bairDet_eq_quotient_complex` (`r₂² − ℓr₃ = Q(z₁)Q(z₂)`); `newton_sq_bound`, `iter_of_sq_bound`, `norm_le_of_two_by_two`. **Imprecision**: "`q(z)`" should read `p(z)`, and the precise nondegeneracy condition is `Q(z₁)Q(z₂) ≠ 0` (no zero of the quadratic factor is a zero of the quotient), which also excludes `z₁ ≠ z₂` with one of them a multiple zero of `p`. That the method fails to be quadratic in the degenerate cases is not formalized. | `ContDiffAt.exists_lipschitzOnWith`, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` |
| Example `z⁴ − 2z² + 1`, `s₀ = 7/4`, `t₀ = −1/2` | `bairExA`, `dlmf_3_8_iv_bairstow_example` (exact factor `(z − 1)²`, `Q(1)² = 16`, local quadratic convergence); convergence from `(7/4, −1/2)` itself not formalized (needs explicit constants) | |
| Table 3.8.3 | `dlmf_table_3_8_3` (all entries correct; `‖e_{k+1}‖ ≤ ‖e_k‖²`, `k ≤ 4`), `tab383`, `errQ`, `tab383_check`, `bairExStepQ`, `bairEx_iterate_cast`, `bairStep_map` | |
| National Physical Laboratory (1961); McNamee (2007) | Not formalized (references) | |

### §3.8(v) Zeros of Analytic Functions (`Azurite/DLMF/Chapter3/Section8Halley.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "Newton's rule is the most frequently used iterative process" | See §3.8(ii) (`dlmf_3_8_ii_simple`, `dlmf_3_8_ii_simple_of_contDiffAt`) | |
| 3.8.12 (Halley's rule) | `halleyStep`, `halleyStep_eq` (`z − 2ff′/(2f′² − ff″)`) | |
| "useful when `f(z)` satisfies a second-order linear differential equation" | `halleyStep_ode` (`f″ + pf′ + qf = 0`: only `f`, `f′` needed) | |
| "The rule converges locally and is cubically convergent" | `dlmf_3_8_v_halley` (simple zero, `f″` Lipschitz), `dlmf_3_8_v_halley_of_contDiffAt` (`C³`, real or complex), `dlmf_3_8_v_halley_analytic`; `taylor2_bound`, `halley_error`, `halley_cube_ball`, `iter_of_cube_bound` | `ContDiffAt.exists_lipschitzOnWith`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, `AnalyticAt.contDiffAt` |
| Initial approximations: phase principle, Rouché's theorem (§1.10(iv)) | See §1.10(iv): `dlmf_1_10_9`, `dlmf_1_10_9_phase`, `dlmf_1_10_iv_rouche` | |
| Fabijonas and Olver (1999); Segura (2002, 2013); Gil and Segura (2003); Gil et al. (2007a) | Not formalized (references) | |

### §3.8(vi) Conditioning of Zeros (`Azurite/DLMF/Chapter3/Section8Conditioning.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.8.13 | `dlmf_3_8_13` (implicit zero `z(α)`: existence, local uniqueness, `dz/dα = −f_α/f_z`; partials continuous at the point) | `implicitFunctionOfBivariate`, `hasStrictFDerivAt_implicitFunctionOfBivariate`, `ContinuousLinearEquiv.unitsEquivAut` |
| 3.8.14 | `coeffPerturb`, `coeffPerturb_eq`, `coeff_coeffPerturb`, `dlmf_3_8_14` (`dz/da_j = −z^j/f′(z)`) | `Polynomial.hasDerivAt`, `Polynomial.continuous` |
| "the computation of zeros of polynomials is often an ill-posed problem" | Illustrated by `dlmf_3_8_16` | |
| 3.8.15 (Wilkinson) | `wilkinson`, `wilkinson_roots`, `wilkinson_eval_eq_zero_iff` | `roots_multiset_prod_X_sub_C` |
| `p′(20) = 19!`, `a₁₉ = 1 + 2 + ⋯ + 20 = 210` | `wilkinson_deriv_twenty`; **erratum** `wilkinson_coeff_nineteen` (`a₁₉ = −210`) | `prod_X_sub_C_coeff_card_pred` |
| 3.8.16 | `dlmf_3_8_16` (`dx/da₁₉ = −20¹⁹/19! ∈ (−4.31, −4.30) × 10⁷`) | |
| Gautschi (1984, §4) | Not formalized (reference) | |

### §3.8(vii) Systems of Nonlinear Equations (prose only)

| Equation | Theorem | Mathlib |
|---|---|---|
| "For fixed-point iterations and Newton's method for solving systems of nonlinear equations, see Gautschi (1997a) and Ortega and Rheinboldt (1970)" | Pointer. Available in Azurite: Newton's method in a normed space with quadratic local convergence (`newton_sq_bound`, `iter_of_sq_bound`, `Section8Bairstow`), contraction iterations (`convergesLocally_of_contract`, `Section8`) | `ContractingWith.fixedPoint`, `ContractingWith.tendsto_iterate_fixedPoint` (Banach) |

### §3.8(viii) Fixed-Point Iterations: Fractals (`Azurite/DLMF/Chapter3/Section8Fractal.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.8.17 | `Function.iterate` (as throughout §3.8); fixed points 3.8.2 `dlmf_3_8_2` | |
| "cannot always be predicted, especially in the complex plane" | Prose | |
| Example 3.8.9: near `±1, ±i` the sequences converge | `quartPhi`, `quartPhi_eq`, `dlmf_3_8_viii_local` (local quadratic convergence at each zero) | |
| Basins of attraction | `basin`, `basin_mem_nhds`, `basin_disjoint`; symmetry `quartPhi_mul_I`, `quartPhi_conj`, `basin_I_mul` | `tendsto_nhds_unique` |
| Julia set; "very complicated structure"; Julia sets are fractals (self-similar) | Not formalized (no Julia-set theory in Mathlib); Julia (1918), Devaney (1986) references | |

## Section 3.9

### §3.9(i) Sequence Transformations (`Azurite/DLMF/Chapter3/Section9.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Real or complex sequences | `𝕜` a normed field; `SeqTransform` | |
| Limit-preserving | `IsLimitPreserving` | |
| 3.9.1 (accelerating) | `IsAccelerating`, `IsAccelerating.tendsto`; `tendsto_of_ratio` (3.9.1 forces `tₙ → σ` when `sₙ ≠ σ` eventually) | |
| "Similarly for convergent series … partial sums" | `partialSum` (§1.9), `tendsto_partialSum` | `HasSum.tendsto_sum_nat` |
| "effective for one type of sequence but may not accelerate convergence for another type" | `shiftT`, `shiftT_limitPreserving`, `shiftT_accelerates_factorial` (`1/n!`), `shiftT_not_accelerating_geometric` (`qⁿ`); `id_not_accelerating` | `factorial_tendsto_atTop` |
| "It may even fail altogether by not being limit-preserving" | `linExtrap` (`sₙ + n(s_{n+1} − sₙ)`), `linExtrap_accelerates` (`1/(n + 1)`), `linExtrap_not_limitPreserving` (`(−1)ⁿ/(n + 1)`) | |

### §3.9(ii) Euler's Transformation of Series (`Azurite/DLMF/Chapter3/Section9Euler.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.9.2 | `eulerTerm`, `dlmf_3_9_2` (convergent `∑ (−1)ᵏaₖ` ⇒ Euler series converges to the same sum); `euler_partial_eq` (binomial means `2^{−N} ∑ C(N, j+1) s_j`), `choose_abel`, `euler_weights`, `toeplitz_tendsto`. **Imprecision**: "provided that the right-hand side converges" is automatic (Euler's transformation is regular) | `Nat.sum_range_choose`, `Nat.choose_le_pow`, `tendsto_pow_const_div_const_pow_of_one_lt` |
| 3.9.3 | `dlmf_3_9_3` | `fwdDiff` |
| 3.9.4 | `dlmf_3_9_4`, `neg_one_pow_fwdDiff` | `fwdDiff_iter_eq_sum_shift` |
| "usually applied to alternating series" | Prose | |
| 3.9.5 | `dlmf_3_9_5` (both series → `ln 2`; Euler terms `1/(k 2ᵏ)`), `fwdDiff_iter_inv_affine` | `Real.hasSum_pow_div_log_of_abs_lt_one`, `Antitone.tendsto_alternating_series_of_tendsto_zero` |
| 3.9.6 | `dlmf_3_9_6` (both series → `π/4`; terms `½ k!/(1·3⋯(2k + 1))`) | `Real.tendsto_sum_pi_div_four` |

### §3.9(iii) Aitken's Δ²-Process (`Azurite/DLMF/Chapter3/Section9Aitken.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.9.7 | `aitken`, `dlmf_3_9_7` (forward-difference form) | `fwdDiff` |
| 3.9.8 (linear convergence) | `IsLinearlyConvergent` | |
| "This transformation is accelerating if `{sₙ}` is a linearly convergent sequence" | `dlmf_3_9_iii_accelerating` (with `sₙ ≠ σ`), `aitken_ratio`; exactness on geometric sequences `aitken_geometric` | |
| Iterated Δ²-process; Brezinski and Redivo Zaglia (1991) | `aitkenIter`; reference not formalized | |

### §3.9(iv) Shanks' Transformation (`Azurite/DLMF/Chapter3/Section9Shanks.lean`, `Section9Hankel.lean`, `Section9ShanksTable.lean`, `Section9ShanksExample.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "a generalization of Aitken's Δ²-process" | `shanks_one` (`k = 1` is Aitken) | |
| 3.9.9 | `shanks` | |
| 3.9.10 | `hankel`, `hankel_zero`, `hankel_one`, `hankel_two` | `Matrix.det` |
| 3.9.11 (Wynn's epsilon algorithm) | `wynnEps`, `wynnEps_succ_succ` | |
| "Then `t_{n,2k} = ε_{2k}^{(n)}`" | `dlmf_3_9_11` (also `ε_{2k+1}^{(n)} = H_k(Δ³sₙ)/H_{k+1}(Δsₙ)`; assumes the Hankel determinants `H_k(Δ²sₙ)`, `H_k(Δsₙ)` nonzero, which DLMF leaves implicit); `wynnEps_three` (`k = 1`). Determinant machinery: `desnanot_jacobi` (via Schur complements, `det_schur`), `det_rowDiff`, `det_onesRow`, `sylvester_hankel`, `sylv1_*`, `sylv2_*`, `hankel_J1`, `hankel_J2` | `Matrix.det_fromBlocks₁₁`, `Matrix.det_permute'`, `sign_finRotate`, `Matrix.det_of_isUpperTriangular`, `Matrix.det_succ_row` |
| "Aitken's Δ²-process is the case `k = 1`" | `shanks_one`, `wynnEps_three` | |
| Padé approximant `[(n + k)/k]_f` (§3.11(iv)) | `pade_eq_shanks` (`t_{n,2k} = [(n + k)/k]_f`), `pade_eq_wynnEps` (`Section11Pade.lean`) | |
| Brezinski and Redivo Zaglia (1991, pp. 78–95) | Not formalized (reference) | |
| Example 3.9.12, `s_∞ = π²/12 = 0.82246 70334 24…` | `s391`, `sQ391`, `s391_eq`, `dlmf_3_9_12` | `hasSum_zeta_two`, `HasSum.even_add_odd`, `Real.pi_gt_d20` |
| Table 3.9.1 | `dlmf_table_3_9_1`; `lapDet`, `lapDet_eq` (Laplace expansion in `ℚ`), `sTab391`, `sT391_eq`, `tQ391`, `tab391`, `tab391_check` (`decide +kernel`), `shanks_s391`, `hankel_ratCast`, `hankel_congr`; **erratum** `t_{9,10}` | `RingHom.map_det` |

### §3.9(v) Levin's and Weniger's Transformations (`Azurite/DLMF/Chapter3/Section9Levin.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.9.13 | `levinGen` (weights `c_{j,k,n} = w(n+j)/w(n+k)`), `levinL`; kernel `levinGen_eq_of_poly`, `alt_choose_poly` | `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`, `fwdDiff_iter_eq_sum_shift` |
| 3.9.14 | `levin39W`, `dlmf_3_9_14`, `levinL_exact` (exact for `s_m = σ + a_{m+1} ∑_{i<k} d_i/(m+1)^i`); `levinL_zero_eq_levinD` (`n = 0` is 2.11.32, §2.11(vi)) | |
| 3.9.15 | `IsLogConvergent`; example `zeta2_isLogConvergent` (`∑ 1/(j+1)²`), `zeta2_tail_bounds`, `hasSum_telescope` | `hasSum_zeta_two`, `hasSum_le` |
| "Sequences that are accelerated by Levin's transformation include logarithmically convergent sequences" | **Erratum** for the special form 3.9.13–3.9.14: `levinL_one_zeta2`, `levinL_one_zeta2_ratio` (ratio → 1/2 for `k = 1`), `levinL_one_not_accelerating`; numerically the ratio → `1/(k+1)` for `k = 2, 3`; Levin's `u`-transformation (exponent `k − 2`) accelerates this sequence (numerical) | |
| Brezinski and Redivo Zaglia (1991, pp. 39–42) | Not formalized (reference) | |
| 3.9.16, 3.9.17 (Weniger) | `wenigerW₁`, `wenigerW₂`, `pochhammer_eval`; kernel by `levinGen_eq_of_poly` | `ascPochhammer` |
| "β and γ … chosen arbitrarily subject to certain conditions"; Weniger (1989) | Not formalized (reference) | |

## Section 3.10

### §3.10(i) Introduction (`Azurite/DLMF/Chapter3/Section10.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "See §1.12 for relevant properties of continued fractions" | Pointer to `Chapter1/Section12*` | |
| 3.10.1 (`aₙ ≠ 0`) | `IsCF`, `dlmf_3_10_1` (`CfConverges`, §1.12) | |
| 3.10.2; "`Cₙ` is the `n`th approximant or convergent" | `dlmf_3_10_2` (`cfConv = cfA/cfB` with recurrences 1.12.5–1.12.6), `cfConv_zero_one` | |

### §3.10(ii) Relations to Power Series (`Azurite/DLMF/Chapter3/Section10Series.lean`, `Section10QD.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "Every convergent, asymptotic, or formal series (3.10.3) can be converted into a continued fraction … with 3.10.4" | **Erratum**: false if some `uₙ = 0` (`n ≥ 1`): `dlmf_3_10_ii_erratum` (via 1.12.7) | |
| 3.10.3–3.10.5 | `eulerA`, `eulerB`, `eulerA_ne_zero`, `dlmf_3_10_4` (`Bₙ = 1`, `Aₙ = u₀ + ⋯ + uₙ`) | |
| arctan example (4.24.3, 4.25.4) | Not formalized (Chapter 4 not yet available) | |
| 3.10.6 (`S`-fraction) | `sfA`, `sfB`, `sNum`, `sDen`, `sDen_coeff_zero`; `pcfP`, `pcfQ` (1.12.5–1.12.6 over a commutative ring), `pcfP_eq_cfP`, `pcfQ_eq_cfQ` | |
| 3.10.7 (correspondence) | `SCorresponds` | `PowerSeries`, `PowerSeries.inv` |
| 3.10.8–3.10.10 (QD algorithm) | `qdTable`, `qdE`, `qdQ`, `dlmf_3_10_8`, `dlmf_3_10_9`, `qdCoeff`, `dlmf_3_10_10` | |
| "the coefficients `aₙ` can always be calculated … by means of the quotient-difference algorithm" | `dlmf_3_10_10_corresponds` (`Section10QD.lean`: if `cₖ ≠ 0` and `e_j^k ≠ 0`, the `S`-fraction with 3.10.10 corresponds to `f`); tails `qdV`, `qdV_tails` (induction on `j` from the rhombus rules), `tail_residual`, `tail_dvd`, `shiftSeries`, `divX`, `pcfP_map`, `pcfQ_map`. Imprecision: "always" needs the `e_j^k` in 3.10.9 to be nonzero (e.g. `cₙ ≡ 1`: `e_1^k = 0`, the `S`-fraction of `1/(1 − z)` terminates) | `PowerSeries.mul_inv_cancel`, `PowerSeries.X_pow_dvd_iff` |
| Instability; Stokes (1980); Gargantini and Henrici (1967) | Not formalized (numerical remarks, references) | |
| 3.10.11 (`J`-fraction), association | `jfA`, `jfB`, `jNum`, `jDen`, `JAssociated` | |
| "`Cₙ` of the Jacobi fraction equals `C_{2n}` of the Stieltjes fraction" | `contrAlpha`, `contrBeta`, `contraction_seq`, `dlmf_3_10_11_contraction`, `sCorresponds_jAssociated` | |
| Examples (§§4.9, 4.35, 5.10, 7.9, 8.9, …); Lorentzen and Waadeland (1992), Cuyt et al. (2008) | Pointers; not formalized | |

### §3.10(iii) Numerical Evaluation of Continued Fractions (`Azurite/DLMF/Chapter3/Section10Eval.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Forward recurrence algorithm (1.12.5) | `cfA`, `cfB`, `dlmf_1_12_5` (§1.12); instability/overflow/rescaling remarks not formalized | |
| 3.10.12 (backward recurrence), "`u₀ = Cₙ`" | `backU`, `dlmf_3_10_12` (exact, nested evaluation `cfConv`); stability remark and Jones and Thron (1974) not formalized | |
| 3.10.13–3.10.15 (forward series recurrence), "the `n`th partial sum … equals the `n`th convergent" | `fsA`, `fsB`, `fsRho`, `fsT`, `fsB_rec`, `fsRho_eq` (`ρ_k = a_k B_{k−1}/B_{k+1}`), `fsT_eq` (`t_k = a₀⋯a_k/(B_k B_{k+1})`), `prod_fsA`, `dlmf_3_10_14` (`B_k ≠ 0`) | |
| Gautschi (1979c) | Not formalized (reference) | |
| 3.10.16–3.10.17 (Steed's algorithm) | `steed`, `steed_zero`, `dlmf_3_10_17` (`Dₙ = B_{n−1}/Bₙ`, `∇Cₙ = Cₙ − C_{n−1}`, `Cₙ = Aₙ/Bₙ`; `B_k ≠ 0`) | |
| Lentz (1976), Thompson and Barnett (1986); Blanch (1964), Lorentzen and Waadeland (1992), Cuyt et al. (2008), Gautschi (1967), Gil et al. (2007a), Wimp (1984); pointers to §§6.18(i), 7.22(i), … | Not formalized (references, pointers) | |

## Section 3.11

### §3.11(i) Minimax Polynomial Approximations (`Azurite/DLMF/Chapter3/Section11Minimax.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Minimax approximation, `εₙ = f − pₙ`, `max |εₙ|` | `polyOn`, `minimaxErr` (sup norm on `C([a, b], ℝ)`), `IsMinimax`, `abs_err_le` | `ContinuousMap.norm_coe_le_norm` |
| "there exists a unique `n`th degree polynomial … that minimizes `max |εₙ(x)|`" | `dlmf_3_11_i_exists_unique` (`a < b`); existence `minimax_exists` (compactness in the finite-dimensional subspace), uniqueness `minimax_unique` via `minimax_extremal` (extremal set has `≥ n + 1` points, Lagrange-interpolating perturbation) and `avg_eq` | `FiniteDimensional.proper_real`, `Lagrange.interpolate`, `eq_of_natDegree_lt_card_of_eval_eq` |
| "A sufficient condition … `n + 2` distinct points … changes sign at these consecutive maxima" | `dlmf_3_11_i_sufficient`; `not_alternates` (a polynomial of degree `≤ n` cannot strictly alternate in sign at `n + 2` points) | `intermediate_value_Ioo` |
| 3.11.1–3.11.5 (Remez step) | `remezSystem`, `remezSystem_injective`, `dlmf_3_11_5` (unique solution for `x₀ < ⋯ < x_{n+1}`), `remez_fixed` (correction `0` at an equioscillating `pₙ`) | `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` |
| 3.11.3–3.11.5 in correction form | `remez_step_iff_delta` (`a_k + δa_k`, `m_j = (−1)^j εₙ(x_j)`), `remez_step_iff` (`p_new(x_j) + (−1)^j m = f(x_j)`), `remezPoly` (`Section11Remez.lean`) | |
| "The iterative process converges locally and quadratically" | `dlmf_3_11_i_remez_local` (`Section11Remez.lean`): for `f ∈ C²` and `p*` equioscillating at `x₀* < ⋯ < x_{n+1}*` (endpoints fixed as in DLMF) with nondegenerate interior extrema `ε*″(x_j*) ≠ 0`, every `p` near `p*` has exactly one zero of `εₙ′` within `δ` of each interior `x_j*`, and the update obeys `‖p_new − p*‖, |m − m*| ≤ K‖p − p*‖²` (coefficient norm `cn`); `dlmf_3_11_i_remez_converges` (iterates converge, quadratically and at least geometrically, `m → m*`). Ingredients: `remez_lower` (uniform invertibility near the nodes, compactness), `lin_near`/`lin_lower`/`lin_unique`/`lin_exists`/`lin_taylor`. These hypotheses make DLMF's "in general" precise | `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, `IsCompact.exists_isMinOn`, `intermediate_value_Icc` |
| Meinardus (1967), Hart et al. (1968), Cody (1970), Ralston (1965) | Not formalized (references) | |

### §3.11(ii) Chebyshev-Series Expansions (`Section11Chebyshev.lean`, `Section11ChebSeries.lean`, `Section11ChebComplex.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.11.6 | `dlmf_3_11_6` (`Tₙ(x) = cos(n arccos x)` on `[−1, 1]`) | `Polynomial.Chebyshev.T_real_cos`, `Real.cos_arccos` |
| 3.11.7, `T₀ = 1`, `T₁ = x` | `dlmf_3_11_7` (every integer `n`), `dlmf_3_11_7_init` | `Polynomial.Chebyshev.T_add_two` |
| 3.11.8 | `dlmf_3_11_8`; integrand integrable, `intervalIntegrable_dlmf_3_11_8` | `Polynomial.Chebyshev.integral_measureT`, `integral_eval_T_real_mul_eval_T_real_measureT_of_ne`, `integral_T_real_mul_self_measureT_of_ne_zero`, `intervalIntegrable_sqrt_one_sub_sq_inv` |
| 3.11.9, `x_ℓ = cos(πℓ/n)`, `∑''` | `dlmf_3_11_9`, `sumDPrime`, `sumDPrime_cos` (`∑''_ℓ cos(mπℓ/n) = n·[2n ∣ m]`, via the Dirichlet kernel `halfDirichlet` of §1.8), `int_dvd_cases` | `Polynomial.Chebyshev.node`, `Int.eq_zero_of_abs_lt_dvd` |
| Gil et al. (2007a, Chapter 3), Mason and Handscomb (2003), Chapter 18 | Not formalized (references) | |
| 3.11.10 | `chebCoeff`, `dlmf_3_11_10`; `fourierA_cheb` (`cₙ` = Fourier cosine coefficient of `f(cos θ)`), `fourierB_cheb` | `intervalIntegral.integral_comp_neg` |
| 3.11.11, uniform convergence for `f` continuously differentiable on `[−1, 1]`, `∑'` | `dlmf_3_11_11` (uniform), `dlmf_3_11_11_hasSum` (pointwise), `chebPartialSum`; `summable_abs_chebCoeff` via `summable_fourierC_cheb` (Parseval for `(f ∘ cos)′`, `fourierC_deriv`) and `dlmf_1_8_1` | `tendsto_sum_nat_add`, `Summable.sum_add_tsum_nat_add` |
| "(3.11.11) is the Fourier-series expansion of `f(cos θ)`" | `chebPartialSum_cos_eq` (truncations = Fourier partial sums), `fourierA_cheb` | |
| "if `f ∈ C^∞[−1, 1]` … usually very rapid; compare (1.8.7)" | `dlmf_3_11_ii_smooth` (`cₙ = o(n^{−m})` for `f ∈ C^m[−1, 1]`, from `dlmf_1_8_7`), `dlmf_3_11_ii_smooth_all` | `ContDiff.differentiable_iteratedDeriv` |
| 3.11.12 | `dlmf_3_11_12` (uniform on `[a, b]`; `dₙ` = 3.11.10 for `t ↦ f(((b − a)t + a + b)/2)`) | `TendstoUniformlyOn.comp` |
| "a very good first approximation to the minimax polynomial … truncate at its `(n + 1)`th term" | `dlmf_3_11_14` (below) | |
| 3.11.13 ("approximately"; "exactly those properties concerning its maxima and minima that are required") | `dlmf_3_11_13`: if `εₙ = d T_{n+1}((2x − a − b)/(b − a))` exactly on `[a, b]`, then `pₙ` is minimax with error `|d|` (via `dlmf_3_11_i_sufficient` at the extrema of `T_{n+1}`) | `Polynomial.Chebyshev.eval_T_real_node`, `node_lt`, `abs_eval_T_real_le_one` |
| 3.11.14, ratio bounded by `1 + Lₙ` | `dlmf_3_11_14` (Powell's bound against any `p` of degree `≤ n` on `[a, b]`), `dlmf_3_11_14_minimax` (against the minimax error), `cheb_tail_hasSum` (the remainder is the tail `∑_{k ≥ n+1}`); ingredients `powell_bound`, `chebPartialSum_bound` (Dirichlet kernel, `|Sₙh| ≤ Lₙ max|h|`), `chebPartialSum_poly` (truncation reproduces polynomials; `integral_cos_pow_mul_cos`, `chebCoeff_poly_eq_zero`) | `fourierPartialSum_eq_fold` (§1.8), `Set.IccExtend` |
| `L₀ = 1` | `lebesgueConst_zero` | |
| "`Lₙ` is a monotonically increasing function of `n`" | `dlmf_3_11_ii_lebesgue_strictMono` (strictly; `Section11Lebesgue.lean`) via Szegő's series `dlmf_3_11_ii_szego` (`Lₙ = (16/π²)∑_{k≥1} H′_{k(2n+1)}/(4k² − 1)`, `hprime`), from the Fourier series of `|sin x|` (`hasSum_abs_sin`, `fourierA_abs_sin`), `∫₀^{π/2} sin²(Mu)/sin u du = H′_M` (`integral_sin_sq_div_sin`, `sin_sq_nat_mul`), dominated convergence, `lebesgueConst_eq_half` | `intervalIntegral.hasSum_integral_of_dominated_convergence`, `hasSum_lt` |
| "`L₁₀₀₀ = 4.07…`" | `dlmf_3_11_ii_lebesgue_1000` (`4.07 ≤ L₁₀₀₀ < 4.08`; numerically `4.0701636…`, `Section11LebesgueNum.lean`): Szegő's series with `H′_M = H_{2M} − ½H_M` (`hprime_eq_harmonic`), `1/(2m) − 1/(12m²) ≤ H_m − ln m − γ ≤ 1/(2m)` (`harmonic_sub_log_bounds`, from `log_one_add_inv_le_trap`/`log_one_add_inv_ge_trap`), `hprime_bounds`, summation by parts `hasSum_log_div`, `∑ 1/(2k+1)² = π²/8` (`hasSum_inv_odd_sq`), kernel-checked rational bounds `dLoQ_40`, `dHiQ_40`, `harmonic_128_bounds`, `euler_bounds`, `log_2001_bounds` | `Real.hasSum_log_one_add_inv`, `tendsto_harmonic_sub_log`, `hasSum_zeta_two`, `Real.log_two_gt_d9`, `Real.pi_gt_d6` |
| "the set of minimax approximations … `½(n + 1)(n + 2)` coefficients, … Chebyshev-series approximations requires only `n + 1`" | `dlmf_3_11_ii_storage` | |
| Calculation of Chebyshev coefficients: "more efficient to make use of the orthogonal property (3.11.9)" | `dlmf_3_11_ii_discrete_coeff` (`c_k = (2/n)∑''_ℓ p(x_ℓ)T_k(x_ℓ)` exactly for `p = ∑'_{j≤n} c_jT_j`, `k < n`) | |
| Recurrences from differential equations; Clenshaw (1957, 1962), Miller (1966), Mason and Handscomb (2003, Chapter 10), Fox and Parker (1968, Chapter 5) | Not formalized (outline and references) | |
| Clenshaw's algorithm 3.11.15, `u_{n+1} = 0`, `u_n = c_n`, sum `= ½(u₀ − u₂)` | `clenshawW`, `clenshawU`, `clenshawU_init`, `clenshawU_succ_succ`, `dlmf_3_11_15` | |
| Oliver (1977) | Not formalized (reference) | |
| Complex variables: "converges within an ellipse" | `dlmf_3_11_ii_complex` (analytic in `chebEllipse ρ = {|z − 1| + |z + 1| < ρ + ρ⁻¹}` ⇒ `f(z) = ∑' cₙTₙ(z)`), `chebCoeffC`, `chebCoeffC_eq`; Joukowski map `norm_joukowski_sub_add`, `joukowski_mem`, `exists_joukowski`, `T_joukowski`; `laurentCoeff_joukowski` (Laurent coefficients on `|w| = 1` = Fourier coefficients of `f(cos θ)`) | `hasSum_laurent` (§1.10), `parallelogram_law_with_norm`, `IsAlgClosed.exists_pow_nat_eq` |
| "no advantage in ℂ … compared with the Maclaurin expansion", Mason and Handscomb (2003, §5.10) | Not formalized (prose, reference) | |

### §3.11(iii) Minimax Rational Approximations (`Section11Rational.lean`, `Section11RationalExist.lean`, `Section11RationalAchieser.lean`, `Section11RationalExample.lean`, `Section11RationalExampleData.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| `f` continuous, weight `w` continuous and nonvanishing on `[a, b]` | hypotheses of every theorem; `weight_mul_pos` (constant sign) | `intermediate_value_uIcc` |
| 3.11.16 | `ratDLMF`, `dlmf_3_11_16` (normalization `q₀ = 1`); general class `RatAdmissible` (`deg P ≤ k`, `deg Q ≤ ℓ`, `Q > 0`) | |
| 3.11.17, minimax | `ratErr`, `ratMaxErr`, `IsRatMinimax`; `abs_ratErr_le`, `ratMaxErr_le`, `exists_ratMaxErr` | `IsCompact.sSup_mem` |
| "can be extended to the case when `pₙ(x)` is replaced by a rational function" (sufficiency) | `dlmf_3_11_iii_sufficient`, `dlmf_3_11_iii_vallee_poussin` (de la Vallée-Poussin bound), `vallee_poussin_deg` | `not_alternates` (§3.11(i)) |
| "There exists a unique solution of this minimax problem" | **Erratum** `dlmf_3_11_iii_not_exists` (fails with `q₀ = 1`); corrected existence `dlmf_3_11_iii_exists` (minimizing sequence, `coeff_norm_le_of_eval_le`, `cancel_zeros`), `dlmf_3_11_iii_exists_normalized` (`0 ∈ [a, b]`), uniqueness `dlmf_3_11_iii_unique` | `IsCompact.tendsto_subseq`, `LinearEquiv.ofInjectiveEndo` |
| 3.11.18, "at least `k + ℓ + 2` values `x_j`" | **Erratum** `dlmf_3_11_iii_degenerate` (`x²`, type `[1, 1]`: three points); corrected `dlmf_3_11_iii_characterization` (Achieser: minimax ⇔ equioscillation at `D + 2 = k + ℓ + 2 − d` points), `dlmf_3_11_iii_alternation`, `ratD`, `ratDefect`, `ratDefect_eq_zero_iff`; ingredients `eq_zero_of_weak_alternates`, `exists_cross_eq` (Bezout), `exists_poly_sign` (separation), `alternation_of_minimax` (perturbation), `exists_coprime_rep` | `Lagrange.coeff_eq_sum`, `isCoprime_div_gcd_div_gcd` |
| Hart et al. (1968), Remez's second algorithm, Remez (1957), Werner et al. (1967), Johnson and Blair (1973) | Not formalized (references) | |
| Example, 3.11.19, Table 3.11.1 | `P33`, `Q33`, `pR33`, `qQ`; `dlmf_3_11_iii_table_upper` (`|R₃,₃ − J₀| ≤ 1.09·10⁻⁸` on `[0, 0.8935769663]`), `dlmf_3_11_iii_table_lower` (every type-`[3, 3]` approximation has error `≥ 1.0821·10⁻⁸`), `dlmf_3_11_iii_table_3_11_1`; `besselJ0_approx` (Maclaurin polynomial, error `≤ 10⁻¹⁷`), `poly_cell` (second-order cell bound), kernel checks `cellS_all`, `altPt_check` | `Polynomial.coeff_iterate_derivative` |
| Figure 3.11.1, "`0 ≤ x ≤ j₀,₁` (`= 0.89357…`)" | **Erratum** `dlmf_3_11_iii_table_erratum` (`j01_bounds`: `2.4 ≤ j₀,₁ ≤ 2.41`; error of `R₃,₃` `≥ 0.04` at `2.4`; competitor `competitor_err` `≤ 0.01`); `besselJ0_pos` on `[0, 2.4]` | |

### §3.11(iv) Padé Approximations (`Section11Pade.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.11.20, 3.11.21, 3.11.22 | `IsPadeForm` (formal power series over a field, `N − fD = O(z^{p+q+1})`), `X_pow_dvd_of_isPadeForm` | `PowerSeries.X_pow_dvd_iff` |
| "denoted by `[p/q]_f(z)`" | `pade` (in `RatFunc K`), well defined: `exists_isPadeForm` (nonzero solution of the homogeneous system), `isPadeForm_cross` (`N₁D₂ = N₂D₁`), `pade_eq` | `LinearMap.ker_ne_bot_of_finrank_lt`, `IsFractionRing.injective` |
| "if `b₀ ≠ 0`, then the Maclaurin expansion of (3.11.21) agrees with (3.11.20) up to … `z^{p+q}`" | `dlmf_3_11_iv_maclaurin` | `PowerSeries.mul_inv_cancel` |
| 3.11.23 (`c_j = 0` for `j < 0`) | `dlmf_3_11_23`, `coeff_mul_poly` | `PowerSeries.coeff_mul` |
| 3.11.24, "Approximants with the same denominator degree are located in the same column" | `padeTable`, `dlmf_3_11_24`; first column `pade_zero_right` (`[n/0]_f = sₙ`), duality `isPadeForm_inv`, `pade_inv` (`[p/q]_f = 1/[q/p]_{1/f}`), first row `pade_zero_left` | `PowerSeries.trunc` |
| Baker and Graves-Morris (1996, §4.7): convergence, continued fractions, Gaussian quadrature | Not formalized (references) | |
| 3.11.25 (Wynn's cross rule) | `dlmf_3_11_25` (lower part, `1 ≤ q < p`, nonvanishing Hankel determinants of the partial sums), `dlmf_3_11_25_upper` (upper part via duality, normal table); ε-table form `wynn_cross_rule` (from the rhombus rule) | |
| "initializing the preceding column by `[n/−1] = ∞`", "initializing `[−1/n] = 0`" | `dlmf_3_11_25_border` (`W` term absent), `dlmf_3_11_25_upper_border` (`N = 0`); `wynn_cross_rule_border`, `inv_sub_inv_inv` | |
| "For the recursive computation of `[n+k/k]_f` by Wynn's epsilon algorithm, see (3.9.11)" | `pade_eq_shanks` (Shanks: `[(n+k)/k]_f = t_{n,2k}`, by Cramer's rule on the bordered Hankel matrices, `det_bordMat_sub`, `fwdDiff_psum`), `pade_eq_wynnEps` (`= ε_{2k}^{(n)}`, with `dlmf_3_9_11`) | `Matrix.exists_mulVec_eq_zero_iff`, `Matrix.det_updateRow_add` |
| 3.11.26 | `dlmf_3_11_26` (`laplace`, §1.14(iii)) | |
| "approximate `F` by a rational function `R` (vanishing at infinity) and then approximate `f` by `r = ℒ⁻¹R`" | `dlmf_3_11_iv_laplace` (`R = ∑ Aᵢ/(s − aᵢ)^{mᵢ+1}`, `r = ∑ Aᵢ t^{mᵢ}e^{aᵢt}/mᵢ!`) | `laplace_pow_mul_cexp` (§1.14) |
| "When `F` has an explicit power-series expansion a possible choice of `R` is a Padé approximation"; Luke (1969b, §16.4), Brezinski (1980), Lorentzen and Waadeland (1992) | Not formalized (prose, references) | |

### §3.11(v) Least Squares Approximations (`Section11LeastSquares.lean`, `Section11DFT.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.11.27, 3.11.28 | `monoBasis`, `lsPoly`, `lsSum` with `w = 1` | |
| "From the equations `∂S/∂a_k = 0` … we derive the normal equations" 3.11.29, 3.11.30 | `momX`, `momF`, `dlmf_3_11_29` (`a` minimizes `S` iff 3.11.29); `dlmf_3_11_v_partial` (`∂S/∂a_k = 2((Xa)_k − F_k)`) | |
| "The matrix is symmetric and positive definite" (`J ≥ n + 1` distinct points) | `dlmf_3_11_29_posDef`, `linIndepOn_mono`; unique least squares polynomial `dlmf_3_11_v_poly_unique` | `Matrix.PosDef.of_dotProduct_mulVec_pos`, `Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero` |
| "the system is ill-conditioned when `n` is large …" | Not formalized (qualitative) | |
| "If `J = n + 1`, then `pₙ(x)` is the Lagrange interpolation polynomial" | `dlmf_3_11_v_lagrange` | `Lagrange.eq_interpolate_of_eval_eq` |
| 3.11.31, 3.11.32 | `lsApprox`, `lsSum`; exact expansion `lsSum_add`, `lsSum_add_single` | |
| 3.11.33–3.11.35, "the matrix is again symmetric" | `gramX`, `gramF`, `dlmf_3_11_33` (minimizer iff normal equations, `w ≥ 0`), `gramX_symm` | |
| 3.11.36, "then the approximation `Φₙ(x)` is determined uniquely" | `LinIndepOn`, `dlmf_3_11_v_unique` (unique minimizing coefficients, `w > 0`), `gramX_posDef` | `Matrix.mulVec_surjective_iff_isUnit` |
| "Then the system (3.11.33) is diagonal" | `dlmf_3_11_v_orthogonal` (`aₖ = Fₖ/Xₖₖ`) | `Matrix.PosDef.diag_pos` |
| "can always be orthogonalized … by the Gram–Schmidt procedure" | `dlmf_3_11_v_gram_schmidt` (triangular `ψₖ = ∑_{ℓ≤k} r_{kℓ}φ_ℓ`, orthogonal, independent), `gramX_lin` | `LDL.lowerInv`, `LDL.diag_eq_lowerInv_conj` |
| Example: `φₖ(x) = e^{ikx}`, `x_j = 2πj/n` | `dftPhi`, `dftNode`, `dftPhi_node` (`φₖ(x_j) = ωₙ^{jk}`) | |
| 3.11.37 | `dlmf_3_11_37`, `geom_omegaN` | `Complex.isPrimitiveRoot_exp`, `geom_sum_eq` |
| 3.11.38, 3.11.39, 3.11.40 | `dftCoeff`, `dlmf_3_11_39` (3.11.39 solves 3.11.38), `dlmf_3_11_39_unique`, `dft_orth_dual` | |
| "the corresponding sum (3.11.32) vanishes" | `dlmf_3_11_v_dft_residual` (with `|·|²`; see errata) | |
| 3.11.41 | `omegaN`, `dlmf_3_11_41` | |
| "requires approximately `n²` multiplications" … "reduced to `nm = n log₂ n` operations" (`n = 2^m`) | `fftL` (radix-2 Cooley–Tukey, instrumented), `dlmf_3_11_v_fft` (= `dftList`, 3.11.41), `dlmf_3_11_v_fft_ops` (`½nm` multiplications, `nm` additions), `dlmf_3_11_v_fft_fewer` (`nm < n²`), `dft_split` | |
| 3.11.42 | `dlmf_3_11_42` (`n = 2N`, `k ∈ ℤ`), `omegaN_two_mul_sq`, `omegaN_two_mul_pow_half` | |
| Factorization of `Ω` into `m` sparse matrices; "If `n` is not a power of 2, then modifications are possible"; Cooley and Tukey (1965), Van Loan (1992), Gautschi (1997a), Björck (1996) | Not formalized (the factorization is the matrix form of `fftL`; references) | |

### §3.11(vi) Splines (`Section11Splines.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| "on each subinterval `[x_k, x_{k+1}]` … a low-degree polynomial is defined with coefficients determined by, for example, values `f_k` and `f′_k`" | Hermite interpolation of order `r` (degree `≤ 2r + 1`): `hermite_exists`, `hermite_unique`, `hermite_zero` | `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative`, `LinearMap.injective_iff_surjective` |
| "The set of all the polynomials defines a function, the spline, on `[a, b]`" | `splineFn` (`P₀` plus truncated jumps `cutPoly`), `splineFn_eq_piece` | |
| "By taking more derivatives into account, the smoothness of the spline will increase" | `splineFn_contDiff` (pieces agreeing to order `r` give `C^r`), `cutPoly_contDiff`; `dlmf_3_11_vi_hermite_spline` (order-`r` Hermite spline is `C^r`), `dlmf_3_11_vi_cubic` (`f_k, f′_k`: cubic `C¹` spline) | `hasDerivAt_of_hasDerivAt_of_ne'`, `contDiff_succ_iff_deriv` |
| §24.17(ii) splines based on Bernoulli and Euler polynomials | Not formalized (cross-reference) | |
| Comparison with Lagrange interpolation (§3.3(i)); multivariate splines; de Boor (2001), Chui (1988), Schumaker (1981) | Not formalized (prose, references) | |
| Cubic Bézier curve: endpoints `(x₀, y₀)`, `(x₃, y₃)`, control points `(x₁, y₁)`, `(x₂, y₂)` | `bezier3`, `bezier3_zero`, `bezier3_one`, Bernstein form `bezier3_bernstein` | `bernsteinPolynomial` |
| "The slope of the curve at `(x₀, y₀)` is tangent to the line between `(x₀, y₀)` and `(x₁, y₁)`; similarly …" | `dlmf_3_11_vi_bezier_tangent` (`B′(0) = 3(P₁ − P₀)`, `B′(1) = 3(P₃ − P₂)`), `bezier3_hasDerivAt` | |
| "described by `x(t)` and `y(t)`, which are cubic polynomials with `t ∈ [0, 1]`" | `dlmf_3_11_vi_bezier_cubic` | |
| "A complete spline results by composing several Bézier curves" | `bezierJoin`, `dlmf_3_11_vi_bezier_join` (continuous when `Q₀ = P₃`; `C¹` when also `Q₁ − Q₀ = P₃ − P₂`) | |
| Typography application; Knuth (1986) | Not formalized (prose, reference) | |

## Section 3.12

### §3.12 Mathematical Constants (`Azurite/DLMF/Chapter3/Section12.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 3.12.1 (`π = 3.14159 26535 89793 23846 …`) | `dlmf_3_12_1` (all 20 decimals; AzFloat enclosure `Encl.pi 96`, `pi96_data` by `decide +kernel`) | |
| 3.12.2 | `dlmf_3_12_2` | `integral_one_div_one_add_sq`, `Real.arctan_one` |
| 3.12.3 (`e = 2.71828 18284 59045 23536 …`, §4.2(ii)) | `dlmf_3_12_3` (all 20 decimals; `e = exp 1`, AzFloat's correctly rounded `ePrecRound 80` rounded down/up via `const_eq_zivLoop`, `e80_data` by `decide +kernel`) | |
| 3.12.4 (`γ = 0.57721 56649 01532 86060 …`, §5.2(ii)) | `dlmf_3_12_4_def` (`γ = lim (Hₙ − ln n)`), `dlmf_3_12_4_partial` (first five decimals, from `euler_bounds`); **20 decimals deferred** until Euler's constant can be computed | `Real.tendsto_harmonic_sub_log` |
| Sloane (2003), Finch (2003) | Not formalized (references) | |

## Chapter 4: Elementary Functions

### §4.2(i) The Logarithm (`Azurite/DLMF/Chapter4/Section2.lean`)

`ln z` is `Complex.log` (`log 0 = 0`), `ph z` is `Complex.arg`; paths are `C¹` maps `γ : ℝ → ℂ` on `[0, 1]`, and `∫₁^z dt/t` along `γ` is `pathLogIntegral γ = ∫₀¹ γ′/γ`.

| Equation | Theorem | Mathlib |
|---|---|---|
| 4.2.1 ("multivalued function of `z` with branch point at `z = 0`") | `exp_pathLogIntegral` (`exp ∫_γ dt/t = z`), `dlmf_4_2_1` (every `ln z + 2kπi` is attained by a path) | `constant_of_has_deriv_right_zero`, `intervalIntegral.integral_hasDerivAt_right` |
| 4.2.2 (path not meeting `(−∞, 0]`) | `dlmf_4_2_2` | `HasDerivAt.clog_real`, `intervalIntegral.integral_eq_sub_of_hasDerivAt` |
| "single-valued analytic function on `ℂ ∖ (−∞, 0]` and real-valued … positive real numbers" | `dlmf_4_2_i_analytic`, `dlmf_4_2_i_real` | `analyticAt_clog`, `Complex.ofReal_log` |
| 4.2.3 | `dlmf_4_2_3` | `Complex.log`, `Complex.mem_slitPlane_iff_arg` |
| "The only zero of `ln z` is at `z = 1`" | `dlmf_4_2_i_zero` (`z ≠ 0`) | |
| 4.2.4, 4.2.5 | `dlmf_4_2_5`, `dlmf_4_2_5_cut` (`ln x = ln |x| + iπ`, `x < 0`) | `Complex.arg_ofReal_of_neg` |
| 4.2.6 | `dlmf_4_2_6` (every path integral is `ln z + 2kπi`) | `Complex.exp_eq_exp_iff_exists_int` |
| "`k` is the excess of the number of times the path … crosses the negative real axis in the positive sense over … the negative sense" | Not formalized (crossing count) | |
| 4.2.7 (closed definition, `x ± i0`) | `dlmf_4_2_7` (one-sided limits from the upper/lower half-planes) | `Complex.continuousWithinAt_log_of_re_neg_of_im_zero`, `Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero` |
| "`ln z` is two-valued on the cut, and discontinuous across the cut" | `dlmf_4_2_i_discontinuous` | |
| Regions of validity of 4.8.7, 4.2.37; §§4.23, 4.24, 4.37, 4.38 | Not formalized here (later sections) | |

### §4.2(ii) Logarithms to a General Base (`Azurite/DLMF/Chapter4/Section2Base.lean`)

`log_a z = ln z / ln a` is `logBase` (principal `ln = Complex.log`).  The constants are certified with AzFloat's correctly rounded `ePrecRound`, `log10EPrecRound`, `ln10PrecRound` at 80 bits, rounded down and up, each identified with Ziv's loop with fuel (`const_eq_zivLoop` in `AzFloat/Equiv/ConstantKernel.lean`, via `zivLoop_eq_of_ne_nan_threshold`) and evaluated by `decide +kernel`.

| Equation | Theorem | Mathlib |
|---|---|---|
| 4.2.8 (`a, b ≠ 0, 1`) | `logBase`, `dlmf_4_2_8`; positive reals: `logBase_ofReal` | `Real.logb` |
| 4.2.9 | `dlmf_4_2_9` | |
| 4.2.10 | `dlmf_4_2_10` | |
| 4.2.11 (`e = 2.71828 18284 59045 23536 …`) | `dlmf_4_2_11` (= `dlmf_3_12_3`, all 20 decimals) | |
| 4.2.12 ("the unique positive number … such that `ln e = 1`") | `dlmf_4_2_12` | `Real.log_exp`, `Real.exp_log` |
| 4.2.13 | `dlmf_4_2_13` | `integral_one_div_of_pos` |
| 4.2.14 | `dlmf_4_2_14` | |
| 4.2.15 | `dlmf_4_2_15` | |
| 4.2.16 | `dlmf_4_2_16` | |
| 4.2.17 (`log₁₀ e = 0.43429 44819 03251 82765 …`) | `dlmf_4_2_17` (all 20 decimals; `log10E80_data`) | |
| 4.2.18 (`ln 10 = 2.30258 50929 94045 68401 …`) | `dlmf_4_2_18` (all 20 decimals; `ln1080_data`) | |
| "Napierian or hyperbolic logarithm", "common or Briggs logarithm" | Not formalized (terminology) | |

### §4.2(iii) The Exponential Function (`Azurite/DLMF/Chapter4/Section2Exp.lean`)

`exp` is `Complex.exp`; the general logarithm `Ln ζ` is `genLogSet ζ = {ln ζ + 2kπi}`, equal to the set of path integrals `∫₁^ζ dt/t` of §4.2(i) (`genLogSet_eq_pathIntegrals`).

| Equation | Theorem | Mathlib |
|---|---|---|
| 4.2.19 | `dlmf_4_2_19` | `NormedSpace.expSeries_div_hasSum_exp`, `Complex.exp_eq_exp_ℂ` |
| "an entire function of `z`, with no real or complex zeros" | `dlmf_4_2_iii_entire`, `dlmf_4_2_iii_ne_zero` | `Complex.differentiable_exp`, `Complex.exp_ne_zero` |
| "It has period `2πi`", 4.2.20 | `dlmf_4_2_20`, `dlmf_4_2_iii_periodic` (the periods are exactly `2kπi`) | `Complex.exp_periodic`, `Complex.exp_eq_one_iff` |
| 4.2.21 | `dlmf_4_2_21` | `Complex.exp_neg` |
| 4.2.22 | `dlmf_4_2_22` | `Complex.norm_exp` |
| 4.2.23 (general value of the phase) | `dlmf_4_2_23` (`exp z = |exp z| e^{iθ} ⟺ θ = Im z + 2kπ`), `dlmf_4_2_23_arg` | `Complex.exp_eq_exp_iff_exists_int` |
| 4.2.24 | `dlmf_4_2_24` | `Complex.exp_mul_I` |
| 4.2.25 (`ζ ≠ 0`) | `dlmf_4_2_25` (`genLogSet`) | |
| Hobson (1928, pp. 289–296) | Not formalized (reference) | |

### §4.2(iv) Powers (`Azurite/DLMF/Chapter4/Section2Pow.lean`)

The principal value is `Complex.cpow`; the general value is `genPowSet z a = {exp(a w) : w ∈ Ln z}`; the principal value under the closed definition (`ph z ∈ [−π, π]`, two values on the cut) is `closedPowSet z a`.

| Equation | Theorem | Mathlib |
|---|---|---|
| 4.2.26 (`z ≠ 0`) | `genPowSet`, `mem_genPowSet_iff`, `genPowSet_eq` | |
| "`z⁰ = 1`", 4.2.27 | `dlmf_4_2_26_zero`, `dlmf_4_2_27` (`a = n`, and `a = −n`), `genPowSet_int` | `Complex.cpow_natCast` |
| "In all other cases, `z^a` is a multivalued function with branch point at `z = 0`" | `dlmf_4_2_iv_multivalued` (single-valued iff `a ∈ ℤ`) | `Complex.exp_eq_one_iff` |
| 4.2.28 | `dlmf_4_2_28` | `Complex.cpow_def_of_ne_zero` |
| "analytic … on `ℂ ∖ (−∞, 0]`, and is two-valued and discontinuous on the cut … unless `a ∈ ℤ`" | `dlmf_4_2_iv_analytic`, `closedPowSet`, `cpow_mem_closedPowSet`, `dlmf_4_2_iv_closed_cut` (the two values `exp(a(ln|x| ± iπ))`, equal iff `a ∈ ℤ`), `dlmf_4_2_iv_discontinuous`, `dlmf_4_2_iv_continuous_int` | `AnalyticAt.cpow` |
| 4.2.29, 4.2.30 ("unrestricted in the general case") | `dlmf_4_2_29_30` (every value `exp(a(ln|z| + iθ))`, `z = |z|e^{iθ}`), principal: `dlmf_4_2_29`, `dlmf_4_2_30` | `Complex.norm_cpow_of_ne_zero` |
| 4.2.31 | `dlmf_4_2_31` | |
| 4.2.32 | `dlmf_4_2_32` | |
| 4.2.33 | `dlmf_4_2_33` | |
| 4.2.34 | `dlmf_4_2_34` | `NormedSpace.expSeries_div_hasSum_exp`, `Real.exp_eq_exp_ℝ` |
| 4.2.35 (`a ≠ 0`, `w ≠ 0`) | `dlmf_4_2_35` (also `z ≠ 0`, where `z^a` is defined) | |
| 4.2.36 | `dlmf_4_2_36` (closed principal value, `−π ≤ Im ≤ π`); `dlmf_4_2_36_open` (Mathlib's principal value, `−π < Im ≤ π`) | `Complex.log_exp` |
| 4.2.37, "without the closed definition the `≥` and `≤` signs would have to be replaced by `>` and `<`" | `dlmf_4_2_37` (closed), `dlmf_4_2_37_open` (strict signs), `dlmf_4_2_37_open_fails` (`z = ∓i`) | `Complex.abs_arg_le_pi_div_two_iff` |
| "Unless indicated otherwise … principal value"; Levinson and Redheffer (1970) | Not formalized (convention, reference) | |

### §4.3 Graphics (`Azurite/DLMF/Chapter4/Section3.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| Figure 4.3.1 ("Parallel tangent lines at `(1,0)` and `(0,1)`", "mirror symmetry across the line `y = x`") | `dlmf_4_3_F1_tangents`, `dlmf_4_3_F1_mirror` | `Real.hasDerivAt_log`, `Real.hasDerivAt_exp` |
| Figure 4.3.2 (strip `−π < Im z < π` onto the cut `w`-plane, `w = e^z`, `z = ln w`) | `logStrip`, `dlmf_4_3_F2_bijOn`, `dlmf_4_3_F2_inverse`, `dlmf_4_3_F2_conformal` | `Complex.log_exp`, `Complex.hasDerivAt_log` |
| "Lines parallel to the real axis … map onto rays", "lines parallel to the imaginary axis … onto circles centered at the origin" | `dlmf_4_3_F2_rays`, `dlmf_4_3_F2_circles` | |
| Labelled points `A`–`F`, `C̄`, `D̄`, `Ē` (`r` real) | `dlmf_4_3_F2_points`; the edges `Im z = ±π` and the sides `x ± i0` of the cut: `dlmf_4_3_F2_edges` | |
| Figure 4.3.3 ("There is a branch cut along the negative real axis") | `dlmf_4_2_i_discontinuous` (§4.2(i)) | |
| Figure 4.3.4 (height `|e^{x+iy}|`, color the phase) | `dlmf_4_2_22`, `dlmf_4_2_23` (§4.2(iii)) | |

### §4.4 Special Values and Limits (`Azurite/DLMF/Chapter4/Section4.lean`)

Powers `e^w` are principal values `(Real.exp 1 : ℂ) ^ w` (`epow`, from 4.2.32).

| Equation | Theorem | Mathlib |
|---|---|---|
| 4.4.1 | `dlmf_4_4_1` | `Complex.log_one` |
| 4.4.2 (`ln(−1 ± i0)`) | `dlmf_4_4_2` (one-sided limits, from 4.2.7) | |
| 4.4.3 | `dlmf_4_4_3` | `Complex.log_I`, `Complex.log_neg_I` |
| 4.4.4 | `dlmf_4_4_4` | `Complex.cpow_zero` |
| 4.4.5 | `dlmf_4_4_5` | `Complex.exp_pi_mul_I` |
| 4.4.6 | `dlmf_4_4_6` | |
| 4.4.7 | `dlmf_4_4_7` | `Complex.exp_int_mul_two_pi_mul_I` |
| 4.4.8 | `dlmf_4_4_8`, `epow_pm` | `Real.cos_pi_div_three`, `Real.sin_pi_div_three` |
| 4.4.9 | `dlmf_4_4_9` | |
| 4.4.10 | `dlmf_4_4_10` | `Real.cos_pi_div_four`, `Real.sin_pi_div_four` |
| 4.4.11 | `dlmf_4_4_11` | |
| 4.4.12 | `dlmf_4_4_12` | |
| 4.4.13 (`Re a > 0`, `a ∈ ℂ`) | `dlmf_4_4_13` | `isLittleO_log_rpow_atTop` |
| 4.4.14 (`Re a > 0`, `x → 0+`) | `dlmf_4_4_14` | `tendsto_log_mul_rpow_nhdsGT_zero` |
| 4.4.15 | `dlmf_4_4_15` | `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` |
| 4.4.16 (`|ph z| ≤ ½π − δ`, `δ ∈ (0, ½π]`) | `dlmf_4_4_16` (`sectorAtInf δ`, `re_ge_of_sector`: `Re z ≥ |z| sin δ`) | `tendsto_norm_cobounded_atTop` |
| 4.4.17 | `dlmf_4_4_17` | `Complex.tendsto_one_add_div_pow_exp` |
| 4.4.18 | `dlmf_4_4_18` | `Real.tendsto_one_add_div_pow_exp` |
| 4.4.19 (`γ = 0.57721 56649 01532 86060 …`) | `dlmf_4_4_19` (limit, and the first five decimals); **20 decimals deferred** (as for 3.12.4) | `Real.tendsto_harmonic_sub_log` |
