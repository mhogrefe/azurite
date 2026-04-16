# Azurite

A Lean 4 library for efficient, formally verified mathematical computation.

Azurite provides array-backed data structures for polynomials, vectors, and matrices with proven equivalences to their Mathlib counterparts. Every computable operation has a corresponding proof that it agrees with the abstract Mathlib definition.

## Module Map

### Core Data Structures

| Module | Description |
|--------|-------------|
| `AzNat/` | Computable multi-limb natural numbers over `Array UInt64`. |
| `AzInt/` | Computable integers as a sign-magnitude pair `(sign : Bool, abs : AzNat)` with a canonical zero invariant (`abs = 0 → sign = true`). Includes conversions to/from all Lean fixed-width int/uint types and `AzNat`, comparison against `UInt64`/`Int64`/`AzNat`, a custom `compare` with derived `Ord`/`LE`/`LT`/`Max`/`Min`, parity tests, `pow2`, `lowMask`, `isPowerOfTwo`, bit-size, trailing-zeros, parsing, and `toString`. |
| `AzPolynomial/` | Dense univariate polynomials over a semiring `R`, stored as `Array R` with a trailing-nonzero invariant. Includes add, mul (basecase + Karatsuba), negation, scalar multiplication, multiplication by `X^n` (`mulXPow`), truncation (`truncate`, BPR Notation 1.16), derivative, evaluation, composition (Horner), exponentiation (binary), quotient/remainder (Euclidean division), signed pseudo-remainder (`pRem`, works over any `CommRing`), root bounds, parsing, and `toString`. |
| `AzMvPolynomial/` | Sparse multivariate polynomials over `R` in variables `σ`, stored as a sorted array of monomials (descending by monic part). Supports multiple monomial orderings (lex, deglex, degrevlex). Includes add, mul (naive + optimized), negation, scalar multiplication, partial derivative, evaluation (`eval`, plus generic `eval₂`/`aeval` into any commutative semiring or `R`-algebra), exact division, monomial exponentiation, rename, map, merge-sorted operations, `bind₁`/`bind₂`/`join₂` substitution, and `finSuccEquiv` (forward direction: `AzMvPolynomial (Fin (n+1)) R → AzPolynomial (AzMvPolynomial (Fin n) R)`). |
| `AzPolynomialQ/` | Rational univariate polynomials with a shared denominator: stores `numerators : Array ℤ` and `denom : ℕ` in canonical (GCD-reduced) form. Enables exact arithmetic without per-coefficient rational normalization, fast pointwise negation, and integer-level `Monic` property evaluation. |
| `AzVector/` | Fixed-length vectors wrapping Lean's `Vector R n`. Includes addition, negation, subtraction, scalar multiplication, dot product, cross product, and basis vectors. |
| `AzMatrix/` | Fixed-size `m × n` matrices wrapping `Vector (Vector R n) m`. Includes addition, negation, subtraction, scalar multiplication, matrix multiplication, matrix-vector multiplication, transpose, and row/column access. |
| `AzFormula/` | Computable first-order formulas over `AzFieldAtom` (field atoms using `AzMvPolynomial`). Provides computable free-variable computation, bound-variable computation, sentence checking, formula constructors, variable renaming, negation normal form (`toNNF`), prenex normal form conversion (`toPrenex`), and noncomputable realization. Generic `AtomVars`, `AtomRename`, `AtomRealization` typeclasses. Modular simplification passes (`elimDoubleNeg`, `elimVacuousQuantifiers`). |

### Equivalence Proofs (`Equiv/` subdirectories)

Each core data structure has an `Equiv/` subdirectory containing proofs that Azurite's computable operations agree with Mathlib's abstract definitions.

#### AzNat ↔ Nat

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Computable equivalence `equivNat : AzNat ≃ Nat` via `toNat`/`ofNat`, including base invariant preservation. |
| `Equiv/Compare` | `compare_eq_compare_toNat`: custom limb-by-limb `compare` logic mapping equivalently to `Ord.compare` on `Nat`, providing the formally verified `LinearOrder AzNat` instance with `≤` and `<`. |

#### AzInt ↔ Int

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection `AzInt ≃ Int` via `toInt`/`ofInt`, including the canonical-zero invariant round-trip. |
| `Equiv/Compare` | `compare_eq_lt_iff_toInt_lt` and friends: custom sign-magnitude `compare` matches `Ord.compare` on `Int`, providing the `LinearOrder AzInt` instance. |
| `Equiv/Conversion` | `toInt_toAzInt` / `toInt_toAzInt = toNat` for every fixed-width `UInt*`/`Int*`/`USize`/`ISize` and `AzNat`, and the reverse `toInt_toUInt*` / `toInt_toInt*` direction. |
| `Equiv/Parity` | `isEven_iff`/`isOdd_iff` agree with `Even`/`Odd` on `Int`. |
| `Equiv/Pow2` | `toInt_pow2 k = 2 ^ k`, `pow2_eq_ofInt`, and `isPowerOfTwo_iff`. |
| `Equiv/LowMask` | `toInt_lowMask k = 2 ^ k - 1` and `lowMask_eq_ofInt`. |
| `Equiv/Size` | `z.size = BPR.Int.size z.toInt` (bit-size agrees with the BPR Chapter 8 notion). |
| `Equiv/TrailingZeros` | `trailingZeros z = some (padicValInt 2 z.toInt)` for nonzero `z`, and `trailingZeros 0 = none`. |

#### AzPolynomial ↔ Polynomial R

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection `AzPolynomial R ≃ Polynomial R` via `toPoly`/`ofPoly`; degree, natDegree, coeff, leadingCoeff, nextCoeff, and monic preservation. |
| `Equiv/Add` | `toPoly (p + q) = toPoly p + toPoly q` |
| `Equiv/Sub` | `toPoly (p - q) = toPoly p - toPoly q` |
| `Equiv/Neg` | `toPoly (-p) = -(toPoly p)` |
| `Equiv/Mul` | `toPoly (p * q) = toPoly p * toPoly q` (basecase) |
| `Equiv/MulXPow` | `toPoly (mulXPow n p) = toPoly p * X ^ n` |
| `Equiv/Karatsuba` | `mulKaratsuba p q = mulBasecase p q` (Karatsuba agrees with basecase, hence with Mathlib) |
| `Equiv/SMul` | `toPoly (c • p) = c • toPoly p` |
| `Equiv/Monomial` | `toPoly (monomial n c) = Polynomial.monomial n c` |
| `Equiv/Map` | `toPoly (map f p) = Polynomial.map f (toPoly p)` |
| `Equiv/Eval` | `eval x p = Polynomial.eval x (toPoly p)` and `evalSpecial p b c = c^natDeg · (toPoly p).eval(b·c⁻¹)` (BPR Algorithm 8.8) |
| `Equiv/QuoRem` | `toPoly (quo P Q) = toPoly P / toPoly Q`, `toPoly (rem P Q) = toPoly P % toPoly Q`, and `degree(rem) < degree(Q)` |
| `Equiv/PRem` | `(toPoly (pRem P Q)).map (algebraMap D K) = BPR.PRem K (toPoly P) (toPoly Q)` for `D` a domain with fraction field `K` (matches BPR §1.3 signed pseudo-remainder) |
| `Equiv/RootBound` | Cauchy root bound correctness: all roots lie within `(-rootBound, rootBound)` |
| `Equiv/Algebra` | Ring homomorphism and algebra structure preservation |
| `Equiv/Comp` | `toPoly (comp p q) = (toPoly p).comp (toPoly q)` |
| `Equiv/Derivative` | `toPoly (derivative p) = Polynomial.derivative (toPoly p)` |
| `Equiv/Pow` | `toPoly (p.pow n) = toPoly p ^ n` and `(ofPoly p).pow n = ofPoly (p ^ n)` |
| `Equiv/Translate` | `toPoly (translate p c) = (toPoly p).comp (X - C c)` and root translation: root at `r` ↔ root of `P` at `r-c` (BPR Algorithm 8.9) |
| `Equiv/Truncate` | `toPoly (truncate i p) = BPR.truncate i (toPoly p)` and coefficient characterization `(truncate i p).coeff j = if j ≤ i then p.coeff j else 0` (BPR Notation 1.16) |
| `Equiv/SpecialTranslate` | `eval z (specialTranslate p b c) = evalSpecial p (c·z−b) c`, field identity `= c^deg · eval(z−b/c) P`, root translation (field and via ring hom `f : R →+* K`) (BPR Algorithm 8.10) |

#### AzMvPolynomial ↔ MvPolynomial σ R

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection `AzMvPolynomial σ R ≃ MvPolynomial σ R` via `toMvPoly`/`ofMvPoly` |
| `Equiv/Add` | `toMvPoly (p + q) = toMvPoly p + toMvPoly q` |
| `Equiv/Sub` | `toMvPoly (p - q) = toMvPoly p - toMvPoly q` |
| `Equiv/Neg` | `toMvPoly (-p) = -(toMvPoly p)` |
| `Equiv/Mul` | `toMvPoly (p * q) = toMvPoly p * toMvPoly q` |
| `Equiv/MulNaive` | Naive multiplication correctness |
| `Equiv/SMul` | Scalar multiplication preservation |
| `Equiv/Cast` | Coefficient casting preservation |
| `Equiv/Map` | Ring homomorphism map preservation |
| `Equiv/Eval` | Evaluation preservation |
| `Equiv/Eval2` | Generic `eval₂`/`aeval` preservation across the bridge |
| `Equiv/Rename` | Variable renaming preservation |
| `Equiv/Derivative` | `toMvPoly (pderivGeneral v p) = MvPolynomial.pderiv v (toMvPoly p)` |
| `Equiv/ExactDiv` | Exact division correctness |
| `Equiv/MergeSorted` | Merge-sorted operation correctness |
| `Equiv/MonomialOrder` | Monomial ordering equivalences |
| `Equiv/Pow` | `toMvPoly (p.pow k) = toMvPoly p ^ k` |
| `Equiv/Bind1` | `toMvPoly (p.bind₁ f) = bind₁ (toMvPoly ∘ f) (toMvPoly p)` (variable substitution) |
| `Equiv/Bind2` | `toMvPoly (p.bind₂ f) = bind₂ f (toMvPoly p)` (coefficient substitution) |
| `Equiv/Join2` | `toMvPoly (p.join₂) = bind₂ toMvPolyRingHom (toMvPoly p)` (coefficient flattening) |
| `Equiv/Vars` | `(toMvPoly p).vars = p.vars` (variable set) |
| `Equiv/ToAzPolynomial` | `toPoly (p.toAzPolynomial) = eval₂ C X (toMvPoly p)` (univariate projection for `[Unique σ]`) |
| `Equiv/ToAzPolynomialAt` | `toPoly (p.toAzPolynomialAt hv) = eval₂ C X (toMvPoly p)` (univariate projection at variable `v`, for arbitrary `σ` with `p.vars ⊆ {v}`) |
| `Equiv/OfAzPolynomial` | `toMvPoly (ofAzPolynomial p) = (Polynomial.toMvPolynomial) (toPoly p)` (univariate inclusion) |
| `Equiv/Algebra` | Algebra structure preservation (CommSemiring, CommRing, IsDomain) |
| `Equiv/AlgebraOfAlgebra` | Iterated-algebra instances: `AzMvPolynomial n A ord` as an `R`-algebra whenever `A` is an `R`-algebra |
| `Equiv/MapHom` | Bundled forms of `map`: `mapRingHom`, `mapAlgHom`, `mapAlgEquiv` |
| `Equiv/RenameHom` | Bundled `R`-algebra-hom form of `rename` |
| `Equiv/Bind1Hom` | Bundled `R`-algebra-hom form of `bind₁` |
| `Equiv/Bind2Hom` | Bundled ring-hom form of `bind₂` |
| `Equiv/AevalHom` | Bundled `R`-algebra-hom form of `aeval` (`AzMvPolynomial n R ord →ₐ[R] S`) |
| `Equiv/ConstantCoeff` | `AzMvPolynomial.constantCoeff : AzMvPolynomial n R ord →+* R` extracting the constant term (computable via `eval₂` on the sparse rep) |
| `Equiv/FinZeroAlgEquiv` | `AzMvPolynomial 0 R ord ≃ₐ[R] R` (zero-variable elimination) |
| `Equiv/FinOneAlgEquiv` | `AzMvPolynomial 1 R ord ≃ₐ[R] AzPolynomial R` (one-variable ↔ univariate) |
| `Equiv/FinSuccEquiv` | `AzMvPolynomial (n+1) R ord ≃ₐ[R] AzPolynomial (AzMvPolynomial n R ord)` (peel off a variable) |
| `Equiv/OptionEquivRight` | Reindexing equivalence splitting off the last variable |
| `Equiv/SumAlgEquiv` | `sumRingEquiv`/`sumAlgEquiv`: `AzMvPolynomial (m+n) R ord ≃ AzMvPolynomial m (AzMvPolynomial n R ord) ord` (split variable block) |
| `Equiv/CommAlgEquiv` | Swap inner/outer coefficient rings: `AzMvPolynomial n (AzMvPolynomial m R ord) ord ≃+* AzMvPolynomial m (AzMvPolynomial n R ord) ord` |

#### AzVector ↔ (Fin n → R)

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection via `toFn`/`ofFn` |
| `Equiv/Add` | `toFn (v + w) i = toFn v i + toFn w i` |
| `Equiv/Sub` | Subtraction preservation |
| `Equiv/Neg` | Negation preservation |
| `Equiv/SMul` | Scalar multiplication preservation |
| `Equiv/Zero` | Zero vector preservation |
| `Equiv/Dot` | Dot product preservation |
| `Equiv/Cross` | Cross product preservation |
| `Equiv/Basis` | Standard basis vector preservation |
| `Equiv/Algebra` | Module/algebra structure preservation |

#### AzMatrix ↔ Matrix (Fin m) (Fin n) R

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection via `toFn`/`ofFn` |
| `Equiv/Add` | Entry-wise addition preservation |
| `Equiv/Sub` | Entry-wise subtraction preservation |
| `Equiv/Neg` | Entry-wise negation preservation |
| `Equiv/SMul` | Scalar multiplication preservation |
| `Equiv/Zero` | Zero matrix preservation |
| `Equiv/Mul` | Matrix multiplication preservation |
| `Equiv/MulVec` | Matrix-vector multiplication preservation |
| `Equiv/RowCol` | Row/column access preservation |
| `Equiv/Transpose` | Transpose preservation |
| `Equiv/Basis` | Standard basis matrix preservation |
| `Equiv/Algebra` | Algebra structure preservation |
| `Equiv/Pow` | `toMat (A.pow k) = toMat A ^ k` and `(ofFn f).pow k = ofFn (f ^ k)` |

#### AzFormula (AzFieldAtom) ↔ Formula (FieldAtom)

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | `mapAtom` functor laws (`mapAtom_id`, `mapAtom_comp`), formula conversion round-trips (`fieldFormulaToAzFormula ∘ azFormulaToFieldFormula = id` and vice versa), `azRealization = realization ∘ azFormulaToFieldFormula`. |
| `Equiv/FreeVars` | `freeVarsOf Φ = freeVars (Φ.toFieldFormula)` — computable free vars agree with noncomputable for both atom types. |
| `Equiv/BoundVars` | `boundVarsOf Φ = boundVars (Φ.toFieldFormula)` — computable bound vars agree with noncomputable for both atom types. |
| `Equiv/Simplify` | `elimDoubleNeg` and `elimVacuousQuantifiers` preserve C-realization. |
| `Equiv/Prenex` | Generic `AtomRealization` typeclass and `gRealization` semantics. `eliminateImplies`, `toNNF`, rename-by-equiv, and `toPrenexNNF` all preserve `gRealization`. `AtomRealization` instance for `AzFieldAtom` (interpret, neg, rename, invariance). Bridge `gRealization = azRealization`. Variable freshness (`freshIndexedVars_fresh/nodup`, `allVarsOf_rename_embed_bound`). Commutation of `azFormulaToFieldFormula` with rename. **Syntactic correctness: `IsPrenex (toPrenex Φ)`** — the pipeline always produces a formula in prenex normal form (`toPrenexNNF_properties` combines quantifier depth preservation, fresh variable consumption, and prenex output in one induction). **Semantic correctness: `azRealization (toPrenex Φ) = (· ∘ embed) ⁻¹' azRealization Φ`** — the full pipeline (NNF → embed → prenex) is semantics-preserving. Auxiliary: `rename_isNNF`, `rename_freshVarsNeeded`, `mergePrenex_fst_quantifierDepth`. Zero `sorry`. |
| `Prenex` | Computable prenex conversion: `mergePrenex`, `toPrenexNNF`, `toPrenex` pipeline for `IndexedVar n` formulas. `freshVarsNeeded` metric for fresh variable allocation. |

#### AzPolynomialQ ↔ AzPolynomial ℚ

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection `AzPolynomialQ ≃ AzPolynomial ℚ`; coefficient, degree, and normalization preservation |
| `Equiv/Parse` | Parsing equivalence |
| `Equiv/ToString` | String conversion equivalence |
| `Equiv/Eval` | `eval p x = Polynomial.eval x (toPoly p)` — BPR special evaluation on integer numerators ↔ Mathlib polynomial evaluation |
| `Equiv/Neg` | `toPoly (-p) = - p.toPoly` and `toAzPolynomial (-p) = - p.toAzPolynomial` |

### Generic Algorithms

| Module | Description |
|--------|-------------|
| `Algorithm/FastPow` | Right-to-left binary exponentiation (exponentiation by squaring) for any `Monoid`. Computes `a ^ n` in O(log n) multiplications. Proven equivalent to `HPow.hPow` (Mathlib's `^`). |

### Utility Modules

| Module | Description |
|--------|-------------|
| `UInt64/` | Helpers on Lean's built-in `UInt64` type. `addWithCarry` (64-bit add with carry-in/out), `subWithBorrow` (64-bit sub with borrow-in/out), `wideMul` (full 128-bit product of two `UInt64`s, returned as a `(hi, lo)` pair), `isPowerOfTwo` (bit-trick power-of-two test), `testBit` (returns `false` for `i ≥ 64`), `setBit`/`clearBit` (identity for `i ≥ 64`), `splitInHalf`/`joinHalves` (convert between `UInt64` and a pair of `UInt32` halves). `Equiv/Basic` provides `UInt64.eq_of_toNat_eq`; the remaining `Equiv/*` files prove the `toNat` semantics of each helper, including `toNat_joinHalves` and the two-sided inverse properties of `splitInHalf`/`joinHalves`. |
| `Nat/NormalizedCompare` | `normalizedCompare`: O(n) comparison of naturals by their normalized bit representations. Proven equivalent to comparing `x / 2^size(x)` vs `y / 2^size(y)`. |
| `Rat/LogBase2` | `floorLogBase2Abs` and `ceilingLogBase2Abs` for rationals, proven equal to `⌊log₂ |q|⌋` and `⌈log₂ |q|⌉`. |
| `Rat/Compare` | `Azurite.Rat.cmp`: a fast multi-stage rational comparison (sign → magnitude bracket → num/den comparison → log₂ comparison → cross-multiply). Proven equivalent to standard `compare` on `ℚ`. |
| `Random/` | Random generators for `Nat`, `Int`, `Rat`, `Bool`, `AzPolynomial`, pairs, and geometric distributions. Used for testing and benchmarks. |
| `Benchmark/` | Performance benchmarks for polynomial multiplication (basecase vs Karatsuba at various sizes) and rational comparison. Uses a C FFI nanosecond timer. |

### Formalized Textbook Content

| Module | Content |
|--------|---------|
| `BasuPollackRoy/Chapter1/Section1_1` | Algebraically closed fields, zero sets (`Zer`), algebraic/constructible sets, first-order formulas in the language of fields, quantifier-free and prenex normal forms, realization, prenex normal form theorem. Exercises 1.1–1.3. |
| `BasuPollackRoy/Chapter1/Section1_2` | Euclidean division, GCD/LCM (definitions and propositions), coprimality, signed remainder sequences. Proposition 1.5, Corollary 1.6, Exercises 1.5–1.7, Proposition 1.8. |
| `BasuPollackRoy/Chapter1/Section1_3` | Projection theorem for constructible sets (in progress). Specialization `P_y(X)` of a polynomial in `C[Y₁,…,Y_k,X]` at `y ∈ C^k` (`specialize`, `eval_specialize`). Projection `Formula.proj` and fiber `Formula.fiber` of a formula-defined set in `C^{k+1}`. Signed pseudo-remainder `PRem(P, Q)` with scaling exponent `pRemExp`. Truncation `Tru_i(Q) = b_i X^i + ⋯ + b_0` (Notation 1.16) with coefficient characterization. |
| `BasuPollackRoy/Chapter2/Section2_1` | Ordered fields (Notation 2.3: sign, absolute value), ordered field examples (ℚ, ℝ), Exercise 2.3 (ℂ not orderable), Proposition 2.4 (sign preservation for large inputs), infinitesimal/unbounded elements over an ordered field extension. Cones (Def 2.6, `IsCone`/`IsProperCone`), Proposition 2.6, Lemma 2.9 (cone extension), Proposition 2.8 (Zorn-based extension to total proper cone), Theorem 2.7 (characterizations of real fields). **Notation 2.18**: `Ri R = R[T]/(T²+1)`, imaginary unit `Ri.i`, conjugation `Ri.conj`, `normSq`/`normSqR`, modulus `|z| = √(a²+b²)`. |
| `BasuPollackRoy/Chapter2/OrderZeroPlus` | **Notation 2.5**: The 0₊ order on F[ε]. `LinearOrder` and `IsStrictOrderedRing` on `F[X]` via trailing coefficient positivity. ε notation, proof that ε is infinitesimal (0 < ε < C a for positive a), `C` is strictly monotone. |
| `BasuPollackRoy/Chapter2/Theorem_2_11*` | **Theorem 2.11**: For an ordered field R, TFAE: (a) R is real closed, (b) R[i] is algebraically closed, (c) R has the intermediate value property, (d) R is real with no non-trivial real algebraic extension. Split across files `Theorem_2_11_a_b`, `_b_c`, `_b_d`, `_c_a`, `_d_a`; combined TFAE in `Theorem_2_11`. Key helpers: `conj_pair_dvd_map`, `quad_of_conj_pair`, `dvd_of_map_dvd_monic`, `irred_degree_eq_two`. |
| `BasuPollackRoy/Chapter2/Proposition_2_19` | **Proposition 2.19**: Over an ordered field R with R[i] algebraically closed, every monic irreducible polynomial is either linear or of the form `(X − c)² + d²` with `d ≠ 0`. Real-closed-field corollary `proposition_2_19_of_isRealClosed`. |
| `BasuPollackRoy/Chapter2/Proposition_2_20` | **Proposition 2.20**: Over an ordered field R with the intermediate value property, if `P ∈ R[X]` does not vanish on `(a, b)` then `P` has constant sign on `(a, b)` (everywhere positive or everywhere negative). Real-closed-field corollary `proposition_2_20_of_isRealClosed`. |
| `BasuPollackRoy/Chapter8/Section8_1` | Complexity structures (D₀–D₇), bitsize of integers and rationals, bitsize bounds for sums and products, monomial counting (Lemma 8.6 with `MonicMonomial` bridge), bitsize of polynomial addition/multiplication. Notation 8.7 (Horner polynomials with sum/eval identities), Algorithm 8.7 (polynomial evaluation), Algorithm 8.8 (special evaluation with `horSpecial` sum characterization, field identity, and bitsize bound `τ + iτ' + bit(p+1)`), Algorithm 8.9 (translation), Algorithm 8.10 (special translation). Cross-references to Azurite implementations of Algorithms 8.1–8.10. |

## Known Textbook Errors (BPR)

While formalizing *Algorithms in Real Algebraic Geometry* (Basu, Pollack, Roy), the following mathematical discrepancies were identified and corrected in Azurite:

*   **Lemma 1.10(b) (Signed Remainder Determinant Sequence):** The textbook states the identity $U_i V_{i+1} - V_i U_{i+1} = (-1)^i$. However, the textbook's definition of the cofactor sequence ($U_{i+2} = U_i - Q_{i+1} U_{i+1}$) drops the negation required to compute signed remainders ($P_{i+2} = - P_i + Q_{i+1} P_{i+1}$). When the strictly correct recurrence is used, the sequence determinant evaluates structurally to $1$ unconditionally. Azurite's formalization proves `lemma_1_10_b` equal to `1` and applies the corrected identity in subsequent proofs (e.g., Proposition 1.12).

## Algorithms Implemented

| Algorithm | Source | Module | Complexity |
|-----------|--------|--------|------------|
| Polynomial addition | BPR Alg. 8.1 | `AzPolynomial/Add` | O(max(p,q)) |
| Polynomial multiplication (basecase) | BPR Alg. 8.2 | `AzPolynomial/Mul` | O(p·q) |
| Karatsuba multiplication | — | `AzPolynomial/Karatsuba` | O(n^1.585) |
| Euclidean division | BPR Alg. 8.3 | `AzPolynomial/QuoRem` | O((p−q)·q) |
| Signed pseudo-remainder | BPR §1.3 | `AzPolynomial/PRem` | O((p−q)·q) over any `CommRing` |
| Shift by `X^n` (mul by monic monomial) | — | `AzPolynomial/MulXPow` | O(n + p) |
| Multivariate polynomial addition | BPR Alg. 8.4 | `AzMvPolynomial/Add` | O(s+t) merge |
| Multivariate polynomial multiplication | BPR Alg. 8.5 | `AzMvPolynomial/Mul` | — |
| Exact division of multivariate polynomials | BPR Alg. 8.6 | `AzMvPolynomial/ExactDiv` | — |
| Fast rational comparison | — | `Rat/Compare` | O(1) amortized for many inputs |
| Cauchy root bound | — | `AzPolynomial/RootBound` | O(n) |
| Formal derivative | — | `AzPolynomial/Derivative` | O(n) |
| Multivariate partial derivative | — | `AzMvPolynomial/Derivative` | O(n) per variable |
| Translation P(X-c) | BPR Alg. 8.9 | `AzPolynomial/Translate` | O(p²·deg(q)) via comp |
| Special Translation c^p·P(X-b/c) | BPR Alg. 8.10 | `AzPolynomial/SpecialTranslate` | O(p²) via Horner fold |
| Exponentiation by squaring | — | `Algorithm/FastPow` | O(log n) |

## Building

```bash
lake build        # build the library
lake build benchmark  # build the benchmark executable
```

## Running Benchmarks

```bash
lake env .lake/build/bin/benchmark
```

## Project Structure

```
Azurite.lean          -- Root import file (all library modules)
Examples.lean         -- Usage examples
lakefile.lean         -- Lake build configuration
Azurite/
  Algorithm/            -- Generic algorithms (e.g., fast exponentiation)
  AzNat/              -- Computable multi-limb natural numbers
    Equiv/            -- Equivalence proofs with Nat
  AzInt/              -- Computable sign-magnitude integers
    Equiv/            -- Equivalence proofs with Int
  AzPolynomial/       -- Univariate polynomials
    Equiv/            -- Equivalence proofs with Polynomial R
  AzMvPolynomial/     -- Multivariate polynomials
    Equiv/            -- Equivalence proofs with MvPolynomial σ R
  AzPolynomialQ/      -- Rational polynomials (shared denominator)
    Equiv/            -- Equivalence proofs with AzPolynomial ℚ
  AzVector/           -- Fixed-length vectors
    Equiv/            -- Equivalence proofs with Fin n → R
  AzMatrix/           -- Fixed-size matrices
    Equiv/            -- Equivalence proofs with Matrix (Fin m) (Fin n) R
  AzFormula/          -- Computable first-order formulas (AzFieldAtom)
    Equiv.lean        -- Equivalence proofs with BPR Formula (FieldAtom)
  BasuPollackRoy/     -- Formalized textbook (BPR)
    Chapter1/
    Chapter2/
    Chapter8/
  Nat/                -- Efficient natural number algorithms
  Rat/                -- Efficient rational number algorithms
  UInt64/             -- Helpers on Lean's built-in UInt64 type
    Equiv/            -- toNat-semantics proofs for UInt64 helpers
  Random/             -- Random generation for testing
  Benchmark/          -- Performance benchmarks
```
