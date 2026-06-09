# Azurite

A Lean 4 library for efficient, formally verified mathematical computation.

Azurite provides array-backed data structures for polynomials, vectors, and matrices with proven equivalences to their Mathlib counterparts. Every computable operation has a corresponding proof that it agrees with the abstract Mathlib definition.

## Module Map

### Core Data Structures

| Module | Description |
|--------|-------------|
| `AzNat/` | Computable multi-limb natural numbers over `Array UInt64`. Schoolbook multiplication plus a Karatsuba implementation (`karatsubaMulLimbs`) with a configurable basecase threshold. Three-way `square` (schoolbook / Karatsuba / Toom-Cook 3). Exponentiation `pow` (sliding-window) and `powBinary` (binary, for benchmarking), both using the fast `square`. Binary GCD (Stein's algorithm, `gcd`) with bulk trailing-zeros shifts. Also provides a `ParsableElement` instance for use as an `AzVector` / `AzMatrix` coefficient type. |
| `AzInt/` | Computable integers as a sign-magnitude pair `(sign : Bool, abs : AzNat)` with a canonical zero invariant (`abs = 0 → sign = true`). Includes conversions to/from all Lean fixed-width int/uint types and `AzNat`, comparison against `UInt64`/`Int64`/`AzNat`, a custom `compare` with derived `Ord`/`LE`/`LT`/`Max`/`Min`, parity tests, `pow2`, `lowMask`, `isPowerOfTwo`, exponentiation `pow` (sign rule over `AzNat`'s sliding-window power, also the `CommRing`'s `npow`), bit-size, trailing-zeros, parsing, `toString`, and a `ParsableElement` instance (so `AzInt` works as a coefficient type for `AzVector` / `AzMatrix` `parseStr`). |
| `AzRat/` | Computable rationals in lowest terms: a `(sign : Bool, num : AzNat, den : AzNat)` with proofs `den ≠ 0`, `num = 0 → sign = true` (canonical zero), and `AzNat.coprime num den` (reduced). Computable conversions `toRat`/`ofRat` to/from `ℚ` (`toRat` builds the `ℚ` directly via `Rat.mk'`, the AzRat invariants being exactly `Rat.mk'`'s nonzero-denominator and coprimality requirements via `AzNat.coprime_iff`) with round-trip equivalence both ways (`toRat_ofRat`, `ofRat_toRat`, axiom-clean). Conversions `AzNat.toAzRat` (`n` as `n/1`), `AzInt.toAzRat` (`z` as `|z|/1` with `z`'s sign), and every primitive `UIntN`/`IntN`/`USize`/`ISize` (`.toAzRat`, delegating through `.toAzInt`) with correctness (`toRat_toAzRat`, `toRat_toAzRat_int`, and per-primitive `*.toRat_toAzRat` agreeing with `toNat`/`toInt` casts into `ℚ`). Rounding `AzRat.round q mode : AzInt × Ordering` (signed numerator over denominator via `AzInt.divRound`, accepting a `RoundingMode`; the `Ordering` records how the result compares to `toRat q`) with correctness `toInt_round` (value agrees with abstract `RoundingTarget.round intSet mode (toRat q)`) and `snd_round` (ordering tag = `compare` of rounded value vs `toRat q`). |
| `AzPolynomial/` | Dense univariate polynomials over a semiring `R`, stored as `Array R` with a trailing-nonzero invariant. Includes add, mul (basecase + Karatsuba), negation, scalar multiplication, multiplication by `X^n` (`mulXPow`), truncation (`truncate`, BPR Notation 1.16), derivative, evaluation, composition (Horner), exponentiation (sliding-window), quotient/remainder (Euclidean division), signed pseudo-remainder (`pRem`, works over any `CommRing`), root bounds, the Sturm sequence (`sturmSequence`, BPR Chapter 2.2), parsing, and `toString`. |
| `AzMvPolynomial/` | Sparse multivariate polynomials over `R` in variables `σ`, stored as a sorted array of monomials (descending by monic part). Supports multiple monomial orderings (lex, deglex, degrevlex). Includes add, mul (naive + optimized), negation, scalar multiplication, partial derivative, evaluation (`eval`, plus generic `eval₂`/`aeval` into any commutative semiring or `R`-algebra), exact division, monomial exponentiation, rename, map, merge-sorted operations, `bind₁`/`bind₂`/`join₂` substitution, and `finSuccEquiv` (forward direction: `AzMvPolynomial (Fin (n+1)) R → AzPolynomial (AzMvPolynomial (Fin n) R)`). |
| `AzPolynomialQ/` | Rational univariate polynomials with a shared denominator: stores `numerators : Array ℤ` and `denom : ℕ` in canonical (GCD-reduced) form. Enables exact arithmetic without per-coefficient rational normalization, fast pointwise negation, and integer-level `Monic` property evaluation. |
| `AzVector/` | Fixed-length vectors wrapping Lean's `Vector R n`. Includes addition, negation, subtraction, scalar multiplication, dot product, cross product, and basis vectors. |
| `AzMatrix/` | Fixed-size `m × n` matrices wrapping `Vector (Vector R n) m`. Includes addition, negation, subtraction, scalar multiplication, matrix multiplication, matrix-vector multiplication, transpose, row/column access, Gaussian elimination (`gauss`, BPR Algorithm 8.15, early-abort; `gaussSteps`, indexed step iteration), row-echelon reduction (`rowEchelon`, always upper-triangular), determinant via Gauss (`det`), determinant via Bareiss recurrence (`bareissDet`, BPR Algorithm 8.16, fraction-free over a domain), and the Bareiss block/minor (`bareissBlock`, `bareissMinor`, `principalMinor`; BPR Notation 8.19). |
| `AzFormula/` | Computable first-order formulas over `AzFieldAtom` (field atoms using `AzMvPolynomial`). Provides computable free-variable computation, bound-variable computation, sentence checking, formula constructors, variable renaming, negation normal form (`toNNF`), prenex normal form conversion (`toPrenex`), and noncomputable realization. Generic `AtomVars`, `AtomRename`, `AtomRealization` typeclasses. Modular simplification passes (`elimDoubleNeg`, `elimVacuousQuantifiers`). |

### Equivalence Proofs (`Equiv/` subdirectories)

Each core data structure has an `Equiv/` subdirectory containing proofs that Azurite's computable operations agree with Mathlib's abstract definitions.

#### AzNat ↔ Nat

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Computable equivalence `equivNat : AzNat ≃ Nat` via `toNat`/`ofNat`, including base invariant preservation. |
| `Equiv/Compare` | `compare_eq_compare_toNat`: custom limb-by-limb `compare` logic mapping equivalently to `Ord.compare` on `Nat`, providing the formally verified `LinearOrder AzNat` instance with `≤` and `<`. |
| `Equiv/Gcd` | `toNat_gcd`: `(gcd a b).toNat = Nat.gcd a.toNat b.toNat` — the binary GCD (Stein's algorithm) agrees with Mathlib's `Nat.gcd`. |

#### AzInt ↔ Int

| File | What it proves |
|------|----------------|
| `Equiv/Basic` | Bijection `AzInt ≃ Int` via `toInt`/`ofInt`, including the canonical-zero invariant round-trip. |
| `Equiv/Compare` | `compare_eq_lt_iff_toInt_lt` and friends: custom sign-magnitude `compare` matches `Ord.compare` on `Int`, providing the `LinearOrder AzInt` instance. |
| `Equiv/Conversion` | `toInt_toAzInt` / `toInt_toAzInt = toNat` for every fixed-width `UInt*`/`Int*`/`USize`/`ISize` and `AzNat`, and the reverse `toInt_toUInt*` / `toInt_toInt*` direction. |
| `Equiv/Parity` | `isEven_iff`/`isOdd_iff` agree with `Even`/`Odd` on `Int`. |
| `Equiv/Pow` | `toInt_pow z n = z.toInt ^ n` and `ofInt_pow`: `AzInt.pow` (sign rule over `AzNat`'s power, the `CommRing`'s `npow`) matches `Int` exponentiation. |
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
| `Equiv/SturmSequence` | `toPoly (sturmSequence P n) = Azurite.BPR.sturmSequence (toPoly P) n` (BPR Chapter 2.2). Computable Sturm sequence via the signed remainder sequence agrees with the noncomputable Polynomial-side construction. |

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
| `Equiv/RowEchelon` | `(M.rowEchelon).1.toFn.BlockTriangular id` — the row-echelon variant produces an upper-triangular matrix (Mathlib `Matrix.BlockTriangular`) |
| `Equiv/Det` | `M.det = Matrix.det M.toFn` — Gaussian-elimination determinant (via the `gauss` early-abort variant) agrees with Mathlib's `Matrix.det`, by per-step row-operation invariance + `Matrix.det_of_upperTriangular` / `Matrix.det_eq_zero_of_row_eq_zero` |
| `Equiv/Bareiss` | **BPR equation (8.5)** `b_{i,j}^{(k)} = (∏ pivots) · g_{i,j}^{(k)}` — `bareissMinor_eq_prod_pivots_times_gaussSteps`. Proven under strict-nonzero-pivot hypothesis via the Gauss-block correspondence `gaussSteps_bareissBlock_toFn` + `det_gaussSteps` + `gaussSteps_blockTriangular` + `Matrix.det_of_upperTriangular`. **BPR Proposition 8.20** (Sylvester-Bareiss recurrence) `b_{i,j}^{(k+2)} · b_{k+1,k+1}^{(k)} = b_{k+2,k+2}^{(k+1)} · b_{i,j}^{(k+1)} − b_{i,k+2}^{(k+1)} · b_{k+2,j}^{(k+1)}` — `bareissMinor_recurrence`. |

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
| `Algorithm/SlidingWindowPow` | Left-to-right **sliding-window** exponentiation for any `Monoid`. Precomputes the `2^(w-1)` odd powers `a^1,…,a^(2^w-1)` with the window width `w` growing with the exponent's bit-length (`slidingWindowSize`), so it uses fewer multiplications than `FastPow` for larger exponents (cubing is one squaring + one multiplication). Proven equivalent to `HPow.hPow` (`slidingWindowPow_eq_pow`). Kept alongside `FastPow` for benchmarking. |
| `Algorithm/ExactDiv` | `ExactDiv D` typeclass: `exactDiv a b : D` returns `c` such that `b * c = a` when `b ∣ a`. Default instance for any `Field K` (uses `a / b`). Instances: `AzInt` (`AzInt/ExactDiv`), `AzPolynomial R` over any `[CommRing R] [DecidableEq R] [ExactDiv R]` (`AzPolynomial/ExactDiv`, synthetic division), and `AzMvPolynomial n R ord` over any `[CommRing R] [IsDomain R] [DecidableEq R] [ExactDiv R]` (`AzMvPolynomial/ExactDivCommRing`, sibling of the existing field-only `AzMvPolynomial.exactDiv`). Used by `AzMatrix/BareissDet` so the fraction-free Bareiss determinant runs end-to-end over `AzInt`, `AzPolynomial AzInt`, or `AzMvPolynomial n AzInt ord` via the chained instances. |

### Utility Modules

| Module | Description |
|--------|-------------|
| `UInt64/` | Helpers on Lean's built-in `UInt64` type. `addWithCarry` (64-bit add with carry-in/out), `subWithBorrow` (64-bit sub with borrow-in/out), `wideMul` (full 128-bit product of two `UInt64`s, returned as a `(hi, lo)` pair), `isPowerOfTwo` (bit-trick power-of-two test), `testBit` (returns `false` for `i ≥ 64`), `setBit`/`clearBit` (identity for `i ≥ 64`), `splitInHalf`/`joinHalves` (convert between `UInt64` and a pair of `UInt32` halves). `Equiv/Basic` provides `UInt64.eq_of_toNat_eq`; the remaining `Equiv/*` files prove the `toNat` semantics of each helper, including `toNat_joinHalves` and the two-sided inverse properties of `splitInHalf`/`joinHalves`. |
| `AzNat/NormalizedCompare` | `normalizedCompare`: **allocation-free** comparison of two `AzNat`s by their normalized (MSB-aligned) bit representations — reads the `k`-th limb of `x·2^shift` on the fly via `getBitsAsLimb` (no temporary shifted `AzNat`), comparing top-down against `y`'s limbs. Proven (`normalizedCompare_eq_cross`, axiom-clean) equal to the cross-multiplication `compare (x·2^size(y)) (y·2^size(x))`, i.e. comparing `x / 2^size(x)` vs `y / 2^size(y)`. The older `Nat`-based `normalizedCompareNat` (`AzNat/NormalizedCompareNat`) is kept for `Rat/LogBase2`. |
| `Rat/LogBase2` | `floorLogBase2Abs` and `ceilingLogBase2Abs` for rationals, proven equal to `⌊log₂ |q|⌋` and `⌈log₂ |q|⌉`. |
| `Rat/Compare` | `Azurite.Rat.cmp`: a fast multi-stage rational comparison (sign → magnitude bracket → num/den comparison → log₂ comparison → cross-multiply). Proven equivalent to standard `compare` on `ℚ`. |
| `Random/` | Random generators for `Nat`, `Int`, `Rat`, `Bool`, `AzPolynomial`, pairs, and geometric distributions. Used for testing and benchmarks. |
| `Benchmark/` | Performance benchmarks for polynomial multiplication (basecase vs Karatsuba at various sizes), rational comparison, and AzNat vs Nat addition. Uses a C FFI nanosecond timer. |

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
| `BasuPollackRoy/Chapter2/Proposition_2_21` | **Proposition 2.21**: If `r` is a root of `P ≠ 0` of multiplicity `µ` in a real closed field `R`, then the sign of `P` to the right of `r` equals `sign(P^{(µ)}(r))` and the sign to the left equals `(−1)^µ · sign(P^{(µ)}(r))`. Helper lemmas: `hasSignRight_of_eval_ne_zero`, `hasSignLeft_of_eval_ne_zero` (constant sign at non-vanishing points); `exists_no_root_Ioo_right/left` (non-vanishing intervals around non-roots). Real-closed-field corollaries `proposition_2_21_right/left_of_isRealClosed`. **Proposition 2.22 (Rolle's theorem)**: If `P(a) = P(b) = 0` with `a < b`, then `P'` has a root in `(a, b)`. Proved via factorization `P = (X−a)^m (X−b)^n Q`, derivative sign analysis of `Q₁ = m(X−b)Q + n(X−a)Q + (X−a)(X−b)Q'`, and reduction to closest root. Real-closed corollary `proposition_2_22_of_isRealClosed`. **Corollary 2.23 (Mean Value Theorem)**: For `P ∈ R[X]` and `a < b`, there exists `c ∈ (a,b)` with `P(b) − P(a) = (b − a) · P'(c)`. Proved by applying Rolle to `Q(X) = (P(b)−P(a))(X−a) − (b−a)(P(X)−P(a))`. Real-closed corollary `corollary_2_23_of_isRealClosed`. **Corollary 2.24**: If `P' > 0` (resp. `< 0`) on `(a,b)`, then `P` is strictly increasing (resp. decreasing) on `[a,b]`. Proved via MVT. Real-closed corollaries `corollary_2_24_increasing/decreasing_of_isRealClosed`. |
| `BasuPollackRoy/Chapter2/SignCondition` | **Definition 2.25**: Sign conditions. `SignCondition ι = ι → SignType`, `IsStrict` (values in `{1, −1}`), `IsRealizedBy` (a family of values realizes a sign condition when each value's sign matches), `realization` (the set of points realizing `σ`), `IsRealizable` (realization is non-empty). Generic over any evaluation; for polynomials use `σ.realization (fun i x => (Q i).eval x)`. **Notation 2.26**: `der P` is the list `[P, P', …, P⁽ᵖ⁾]` of successive derivatives. |
| `BasuPollackRoy/Chapter2/Proposition_2_27` | **Proposition 2.27 (Basic Thom's Lemma)**: Let `P ∈ R[X]` with `natDegree P ≤ n` and `σ` a sign condition on the first `n + 1` derivatives. Then the realization `{x | ∀ i ≤ n, sign(P⁽ⁱ⁾(x)) = σ(i)}` is either empty, a singleton, or an open interval. Proved by induction on `n`, using MVT (Cor 2.23), monotonicity from derivative sign (Cor 2.24), and IVP. Defines `IsOpenInterval` (nonempty, ord-connected, no min/max), `derReali` (derivative realization set). Helper lemmas: `sign_filter_mono/anti` (sign filtering preserves the trichotomy for monotone/antitone functions). Real-closed corollary `proposition_2_27_of_isRealClosed`. |
| `BasuPollackRoy/Chapter2/Proposition_2_28` | **Proposition 2.28 (Thom Encoding)**: Let `P ∈ R[X]` be non-zero of degree `p`, and let `x, x'` realize sign conditions `σ, σ'` on `Der(P)`. **Part 1 (Root injectivity)**: If `σ = σ'` and `σ(P) = 0`, then `x = x'`. Proved by showing the realization set is either empty, a singleton (done), or an open interval (contradicts finiteness of roots). **Part 2 (Comparison)**: If `σ ≠ σ'`, let `j` be the largest index where they differ. Then `σ(j+1) = σ'(j+1) ≠ 0`, and `x < x'` is determined by `σ(j+1)` and the ordering of `σ(j)` vs `σ'(j)`. Proved using Proposition 2.27, strict monotonicity/antitonicity from derivative sign, and Part 1 for the non-zero claim. Real-closed corollaries `proposition_2_28_part1/part2_of_isRealClosed`. **Definition 2.29 (Thom encoding)**: A sign condition `σ` on `Der(P)` is a Thom encoding of `x` if `σ(P) = 0` and `derReali P n σ = {x}`. `IsThomEncoding P n σ x`. Theorem `isThomEncoding_of_mem`: any root realization gives a Thom encoding (immediate from Part 1). Real-closed corollary `isThomEncoding_of_mem_of_isRealClosed`. **Example 2.30**: Roots of `X² − 2` are distinguished by derivative sign: `r² = s² = 2` and `sign(r) = sign(s)` imply `r = s`. |
| `BasuPollackRoy/Chapter2/Section2_2` | **Notation 2.32 (Sign variations)**: `Var(a)` counts the number of adjacent pairs of opposite signs in a finite sequence `a : List R` over an ordered ring `R`, after dropping all zeros. Helper `varNonzero` implements the pairwise recursion on zero-free lists (`varNonzero_cons_cons` unfolding lemma). `Var` extends this by filtering zeros (`Var_eq_varNonzero_filter`, `Var_of_forall_ne_zero`). Sign-helper lemmas: `varNonzero_eq_zero_of_forall_nonneg/nonpos`, `Var_eq_zero_of_forall_nonneg/nonpos` (a list of same-signed entries has zero variations), `Var_zero_cons` (prepending a zero is a no-op). **`Var(P)` and `pos(P)`**: `varPoly P = Var(a₀, …, aₚ)` is the sign variations in the coefficient sequence of `P = aₚ Xᵖ + ⋯ + a₀`. `posRoots P` is the number of positive real roots of `P` counted with multiplicity (via `Polynomial.roots.filter (0 < ·)`). **Notation 2.34 (Sign variations at a point)**: `varAt P a` is `Var(P₀(a), …, P_d(a))` for `P : List R[X]` at `a : ExtendedPoint R` (an element of `R ∪ {−∞, +∞}`). At `±∞` the sign comes from the leading monomial per Proposition 2.4: `evalPoly P posInf = leadingCoeff P`, `evalPoly P negInf = (−1)^natDegree · leadingCoeff P`. Unfolding lemmas `varAt_finite/posInf/negInf/nil`. **`Var(P; a, b)`**: `varBetween P a b = varAt P a − varAt P b : ℤ`. **`num(P; (a, b])`**: `numRoots P a b : ℕ` is the multiplicity-weighted root count of `P` in the half-open interval `(a, b]`, pattern-matched over `a, b : ExtendedPoint R` (empty when `a = +∞` or `b = −∞`; total roots when `(−∞, +∞)`). |
| `BasuPollackRoy/Chapter2/CauchyIndex` | **BPR Definition 2.53 (Cauchy index)**: `cauchyIndexOn Q P a b` for `a, b : ExtendedPoint R` is the number of jumps of `Q/P` from `−∞` to `+∞` minus the number from `+∞` to `−∞` on the open interval `(a, b)`. `cauchyIndex Q P := cauchyIndexOn Q P .negInf .posInf` is the full-line version. Helper `ExtendedPoint.openInterval` exposes `(a, b) ⊆ R` as a `Set R`. **Bounds:** `cauchyIndexOn_le_card_roots_toFinset` and `cauchyIndexOn_le_natDegree`. **Extraction:** `cauchyIndexOn_eq_natDegree_extract` — when the index attains `P.natDegree`, then `P.roots.toFinset.card = P.natDegree`, `P.roots.Nodup`, every distinct `P`-root lies in `(a, b)` and produces a `−∞ → +∞` jump, and none produces a `+∞ → −∞` jump. **Sign-analysis machinery:** `derivative_eval_at_root_of_splits`, `sign_prod_sub`, `sign_derivative_at_simple_root`, `sign_eval_at_non_root`. **Combinatorial machinery:** `card_filter_gt_Q_eq_P`, `P_root_not_Q_root`. **Composite jump lemmas:** `jumps_at_P_root` (every `P`-root produces a `−∞ → +∞` jump under the structural conditions), `exists_Q_root_in_gap` (Q has a root between consecutive P-roots, via Prop 2.21 + IVP). Includes `Interlacing P Q` predicate. **Remark 2.55(a) (fully proven, both directions):** with `0 < P.natDegree` and `Q.degree < P.degree`, `cauchyIndexOn Q P a b = P.natDegree` iff `Q.natDegree + 1 = P.natDegree`, leading-coefficient signs of `P` and `Q` agree, all roots of `P` and `Q` are simple and lie in `(a, b)`, and `P, Q` interlace. The proof uses the IVP hypothesis to apply Proposition 2.21 (left/right) for sign analysis, plus an explicit bijection from non-max P-roots to `Q.roots.toFinset` for the cardinality and interlacing arguments. The leading-coefficient sign claim uses `hasSignAtPosInfty_leadingCoeff` plus IVP-driven constancy of `Q · P` past `max_P`. **Remark 2.55(b) (fully proven)** (`cauchyIndexOn (Q % P) P a b = cauchyIndexOn Q P a b`, taking IVP as a hypothesis): the proof reduces via `Finset.filter_congr` to a per-root jump-iff and uses several proven helpers — `rootMultiplicity_mod_lt_iff_of_mod_ne` (the multiplicity-equivalence `Q.rootMul x < µ_P ↔ (Q%P).rootMul x < µ_P` with mults equal under either, via the proven `Polynomial.rootMultiplicity_add_of_lt` and `Polynomial.rootMultiplicity_neg`), and `hasSignRight_mod_iff_of_mod_ne` (sign agreement on the right of any `P`-root, using Proposition 2.21 + uniqueness of `HasSignRight` to reduce to comparing the canonical `(D^k)`-derivative signs, with the `K · P²`-difference contributing nothing via the helper `eval_iterate_derivative_eq_zero_of_lt_rootMultiplicity` proved by Leibniz expansion of `p = (X − Cx)^µ · q`). |
| `BasuPollackRoy/Chapter2/Jumps` | **BPR Chapter 2.2 jump predicates**: `JumpsFromNegInfToPosInf Q P x` and `JumpsFromPosInfToNegInf Q P x` capture when the rational function `Q/P` jumps from `−∞` to `+∞` (resp. `+∞` to `−∞`) at a root `x` of `P`. Both require `P.rootMultiplicity x > Q.rootMultiplicity x` with odd difference; the two differ in the right-hand sign of `Q · P` (`+1` vs `−1`). **Implied facts:** sign of `Q · P` flips across `x` over any ordered field with the IVP (`hasSignLeft`); over `ℝ`, `Q/P` actually tends to `±∞` from each side via `Filter.Tendsto … atTop` / `atBot` (`tendsto_atTop_nhdsGT`, `tendsto_atBot_nhdsLT`, `tendsto_atBot_nhdsGT`, `tendsto_atTop_nhdsLT`). The `ℝ` proof uses the factorisation `Q · P = (X − C x)^(m+n) · R` and `P = (X − C x)^m · P̃` together with `Polynomial.continuous`, `Tendsto.inv_tendsto_nhdsGT_zero` / `nhdsLT_zero`, and `Tendsto.atTop_mul_pos` / `atBot_mul_pos`. |
| `BasuPollackRoy/Chapter2/SturmSequence` | **Sturm sequence** (BPR Chapter 2.2 definition): `sturmSequence P = SRemS P P.derivative`, the signed remainder sequence of `P` and its derivative (Definition 1.7 specialized to `Q = P'`). Defined for any field; the "non-zero `P` over a real closed field" hypothesis is a precondition for downstream theorems, not for the definition. Includes unfolding lemmas `sturmSequence_zero` (`= P`) and `sturmSequence_one` (`= P.derivative`). |
| `BasuPollackRoy/Chapter2/TarskiQuery` | **BPR Tarski-query**: `tarskiQueryOn Q P a b` for `a, b : ExtendedPoint R` is `∑_{x ∈ (a, b), P(x) = 0} sign(Q(x)) : ℤ`, summing over `P.roots.toFinset` filtered by membership in the open interval. `tarskiQuery Q P := tarskiQueryOn Q P .negInf .posInf` is the full-line version. Includes the simp unfolding `tarskiQuery_eq_tarskiQueryOn_negInf_posInf` and the equivalent root-count form `tarskiQueryOn_eq_card_pos_sub_card_neg`: `tarskiQueryOn Q P a b = #{x ∈ (a, b) ∩ P.roots | Q(x) > 0} − #{x ∈ (a, b) ∩ P.roots | Q(x) < 0}`. |
| `BasuPollackRoy/Chapter2/Lemma_2_60` | **BPR Lemma 2.60 (fully proven)**: Cauchy index of `Q/P` vs `−R/Q` (where `R = P % Q`) under one SRemS step. Statement: `2 · (Ind(Q/P; a, b) − Ind(−R/Q; a, b)) = σ(b) − σ(a)` where `σ(t) = sign(P(t)·Q(t))` (assumed nonzero at `a` and `b`), under the `a < b` hypothesis encoded as `ExtendedPoint.Lt a b` (matching BPR's explicit "for `a < b`" assumption). Equivalently: `Ind(Q/P) = Ind(−R/Q)` when `σ(a) = σ(b)`, and `Ind(Q/P) = Ind(−R/Q) + σ(b)` when `σ(a) ≠ σ(b)`. **Components:** `ExtendedPoint.Lt` (strict order on extended endpoints, defined by case analysis: false for empty-interval pairs, true for ordered finite/infinite pairs); `cauchyIndexOn_neg_left` (`Ind(−Q/P) = −Ind(Q/P)`); `cauchyIndexOn_neg_mod` (`Ind(−(P%Q)/Q) = −Ind(P/Q)`); the leading-factor factorization `divByMonic_pow_mul_eq_mul` (`(P·Q)~(x) = P̃(x) · Q̃(x)`); jump-zero helpers `jumpContrib_eq_zero_of_rootMultiplicity_zero` and `jumpContrib_eq_zero_of_le`; the per-jump-formula helper `jumpContrib_eq_sign_leading_factor` (when `µ_P > µ_Q` and the diff is odd, `jumpContrib Q P x = sign((Q·P)~(x))`, proved via Prop 2.21 + uniqueness); `per_root_jump_sum_eq_signFlip` (per-root identity `jumpContrib Q P x + jumpContrib P Q x = signFlipAt (P·Q) x`, with both even-sum and odd-sum cases handled); `cauchyIndexOn_eq_sum_jumpContrib` (rewriting `cauchyIndexOn` as a `jumpContrib` sum); `cauchyIndexOn_swap_sum` (combines the per-root identity with `Finset.sum_union_eq_left/right` and `cauchyIndexOn_eq_sum_jumpContrib` to derive `2 · (Ind(Q/P) + Ind(P/Q)) = σ(b) − σ(a)`); the final `lemma_2_60` derived from `cauchyIndexOn_swap_sum` plus `cauchyIndexOn_neg_mod`. Sub-helpers: `sign_jump_at_root_eq_signFlipAt` (single-root jump = `2 · signFlipAt F r`); `sign_eval_eq_of_no_root_Ioo` (finite no-root interval has constant sign); `roots_filter_eq_empty_of_no_root`; `sign_eval_eq_canonical_left/right` (`sign(F(a)) = canonical s_left/right at adjacent root r`); `running_sign_flip_count_finite` (finite-endpoint version, by strong induction on root count picking `Finset.min'`); `running_sign_flip_count` (ExtendedPoint version, dispatched by case analysis on `(a, b) ∈ {finite, posInf, negInf}²`: non-empty cases reduce to the finite version via `exists_finite_left_of_negInf` / `exists_finite_right_of_posInf`; empty-interval cases dismissed by `Lt`-derived contradictions). Helper definitions: `signFlipAt`, `jumpContrib`, `sigmaPQ`. |
| `BasuPollackRoy/Chapter2/Lemma_2_59` | **BPR Lemma 2.59 (fully proven)**: Var of the signed remainder sequence at a single SRemS step. With `R' = P % Q` and `Q ≠ 0`: at any `x : ExtendedPoint K` where `evalPoly P x ≠ 0` and `evalPoly Q x ≠ 0`, `varAt (SRemSList P Q (n+2)) x = varAt (SRemSList Q (-R') (n+1)) x + (1 if (P·Q)(x) < 0 else 0)` (`lemma_2_59_pointwise`). The interval-difference form `lemma_2_59` follows by subtraction at `a` and `b`. Key infrastructure: `SRemSList P Q n = (List.range n).map (SRemS P Q)`, head decomposition `SRemSList_succ` (needs `Q ≠ 0`) and `SRemSList_head_decomp` (no hypothesis), tail identity `SRemS_succ` (`SRemS P Q (i+1) = SRemS Q (-(P%Q)) i` for `Q ≠ 0`), generic `Var_cons_cons_of_ne_zero` (`Var (a::b::L) = Var (b::L) + [a*b<0]` when `a, b ≠ 0`), and its `varAt` specialisation. |
| `BasuPollackRoy/Chapter2/Theorem_2_58` | **BPR Theorem 2.58 (fully proven)**: `Var(SRemS(P, Q); a, b) = Ind(Q/P; a, b)` for `P ≠ 0` over a real closed field, under `ExtendedPoint.Lt a b` and the "no-root-on-SRemS" hypothesis (`a` and `b` are not roots of any nonzero polynomial in the signed remainder sequence). Proven by strong induction on the truncation index `n` (with `SRemS P Q n = 0`): the `n = 0` case contradicts `P ≠ 0`; the `n = 1` case forces `Q = 0`, so both sides vanish (`varAt [P]` is `Var [P(x)] = 0` by `Var_singleton`, and `cauchyIndexOn 0 P a b = 0` by `cauchyIndexOn_zero_left` since `JumpsFrom...0 P x` is impossible); the `n + 2` case splits on `Q = 0` (`SRemSList P 0 (n+2) = [P, 0, …, 0]` reduces by `varAt_singleton_with_trailing_zeros`) versus `Q ≠ 0` (combine Lemma 2.59, Lemma 2.60, and the IH applied to the tail `(Q, -R)` at index `n + 1` via the tail identity `SRemS Q (-R) i = SRemS P Q (i+1)`). The σ-correction algebra uses `two_mul_indicator_eq` (`2·(if P·Q < 0 then 1 else 0) = 1 - sigmaPQ`, by trichotomy of `sign`). Helper lemmas: `varNonzero_eq_zero_of_length_le_one`, `Var_singleton`, `varAt_singleton_with_trailing_zeros`, `not_jumpsFromNegInfToPosInf_zero`, `not_jumpsFromPosInfToNegInf_zero`, `cauchyIndexOn_zero_left`. |
| `BasuPollackRoy/Chapter2/Proposition_2_57` | **BPR Proposition 2.57 (fully proven)**: `tarskiQueryOn Q P a b = cauchyIndexOn (P.derivative * Q) P a b`, taking IVP as a hypothesis. The proof goes via per-root iffs `jumpsFromNegInfToPosInf_derivative_iff_pos` (`JumpsFromNegInfToPosInf (P'·Q) P x ↔ 0 < Q(x)`) and `jumpsFromPosInfToNegInf_derivative_iff_neg` (`JumpsFromPosInfToNegInf (P'·Q) P x ↔ Q(x) < 0`). Key helpers: `rootMultiplicity_derivative` (`P'.rootMul x + 1 = P.rootMul x` when `µ ≥ 1`, via the factorization `P' = (X−Cx)^{µ−1} · g` with `g(x) = µ · P̃(x) ≠ 0` using char-0); `derivative_ne_zero_of_mem_roots` (in char 0, P-with-a-root has nonzero derivative); `hasSignRight_derivative_mul_self` (when `Q(x) ≠ 0`, `P'·Q·P` has sign `sign(Q(x))` on the right of `x`, via the factorization `P'·Q·P = (X−Cx)^{2µ−1} · (g · Q · P̃)` whose value at `x` is `µ · P̃(x)² · Q(x)`, plus IVP). The main theorem combines these via `Finset.filter_congr` after rewriting `tarskiQueryOn` as a difference of root counts. **Corollary `cauchyIndexOn_derivative_self_eq_card_roots_in_openInterval`** specialises `Q = 1` to recover the number-of-distinct-roots formula: `#{x ∈ P.roots.toFinset | x ∈ (a, b)} = cauchyIndexOn P' P a b`. |
| `BasuPollackRoy/Chapter2/Theorem_2_33` | **Theorem 2.33 (Descartes' rule of signs, fully proven)**: Over a real closed field `R`, for `P ∈ R[X]`, `Var(P) ≥ pos(P)` and `Var(P) − pos(P)` is even. Stepping-stone identity `varPoly_eq_varBetween_der` proves `Var(P) = Var(Der(P); 0, +∞)` via two fully-formalized helpers: `varAt_der_posInf` (leading coeffs of successive derivatives all share the sign of `leadingCoeff P`, using `coeff_iterate_derivative_at_natDegree_sub` and `natDegree_and_leadingCoeff_iterate_derivative`) and `varAt_der_finite_zero` (derivative-at-zero equals `i! · aᵢ`, so positive scaling preserves `Var`, via `varNonzero_map_mul_pos` and `Var_map_range_scale_eq`). The main theorem `descartes_rule_of_signs` reduces via `varPoly_eq_varBetween_der` and `posRoots_eq_numRoots` to `budan_fourier_posInf` on the half-open interval `(0, +∞)`. |
| `BasuPollackRoy/Chapter2/Exercise_2_11` | **Exercise 2.11**: The real algebraic numbers `ℝ_alg = algebraicClosure ℚ ℝ` are real closed. Proves `IsRealClosed R_alg` by establishing: (1) `IsSemireal` — sums of squares transfer along the embedding to ℝ, ruling out `−1`; (2) `isSquare_or_isSquare_neg` — for nonneg `x`, `√x` is algebraic via `p.comp(X²)` witness using `leadingCoeff_comp`; (3) `exists_isRoot_of_odd_natDegree` — odd-degree real polynomials have roots by strong induction on degree using `Irreducible.natDegree_le_two`, then roots of polynomials with algebraic coefficients are algebraic by `IsIntegral.trans_isAlgebraic`. |
| `BasuPollackRoy/Chapter2/Theorem_2_31` | **Theorem 2.31**: Every algebraically closed field of characteristic zero contains a real closed subfield. Proves existence of a maximal semireal intermediate field `R` over `ℚ` via Zorn's lemma (`zorn_le₀`), using `Subfield.mem_sSup_of_directedOn` for chain completeness and `IsAlgClosed.lift` to show maximality implies `HasNoNontrivialRealAlgebraicExtension`, then applies Theorem 2.11 (d⇒a). |
| `BasuPollackRoy/Chapter8/Section8_1` | Complexity structures (D₀–D₇), bitsize of integers and rationals, bitsize bounds for sums and products, monomial counting (Lemma 8.6 with `MonicMonomial` bridge), bitsize of polynomial addition/multiplication. Notation 8.7 (Horner polynomials with sum/eval identities), Algorithm 8.7 (polynomial evaluation), Algorithm 8.8 (special evaluation with `horSpecial` sum characterization, field identity, and bitsize bound `τ + iτ' + bit(p+1)`), Algorithm 8.9 (translation), Algorithm 8.10 (special translation). Cross-references to Azurite implementations of Algorithms 8.1–8.10. |

## Known Textbook Errors (BPR)

While formalizing *Algorithms in Real Algebraic Geometry* (Basu, Pollack, Roy), the following mathematical discrepancies were identified and corrected in Azurite:

*   **Lemma 1.10(b) (Signed Remainder Determinant Sequence):** The textbook states the identity $U_i V_{i+1} - V_i U_{i+1} = (-1)^i$. However, the textbook's definition of the cofactor sequence ($U_{i+2} = U_i - Q_{i+1} U_{i+1}$) drops the negation required to compute signed remainders ($P_{i+2} = - P_i + Q_{i+1} P_{i+1}$). When the strictly correct recurrence is used, the sequence determinant evaluates structurally to $1$ unconditionally. Azurite's formalization proves `lemma_1_10_b` equal to `1` and applies the corrected identity in subsequent proofs (e.g., Proposition 1.12).

## Algorithms Implemented

| Algorithm | Source | Module | Complexity |
|-----------|--------|--------|------------|
| Polynomial addition | BPR Alg. 8.1 | `AzPolynomial/Add` | O(max(p,q)) |
| Polynomial multiplication (basecase) | BPR Alg. 8.2 | `AzPolynomial/Mul` | O(p·q) |
| Karatsuba multiplication (polynomial) | — | `AzPolynomial/Karatsuba` | O(n^1.585) |
| Karatsuba multiplication (multi-limb Nat) | — | `AzNat/Karatsuba` | O(n^1.585) |
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
| Gaussian elimination (`gauss` early-abort + `rowEchelon` always-triangular + `det`) | BPR Alg. 8.15 | `AzMatrix/RowEchelon`, `AzMatrix/Det` | O(n³) over a field |
| Dodgson-Jordan-Bareiss fraction-free det (`bareissDet`) | BPR Alg. 8.16 | `AzMatrix/BareissDet` | O(n³) over a field; stays in entry ring when that ring is a domain |
| Binary GCD (Stein's algorithm) | MCA Alg. 1.18 | `AzNat/Gcd` | O(n²) |
| Exponentiation by squaring | — | `Algorithm/FastPow` | O(log n) |
| Sliding-window exponentiation (exponent-dependent window) | — | `Algorithm/SlidingWindowPow` | O(log n), fewer mults than binary |

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
