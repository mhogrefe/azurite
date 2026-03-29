# Azurite

A Lean 4 library for efficient, formally verified mathematical computation.

Azurite provides array-backed data structures for polynomials, vectors, and matrices with proven equivalences to their Mathlib counterparts. Every computable operation has a corresponding proof that it agrees with the abstract Mathlib definition.

## Module Map

### Core Data Structures

| Module | Description |
|--------|-------------|
| `AzPolynomial/` | Dense univariate polynomials over a semiring `R`, stored as `Array R` with a trailing-nonzero invariant. Includes add, mul (basecase + Karatsuba), negation, scalar multiplication, evaluation, composition (Horner), exponentiation (binary), quotient/remainder (Euclidean division), root bounds, parsing, and `toString`. |
| `AzMvPolynomial/` | Sparse multivariate polynomials over `R` in variables `σ`, stored as a sorted array of monomials (descending by monic part). Supports multiple monomial orderings (lex, deglex, degrevlex). Includes add, mul (naive + optimized), negation, scalar multiplication, evaluation, exact division, monomial exponentiation, rename, map, and merge-sorted operations. |
| `AzPolynomialQ/` | Rational univariate polynomials with a shared denominator: stores `numerators : Array ℤ` and `denom : ℕ` in canonical (GCD-reduced) form. Enables exact arithmetic without per-coefficient rational normalization. |
| `AzVector/` | Fixed-length vectors wrapping Lean's `Vector R n`. Includes addition, negation, subtraction, scalar multiplication, dot product, cross product, and basis vectors. |
| `AzMatrix/` | Fixed-size `m × n` matrices wrapping `Vector (Vector R n) m`. Includes addition, negation, subtraction, scalar multiplication, matrix multiplication, matrix-vector multiplication, transpose, and row/column access. |

### Equivalence Proofs (`Equiv/` subdirectories)

Each core data structure has an `Equiv/` subdirectory containing proofs that Azurite's computable operations agree with Mathlib's abstract definitions.

#### AzPolynomial ↔ Polynomial R

| File | What it proves |
|------|---------------|
| `Equiv/Basic` | Bijection `AzPolynomial R ≃ Polynomial R` via `toPoly`/`ofPoly`; degree, natDegree, coeff, leadingCoeff, nextCoeff, and monic preservation. |
| `Equiv/Add` | `toPoly (p + q) = toPoly p + toPoly q` |
| `Equiv/Sub` | `toPoly (p - q) = toPoly p - toPoly q` |
| `Equiv/Neg` | `toPoly (-p) = -(toPoly p)` |
| `Equiv/Mul` | `toPoly (p * q) = toPoly p * toPoly q` (basecase) |
| `Equiv/Karatsuba` | `mulKaratsuba p q = mulBasecase p q` (Karatsuba agrees with basecase, hence with Mathlib) |
| `Equiv/SMul` | `toPoly (c • p) = c • toPoly p` |
| `Equiv/Monomial` | `toPoly (monomial n c) = Polynomial.monomial n c` |
| `Equiv/Map` | `toPoly (map f p) = Polynomial.map f (toPoly p)` |
| `Equiv/Eval` | `eval x p = Polynomial.eval x (toPoly p)` and `evalSpecial p b c = c^natDeg · (toPoly p).eval(b·c⁻¹)` (BPR Algorithm 8.8) |
| `Equiv/QuoRem` | `toPoly (quo P Q) = toPoly P / toPoly Q`, `toPoly (rem P Q) = toPoly P % toPoly Q`, and `degree(rem) < degree(Q)` |
| `Equiv/RootBound` | Cauchy root bound correctness: all roots lie within `(-rootBound, rootBound)` |
| `Equiv/Algebra` | Ring homomorphism and algebra structure preservation |
| `Equiv/Comp` | `toPoly (comp p q) = (toPoly p).comp (toPoly q)` |
| `Equiv/Pow` | `toPoly (p.pow n) = toPoly p ^ n` and `(ofPoly p).pow n = ofPoly (p ^ n)` |

#### AzMvPolynomial ↔ MvPolynomial σ R

| File | What it proves |
|------|---------------|
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
| `Equiv/Rename` | Variable renaming preservation |
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
| `Equiv/Algebra` | Algebra structure preservation (CommSemiring, CommRing, IsDomain) |

#### AzVector ↔ (Fin n → R)

| File | What it proves |
|------|---------------|
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
|------|---------------|
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

#### AzPolynomialQ ↔ AzPolynomial ℚ

| File | What it proves |
|------|---------------|
| `Equiv/Basic` | Bijection `AzPolynomialQ ≃ AzPolynomial ℚ`; coefficient, degree, and normalization preservation |
| `Equiv/Parse` | Parsing equivalence |
| `Equiv/ToString` | String conversion equivalence |
| `Equiv/Eval` | `eval p x = Polynomial.eval x (toPoly p)` — BPR special evaluation on integer numerators ↔ Mathlib polynomial evaluation |

### Generic Algorithms

| Module | Description |
|--------|-------------|
| `Algorithm/FastPow` | Right-to-left binary exponentiation (exponentiation by squaring) for any `Monoid`. Computes `a ^ n` in O(log n) multiplications. Proven equivalent to `HPow.hPow` (Mathlib's `^`). |

### Utility Modules

| Module | Description |
|--------|-------------|
| `Nat/Compare` | `normalizedCompare`: O(log n) comparison of naturals by their normalized bit representations. Proven equivalent to comparing `x / 2^size(x)` vs `y / 2^size(y)`. |
| `Rat/LogBase2` | `floorLogBase2Abs` and `ceilingLogBase2Abs` for rationals, proven equal to `⌊log₂ |q|⌋` and `⌈log₂ |q|⌉`. |
| `Rat/Compare` | `Azurite.Rat.cmp`: a fast multi-stage rational comparison (sign → magnitude bracket → num/den comparison → log₂ comparison → cross-multiply). Proven equivalent to standard `compare` on `ℚ`. |
| `Random/` | Random generators for `Nat`, `Int`, `Rat`, `Bool`, `AzPolynomial`, pairs, and geometric distributions. Used for testing and benchmarks. |
| `Benchmark/` | Performance benchmarks for polynomial multiplication (basecase vs Karatsuba at various sizes) and rational comparison. Uses a C FFI nanosecond timer. |

### Formalized Textbook Content

| Module | Content |
|--------|---------|
| `BasuPollackRoy/Chapter1/Section1_1` | Algebraically closed fields, zero sets (`Zer`), algebraic/constructible sets, first-order formulas in the language of fields, quantifier-free and prenex normal forms, realization, prenex normal form theorem. Exercises 1.1–1.3. |
| `BasuPollackRoy/Chapter1/Section1_2` | Euclidean division, GCD/LCM (definitions and propositions), coprimality, signed remainder sequences. Proposition 1.5, Corollary 1.6, Exercises 1.5–1.7, Proposition 1.8. |
| `BasuPollackRoy/Chapter8/Section8_1` | Complexity structures (D₀–D₇), bitsize of integers and rationals, bitsize bounds for sums and products, monomial counting (Lemma 8.6 with `MonicMonomial` bridge), bitsize of polynomial addition/multiplication. Notation 8.7 (Horner polynomials with sum/eval identities), Algorithm 8.7 (polynomial evaluation), Algorithm 8.8 (special evaluation with `horSpecial` sum characterization, field identity, and bitsize bound `τ + iτ' + bit(p+1)`). Cross-references to Azurite implementations of Algorithms 8.1–8.8. |

## Algorithms Implemented

| Algorithm | Source | Module | Complexity |
|-----------|--------|--------|------------|
| Polynomial addition | BPR Alg. 8.1 | `AzPolynomial/Add` | O(max(p,q)) |
| Polynomial multiplication (basecase) | BPR Alg. 8.2 | `AzPolynomial/Mul` | O(p·q) |
| Karatsuba multiplication | — | `AzPolynomial/Karatsuba` | O(n^1.585) |
| Euclidean division | BPR Alg. 8.3 | `AzPolynomial/QuoRem` | O((p−q)·q) |
| Multivariate polynomial addition | BPR Alg. 8.4 | `AzMvPolynomial/Add` | O(s+t) merge |
| Multivariate polynomial multiplication | BPR Alg. 8.5 | `AzMvPolynomial/Mul` | — |
| Exact division of multivariate polynomials | BPR Alg. 8.6 | `AzMvPolynomial/ExactDiv` | — |
| Fast rational comparison | — | `Rat/Compare` | O(1) amortized for many inputs |
| Cauchy root bound | — | `AzPolynomial/RootBound` | O(n) |
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
  BasuPollackRoy/     -- Formalized textbook (BPR)
    Chapter1/
    Chapter8/
  Nat/                -- Efficient natural number algorithms
  Rat/                -- Efficient rational number algorithms
  Random/             -- Random generation for testing
  Benchmark/          -- Performance benchmarks
```
