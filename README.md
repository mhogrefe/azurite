<p align="center">
  <img src="logo/azurite_logo-and-name.svg" alt="Azurite" width="420">
</p>

# Azurite

A Lean 4 library for efficient, formally verified mathematical computation.

Azurite provides computable, array-backed implementations of the objects of
computer algebra (multi-precision naturals, integers and rationals,
polynomials in one and several variables, vectors and matrices, residue rings,
and first-order formulas) together with proofs that every operation agrees
with its abstract [Mathlib](https://github.com/leanprover-community/mathlib4)
counterpart.  On top of these it formalizes the algorithms of several standard
texts and runs them: the computable code is the code that is proven correct,
and it is fast enough to use.

Lean's built-in `Nat`, `Int` and `Rat` are implemented by the runtime on top of
GMP, and Mathlib's polynomials, matrices and residue rings are noncomputable
abstractions built over them.  The `Az*` types replace both: their limbs are
`UInt64` arrays, every operation is written in Lean, and each is proven to agree
with the corresponding `Nat`, `Int`, `ℚ` or Mathlib value.  Large-number
computation therefore never leaves verified Lean code, and the built-in and
Mathlib types appear only in specifications and as the baseline the benchmarks
compare against.

## Highlights

- **Verified arithmetic.** Multi-limb naturals with proven Karatsuba, Toom–Cook,
  divide-and-conquer division, square roots and modular arithmetic; integers,
  rationals, `ℤ/m` and `ℤ/2^k` with tuned proven arithmetic.
- **Verified computer algebra.** Univariate and multivariate polynomials with
  GCD, squarefree factorization, subresultants, Cauchy index and Tarski queries,
  factorization over finite fields, and matrices with proven determinant, rank
  and characteristic polynomial algorithms.
- **Formalized textbooks.** Basu–Pollack–Roy, *Algorithms in Real Algebraic
  Geometry* (Chapters 1–4, 8, 10, including real closed fields, Tarski–Seidenberg
  quantifier elimination and semialgebraic geometry); von zur Gathen–Gerhard,
  *Modern Computer Algebra* (Chapter 14); Crandall–Pomerance, *Prime Numbers*
  (Chapters 2 and 4); Cohen–Lenstra, *Primality Testing and Jacobi Sums* and its
  1987 implementation paper.
- **A verified primality test.** `AzNat.isPrime` is Miller–Rabin rejection
  followed by a fully proven APR-CL certificate checker, with trial division as
  the fallback; `isPrime n = true ↔ Nat.Prime n` is a theorem.  A 247-digit
  prime is certified in under 30 seconds.
- **Small trusted base.** Every declaration depends only on the three standard
  axioms (`propext`, `Classical.choice`, `Quot.sound`); `native_decide` and
  `sorry` are rejected by CI.

The detailed per-module catalog, equivalence-proof tables and algorithm list are
in [`docs/module_map.md`](docs/module_map.md); the sources are listed in
[`docs/bibliography.md`](docs/bibliography.md).

## Getting started

Azurite builds with the Lean toolchain in [`lean-toolchain`](lean-toolchain) and
the Mathlib revision pinned in [`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get    # fetch the prebuilt Mathlib oleans
lake build            # build the library
lake test             # run the #guard test suites (AzuriteTests)
lake build benchmark  # build the benchmark executable
lake env .lake/build/bin/benchmark   # run it
```

CI ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)) builds the
library, runs the tests, and checks with
[`scripts/check_axioms.lean`](scripts/check_axioms.lean) that no declaration
uses an axiom beyond the standard three.

## Layout

```
Azurite.lean          root import file (all library modules)
AzuriteTests.lean     root import file for the #guard test suites (lake test)
Examples.lean         usage examples
Azurite/
  UInt64/                        limb-level helpers with toNat semantics
  AzNat/ AzInt/ AzRat/           multi-precision naturals, integers, rationals
  AzZMod/ AzZModPow2/ AzPolyMod/ residue rings ℤ/m, ℤ/2^k, R[x]/(f)
  AzPolynomial/ AzMvPolynomial/  polynomials in one and several variables
  AzPolynomialQ/ AzRationalFunction/ AzMvRationalFunction/
  AzVector/ AzMatrix/            vectors and matrices
  AzFormula/                     computable first-order formulas
  Algorithm/ Rounding/ Random/ ExhaustiveGenerator/   shared algorithms and test generators
  BasuPollackRoy/ GathenGerhard/ CrandallPomerance/ CohenLenstra/   formalized texts
  APRCL/                         the APR-CL primality test (certificate checker and generator)
  Benchmark/                     the benchmark harness
docs/                 module map and design notes
benchmarks/           benchmark configurations, raw results and charts
scripts/              axiom checker and build helper
```

Each computable directory keeps its implementation at the top level and the
correctness proofs (the equivalences with the Mathlib objects) in an `Equiv/`
subdirectory.

## AI usage

Azurite is written using Claude. I have manually verified that the statements of key theorems are formalized correctly. The statements of Az* equivalence are generally simple to understand: for example, the equivalence of `AzPolynomial` multiplication with Mathlib's `Polynomial` multiplication is
```lean
ofPoly_mul (p q : Polynomial R) :
    AzPolynomial.ofPoly (p * q) = AzPolynomial.ofPoly p * AzPolynomial.ofPoly q
```

## License

Apache License 2.0; see [LICENSE](LICENSE).
