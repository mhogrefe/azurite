<p align="center">
  <img src="logo/azurite_logo-and-name.svg" alt="Azurite" width="420">
</p>

# Azurite

A Lean 4 library for efficient, formally verified mathematical computation.

Azurite provides computable, array-backed implementations of the objects of
computer algebra (multi-precision naturals, integers and rationals,
arbitrary-precision floats, polynomials in one and several variables, vectors
and matrices, residue rings, and first-order formulas) together with proofs
that every operation agrees
with its abstract [Mathlib](https://github.com/leanprover-community/mathlib4)
counterpart.  On top of these it formalizes the algorithms of several standard
texts and runs them: the computable code is the code that is proven correct,
and it is fast enough to use.

Lean's built-in `Nat`, `Int` and `Rat` are implemented by the runtime on top of
GMP, and Mathlib's polynomials, matrices and residue rings are noncomputable
abstractions built over them.  The `Az*` types replace both: their limbs are
`UInt64` arrays, every operation is written in Lean, and each is proven to agree
with the corresponding `Nat`, `Int`, `ℚ` or Mathlib value.  Large-number
computation therefore never leaves verified Lean code: `Nat` still appears where
small numbers belong, such as array indices, sizes and exponents, but large
values are always `AzNat`, and the Mathlib types appear only in specifications
and as the baseline the benchmarks compare against.

## Highlights

- **Verified arithmetic.** Multi-limb naturals with proven Karatsuba, Toom–Cook,
  divide-and-conquer division, square roots and modular arithmetic; integers,
  rationals, `ℤ/m` and `ℤ/2^k` with tuned proven arithmetic.
- **Correctly rounded floats.** `AzFloat` is an arbitrary-precision binary
  float whose elementary and special functions are proven to return the
  correctly rounded value in every rounding mode; see
  [below](#arbitrary-precision-floats).
- **Verified computer algebra.** Univariate and multivariate polynomials with
  GCD, squarefree factorization, subresultants, Cauchy index and Tarski queries,
  factorization over finite fields, and matrices with proven determinant, rank
  and characteristic polynomial algorithms.
- **Formalized textbooks.** Basu–Pollack–Roy, *Algorithms in Real Algebraic
  Geometry* (Chapters 1–4, 8, 10, including real closed fields, Tarski–Seidenberg
  quantifier elimination and semialgebraic geometry); von zur Gathen–Gerhard,
  *Modern Computer Algebra* (Chapter 14); Crandall–Pomerance, *Prime Numbers*
  (Chapters 2 and 4); Cohen–Lenstra, *Primality Testing and Jacobi Sums* and its
  1987 implementation paper; Brent–Zimmermann, *Modern Computer Arithmetic*
  (parts of Chapters 2 and 4); the NIST *Digital Library of Mathematical
  Functions*, equation by equation (Chapters 1–5 largely complete, Chapter 6 in
  progress).
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

## Arbitrary-precision floats

`AzFloat` is a binary float with an `AzNat` significand of any precision and an
unbounded `AzInt` exponent, so nothing overflows or underflows and there are no
subnormals.  It has `NaN` and `±∞` but no negative zero.  Every function takes
a precision and a rounding mode (`Floor`, `Ceiling`, `Down`, `Up`, `Nearest`
with ties to even) and returns the rounded result together with an `Ordering`
that compares it with the exact value.

Each function is specified as the rounding of its exact real value, and the
implementation is proven *equal* to that specification, not merely close to it:

```lean
theorem expPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    expPrecRound x p mode = liftVal Spec.exp x p mode
```

What is implemented, for most functions with both float and rational
arguments:

- **Arithmetic.** Sums, products, quotients, fused multiply-add, sums of
  products, square and cube roots, reciprocal square root, integer powers,
  remainder, rounding to an integer, decimal and hexadecimal conversion.
- **Elementary functions.** `exp`, `ln`, logarithms and powers in arbitrary
  bases, with the `expm1`- and `log1p`-style variants; the trigonometric,
  hyperbolic and inverse functions, including the forms with a period
  (`sin (π x)`, `atan2`, and so on).
- **Special functions.** `Γ`, `1/Γ`, `ln Γ`, `ψ` and its zeros, polygamma, Beta,
  Pochhammer symbols, the Barnes `G`-function, the `q`-gamma and `q`-beta
  functions, the arithmetic–geometric mean, Lambert `W`, the Wright `ω` and
  tree functions, the Gudermannian.
- **Constants.** `π`, `e`, `ln 2`, `φ`, Euler's `γ`, Catalan's constant, the
  Glaisher–Kinkelin, Gauss, lemniscate and omega constants, `e^π`, `2^√2`,
  `Γ(1/3)`, `Γ(1/4)` and others.
- **Machine floats.** `emulate` turns an `AzFloat` function into a correctly
  rounded function on Lean's 64-bit `Float`, subnormals included; sums,
  products and the fused operations are provided this way.
- **Intervals.** Enclosure arithmetic that the Lean kernel can evaluate, used
  to prove the numerical claims of the DLMF.

**Termination.** Correct rounding needs to know that the exact value is not a
rounding boundary, which is a statement about its arithmetic nature.  Where
that is proven, the function is total and unconditionally correct, and the
library carries the number theory this takes: the transcendence of `e`, Niven's
theorems, the quadratic case of Gelfond–Schneider (`e^π`, `2^√2`), Chudnovsky's
theorem (`Γ(1/3)`, `Γ(1/4)`), and a vendored proof of the irrationality of
Catalan's constant.  Where it is an open problem (Euler's `γ`, most values of
`Γ`), the function takes a fuel parameter with a specification (`ZivSpec`): at
every fuel the result is correctly rounded or `NaN`, and it is correctly
rounded for all large enough fuel unless the value is a rounding boundary.  The
open statements are collected in
[`docs/open_problems.md`](docs/open_problems.md).

The design notes and timings are in
[`docs/azfloat_plan.md`](docs/azfloat_plan.md).

## Getting started

Azurite builds with the Lean toolchain in [`lean-toolchain`](lean-toolchain) and
the Mathlib revision pinned in [`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get    # fetch the prebuilt Mathlib oleans
lake build            # build the library
lake test             # run the #guard test suites (AzuriteTests)
lake build benchmark  # build the benchmark executable
lake env .lake/build/bin/benchmark   # run it
lake exe examples     # certify a 247-digit prime, factor polynomials (compiled)
```

[`Examples.lean`](Examples.lean) is a guided tour: primality of large numbers,
factorization over finite fields, squarefree factorization in `ℤ[x, y, z]` and
exact linear algebra, each paired with the theorem that makes it correct.  Its
`#guard`s run when the library is built; `lake exe examples` runs the same
computations at compiled speed on inputs too large for the interpreter.

CI ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)) builds the
library, runs the tests, and checks with
[`scripts/check_axioms.lean`](scripts/check_axioms.lean) that no declaration
uses an axiom beyond the standard three.

## Layout

```
Azurite.lean          root import file (all library modules)
AzuriteTests.lean     root import file for the #guard test suites (lake test)
Examples.lean         guided tour (#guard-checked); Examples/Basics.lean, Examples/Main.lean (lake exe examples)
Azurite/
  UInt64/                        limb-level helpers with toNat semantics
  AzNat/ AzInt/ AzRat/           multi-precision naturals, integers, rationals
  AzFloat/                       arbitrary-precision floats, correctly rounded functions
  AzZMod/ AzZModPow2/ AzPolyMod/ residue rings ℤ/m, ℤ/2^k, R[x]/(f)
  AzPolynomial/ AzMvPolynomial/  polynomials in one and several variables
  AzPolynomialQ/ AzRationalFunction/ AzMvRationalFunction/
  AzVector/ AzMatrix/            vectors and matrices
  AzFormula/                     computable first-order formulas
  Algorithm/ Rounding/ Random/ ExhaustiveGenerator/   shared algorithms and test generators
  BasuPollackRoy/ GathenGerhard/ CrandallPomerance/ CohenLenstra/   formalized texts
  BrentZimmermann/ DLMF/         formalized texts behind the float functions
  Transcendental/ Chudnovsky/ Feldman/ CatalanIrrational/   irrationality and transcendence proofs
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

## Project status

Azurite is in active development and is very incomplete. A several-hundred-page blueprint exists, but I'm not releasing it yet because it isn't polished. Some major goals of the project include
- Formalizing the rest of Basu-Pollack-Roy
- Computable algebraic numbers
- A practical formally-verified CAD implementation
- Ball arithmetic on top of the float functions, and more special functions
  (Airy, Bessel, hypergeometric)
- Proofs of results in polyhedral geometry like the classification of convex regular-faced polyhedra

## License

Apache License 2.0; see [LICENSE](LICENSE).
