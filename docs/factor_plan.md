# Integer factorization: plan and ledger

Started 2026-11-26.  Goal: `AzNat.factor : AzNat → List (AzNat × Nat)` — the primes with their
(nonzero) exponents, by increasing prime — fully proven and efficient.

## Ground rules

* The high-level strategy follows the list of methods FLINT documents (trial division,
  perfect-power detection, Pollard–Brent rho, Hart's one-line method, SQUFOF, `p ± 1`, the
  elliptic curve method, the quadratic sieve).  No source code of another library is read;
  the algorithms come from the papers below.
* Theory on `ℕ` is kept apart from the code on `Az*` types; every new function on an `Az*`
  type is reported to the user (Malachite mapping).
* What is proven: the result.  A divisor is used only after three comparisons (`1 < d < n`,
  `d ∣ n`), primality is `AzNat.isPrime`, and a list of primes with product `n` is Mathlib's
  factorization.  The methods that *find* divisors are unproven searches behind
  `findDivisor`; complete trial division (`trialFactor`) is the proven last resort, which
  makes the function total.

## Sources (`~/azurite-sources`)

| Method | Source |
|---|---|
| general | Crandall, Pomerance, *Prime Numbers: A Computational Perspective*, ch. 5–7 |
| perfect powers | Bernstein, *Detecting perfect powers in essentially linear time* (1998) |
| rho | Brent, *An improved Monte Carlo factorization algorithm* (1980) |
| one-line | Hart, *A one line factoring algorithm* (2012) |
| SQUFOF | Gower, Wagstaff, *Square form factorization* (2008) |
| `p − 1` | Pollard, *Theorems on factorization and primality testing* (1974) |
| `p + 1` | Williams, *A p + 1 method of factoring* (1982) |
| ECM | Lenstra (1987); Montgomery, *Speeding the Pollard and elliptic curve methods* (1987); Zimmermann, Dodson, *20 years of ECM* (2006) |
| quadratic sieve | Pomerance (1984); Silverman, *The multiple polynomial quadratic sieve* (1987); Montgomery, *A block Lanczos algorithm…* (1995); for self-initialization the walkthrough at programmingpraxis.com/2013/03/19/quadratic-sieve/ (Contini's thesis not at hand) |

## Steps

1. **Proven skeleton — DONE 2026-11-26.**
2. **Pollard–Brent rho — DONE 2026-11-26** (untimed).
3. Hart's one-line method, SQUFOF.
4. `p − 1`, `p + 1`.
5. ECM.
6. Quadratic sieve.

After each step: timings on semiprimes of growing size, to place the hand-over points.

## 2026-11-26 — perfect powers

`AzNat/PerfectPower.lean`, `AzNat/Equiv/PerfectPower.lean`, theory
`Bernstein/PerfectPower.lean`: `isPerfectPower`, `expressAsPower` (2-adic variant, Bernstein
§21–§22).  Proven: `isPerfectPower_eq_true_iff`, `expressAsPower_eq_some`,
`expressAsPower_eq_none_iff`.  The Newton iterations are hints; the candidate root is tested
and `odd_root_unique` makes it the only possible one.  Untimed (`benchmark perfect_power`).

## 2026-11-26 — step 1, the skeleton

`AzNat/Factor.lean`, `AzNat/Equiv/Factor.lean`.

* `factor n = groupRuns (mergeSort (primeFactorList n))`.
* `primeFactorList`: `[]` for `n ≤ 1`; `trialDivide` (the primes up to `trialBound = 4096`,
  one division of `n` per prime: `trialDivideBy`, `pullOut`), then `splitFactors` on the
  cofactor.
* `splitFactors find fuel n`: `[n]` if `isPrime n`; the factors of `x`, each `k` times, if
  `expressAsPower n = some (x, k)`; those of `d` and `n / d` if `find n = some d` passes the
  check; `trialFactor n` otherwise and when the fuel (the bit length) runs out.
* `trialFactor`: complete trial division by `2, 3, 4, …` up to the square root (well-founded
  recursion on `n + (n − d)`).
* `findDivisor _ = none` for now.
* Proven: `trialFactor_spec`, `trialDivide_spec`, `splitFactors_spec` (for every `find`),
  `primeFactorList_perm`, `sorted_primeFactorList`, `groupRuns_expand/pos/key_mem/sorted`,
  **`factor_expand`** (the factorization written out is `Nat.primeFactorsList n.toNat`),
  `factor_prime`, `factor_pos`, `factor_sorted`, **`factor_exponent`**
  (`e = n.toNat.factorization p.toNat`), `factor_prod`.
* Known to be slow until step 2: a composite cofactor with two prime factors above 4096
  goes to complete trial division.  Trial division by the small primes is one division each
  (to be replaced by a remainder tree or a product–gcd as in the ECPP generator).

### New functions on `Az*` types

`AzNat.factor`, `primeFactorList`, `splitFactors`, `findDivisor`, `trialDivide`,
`trialDivideBy`, `pullOut`, `trialFactor`, `trialFactor.go`, `groupRuns`, `trialBound`;
perfect powers: `isPerfectPower`, `expressAsPower`, `perfectPowerStep`, `primeRoot?`,
`oddRoot?`, `kthRoot?`, `powModPow2`, `subLow`, `invModPow2Hint`, `rootHint`.

## 2026-11-26 — step 2, Pollard's rho method with Brent's cycle finding

`AzNat/PollardRho.lean` (a search: nothing proven, nothing needed).

* `rhoBrent n c x₀ batch budget`: Brent's algorithm `P₂″` (BIT 20 (1980), §7) for
  `f(y) = y² + c`: `x = y_r` for `r = 1, 2, 4, …`, the differences `x − y_k` for
  `3r/2 ≤ k < 2r` multiplied together modulo `n`, one gcd per `batch` of them, and the
  batch gone through again term by term when the gcd is `n`.  Returns the divisor and the
  number of terms computed.  In Montgomery form throughout (`MontCtx`: the map becomes
  `y² R⁻¹ + c`, and the unit factors `R⁻¹` do not change the gcd).
* `pollardRho n tries budget`: `c = 1, …, tries`, `x₀ = 2`, `rhoBatch = 128`.
* `findDivisor n = pollardRho n 16 rhoBudget`, `rhoBudget = 2^36` terms per constant —
  generous on purpose: until ECM and the sieve exist there is nothing to hand over to, and
  the alternative is complete trial division.  To be bounded by size once they do.
* Expected cost about `3.1 √p` multiplications modulo `n` for the smallest prime factor `p`
  (Brent (7.1)); not yet measured here.
* Benchmark: `benchmark factor <max digits per prime>` (products of two primes of 4 to 12
  digits, and a few other shapes).
* To do when timed: a one-word path (`n < 2^64`, native `UInt64` Montgomery arithmetic) if
  the `AzNat` overhead per term shows; the hand-over to SQUFOF / ECM.
* New functions on `Az*` types: `AzNat.absDiff`, `rhoNext`, `rhoBrent`, `pollardRho`,
  constants `rhoBatch`, `rhoBudget`.

## 2026-11-27 — first timings (compiled, quiet machine)

**Perfect powers** (`benchmark perfect_power 30000`; ms; 2-adic `isPerfectPower` / one
`isPow` per prime exponent):

| bits | odd, not a power | `· 2^30`, not a power | a 7th power | a square |
|---|---|---|---|---|
| 64 | 0.092 / 0.171 | 0.015 / 0.256 | 0.022 / 0.023 | 0.007 / 0.005 |
| 256 | 0.273 / 0.746 | 0.020 / 0.840 | 0.038 / 0.056 | 0.017 / 0.015 |
| 1024 | 1.06 / 3.90 | 0.040 / 3.99 | 0.070 / 0.131 | 0.038 / 0.045 |
| 4096 | 4.71 / 36.1 | 0.084 / 36.3 | 0.218 / 0.627 | 0.133 / 0.200 |
| 10000 | 17.6 / 242 | 0.260 / 244 | 0.589 / 2.36 | 0.339 / 0.762 |
| 30000 | 185 / 3859 | 1.81 / 3890 | 3.03 / 18.5 | 1.37 / 4.75 |

2–21× faster on odd non-powers, 17–2100× when a power of two divides `n` (few exponents
to try).  But the odd case is not linear: about 5 µs per prime exponent at 64 bits and
57 µs at 30000 bits (3245 exponents).  The time is in the many large exponents, whose roots
have a few bits: each still costs some 250 `AzNat` operations on one-limb numbers (Newton
levels, each with a power).  To do: a one-word path (`UInt64`, wrapping arithmetic) for
`2⌈f/p⌉ ≤ 64`, which is all `p ≥ f/32`.

**Factorization** (`benchmark factor 9`; products of two primes of `d` digits; ms, of which
primality of the two factors):

| `d + d` digits | bits | time | primality |
|---|---|---|---|
| 4 + 4 | 24–25 | 0.05–0.24 | 0.002–0.005 |
| 5 + 5 | 31–32 | 0.93–1.68 | 0.007–0.015 |
| 6 + 6 | 38 | 0.11–0.63 | 0.02–0.04 |
| 7 + 7 | 44–45 | 0.16–1.31 | 0.07–0.14 |
| 8 + 8 | 51–52 | 0.33–3.19 | 0.23–0.50 |
| 9 + 9 | 57–58 | 1.75–27.7 | 0.9–1.6 |

(the low figure of each row is a square of a prime, found by `expressAsPower`).  Others:
`30!` 0.019; `10^40 + 1` 15.2; `2^64 + 1` 2.03; `(10^9 + 7)^5` 1.21;
`2^101 − 1 = 7432339208719 · 341117531003194129` 2455.

Reading:

* Rho costs about 290 ns per term (two Montgomery products on two-limb numbers, about
  150 ns each): `2^101 − 1` needs `≈ 3.1 √p ≈ 8.5 · 10^6` terms.  A one-word path would be
  an order of magnitude faster for `n < 2^64`, where rho does most of its work.
* At 31–32 bits the time is `isPrime n` itself on the composite input: up to 32 bits it is
  `isPrimeNaive` (trial division by the odd numbers up to `√n`, on `AzNat`), about 1 ms.
  The same shows in the primality column: a 9-digit prime costs 0.5–0.8 ms to prove.
* Trial division by the 564 primes up to 4096 is one `AzNat` remainder each (tens of µs in
  all), visible at the smallest sizes.

## 2026-11-27 — the one-word layer

Written while the machine was busy: **not timed yet** (`benchmark factor`,
`benchmark perfect_power` to be repeated).

* **`AzNat/IsPrimeWord.lean`** — `isPrimeWord n : Option Bool`, `trialOddWord`: trial
  division of `n < 2^32` by `2` and the odd numbers up to `√n` in `UInt64` arithmetic.
  Proven (`Equiv/IsPrimeWord.lean`): `isPrimeWord_eq_some`
  (`= some b → (b = true ↔ Nat.Prime n.toNat)`).  `AzNat.isPrime` uses it up to 32 bits
  (`isPrimeNaive` only if it returned `none`, which it does not below `2^32`);
  `isPrime_eq_true_iff` unchanged in statement.
* **`AzNat/FactorWord.lean`** (namespace `AzNat.Word`, nothing proven) — `mulHi`, `mulMont`
  (Montgomery product modulo an odd `n < 2^63`, `R = 2^64`), `addMod`, `montOne`, `montR2`,
  `powMont`, `millerRabinRound`, `isProbablePrime` (twelve bases), `absDiff`, `rhoBrent`
  (Brent's `P₂″`, 64 differences per gcd), `sqrtWord`, `smallPrimes` (up to 1024),
  `splitWord`, **`factorWord n : Option (List UInt64)`**: trial division to 1024, cofactors
  below `2^20` are prime, otherwise Miller–Rabin, a square test, rho with
  `c = 1, 2, 3, 5, 7, 11` and `2^22` terms each; `none` when something is not split.
* **`AzNat/Factor.lean`** — `listProd`, `checkFactors n l` (product `= n`, all `isPrime`),
  `factorHint n` (`factorWord` for `n < 2^63`), `hinted n slow` (the proposal if it passes
  the check, the slow path otherwise); used at the top of `primeFactorList` and of every
  step of `splitFactors`, so every cofactor below `2^63` goes to machine words.  Proven:
  `checkFactors_spec`, `hinted_spec`; the main theorems are unchanged.
* **Perfect powers** — `lowBitsWord`, `powWord` (`r^k mod 2^64`), `invWordHint`,
  `rootWordHint`, **`oddRootWord?`**: the test of `oddRoot?` in `UInt64` when
  `2⌈f/p⌉ ≤ 64`, chosen by `primeRoot?`.  Proven: `toNat_lowBitsWord`, `toNat_powWord`,
  `oddRootWord?_spec`.
* No `native_decide`, no `@[extern]`: `UInt64` here is Lean's own type, and the proofs use
  the core lemmas (`UInt64.toNat_mul`, `toNat_mod`, …).
* Still on `AzNat`: primality of primes between `2^32` and `2^64` (Miller–Rabin + APR-CL,
  milliseconds) — a candidate for an `n − 1` certificate found with `factorWord`; trial
  division of large `n` by small primes (one division each).

## 2026-11-27 — timings with the one-word layer (quiet machine)

**Factorization** (`benchmark factor 9`; ms; before = the table above):

| `d + d` digits | bits | before | now | primality now |
|---|---|---|---|---|
| 4 + 4 | 24–25 | 0.05–0.24 | 0.003–0.060 (the first call of the process) | ≤ 0.001 |
| 5 + 5 | 31–32 | 0.93–1.68 | 0.003–0.012 | ≤ 0.001 |
| 6 + 6 | 38 | 0.11–0.63 | 0.004–0.035 | 0.001 |
| 7 + 7 | 44–45 | 0.16–1.31 | 0.022–0.078 | 0.001–0.003 |
| 8 + 8 | 51–52 | 0.33–3.19 | 0.029–0.214 | 0.004–0.007 |
| 9 + 9 | 57–58 | 1.75–27.7 | 0.036–0.52 | 0.009–0.022 |

Two 9-digit primes: 16–28 ms → 0.46–0.52 ms.  `(10^9 + 7)^5`: 1.21 → 0.25.  Unchanged, as
expected, where the cofactor to split has more than 63 bits: `10^40 + 1` 15.4,
`2^101 − 1` 2530 (rho on `AzNat`), `2^64 + 1` 1.97 (1.2 of it the APR-CL proof of the
47-bit prime).  `30!` went from 0.019 to 0.12–0.14: not understood; it is now the first
number of the run to go through `trialDivide`, so possibly a cold start — to check.

**Perfect powers.**  The first rerun was disappointing at large sizes (30000 bits: 185 →
171 ms).  `benchmark perfect_power (10^9 + bits)` (new: the time by ranges of the exponent)
showed 167 ms in the 3087 exponents of the machine-word path: for these `b = ⌈f/p⌉` is
one or two bits, the comparison on `2b` bits let a quarter of the candidates through, and
each then cost a full power `r^p`.  `oddRootWord?` now compares on all 64 bits (the word
power is at hand).  After that (odd, not a power; ms; first version / now / one `isPow` per
exponent):

| bits | first version | now | by roots |
|---|---|---|---|
| 64 | 0.092 | 0.025 | 0.23 |
| 256 | 0.273 | 0.067 | 0.76 |
| 1024 | 1.06 | 0.24 | 3.97 |
| 4096 | 4.71 | 0.88 | 37.4 |
| 10000 | 17.6 | 2.11 | 246 |
| 30000 | 185 | 8.24 | 4011 |
| 100000 | — | 51.0 | — |

At 30000 bits by ranges of the exponent: `3`: 1.2 ms; `5, 7`: 0.9; `11 … 31`: 0.9;
`37 … 929` (147 primes, `AzNat` path): 2.8; `937 …` (3087 primes, machine words): 2.0;
the inverse hint 0.35.  No wrong candidate anywhere (the `rootInt` fallback is not taken).

## 2026-11-27 — rho in two machine words

`AzNat/RhoTwoWord.lean` (namespace `AzNat.TwoWord`, nothing proven): for an odd `n` of 65
to 126 bits, residues in two `UInt64` words, Montgomery product with `R = 2^128`
(`mulMont`: the four-word product, two clearing rounds, `reduce`), `addMod`, `absDiff`,
`next`, and the loops as recursions on words (`advance`, `batch`) so that a term allocates
nothing; `rhoBrent n c batchSize budget` drives them, with one `AzNat` gcd per batch.
`pollardRho` uses it for 65–126 bits and the `AzNat` version elsewhere.  Guards check
`mulMont` against its definition (`r · 2^128 ≡ a b`, `r < n`) on 400 moduli.
**Not timed** (the machine was busy): compare `2^101 − 1` (2.53 s before) and `10^40 + 1`
with `benchmark factor 9`.
New functions: `TwoWord.reduce`, `mulMont`, `addMod`, `absDiff`, `next`, `advance`, `batch`,
`toAzNat`, `rhoBrent`.

### Timed 2026-11-27 (quiet machine, `benchmark factor 13`)

* `2^101 − 1 = 7432339208719 · 341117531003194129`: 2530 → **152 ms** (about 17 ns per
  term against 290).  `2^64 + 1`: 1.97 → 1.36 ms (1.14 of it primality).  `10^40 + 1`
  (133 bits, still on `AzNat`): 13.8 ms.
* Products of two primes of `d` digits (ms, of which primality):

  | `d + d` | bits | time | primality |
  |---|---|---|---|
  | 10 + 10 | 64–65 | 2.3–3.8 | 1.1–1.2 |
  | 11 + 11 | 71–72 | 11.6–13.0 | 1.8–2.0 |
  | 12 + 12 | 77–78 | 33–39 | 1.8–8.3 |
  | 13 + 13 | 84–85 | 65–82 | 1.8–9.4 |

  (squares of primes: 0.9–5.1 ms, nearly all of it primality.)
* Found on the way: a number of exactly 64 bits fell between the paths (`factorWord` takes
  `n < 2^63`, the two-word rho took 65 bits and more) and cost 38 ms on `AzNat`; the
  two-word rho now starts at 64 bits (3.8 ms).
* Primality is now a visible share: the proof of a prime of 33 to 44 bits by Miller–Rabin
  and APR-CL costs 1–9 ms, more than finding it up to about 11 digits.  A certificate from
  the factorization of `n − 1` (which `factorWord` gives at once) is the natural remedy.

## 2026-11-27 — primality of one-word primes by the factorization of `n − 1`

`AzNat/IsPrimeLucas.lean`, `AzNat/Equiv/IsPrimeLucas.lean`.  **Not timed yet.**

* `lucasHint n` (machine words, not verified): `2 ::` the factors of `(n − 1)/2` from
  `Word.factorWord`, and the first of twenty small primes `a` with `a^((n−1)/q) ≠ 1` for
  every prime `q ∣ n − 1` (`Word.powMont`).
* `lucasCheck n a l` (on `AzZMod n`): `listProd l = n − 1`, `a^(n−1) = 1`,
  `a^((n−1)/q) ≠ 1` for the distinct `q` of `l`.
* `lucasCertified fuel n`: up to 32 bits `isPrimeWord`; up to 63 bits the hint, the check,
  and the certification of every `q` (fuel 40 from `isPrime`: each level at least halves).
* Proven: `lucasCheck_prime` (with Mathlib's `lucas_primality`), **`lucasCertified_prime`**
  (`= true → Nat.Prime n.toNat`), `toNat_listProd`, `isPrimeWord_toUInt64`.
* `isPrime`, 33–80 bits: `(size ≤ 63 ∧ Word.isProbablePrime ∧ lucasCertified 40) ∨
  (millerRabin ∧ aprclOrEcpp)` — the machine-word probable-prime test only decides whether
  the certificate is attempted, so that composites do not pay for a factorization of
  `n − 1`; `isPrime_eq_true_iff` unchanged in statement.
* Not covered: numbers of exactly 64 bits (the machine-word arithmetic needs `n < 2^63`),
  and 65–80 bits (two words): still Miller–Rabin and APR-CL.
* `listProd` moved here from `Factor.lean`.
* New functions: `AzNat.lucasHint`, `lucasCheck`, `lucasCertified`, `listProd`.
