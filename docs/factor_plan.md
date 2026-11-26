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
2. Pollard–Brent rho.
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
