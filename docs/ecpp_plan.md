# Elliptic curve primality proving (fastECPP): plan and ledger

Started 2026-11-23.  Target: a computable, proven primality test by elliptic curves, in the
asymptotically fast form (fastECPP), following the pattern of the APR-CL work
(`docs/aprcl_implementation_plan.md`): a certificate generator that is not proven, and a
certificate checker that is.

```lean
def ecppCheck (n : AzNat) (cert : EcppCertificate) : Bool
theorem ecppCheck_sound : ecppCheck n cert = true → n.toNat.Prime
def ecppGenerate (n : AzNat) : Option EcppCertificate     -- no theorem beyond termination
```

## Ground rules (user, 2026-11-23)

* **Theory and implementation are kept apart.**  The mathematics (curves over fields and
  over `ℤ/Nℤ`, the Hasse bound, the primality criterion) is stated and proven on Mathlib
  objects, in its own directory, with no `Az*` type in it.  The computable code on `Az*`
  types lives elsewhere and is connected to the theory by equivalence theorems, as for every
  other `Az*` algorithm.
* **Every new function on an `Az*` type is reported to the user** when it is added (for the
  Malachite mapping pages).  The running list is at the end of this file.
* Complex floating point, when the class polynomials need it: components correctly rounded
  (user, 2026-11-23); the type and its field operations first, functions later.

## Sources

| Source | Status | Used for |
|---|---|---|
| F. Morain, *Implementing the asymptotically fast version of the elliptic curve primality proving algorithm*, Math. Comp. 76 (2007) | read 2026-11-23 (`~/azurite-sources/fastecpp-final.pdf`, 11 pages) | the structure of the generator (§4 Step 1′, §5) |
| A. O. L. Atkin, F. Morain, *Elliptic curves and primality proving*, Math. Comp. 61 (1993) | user has it; **not needed** (decided 2026-11-23) | the criterion is proven directly; the curve from a root of the class polynomial and the twists are standard and unproven (generator); §8.4.3, §8.6.3 are optimizations |
| J. S. Chahal, B. Osserman, *The Riemann hypothesis for elliptic curves*, Amer. Math. Monthly 115 (2008) 431–442 | read 2026-11-23 (`~/azurite-sources/chahal-osserman.pdf`) | **the proof of the Hasse bound** (Manin's), §4 |
| A. W. Knapp, *Elliptic Curves* (1992), §X.3 (pp. 296–301) | read 2026-11-23 (`~/azurite-sources/knapp-elliptic-curves.pdf`, PDF pages 312–317) | **the complete proof of the Hasse bound over `𝔽_p`** (Manin's): Lemma 10.7 (the point count), Lemma 10.8 (the Basic Identity, with its proof) |
| J. S. Chahal, *Manin's proof of the Hasse inequality revisited*, Nieuw Arch. Wiskd. 13 (1995) | not needed (Knapp has the proof) | |
| Franke, Kleinjung, Morain, Wirth, *Proving the primality of very large numbers with fastECPP*, ANTS VI (2004) | not yet seen | extraction of small factors from many `m` at once, early abort (Morain §5.3) |
| A. Enge, class polynomials by floating point approximations; Enge–Morain on invariants | not yet seen | Step 2 at scale |
| Crandall–Pomerance, *Prime Numbers*, Ch. 7 | user has the book | pseudocode for curve arithmetic and Cornacchia, as a cross-check |

## Inventory of Morain 2007

| § | Content | Layer | Notes |
|---|---|---|---|
| 2 | fundamental discriminants `−D = ∏ q*ᵢ`, genera, class number, splitting of `p` ⇔ `4p = U² + DV²` | generator (unproven) | only the *definitions* are needed; the splitting theorem is not, since the checker checks |
| 3.1 | curves over `ℤ/Nℤ`, pseudo-addition, division polynomials, Theorem 3.1 (`ψ_m(P) = 0` ⇔ `[m]P = O`), **Proposition 3.1** (the criterion for `m = 2N′`) | theory | Morain states the simplified criterion "compare [27]" (Goldwasser–Kilian) and proves it from Hasse.  Mathlib has division polynomials (definitions, degrees) but not Theorem 3.1, to my knowledge; it does have the group law over a field and `map` lemmas for the projective and Jacobian addition formulas over rings.  **Plan: state the criterion with scalar multiplication in Jacobian or projective coordinates, not with `ψ_m`** — the reduction mod `p` is then Mathlib's `map_addXYZ`/`map_dblXYZ`. |
| 3.2 | the algorithm, Steps 1–5 | generator | |
| 3.4 | finding a point: smallest `x` with `x³ + ax + b` a non-zero square, then a square root mod `N` | generator | `AzZMod.sqrt?` exists |
| 3.5 | `H_D(X) = ∏ (X − j((−B + √−D)/(2A)))` over reduced forms, height `≈ π√D ∑ 1/A` | generator | complex floating point (see ground rules) |
| 3.6 | a root of `H_D` mod `N` by Cantor–Zassenhaus splitting | generator | `GathenGerhard` Ch. 14 is formalized and implemented for prime fields; here the modulus is only a probable prime |
| 3.7 | `√−D mod N`, Cornacchia, test `m = 2N′` | generator | |
| 4.1 | **Step 1′**: the `r` smallest primes `q` with `(q*/N) = 1`, their square roots, discriminants as products | generator | the fast variant; this loop is written first, not the plain one |
| 4.2 | subsets instead of pairs; fundamental discriminants only | generator | |
| 5.1 | class numbers (Louboutin's formula) | generator | enumeration of reduced forms first |
| 5.2 | Cornacchia with a single-precision cofactor recurrence and a final check | generator | first version without the single-precision trick |
| 5.3 | `m = cN′` with `c` `B`-smooth; sieving by `(N + 1) mod pᵢ` and `U mod pᵢ`; early abort `N/N′ ≥ 2^δ`; other invariants; Galois decomposition of `H_D` | generator | the criterion must therefore be the general one (cofactor `c`), from Atkin–Morain |
| 5.4 | how many discriminants: until `∑ g/h ≈ t/2`; order by `(h/g, h, D)` | generator | |
| 6 | timings: 1000 digits in 334 s, 2000 in 5557 s (2.4 GHz Athlon 64) | — | reference for our benchmarks |

## Inventory of the proof of the Hasse bound (Knapp §X.3; Chahal–Osserman §4)

Setting (Knapp): `p > 3`, `E : y² = x³ + ax + b` over `𝔽_p`; over `K = 𝔽_p(x)` the cubic
(10.13) `Y² = (X³ + aX + b)/(x³ + ax + b)` with the points `(x, 1)` and
`(x^p, (x³ + ax + b)^((p−1)/2))`; `Z_n = (x^p, …) + n (x, 1)` (10.14); `d_n = 0` if
`Z_n = ∞`, else **`max(deg num X_n, deg den X_n)`** in lowest terms.  (Chahal–Osserman take
the degree of the numerator only; Knapp's height needs no side condition on the degrees and
is the one formalized.)

| Item | Content | Status |
|---|---|---|
| the curve | in Weierstrass form over `K`: `y′² = x′³ + aλ² x′ + bλ³` with `λ = x³ + ax + b`, `x′ = λX`, `y′ = λ²Y`, so that Mathlib's group law applies | **DONE** `twist`, `lam`, `basePt`, `negBasePt`, `ptHeight` (`Theory/ManinCurve.lean`, over any field with `2 ≠ 0`, `4a³ + 27b² ≠ 0`) |
| Lemma 10.7 | `d_0 = p`, `d_{−1} − d_0 − 1 = #E(𝔽_p) − p − 1`: (10.16) `X_{−1} = −x − x^p + (1 + λ^((p−1)/2))² λ/(x − x^p)²`; the numerator has degree `2p + 1`; `x^p − x = ∏ (x − j)`; the factor `x − j` survives in the denominator twice, once or not at all as `λ(j)` is a residue, `0` or a non-residue | **DONE 2026-11-23** `Theory/ManinCount.lean` (`countNum`, `expG`, `expR`, `pow_expG_dvd`, `not_pow_succ_dvd`, `prod_X_sub_C_eq`, `natDegree_countNum`, **`rfHeight_countNum`**) and `Theory/ManinHasse.lean` (`startPt`, `ptHeight_startPt`, `ptHeight_startPt_sub`, `card_sq_eq`, `card_point`) |
| Lemma 10.8 | **Basic Identity** `d_{n−1} + d_{n+1} = 2 d_n + 2`.  Degenerate cases: `Z_n = ∞` (`1 + 1 = 0 + 2`), `Z_{n∓1} = ∞` (`0 + 4 = 2 + 2`, with `X(2(x, 1)) = ((x² − a)² − 8bx)/(4λ)`).  Generic case: (10.18)–(10.20) | **DONE 2026-11-23** **`ptHeight_sub_add`** — for *every* point `Z` of the twisted curve, `h(Z − (x, 1)) + h(Z + (x, 1)) = 2 h(Z) + 2`.  Pieces: `twist_sum_prod` ((10.19), (10.20) as field identities), `rfHeight_add_of_relations` (`Theory/ManinHeight.lean`: the identity for rational functions, no curve), `twist_dbl`, `isCoprime_dbl`, `ptHeight_dbl_basePt`, `rfHeight_div_of_coprime` |
| (10.21)–(10.22) | `BD = (Qx − P)²` up to a unit | **DONE** `exists_unit_of_relations`, `isUnit_of_dvd_forms` (`Theory/ManinAlgebra.lean`).  **Knapp's text has a gap here**: it writes `AC = S N₁`, `BD = S M` with `S = gcd(AC, BD)`, which presumes `gcd(N₁, M) = 1`; a common prime factor of `Qx − P` and `(x² − a)² − 8bx` is not excluded.  The formalized argument uses `N₂` as well: no prime divides `N₁`, `N₂` and `M`, because modulo a prime factor of `Qx − P` they are `Q² g` and `2Q² f`, and `(3x² + 4a) g − (3x³ − 5ax − 27b) f = 4a³ + 27b²` |
| cases (a)–(d) | the degrees | **DONE**, differently: `height_add_height` (`max(deg A, deg B) + max(deg C, deg D) = max(deg AC, deg BD, deg(AD + BC))`) and `max_natDegree_forms` (the largest degree of `N₁`, `N₂`, `M` is `2 max(deg P, deg Q) + 2`) |
| (10.25) | `d_n = n² − (d_{−1} − d_0 − 1) n + d_0` | **DONE** `degree_quadratic` (`Theory/Manin.lean`) |
| **Theorem 10.5** | **the Hasse bound** | **DONE 2026-11-23: `hasseBound : HasseBound`** (`Theory/ManinHasse.lean`, `hasse_short`) |
| conclusion | discriminant `≤ 0` | **DONE** `sq_le_of_quadratic_nonneg`, `sq_le_of_degree`, `prime_ne_mul_succ` (Knapp argues with two consecutive `d_n` not both `0`; here: `p ≠ n(n + 1)`) |

## Layers

1. **Theory** (Mathlib objects only): `Azurite/ECPP/Theory/`, namespace `Azurite.ECPP`.
   **DONE 2026-11-23: the criterion and the Hasse bound, so soundness is unconditional**
   (`Theory/Soundness.lean`: `EcppStep.isPrime`, `EcppProof.isPrime`).
   * `Theory/Chain.lean`: `MulChain W U k T` — the Jacobian triple `T` over a commutative
     ring is obtained from `U` along a computation of `k · U` by Mathlib's formulas
     `dblXYZ`, `addXYZ`, with **the `Z`-coordinate `addZ` of every addition a unit**, up to
     changes of representative.  `MulChain.toAffine`: under a ring homomorphism to a field
     where `U` is a nonsingular point, `T` is the point `k • U` (Mathlib's
     `Jacobian.Point.toAffine`, `toAffine_add`, `map_addXYZ`, `map_dblXYZ`).  The doubling
     formula is complete; the addition formula is right exactly when `addZ ≠ 0`.
   * `Theory/Hasse.lean`: `shortW a b` (`y² = x³ + ax + b`), `HasseBound : Prop` —
     `(#E(𝔽_p) − (p + 1))² ≤ 4p` for every such curve with `4a³ + 27b² ≠ 0` over `𝔽_p`,
     `p ≥ 5` (the setting of Chahal–Osserman); `finite_point`.  The statement; proven as
     `hasseBound` in `Theory/ManinHasse.lean`.
   * `Theory/Manin.lean`: the arithmetic end of the proof; `Theory/ManinAlgebra.lean`: the
     polynomial algebra of the Basic Identity (see the inventory above).
   * `Theory/Criterion.lean`: **`prime_of_point_of_order`** — `N > 1` coprime to `6`, a curve
     `y² = x³ + ax + b` over `ℤ/Nℤ` with `4a³ + 27b²` a unit, a solution `(u, v)`, a prime `q` with `⌊√N⌋ + 1 < q` and
     `4⌊√N⌋ < (q − ⌊√N⌋ − 1)²` (the integer form of `q > (N^(1/4) + 1)²`), and a chain
     `V = (q − 1)·(u, v)` with `Z_V` a unit and `V = −(u, v)`: then `N` is prime.
     `EcppStep N q`, `EcppProof N`, `EcppProof.prime`.
   * **Form of the criterion: a point of order `q`.**  The curve order `m`, the cofactor
     and the point `P₀` with `(m/q)·P₀ = (u, v)` are the search's business; the certificate
     carries `(u, v)` itself.  The checker then does one scalar multiplication by `q − 1`
     and compares with `−(u, v)` — no "`[m]P = O` by the formulas", which the incomplete
     addition formula cannot certify (a zero `Z` may also come from adding equal points).
   * Nothing is left to do in this layer.
2. **Implementation on `Az*` types** — **done 2026-11-23**.
   * `Theory/Ladder.lean` (still Mathlib objects only): the specification of the scalar
     multiplication — `dblShort`, `addShort`, `addZShort` (Mathlib's `dblXYZ`, `addXYZ`,
     `addZ` on the short curve with second point `(u, v, 1)`, as explicit expressions),
     `OnCurve`, `addMixed` (the usual mixed addition), `addMixed_eq_smul` (on the curve it
     is Mathlib's representative scaled by the unit `−Z`), `onCurve_dblShort`,
     `onCurve_addMixed`, `ladder`, `ladder_chain`, `ecppStep_of_ladder`.
   * `Curve.lean`: `JacPoint`, `jacDbl`, `jacAddMixed`, `jacMul` over `AzZMod n`;
     `Equiv/Curve.lean`: they are the specification through `AzZMod.toZMod`.
   * `Check.lean`: `StepCert`, `checkStep`, `check`; the chain ends with `AzNat.isPrimeAprcl`
     (the APR-CL test, called `AzNat.isPrime` until 2026-11-26).
     `Equiv/Check.lean`: **`check_prime : check n cert = true → Nat.Prime n.toNat`**.
   * **The addition (changed 2026-11-23, after the first timings).**  The first version used
     Mathlib's representative (`Z₃ = X − uZ²`, some 35 multiplications) with a separate
     product of the additions' `Z`.  Now the usual mixed addition (11 multiplications,
     `Z₃ = ZH`): the three polynomial identities it needs hold modulo the curve equation,
     with small cofactors (`linear_combination`), the ladder carries `OnCurve` along, and
     the final `Z` is itself the product of all the steps' `Z`-factors, so one gcd of it
     certifies everything.  A windowed or NAF multiplication is still open.
   * Tests `Tests/Check.lean`: certificates made outside the library (point counting for a
     small curve; curves `y² = x³ + ax` for 12, 30 and 60 digits), and rejections.
3. **Generator** (unproven) — **first version done 2026-11-23**, in `ECPP/Gen/`.
   * `Forms.lean`: reduced forms, class numbers, fundamental discriminants and their prime
     discriminants, `discriminantTable` (small `Nat` arithmetic).
   * `ClassPoly.lean`: `hilbertClassPoly D` by `AzComplexFloat` — `q = e^(2πiτ)`, the
     pentagonal series for `∏ (1 − qⁿ)`, `f = Δ(2τ)/Δ(τ)`, `j = (256f + 1)³/f`, conjugate
     roots paired into real quadratic factors, coefficients accepted only near integers.
   * `Modular.lean`: `AzZMod.inv?`, `sqrtSmall?`, `cornacchia4`, `smallPrimes`,
     `trialDivide`, `polyOfInts`, `rootOfSplitPoly`.
   * `Search.lean`: `findStep` (Morain's Step 1′ with a cache of `√q*` shared by all `D`,
     Cornacchia, trial division, curve from `j` or the `D = 3, 4` families, point and
     `checkStep`), `genChain` (down to `baseBits` bits, with backtracking),
     **`ecppCertificate`**, **`provePrime`**; `Equiv/Search.lean`: **`provePrime_sound`**.
   * `GenParams` defaults: `dMax 2000`, `hMax 24`, `trialBound 2^24` (largest; about `bits^2.7 / 64` is used for each `n`), `batch 16`, `trialExtra 0`, `baseBits 64`, and
     `tiers 2` — when no step is found for some `n` the discriminant set and the trial bound
     are enlarged (×4, class number ×2) up to twice (`GenParams.tierTables`,
     `findStepTiers`).  Without the tiers about one prime in three of 100–200 digits got no
     certificate (a level with some 70 smooth orders and no prime cofactor).
   * **Timed 2026-11-23** (`benchmark ecpp <limit> "digits:D"`, three probable primes above
     `10^D`, compiled; `"…,parts:1"` times the pieces, `"…,trace:1"` follows the chain):

     | digits | steps | generator | checker | `AzNat.isPrime` (APR-CL) |
     |---|---|---|---|---|
     | 20 | 1 | 5 ms | 2–5 ms | 3–15 ms |
     | 30 | 2–4 | 11–17 ms | 3–14 ms | 5–33 ms |
     | 50 | 6–13 | 45–91 ms | 9–15 ms | 192–274 ms |
     | 75 | 9–12 | 100–153 ms | 19–29 ms | 540–1061 ms |
     | 100 | 16–22 | 0.29–0.54 s | 52–83 ms | 1.02–2.02 s |
     | 150 | 23–30 | 0.92–4.2 s | 0.18–0.27 s | 5.3–6.1 s |
     | 200 | 40–44 | 2.4–5.1 s | 0.51–0.57 s | 12.0–13.5 s |
     | 250 | 54–64 | 10.0–21.9 s | 1.4–1.5 s | 26.7–27.7 s |
     | 300 | 55–67 | 20.1–28.7 s | 2.0–2.3 s | 48.5–51.8 s |

     This is the third run (packed powers in the root finding, shared square-root cache,
     twists for `D = 3, 4`; APR-CL column from the second run).  The second run had the
     generator at 26.8–35.7 s for 300 digits, the first at 34–44 s.  Profile of the third
     run at 300 digits (20.0 and 23.4 s): square roots 23 / 32 %, roots of class
     polynomials 35 / 26 %, curves 20 / 18 %, probable-prime tests 16 / 18 %.
     About the second run:
     It had the mixed addition, one Miller–Rabin round in
     `probablePrime` and `tryCurve` giving up at the first failed check.  The first run
     (Mathlib's addition, five rounds) had the checker at 3.4–3.7 s and the generator at
     34–44 s for 300 digits: the checker gained a factor 1.4–1.8, the generator 1.2–2.
     Generator + checker is ahead of APR-CL from 50 digits on (about 1.5 times at 300
     digits); its variance is large (the search), APR-CL's is small.  Checking a certificate
     is 15–25 times cheaper than APR-CL.  Pieces at 100 / 300 digits: `probablePrime`
     0.5 / 7.6 ms, trial division of one `m` 0.3 / 0.6 ms (1900 primes), one `checkStep`
     8 / 118 ms, the first `findStep` 31 / 607 ms; `H_{−431}` (h = 21) 25 ms.
     The chain at 300 digits (`trace:1`): 57 steps, a median step near 1000 bits costs
     0.3–0.6 s, and a few steps cost far more (8.8 s, 2.3 s, 2.2 s, 1.5 s, 1.2 s — half of
     the total); what those spend their time on is not measured yet.
   * **Profile (2026-11-23, `"digits:300,profile:1"`, two primes, 27.1 and 27.9 s)**: root
     of the class polynomial modulo `n` 45 / 33 %, square roots of prime discriminants
     19 / 30 %, curves 20 / 18 %, probable-prime tests 12 / 15 %, trial division 3 %,
     Cornacchia and the class polynomials themselves under 1 % each.  Single roots cost up
     to 7.5 s (`D = 1615`).
   * **After the profile (2026-11-23, timed in the third run):** (1) the power `(X + r)^((n−1)/2)`
     modulo `g` in `rootOfSplitPoly` by packed multiplication (`PackedMod`: Kronecker
     substitution, three large products per modular product instead of `2h²` modular
     multiplications); (2) the square-root cache is kept from one tier to the next
     (`findStepWith`); (3) for `D = 3` and `D = 4` the six and four twists by powers of a
     non-residue instead of `b = 1, 2, 3, …`.
   * **Montgomery reduction (2026-11-24, fourth run).**  A multiplication modulo `n` spent
     about 80 % of its time in the division.  `AzNat/Montgomery.lean` (theory in
     `Montgomery/Theory.lean`, proofs in `AzNat/Equiv/Montgomery.lean`) reduces by `n/2`
     passes of the fused two-row multiply-accumulate instead; measured with
     `benchmark ecpp 1 "modmul:1"` (ns per modular multiplication, plain / Montgomery):
     64 bits 226–256 / 173–181, 256 bits 954–962 / 406–407, 1024 bits 5390–5494 / 2806–2861,
     2048 bits 16 223–16 420 / 8895–8984.  Used, with no change to any definition the
     theory talks about, through three proven `@[csimp]` replacements — `AzZMod.pow`,
     `AzZMod.powAzNat` (odd modulus, exponent of at least 32 bits) and `ECPP.jacMul`
     (`ECPP/CurveMont.lean`, odd `n`, multiplier of at least 32 bits) — and directly in the
     unproven `PackedMod` of the generator.  Timed (three primes per size, same as the third
     run):

     | digits | generator | checker |
     |---|---|---|
     | 100 | 0.21–0.36 s (was 0.29–0.54) | 28–44 ms |
     | 200 | 1.5–3.2 s (was 2.4–5.1) | 0.24–0.27 s (was 0.51–0.57) |
     | 300 | 12.7–16.8 s (was 20.1–28.7) | 0.88–0.96 s (was 2.0–2.3) |

     Profile at 300 digits (one prime, 12.7 s): root of the class polynomial 5.8 s (46 %),
     square roots 2.1 s (17 %), probable-prime tests 1.9 s (15 %), curves 1.8 s (14 %),
     trial division 0.7 s.  With the powers alone switched the same prime took 15.7 s
     (root 6.9 s, curves 3.7 s): the root gained little from Montgomery form, so its time is
     not in the reductions of the coefficients; what it is in is not measured yet.
     Pitfall met on the way: binding the Montgomery data with `letI` inlines
     `MontCtx.make` (two divisions) into every multiplication — bind it with `let` and pass
     the instance explicitly.
   * **The root of the class polynomial (2026-11-24, fifth run).**  Breakdown of one
     squaring of the packed power (`"digits:300,root:1"`, degree 24): the three large integer
     products were 91 % (square 0.74 ms, quotient product 0.93 ms, `q·g` 1.07 ms of 3.0 ms),
     the Montgomery reductions of the coefficients 6 %, packing under 1 %; the gcd of a round
     costs 8 ms against 3 s for the power.  Two changes:
     (1) *evaluation at `±2^(64 hw)`* (`EvalPM`, `evalPM`, `splitPM`): the coefficients fill
     only half of a slot of the usual packing, so each product is done as two products of
     half the size (sum and difference give the even and the odd coefficients) — one squaring
     3.0 → 2.3 ms at degree 24, 8.9 → 6.8 ms at degree 48, no gain below degree 8;
     (2) *the factor over the genus field* (`genusClassPoly`, `genusPolyMod`,
     `classPolyRoot`): for `−D` a product of `t ≥ 2` prime discriminants, `H_{−D}` splits
     over `ℚ(√d₁, …, √d_t)` into `2^(t−1)` factors; the product of `X − j` over one genus of
     forms is recognised as `2^(−t) ∑_S A_S ∏_{i∈S} √dᵢ` from the `2^(t−1)` real genus
     products, and the square roots of the `dᵢ` modulo `n` give a factor of degree
     `h / 2^(t−1)` modulo `n` (`D = 1615`: 24 → 6; `D = 1155`: 8 → 1).  Falls back to
     `H_{−D}` when `t = 1` or anything fails.  Tested against `H_{−D}` (`Tests/Gen`).
     Timed (same primes):

     | digits | generator | before (fourth run) |
     |---|---|---|
     | 100 | 0.19–0.33 s | 0.21–0.36 s |
     | 200 | 1.4–3.1 s | 1.5–3.2 s |
     | 300 | 8.5–13.7 s | 12.7–16.8 s |

     Profile at 300 digits (8.7 s): square roots 2.2 s, probable-prime tests 1.9 s, curves
     1.9 s, root 1.6 s (was 5.8 s; with (1) alone 5.1 s), trial division 0.8 s, class
     polynomials 0.2 s.  No single piece dominates any more.
     Open: order the discriminant table by `h / 2^(t−1)` instead of `h` (more discriminants
     at the same root cost); low short products for the two reduction products; `AzNat`
     products at 400–800 limbs scale about twice worse than from 32 limbs by the Toom
     exponent (384 limbs: 0.26 ms square, 0.35 ms product) — not looked into.
   * Not yet done from the paper: the simultaneous smoothness test of all the `m` (now trial
     division of each `m`), early abort, fast Cornacchia (half-gcd), Weber or other small
     class invariants (now `j`, whose polynomials are much larger), root finding by fast
     polynomial arithmetic, a larger discriminant set with caching of `H_D` across steps.

## Open decisions

* The certificate format (our own record, or one that can be read by existing checkers).

## New functions on `Az*` types (reported to the user as they land)

All in namespace `Azurite.ECPP`, over `AzZMod n` (2026-11-23):

| Function | Type | What it is |
|---|---|---|
| `JacPoint n` | `Type` | `AzZMod n × AzZMod n × AzZMod n`: `(X, Y, Z)` for `(X/Z², Y/Z³)` |
| `jacDbl a P` | `JacPoint n` | doubling on `y² = x³ + ax + b` |
| `jacAddMixed u v P` | `JacPoint n` | `P + (u, v)`, the usual mixed addition (incomplete), `Z₃ = Z·(uZ² − X)` |
| `jacMul a u v fuel k` | `Option (JacPoint n)` | `k · (u, v)`; the final `Z` is the product of all the steps' `Z`-factors |
| `StepCert` | structure | `a b u v q : AzNat` |
| `checkStep n c` | `Bool` | one step of a certificate for `n` |
| `check n cert` | `Bool` | the chain, ending with `AzNat.isPrimeAprcl` |

No new function on `AzNat` or `AzZMod` themselves was needed.

### Generator (2026-11-23)

| Function | Type | What it is |
|---|---|---|
| `AzZMod.inv? a` | `Option (AzZMod m)` | inverse, `none` for a non-unit (no coprimality proof needed) |
| `ECPP.resOfInt n d` | `AzZMod n` | a small `Int` as a residue |
| `ECPP.sqrtSmall? n d` | `Option (AzZMod n)` | `√d` modulo `n` for a small integer `d` (Jacobi symbol, then `AzZMod.sqrt?`) |
| `ECPP.cornacchia4 n D r` | `Option (AzNat × AzNat)` | `x² + D y² = 4n` from `r² ≡ −D` |
| `ECPP.trialDivide m primes` | `AzNat × AzNat` | cofactor and removed part (no longer used by the search) |
| `ECPP.smoothParts P ms` | `Array (AzNat × AzNat)` | for each `m` of the batch, cofactor and the part made of primes dividing the primorial `P`: one `P mod ∏ ms`, then `gcd(R mod m, m)` divided out repeatedly (Bernstein 2004) |
| `ECPP.polyOfInts n c` | `AzPolynomial (AzZMod n)` | integer coefficients reduced modulo `n` |
| `ECPP.rootOfSplitPoly n h` | `Option (AzZMod n)` | a root of a polynomial that splits into distinct linear factors |
| `ECPP.EvalPM`, `evalPM hw a` | structure | a polynomial with coefficients below `B = 2^(64 hw)` evaluated at `±B`: `plus`, `minus` (absolute value), `neg` (2026-11-24) |
| `ECPP.splitPM hw p m neg`, `EvalPM.mul`, `EvalPM.sqr` | `AzNat × AzNat` | from the values of a product at `±B`: its even and its odd coefficients, each packed `2 hw` limbs apart |
| `ECPP.unpackCoeffs c hw k eo` | `Array AzNat` | the first `k` coefficients of such a pair, each through the Montgomery reduction of `c` |
| `ECPP.PackedMod`, `PackedMod.make n g` | structure | arithmetic modulo `n` and a monic `g`: Montgomery data of `n`, `g` and the inverse of the reversed `g` as `EvalPM`, coefficients in Montgomery form |
| `ECPP.genusChar d f` | `Int` | the genus character of the prime discriminant `d` on a reduced form |
| `ECPP.positiveSubsets ds` | `List (List Bool)` | the sets of prime discriminants with positive product |
| `ECPP.GenusPoly`, `genusClassPolyAt D p`, `genusClassPoly D` | structure, `Option GenusPoly` | a factor of `H_{−D}` over the genus field: the integers `A_S(k)` by `AzFloat`/`AzComplexFloat` |
| `ECPP.genusPolyMod n G` | `Option (AzPolynomial (AzZMod n))` | that factor modulo `n`, from the square roots of the prime discriminants |
| `ECPP.classPolyRoot n D` | `Option (AzZMod n)` | a root of `H_{−D}` modulo `n`: through the genus factor, else through `H_{−D}` |
| `PackedMod.reduce`, `sqr`, `mulLinear r`, `powLinear r e` | `Array AzNat` | reduction of a packed product, square, times `X + r`, `(X + r)^e` modulo `g` |
| `AzNat.kroneckerPack w a` | `AzNat` | `∑ aᵢ · 2^(64 w i)` for an `Array AzNat` of coefficients below `2^(64 w)` (**proven**, `kroneckerPack_toNat`) |
| `AzNat.kroneckerCoeff w x k` | `AzNat` | `⌊x / 2^(64 w k)⌋ mod 2^(64 w)` (**proven**, `kroneckerCoeff_toNat`) |
| `AzNat.maxLimbs a`, `AzNat.sumLimbs a` | `Nat` | the largest and the total limb count of an `Array AzNat` |
| `AzPolynomial.mulKronecker p q` | `AzPolynomial (AzZMod m)` | product by Kronecker substitution (**proven**, `toPoly_mulKronecker`); the multiplication of `AzPolynomial (AzZMod m)` from 3 coefficients on |
| `AzPolynomial.mulKroneckerNat p q` | `AzPolynomial AzNat` | the same over `AzNat` (**proven**, `toPoly_mulKroneckerNat`); used when `useKroneckerNat p q` |
| `AzPolynomial.mulKroneckerInt p q` | `AzPolynomial AzInt` | the same over `AzInt` (**proven**, `toPoly_mulKroneckerInt`); used when `useKroneckerInt p q` |
| `AzPolynomial.posParts a`, `negParts a` | `Array AzNat` | the nonnegative coefficients / absolute values of the negative ones of an `Array AzInt` |
| `AzPolynomial.kroneckerPackInt w a` | `AzInt` | `∑ aᵢ · 2^(64 w i)` for signed coefficients |
| `AzPolynomial.kroneckerWidth m n` | `Nat` | limbs per coefficient over `AzZMod m`: `2^(64 w) > n · m²` |
| `AzPolynomial.kroneckerDense a s`, `useKroneckerNat p q`, `useKroneckerInt p q` | `Bool` | the dispatch rules |
| `AzPolynomialMulConfig R` (`dmul`, law `dmul_eq`), `.basecase`, `.karatsuba`, `.karatsubaWith t` | class / values | the multiplication of `AzPolynomial R`: `*` is `dmul`, **proven** the schoolbook product (`mul_eq_mulBasecaseFold`); one instance per coefficient type |
| `ECPP.cpow z k p` | `AzComplexFloat` | `z^k` by binary powering at precision `p` |
| `ECPP.eulerProduct q bits p` | `AzComplexFloat` | `∏ (1 − qⁿ)` by the pentagonal series |
| `ECPP.jOfForm D A B p` | `AzComplexFloat` | `j((−B + √−D)/(2A))` |
| `ECPP.mulLinear`, `mulQuadratic` | `List AzFloat` | a real polynomial times `X − r`, `X² + sX + t` |
| `ECPP.nearInteger? x` | `Option AzInt` | a float within `2^(−8)` of an integer, as that integer |
| `ECPP.hilbertClassPolyAt D p`, `hilbertClassPoly D` | `Option (List AzInt)` | `H_{−D}`, constant term first |
| `ECPP.candidateOrders n D x y` | `List AzNat` | `n + 1 ± x` (and the extra orders for `D = 3, 4`) |
| `ECPP.aboveBound n q`, `probablePrime q` | `Bool` | the size condition; one Miller–Rabin round (base 2) |
| `ECPP.tryCurve a b c q tries` | `Option StepCert` | point, cofactor multiple, `checkStep` |
| `ECPP.cmCurves n D tries` | `List (AzZMod n × AzZMod n)` | the curves to try for `−D` (the six or four twists for `D = 3, 4`) |
| `ECPP.smallSexticNonResidue n` | `Option Nat` | a small number that is neither a square nor a cube modulo `n` |
| `ECPP.powersOf g k` | `List (AzZMod n)` | `g⁰, …, g^(k−1)` |
| `ECPP.findStep P T n skip` | `Option StepCert` | one step of a certificate |
| `ECPP.findStepWith P T n skip cache` | `Option StepCert × SqrtCache n` | the same, with the square roots found given and returned |
| `ECPP.processBatch P prim n batch toSkip` | `Option StepCert × Nat` | a batch of candidate orders `(D, m)`: `smoothParts`, then by increasing cofactor the probable-prime test, the curves and the point |
| `ECPP.classPolys D` | `ClassPolys` (four `Thunk`s) | the Weber / Hilbert polynomials of `−D` and their genus factors from the table of the process (`classPolyCache`, `D ≤ 80000`), each computed once |
| `ECPP.sharedPrimorials`, `primorialsUpTo top` | `Array (Thunk AzNat)` | the ladder of prime products of the process (up to `2^32`) |
| `ECPP.primorialLadder top`, `GenTables.primorialFor T n` | `Array (Thunk AzNat)`, `AzNat` | the products of the primes below `2^j` (lazy), and the one used for `n` (`j = ⌊2.7 log₂ bits⌋ − 6`, between 10 and the cap) |
| `ECPP.findStepTiers P tiers n skip` | `Option StepCert` | the first tier of tables that gives a step |
| `ECPP.genChain`, `ecppCertificate n P` | `Option (List StepCert)` | the certificate |
| `ECPP.provePrime n P` | `Bool` | search and check; `true` proves primality |

### Montgomery reduction (2026-11-24)

| Function | Type | What it is |
|---|---|---|
| `AzNat.montNegInv n₀` | `UInt64` | `−n₀⁻¹ mod 2^64` for odd `n₀` (**proven**, `montNegInv_mul`) |
| `AzNat.redcStep`, `redcLoop`, `redcLimbs N ne ninv a` | `Array UInt64` | Montgomery reduction on a `2 ne + 1`-limb buffer, two limbs per pass (**proven**, `redcLimbs_spec`) |
| `AzNat.MontCtx`, `MontCtx.make m extra` | structure | the precomputed data of an odd modulus: padded limbs, `−m⁻¹ mod 2^64`, `R mod m`, `R² mod m` (`R = 2^(64 ne)`, `ne` even, at least the limb count of `m` plus `extra`) |
| `MontCtx.redc c t` | `AzNat` | `t R⁻¹ mod m` for `t < m R` (**proven**, `MontCtx.redc_spec`, `redc_cast`) |
| `MontCtx.mul c a b`, `sqr c a` | `AzNat` | `a b R⁻¹ mod m`, `a² R⁻¹ mod m` (**proven**, `mul_spec`, `sqr_spec`) |
| `MontCtx.toMont c a`, `fromMont c a` | `AzNat` | `a R mod m`, `a R⁻¹ mod m` (**proven**, `toMont_spec`, `fromMont_spec`) |
| `AzZMod.Mont m`, class `AzZMod.MontData m` | structure / class | a reduced residue in Montgomery form; `+`, `−`, `*`, squaring, `1` given the data of an odd `m` (**proven** against `ZMod` through `Mont.toZMod`) |
| `AzZMod.toMont a`, `ofMont x` | `Mont m`, `AzZMod m` | into and out of Montgomery form |
| `AzZMod.powMont hm a n`, `powAzNatMont hm a n` | `AzZMod m` | `a ^ n` in Montgomery form (**proven**, `toZMod_powMont`, `toZMod_powAzNatMont`) |
| `AzZMod.powFast`, `powAzNatFast`, `montPowMinBits` | `AzZMod m`, `ℕ` | what `pow`/`powAzNat` compile to (**proven** equal, `@[csimp]`); the exponent size from which Montgomery form is used (32 bits) |
| `ECPP.jacDblG`, `jacAddMixedG`, `jacMulG` | generic | the curve formulas over any type with `+`, `−`, `*`, squaring, `1` |
| `ECPP.ofMontPt P`, `jacMulMont hn a u v fuel k`, `jacMulFast` | `JacPoint n`, `Option (JacPoint n)` | the ladder in Montgomery form; what `jacMul` compiles to (**proven** equal, `jacMul_eq_jacMulFast`, `@[csimp]`) |

Small-number helpers on `Nat`/`Int` (not `Az*`): `reducedForms`, `classNumber`,
`isFundamental`, `primeDiscriminants`, `discriminantTable`, `smallPrimes`,
`smallNonResidue`, `classPolyBits`; records `RedForm`, `GenParams` (with `tables`, `tierTables`),
`GenTables`, `SqrtCache`.

### `AzComplexFloat` (2026-11-23)

A new type, namespace `Azurite.AzComplexFloat`: a pair `re`, `im` of `AzFloat`s.  Every
rounded function takes `(pRe pIm : Nat) (mRe mIm : RoundingMode)` — a pair of precisions
and a pair of modes for the real and imaginary parts, as in MPC and rug — and returns `Rounded = AzComplexFloat × Ordering × Ordering`.  Proven: for finite operands each
component is the correct rounding of the exact complex value (`Equiv/Arith.lean`).

| Function | What it is |
|---|---|
| `ofFloat x`, `zero`, `one`, `i`, `nan` | constructors and constants |
| `isFinite`, `isNaN`, `isZero` | predicates |
| `neg` (`-z`), `conj` | exact |
| `addPrecRound z w pRe pIm mRe mIm`, `subPrecRound` | componentwise |
| `mulPrecRound z w pRe pIm mRe mIm` | `ac − bd`, `ad + bc`, one rounding each |
| `sqrPrecRound z pRe pIm mRe mIm` | `a² − b²`, `2ab` |
| `mulFloatPrecRound z x pRe pIm mRe mIm`, `divFloatPrecRound` | by a real float |
| `normSqrPrecRound z p mode` | `a² + b²` as an `AzFloat × Ordering` |
| `divPrecRound z w pRe pIm mRe mIm` | finite operands, nonzero divisor; `NaN` otherwise |
| `cisPrecRound x pRe pIm mRe mIm` | `cos x + i sin x` for a real float `x` |

Open for the full type (not needed by the generator): the conventions for infinities and
division by zero in `divPrecRound` (to follow MPC), precision-less variants (`add`, `mul`, …), `abs`/`arg`, `sqrt`, `exp`, `ln`, string
conversion.  `divPrecRound` forms exact sums, whose precision grows with the gap between
the exponents of the terms.

## 2026-11-25 — batched trial division

The candidate orders of a step are collected in batches of `GenParams.batch` and divided at
once by all the primes below the bound (`smoothParts`), and within a batch the candidates are
tried by increasing cofactor.  The bound went from `2^14` for every `n` to `2^j` with
`j = ⌊2.7 log₂ bits⌋ − 6` (`2^16`, `2^19`, `2^20` at 100, 200, 300 digits; at most
`trialBound = 2^24`, then ×4 per tier).

**Timed 2026-11-25** (`benchmark ecpp 10 "digits:D,noaprcl:1"`, totals over the first ten
probable primes above `10^D`; before = the one-by-one trial division with bound `2^14`):

| digits | steps before → now | generator (s) before → now | checker (s) before → now |
|---|---|---|---|
| 50 | 77 → 52 | 0.36 → 0.24 | 0.076 → 0.071 |
| 100 | 178 → 144 | 2.25 → 1.70 | 0.37 → 0.31 |
| 200 | 399 → 288 | 24.2 → 15.2 | 2.75 → 1.93 |
| 300 | 607 → 434 | 132.8 → 76.5 | 10.0 → 6.9 |

Tuning runs (same primes, generator total in s at 100 / 200 / 300 digits), bound exponent
`2 log₂ bits + e`: `e = 0` (2^16, 2^18, 2^18) 1.61 / 14.3 / 105.7; `e = 2` 1.87 / 17.8 / 71.6;
`e = 4` 5.09 / 39.3 / 100.4; batch 32 and 8 at `e = 2`: 1.99 / 18.8 / 81.5 and
1.83 / 18.3 / 82.1 (16 kept).  The time per prime varies by a factor of two with the chain
taken, so differences below about 10 % between settings are not significant.  Profile of one
300-digit prime after the change (8.5 s): square roots 2.3, curves 1.7, class-polynomial
roots 1.5, probable primes 1.4, trial division 1.3 (of which the product of the primes below
`2^20`, built once).

Tried and reverted the same day (no gain, ten primes each): Jacobi symbols of all the prime
discriminants of a `D` before any root; table ordered by `h / 2^(t−1)`; later tiers skipping
the previous tier's discriminants.

## 2026-11-26 — `AzNat.isPrime` uses elliptic curves

* `AzNat.isPrimeAprcl` (`AzNat/IsPrimeAprcl.lean`): the APR-CL test, the `isPrime` of before,
  with `isPrimeAprcl_eq_true_iff`.  The base case of `ECPP.check`.
* `AzNat.isPrime` (`AzNat/IsPrime.lean`): `isPrimeAprcl` up to 80 bits; above,
  `millerRabin n 0 0 && (ECPP.provePrime n || aprclOrNaive n)`.  `isPrime_eq_true_iff`
  unchanged in statement (`provePrime_sound`, `aprclOrNaive_eq_true_iff`,
  `millerRabin_eq_true_of_prime`).
* **Composites that pass Miller–Rabin.**  The first build hung for hours on the guard for
  `3317044064679887385961981` (a strong pseudoprime to the twelve bases): the search went
  through every discriminant of every tier.  Now the search for a step gives up at a sign
  that `n` is composite: a prime discriminant of Jacobi symbol `1` without a square root
  (`SqrtCache.composite`), or `GenParams.maxFailures = 3` probable-prime cofactors for which
  no curve gives a step.  That pseudoprime and `318665857834031151167461` are now rejected at
  once.  A prime that trips the failure count only loses its certificate (`isPrime` then asks
  APR-CL).
* Guards (interpreter, time of the whole file): `10^50 + 151` ≈ 2 s, `10^100 + 267` ≈ 27 s
  (both in `AzNat/IsPrime.lean`), `2^521 − 1` ≈ 2.4 min (`ECPP/Tests/Gen.lean`);
  `10^200 + 357` took 5.5 min and was left out.
* Changed signatures (generator, unproven): `SqrtCache` is a structure (`roots`,
  `composite`); `processBatch` also returns the number of failed cofactors.

## 2026-11-26 — Weber class invariants

Generator only (unproven, `ECPP/Gen/ClassPoly.lean`, `Gen/Search.lean`), for `D ≡ 7 (mod 8)`.

* `weberFn which D A B p`: `𝔣, 𝔣₁, 𝔣₂` at `τ = (−B + √−D)/(2A)` from the pentagonal series,
  all powers of `q` from one `w = e^(2πiτ/48)` (one `exp`, one `cis`).
* `weberValue D cube f p`: the invariant of a form by the recipe of Yui–Zagier (Math. Comp. 66
  (1997), §3): a 48th root of unity `ζ^(b(a−c−ac²))` or `ζ^(b(a−c+a²c))`, the sign
  `(−1)^((D+1)/8)`, and `𝔣`, `𝔣₁` or `𝔣₂` by the parities of `a`, `c`; cubed when `3 ∣ D`.
  The recipe was written from memory and settled by experiment: of the eight variants of
  the signs, only this one gives integer coefficients for `D = 23, 31, 47, 71, 95, 119, 191,
  1319` and (cubes) `15, 39, 87, 255`.
* `weberClassPoly D`, `genusWeberPoly D` (the factor over the genus field, by the same code as
  for `j`: `formsPoly`, `genusPolyAt`, `retry3` are now shared).  Starting precision
  `classPolyBits D / 48` (`/ 16` for cubes) plus the margin.
* `weberRoot n D`: a root `u` modulo `n`, then `(x − 16)³ / x`, `x = u^24` (`u^8` for cubes);
  `classPolyRoot` tries it first and falls back to `hilbertRoot` (the path of before).
* Tests (`ECPP/Tests/Gen.lean`): `W_23`, `W_31`, `W_47`, and for eleven discriminants (prime,
  composite, with `3`, three prime discriminants) the number from `weberRoot` modulo a
  12-digit prime is a root of `H_{−D}`.
* Not covered: `D ≡ 3 (mod 8)` and even `D` (other invariants: `γ₂`, `𝔣₁` at level 2, …).
* **TIMED 2026-11-26.**  Certificates (`benchmark ecpp 10 "digits:D,noaprcl:1"`, ten primes,
  old and new binary alternately, generator ms): 100 digits 1595, 1577 → 1572, 1560;
  200 digits 14533, 14567 → 14978, 14778; 300 digits 75157, 75143 → 75800, 75365.  No
  change (same 144 / 288 / 434 steps), as expected with `D ≤ 2000`, `h ≤ 24`: the class
  polynomials are a small part.  The polynomials themselves (`benchmark ecpp 1 "classpoly:1"`,
  `H_{−D}` / Weber, ms): `D = 1319` (`h = 45`) 138 / 49; `4079` (85) 846 / 96; `9239` (139)
  4539 / 250; `20639` (179) 12826 / 456; `49871` (357) 119348 / 2399; with the genus factor
  `1295` (36) 103 / 27, `5015` (88) 1064 / 101.  So 3× at `h ≈ 40`, 9–10× at `h ≈ 85`, 28× at
  `h ≈ 180`, 50× at `h ≈ 360`; the gain will show once the search uses larger discriminants.

## 2026-11-26 — the discriminant set

Generator only (`Gen/Forms.lean`, `Gen/Search.lean`).

* `smoothFundamental Dmax pMax`, `smoothDiscriminantTable Dmax pMax gMax hMax hMaxWeber
  sqrtCost rootCost`: the fundamental `D ≤ Dmax` built from the primes up to `pMax`, with
  `h ≤ hMax` (`hMaxWeber` for `D ≡ 7 (mod 8)`) and at most `gMax` classes per genus; ordered
  greedily by estimated cost in µs: class polynomial (`1100 h` Weber, `50 h²` Hilbert,
  nothing for `h = 1`), root (`rootCost · g` for `g > 1`), `sqrtCost` per prime discriminant
  not yet used by an earlier `D`.  `oddPrimeFactors` is now trial division (it scanned
  `0 … n`).
* Defaults: `dMax 20000`, `pMax 1000`, `gMax 8`, `hMax 24`, `hMaxWeber 64`, `sqrtCost 2000`,
  `rootCost 10000` (1348 discriminants, 54 ms to build; the table of before: `D ≤ 2000`,
  `h ≤ 24`, 528 discriminants by increasing `h`).  Tiers: ×2 for `dMax`, `pMax`, `gMax`,
  `hMax`, `hMaxWeber` (tier 1: 5233 discriminants, 0.5 s).
* The tables of the default parameters are top-level constants of unforced thunks
  (`defaultTierTables`), so they are built once per process and not once per call;
  `smallTierTables` (`dMax 2000`, `pMax 2000`, costs for short `n`) for `n ≤ 256` bits.
* **Timed 2026-11-26** (ten primes, generator total; before = Weber build with the table of
  before): 30 digits 0.109 → 0.120 s; 50: 0.241 → 0.243; 100: 1.69–1.78 → 1.52, 1.54;
  200: 15.2 → 13.3, 13.3; 300: 76.3–76.7 → 62.1, 61.9 (−12 %, −13 %, −19 %).  Profile of
  four 300-digit primes (first-step chains): 32.8 → 24.5 s; per prime now square roots
  1.0–1.7 s (were 1.4–2.5), trial division 1.1–1.3, probable primes 0.8–1.4, roots 0.6–1.4,
  curves 1.3–1.5, class polynomials 0.1–0.2.
* What did not work: (1) primes up to 100 only, ordered by largest prime (`D ≤ 50000`):
  the profile improved (sqrt 2.4 → 0.7 s) but the full runs were 15–25 % SLOWER — for an `n`
  for which the few small primes are non-residues nearly every `D` dies, the level has no
  step and the search backtracks (yield has a large variance on a small prime set);
  (2) ordering by largest prime: uses `D` with expensive class polynomials and roots
  early, bad for short `n`; (3) fewer classes per genus (`gMax 4`: 81.8 s, `gMax 2`: 99.7 s
  at 300 digits against 71 s, tables rebuilt per prime in these runs); (4) `dMax 50000`:
  84 s (0.15 s table per prime in that run, and tier tables of seconds).  Weights
  `sqrtCost 1000 / 4000`, `rootCost 5000 / 20000`: within noise, `sqrtCost 1000` worse.
* Benchmark: keys `pmax`, `gmax`, `hweber`, `sqrtcost`, `rootcost`; the `classpoly` stage
  of the profile now times what the search uses (Weber when available).  Any non-default
  key rebuilds the tables per prime (about 55 ms, and 0.5 s per tier escalation).

## 2026-11-26 — per-process caches

Generator only (`Gen/ClassPoly.lean`, `Gen/Search.lean`).

* `classPolys D`: a table indexed by `D < 80001` (`classPolyCache`, a thunk, so nothing is
  built at program start) of `ClassPolys` — four thunks: Weber polynomial, its genus factor,
  Hilbert polynomial, its genus factor.  `weberRoot` / `hilbertRoot` read from it, so a
  polynomial is computed once per process instead of once per level that uses `D`.  Larger
  `D` are computed directly.
* `sharedPrimorials` (`primorialsUpTo`): one ladder for all parameter sets, and each level is
  the one below times the primes between (`primorialLadder`): all of `2^10 … 2^20` in
  289 ms once per process (442 ms from scratch; `benchmark ecpp 1 "ladder:1"`).
* **Timed 2026-11-26** (ten primes, generator total ms, before / after, alternating runs):
  30 digits 98, 94 / 98, 99; 50: 240, 239 / 232, 232; 100: 1501, 1496 / 1427, 1447 (−4 %);
  200: 13316, 13625 / 13402, 13352; 300: 59915, 60208, 61145, 63374 / 59372, 64791, 61232,
  60011 (no difference beyond the ±4 % noise).  One 300-digit prime in a fresh process:
  6.34 → 5.89 s.  The prime products were already shared in the default path, and class
  polynomials are 2–3 % of the work at 300 digits, so the gain is small, as expected.
* The profile's `classpoly` stage reads the same table (a polynomial is counted once).

## 2026-11-26 — elliptic curves when APR-CL gives up

`AzNat/IsPrime.lean`, `AzNat/Equiv/IsPrime.lean`.

* `isPrime` is now: trial division up to 32 bits; up to 80 bits Miller–Rabin and
  `aprclOrEcpp` (the APR-CL verdict, and `ecppOrNaive` when it gives up); above, as before
  (the certificate search comes first there, so after APR-CL only trial division is left).
* `ecppOrNaive n`: `provePrime n ecppFallbackParams` when `n` has more than
  `ecppFallbackBits = 36` bits, then (or otherwise) `isPrimeNaive`.  `ecppFallbackParams` =
  `smallParams` with `baseBits := 32`, so the chain ends where the checker's base case
  (`isPrimeAprcl`) is trial division.
* Proven: `ecppOrNaive_eq_true_iff`, `aprclOrEcpp_eq_true_iff`; `isPrime_eq_true_iff`
  unchanged in statement.
* **Timed 2026-11-26** (`benchmark ecpp 1 "fallback:1"`, five primes each, ms per prime,
  trial division / certificate): 34 bits 2.9 / 7.6; 36: 5.4–5.9 / 5.9–6.2; 38: 11 / 5.7;
  40: 22 / 6.7; 44: 93 / 5.5; 48: 356 / 6.2; 52: 1440 / 6.3–9.0; 56: 5800 / 6.2;
  60: 22900 / 7.0; 64: 92600 / 7.7.  The certificate time is mostly the table of
  discriminants, rebuilt per call for non-default parameters (about 5 ms).
* APR-CL has never been seen to give up, so the path is tested by guards on `ecppOrNaive`.
* New functions on `Az*` types: `AzNat.ecppOrNaive`, `AzNat.aprclOrEcpp`
  (`AzNat → Bool`), constants `AzNat.ecppFallbackParams`, `AzNat.ecppFallbackBits`.
