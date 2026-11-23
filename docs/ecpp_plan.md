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
| the curve | in Weierstrass form over `K`: `y′² = x′³ + aλ² x′ + bλ³` with `λ = x³ + ax + b`, `x′ = λX`, `y′ = λ²Y`, so that Mathlib's group law applies | to do |
| Lemma 10.7 | `d_0 = p`, `d_{−1} − d_0 − 1 = #E(𝔽_p) − p − 1`: (10.16) `X_{−1} = −x − x^p + (1 + λ^((p−1)/2))² λ/(x − x^p)²`; the numerator has degree `2p + 1`; `x^p − x = ∏ (x − j)`; the factor `x − j` survives in the denominator twice, once or not at all as `λ(j)` is a residue, `0` or a non-residue | to do |
| Lemma 10.8 | **Basic Identity** `d_{n−1} + d_{n+1} = 2 d_n + 2`.  Degenerate cases: `Z_n = ∞` (`1 + 1 = 0 + 2`), `Z_{n∓1} = ∞` (`0 + 4 = 2 + 2`, with `X(2(x, 1)) = ((x² − a)² − 8bx)/(4λ)`).  Generic case: (10.18)–(10.20) | formulas from the group law: to do |
| (10.21)–(10.22) | `BD = (Qx − P)²` up to a unit | **DONE** `exists_unit_of_relations`, `isUnit_of_dvd_forms` (`Theory/ManinAlgebra.lean`).  **Knapp's text has a gap here**: it writes `AC = S N₁`, `BD = S M` with `S = gcd(AC, BD)`, which presumes `gcd(N₁, M) = 1`; a common prime factor of `Qx − P` and `(x² − a)² − 8bx` is not excluded.  The formalized argument uses `N₂` as well: no prime divides `N₁`, `N₂` and `M`, because modulo a prime factor of `Qx − P` they are `Q² g` and `2Q² f`, and `(3x² + 4a) g − (3x³ − 5ax − 27b) f = 4a³ + 27b²` |
| cases (a)–(d) | the degrees | **DONE**, differently: `height_add_height` (`max(deg A, deg B) + max(deg C, deg D) = max(deg AC, deg BD, deg(AD + BC))`) and `max_natDegree_forms` (the largest degree of `N₁`, `N₂`, `M` is `2 max(deg P, deg Q) + 2`) |
| (10.25) | `d_n = n² − (d_{−1} − d_0 − 1) n + d_0` | **DONE** `degree_quadratic` (`Theory/Manin.lean`) |
| conclusion | discriminant `≤ 0` | **DONE** `sq_le_of_quadratic_nonneg`, `sq_le_of_degree`, `prime_ne_mul_succ` (Knapp argues with two consecutive `d_n` not both `0`; here: `p ≠ n(n + 1)`) |

## Layers

1. **Theory** (Mathlib objects only): `Azurite/ECPP/Theory/`, namespace `Azurite.ECPP`.
   **Criterion DONE 2026-11-23, conditional on the Hasse bound** (a hypothesis, not an axiom).
   * `Theory/Chain.lean`: `MulChain W U k T` — the Jacobian triple `T` over a commutative
     ring is obtained from `U` along a computation of `k · U` by Mathlib's formulas
     `dblXYZ`, `addXYZ`, with **the `Z`-coordinate `addZ` of every addition a unit**, up to
     changes of representative.  `MulChain.toAffine`: under a ring homomorphism to a field
     where `U` is a nonsingular point, `T` is the point `k • U` (Mathlib's
     `Jacobian.Point.toAffine`, `toAffine_add`, `map_addXYZ`, `map_dblXYZ`).  The doubling
     formula is complete; the addition formula is right exactly when `addZ ≠ 0`.
   * `Theory/Hasse.lean`: `shortW a b` (`y² = x³ + ax + b`), `HasseBound : Prop` —
     `(#E(𝔽_p) − (p + 1))² ≤ 4p` for every such curve with `4a³ + 27b² ≠ 0` over `𝔽_p`,
     `p ≥ 5` (the setting of Chahal–Osserman); `finite_point`.  **Statement only.**
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
   * Still to do here: the Hasse bound.
2. **Implementation on `Az*` types** (not started): curve arithmetic over `AzZMod N`, the
   certificate type, `ecppCheck`, with `ecppCheck_sound` by the bridge to layer 1.  What the
   theory asks of it: a computation of `(q − 1)·(u, v)` whose steps are Mathlib's formulas
   up to unit scalings, and the unit conditions — **one gcd with `N` of the product of the
   `Z`-coordinates of all additions and of the final `Z`** (the standard Jacobian
   `Z₃ = Z₁Z₂H` accumulates that product by itself).
3. **Generator** (unproven, not started): Step 1′ loop, Cornacchia, class polynomial, root
   mod `N`, curve and point, recursion; then the upgrades of Morain §5.3.

## Open decisions

* The certificate format (our own record, or one that can be read by existing checkers).

## New functions on `Az*` types (reported to the user as they land)

None yet.
