# Plan: a full Toom–Cook ladder for `AzNat` multiplication

Status: plan written 2026-09-26; progress is recorded in the status log at the end.

## Goal

Follow the textbook ladder for integer multiplication (Brent–Zimmermann, *Modern Computer
Arithmetic*, §1.3): a basecase for small operands, Toom–Cook variants of increasing order for
medium sizes, and FFT multiplication for the largest ones, with the unbalanced variants of
§1.3.5 and squaring versions. Every algorithm is written from its published description (the
sources are listed at the end) and proven equal to `Nat` multiplication, as the existing
Karatsuba and Toom-3 are; the interpolation formulas are derived in-house
(`scripts/ToomInterpolation.lean`) and every threshold is measured on this library. No
implementation code of any other library is consulted.

The ladder we are aiming at, in the order it should be built:

| stage | operands | points | multiplications | replaces |
|---|---|---|---|---|
| schoolbook | any | – | `n·m` limb products | *done* |
| Toom-2 (Karatsuba) | balanced | 3 | 3 of `n/2` | *done* |
| Toom-3 | balanced | 5 | 5 of `n/3` | *done* |
| Toom-(3,2), Toom-(4,2) | 3:2 and 2:1 | 4, 5 | 4 of `n/3`, 5 of `n/4` | padding + Karatsuba, or schoolbook |
| Toom-4 | balanced | 7 | 7 of `n/4` | Toom-3 above a threshold |
| Toom-(4,3), Toom-(5,3), Toom-(6,3), Toom-(5,4) | other ratios | 6–8 | | padding |
| Toom-6.5 (7 × 6 blocks) | balanced | 12 | 12 of `n/6.5` | Toom-4 above a threshold |
| Toom-8.5 (9 × 8 blocks) | balanced | 16 | 16 of `n/8.5` | Toom-6.5 above a threshold |
| Schönhage–Strassen FFT | balanced, huge | – | `O(n log n log log n)` | Toom-8.5 above a threshold |

Squaring gets the same ladder with the pointwise products replaced by squares.

## Where we are

The dispatcher is `AzNat.mulLimbsParam` in `Azurite/AzNat/Mul.lean`. It uses schoolbook when the
shorter operand has fewer than 16 limbs or the length ratio is below 1/4, otherwise pads both
operands to the longer length and runs Karatsuba (`Mul/Karatsuba.lean`, 264 lines, proof 1353
lines) below 256 limbs and Toom-3 (`Mul/ToomCook3.lean`, 230 lines, proof 922 lines) above.
Squaring mirrors this in `Square.lean` and `Square/`.

Toom-3 is written in the style we should generalize from:

- one recursive function `toomCook3MulLimbsRec` over slices `(lo, len)` of the limb arrays,
  recursing on `len` with `termination_by`;
- evaluation helpers (`sum012`, `sum124`, `diffM1`) that return fresh `(k + 1)`-limb buffers, with
  the one signed evaluation `a₀ − a₁ + a₂` handled as a magnitude plus a `Bool` sign;
- a non-recursive interpolation helper `toomCook3Interpolate` on `AzNat` values, with the two
  exact divisions done by `>>> 1` and the constant-folded `divBy6`;
- the proof split into `toomCook3_nat_identity` (the algebra, stated over `ℕ` with truncated
  subtraction and the sign bits), `*_toNat` lemmas for each helper, and the recursion lemma.

Two facts about our cost model matter for everything below. First, from the benchmark notes:
`Array UInt64` is boxed, so every limb store allocates, and the linear-time passes of an
evaluation/interpolation stage are relatively far more expensive than in a C implementation with
unboxed limbs. That is why our Toom-3 crossover is as high as 256 limbs, and it will push every
higher crossover up by a similar factor. Second, `AzNat` is currently 30–70× slower than Lean's
built-in `Nat` at a few thousand bits. Higher Toom variants shrink the number of limb products
but add linear passes, so their payoff here is smaller than with unboxed limbs and only appears
at sizes of thousands of limbs. The ladder is still the right structure to build, and it is a
prerequisite for the FFT stage, but constant-factor work on limb arithmetic remains the larger
lever for the sizes the library uses today (APR-CL at 247 digits is 13 limbs and never leaves
schoolbook).

## Design changes before adding variants

### 1. Signed intermediates: do evaluation and interpolation in `AzInt`

Toom-3 has one negative evaluation point and threads a `Bool` sign by hand. Toom-4 has three
signed points (−1, −2, and the scaled 1/2 point is positive), Toom-6.5 has five, Toom-8.5 has
seven, and the interpolation sequences subtract freely. Hand-rolled signs would make the code and
the `ℕ`-with-truncated-subtraction proofs unmanageable.

Proposal: evaluate each operand at every point into an `AzInt` (sign-magnitude, which we already
have with proven `toInt` lemmas for `+`, `-`, `mulUInt64`, shifts), multiply pointwise as
`sign := (sa == sb), magnitude := recursive AzNat multiplication`, and run the whole
interpolation in `AzInt`. The final coefficients are provably nonnegative, so the last step
converts back to `AzNat` magnitudes for assembly. The algebra of each variant then becomes a
polynomial identity over `ℤ`, which `ring`/`linear_combination` proves in one line, with exact
divisions handled by `Int.mul_ediv_cancel_left` after `ring` shows the numerator is the divisor
times the intended value. This should make the Toom-4 proof shorter than the Toom-3 proof despite
having seven points.

Toom-3 itself can stay as is; rewriting it in the new style is optional and would only be worth
doing to have one uniform framework.

### 2. Exact division by small constants

Interpolation needs exact division by powers of two (a shift) and by small odd numbers. Toom-3
needed 6. The table below (from `scripts/ToomInterpolation.lean`) lists the odd divisors of the
closed-form solution for each variant; an operation sequence (see 3) never needs more than these
and usually needs fewer.

The right tool is exact division by a single limb via the modular inverse, Algorithm 1.10 of
Brent–Zimmermann (Jebelean's algorithm): for odd `d`, `d⁻¹ mod 2^64` is a constant, and the
quotient limbs are produced low to high as `q_i = (r_i · d⁻¹) mod 2^64` with a borrow of the high
half of `q_i · d`. This is `AzNat/ExactDivOdd.lean` with `exactDivOdd (d dinv) (n)`, proven for `d ∣ n` in
`Equiv/ExactDivOdd.lean` (*done*), plus `AzInt` wrappers to come; `divBy6` can later become
`>>> 1` followed by `exactDivOdd 3`.
The Möller–Granlund machinery is not needed here because the division is known to be exact.

### 3. Operation sequences, not closed forms

The closed-form rows of the inverse Vandermonde matrix have large denominators (180 for Toom-4)
and many terms. The published sequences (Bodrato–Zanoni for Toom-4, Bodrato for Toom-6.5 and
Toom-8.5) reach the coefficients with about one addition or subtraction per point per step and
divisions only by 2, 3, 9, 15, 45 and similar. We derive our own sequence for each variant with
the interpolation tool: start from the point products, repeatedly combine the pair that
eliminates a coefficient, and check the result against the matrix. The sequence is then
transcribed into the Lean interpolation helper, and the `ℤ` identity is what the proof checks, so
the sequence itself does not need to be optimal, only correct and free of inexact divisions.

### 4. Unbalanced operands without padding

Padding the shorter operand to the longer length costs a full balanced multiplication at the
larger size. Toom-(r, s) splits `A` into `r` blocks and `B` into `s` blocks of the same block size
and needs `r + s − 1` products. With the `AzInt` framework, Toom-(3,2) and Toom-(4,2) are the
Toom-3 points on a different block structure (`AzInt` evaluation of `B` with fewer blocks), so
they share the interpolation helper: Toom-(4,2) uses exactly Toom-3's five points and Toom-(3,2)
drops the point 2. Toom-(4,3) and Toom-(5,3) similarly reuse the six- and seven-point helpers.

The dispatcher then chooses by the ratio `lenA / lenB`: near 1 balanced, near 3/2 Toom-(3,2),
near 2 Toom-(4,2), near 4/3 Toom-(4,3), near 5/3 Toom-(5,3), near 2 with large operands Toom-(6,3),
and for ratios beyond what any variant covers, the standard treatment of unbalanced operands
(Brent–Zimmermann §1.3.5): split the longer operand into pieces the size of the shorter and add
the partial products, which we can prove once generically.

### 5. Squaring

Each variant's squaring version is the same recursion with one operand: evaluations of `A` only,
squares instead of products (all signs positive, so the interpolation helper is reused with
nonnegative inputs), and the squaring ladder as the recursive call. Toom-3 squaring already works
this way and is 90 lines plus a 214-line proof; higher variants will be similar.

## Interpolation data

Derived by `lake env lean --run scripts/ToomInterpolation.lean` (Vandermonde inverse over
`AzRat` with `AzMatrix`, checked exactly against the identity):

| variant | blocks `A × B` | points | products | closed-form denominators (odd part, factored) |
|---|---|---|---|---|
| toom22 | 2 × 2 | `0, 1, ∞` | 3 | none |
| toom32 | 3 × 2 | `0, ±1, ∞` | 4 | 2 |
| toom33 | 3 × 3 | `0, ±1, 2, ∞` | 5 | 2, 6 = 2·3 |
| toom42 | 4 × 2 | `0, ±1, 2, ∞` | 5 | 2, 6 |
| toom43 | 4 × 3 | `0, ±1, ±2, ∞` | 6 | powers of 2 to 8, 3 |
| toom52 | 5 × 2 | `0, ±1, ±2, ∞` | 6 | powers of 2 to 8, 3 |
| toom44 | 4 × 4 | `0, ±1, ±2, 1/2, ∞` | 7 | powers of 2 to 8; 3, 9, 45 = 3²·5 |
| toom53 | 5 × 3 | `0, ±1, ±2, 1/2, ∞` | 7 | same as toom44 |
| toom54 | 5 × 4 | `0, ±1, ±2, ±1/2, ∞` | 8 | powers of 2 to 8; 9, 45 |
| toom63 | 6 × 3 | `0, ±1, ±2, ±1/2, ∞` | 8 | same as toom54 |
| toom65 | 7 × 6 | `0, ±1, ±2, ±1/2, ±4, ±1/4, ∞` | 12 | powers of 2 to 128; primes 3, 5, 7, 17 |
| toom85 | 9 × 8 | `0, ±1, ±2, ±1/2, ±4, ±1/4, ±8, ±1/8, ∞` | 16 | powers of 2 to 8192; primes 3, 5, 7, 11, 13, 17, 31 |

The closed-form rows for the two high variants have denominators in the millions (for example
`3⁵·5²·7·17 = 722925` for toom65), which is why an operation sequence is required there: the
Toom-6.5 and Toom-8.5 sequences in the literature divide only by small products of these primes
(such as 3, 9, 15, 45 and 255 = 3·5·17), one at a time. The prime sets, however, are exactly what
the table says, so the exact-division primitive must support at least 3, 5, 7, 11, 13, 17 and 31,
which a single `exactDivOdd` with a per-divisor inverse constant does. For everything up to
toom63 the closed forms are already small enough to implement directly if a sequence is not
worth the trouble.

The Toom-3 row reproduces the formulas in `toomCook3Interpolate`:
`c₁ = (−3v₀ + 6v₁ − 2v₋₁ − v₂ + 12v_∞)/6`, `c₂ = (−2v₀ + v₁ + v₋₁ − 2v_∞)/2`,
`c₃ = (3v₀ − 3v₁ − v₋₁ + v₂ − 12v_∞)/6`.

## Milestones

1. **Exact division by a limb** (`exactDivOdd`, proven; `divBy6` rewritten on top of it). Small
   and self-contained; unblocks everything else.
2. **Signed evaluation framework**: `AzInt` block evaluation at the points `0, ±1, ±2, ±1/2, ±4,
   ±1/4, ±8, ±1/8, ∞` as a small library with `toInt` lemmas, plus pointwise signed products.
3. **Toom-4** (balanced, 7 points), with the `ℤ` identity proof. This is the template for all later
   variants. Squaring version alongside.
4. **Toom-(3,2), Toom-(4,2)** and the ratio-based dispatcher with the generic fallback loop for
   extreme ratios (Toom-(4,3) and Toom-(5,3) wait for the ratio sweep of milestone 5 to show a
   gap worth filling). This is the most practically useful step for the library's own users,
   because polynomial and matrix code multiplies unbalanced operands constantly.
5. **Thresholds**: extend `Tune.lean` with a Toom-4 cutoff sweep and a ratio sweep for the
   unbalanced variants. Needs a quiet machine; expect the Toom-4 crossover in the 600–1000 limb
   range given the Toom-3 experience.
6. **Toom-6.5 and Toom-8.5**, only if the Toom-4 measurements suggest they will win before the FFT
   crossover in our cost model. Whether such a window exists between Toom-4 and the FFT is an
   empirical question; with our allocation overhead it may not, in which case Toom-4 hands over
   to the FFT directly.
7. **Schönhage–Strassen FFT**: the user will walk through the textbook description
   (Brent–Zimmermann §2.3, or von zur Gathen–Gerhard §8.3). It needs modular arithmetic in
   `ℤ/(2^N + 1)` on limb arrays, which is a natural extension of `AzZModPow2`.

Milestones 1–4 need no benchmarking. Milestone 5 is where the machine has to be quiet.

## Sources

Brent–Zimmermann, *Modern Computer Arithmetic*, Chapter 1 (Toom–Cook, Algorithm 1.4; exact
division, Algorithm 1.10) and §2.3 (FFT). Marco Bodrato and Alberto Zanoni, *Integer and
polynomial multiplication: towards optimal Toom–Cook matrices*, ISSAC 2007 (Toom-4 and the point
set 0, ±1, ±2, 1/2, ∞). Marco Bodrato, *Towards optimal Toom–Cook multiplication for univariate
and multivariate polynomials in characteristic 2 and 0*, WAIFI 2007 (interpolation sequences).
Marco Bodrato, *High degree Toom'n'half for balanced and unbalanced multiplication*, ARITH 2011
(Toom-6.5 and Toom-8.5). Tudor Jebelean, *An algorithm for exact division*, J. Symbolic
Computation 15 (1993) (exact division by the modular inverse). These are published descriptions;
no implementation code is consulted.

## Status log

* **2026-09-26 — Milestone 1 done: `AzNat.exactDivOdd`.** `Azurite/AzNat/ExactDivOdd.lean`
  (Jebelean's exact division by an odd limb, low-to-high, one `wideMul` and one borrow
  subtraction per limb; inverse constants `inv3`, `inv5`, `inv9`, `inv45` checked by `decide`) and
  `Equiv/ExactDivOdd.lean` (`exactDivOdd_toNat`: `d * dinv = 1 → d ∣ n → (exactDivOdd d dinv
  n).toNat = n.toNat / d.toNat`, via the invariant `T_i = hi + borrow + d · (Q / β^i)`; 3-axiom).
  `divBy6` is left as is for now so Toom-3 is untouched; the Toom-4 interpolation will use
  `>>> k` followed by `exactDivOdd`.
* **2026-09-26 — Milestone 2 done: the signed evaluation framework.** `Azurite/AzNat/Mul/ToomEval.lean`
  and `Equiv/Mul/ToomEval.lean`: `blocks`, `hornerInt64`, `signedMulWith`, `AzInt.exactDivOdd`,
  `assemble`, each with its integer specification (`polyEvalInt`), the triangle bound for fitting
  evaluations into `n` limbs, and the block decomposition `sliceVal_eq_polyEval_blocks`. All
  3-axiom. Toom-4 now needs only: the block sizes and bounds for `k = ⌈len/4⌉`, the seven
  evaluations, the recursive products through `signedMulWith (k + 1)`, an interpolation helper
  in `AzInt`, and its `ring` identity.
* **2026-09-26 — Milestone 3 (multiplication half) done: Toom-4.** `Azurite/AzNat/Mul/ToomCook4.lean`
  (`toomCook4Interpolate`, `toomCook4MulLimbsRec` with `k = ⌈len/4⌉`, all seven products through
  `signedMulWith (k + 1)` with the recursive call; `mulToomCook4` for tests/benchmarks) and
  `Equiv/Mul/ToomCook4.lean` (`toomCook4Interpolate_toInt`, the array-free `toomCook4_core_toNat`,
  `toomCook4MulLimbsRec_toNat`, `toNat_mulToomCook4`; 3-axiom). The interpolation sequence was
  derived by hand and needs exact division only by 2, 4, 3, 5, 9 (no 45):
  `c4 = (e2 − 4e1)/12`, `c3 = (17 o1 − o2 − h)/9`, `c5 = ((o2 − o1)/3 − c3)/5`,
  `c1 = ((h − o1)/3 − c3)/5`. Proof size: 330 lines for seven points, versus 922 for Toom-3's five
  — the `AzInt` framework paid off as expected. Dispatcher integration waits for the threshold sweep of milestone 5.
  Efficiency note: `v0` and `v∞` are computed on `k + 1` limbs like the other five; using `k` and
  `m` limbs for them is a later constant-factor refinement.
* **2026-09-26 — Milestone 3 complete: Toom-4 squaring.** `Azurite/AzNat/Square/ToomCook4.lean` and
  `Equiv/Square/ToomCook4.lean`: the same recursion with one operand, squares through the new
  framework helper `signedSquareWith`, and `toomCook4Interpolate` reused unchanged. The algebra was
  factored into `toomCook4_assemble_toNat` (seven product equations in, assembled product out), so
  the squaring proof is 60 lines; `toNat_squareToomCook4` is 3-axiom.

* **2026-09-26 — Milestone 4 done: unbalanced variants and the new dispatcher.**
  `Azurite/AzNat/Mul/ToomUnbalanced.lean`: Toom-(3,2) (points `0, ±1, ∞`, `toomInterp4`) and
  Toom-(4,2) (Toom-3's points `0, ±1, 2, ∞`, `toomInterp5` in `AzInt`), both one-shot with a common
  block size `k = max ⌈lenA/r⌉ ⌈lenB/s⌉` and every product handed to a `BalancedMul` (the balanced
  ladder at `k + 1` limbs); `mulChunksLimbs` splits the longer operand into pieces the size of the
  shorter and assembles the partial products. `Azurite/AzNat/Mul.lean` now has `MulThresholds`
  (schoolbook 16, Toom-3 256, Toom-4 1024 provisional, unbalanced 32), `balancedMulLimbs` (the
  ladder), and `mulLimbsOrdered` choosing by the ratio `lenA/lenB`: below 5/4 pad and go
  balanced, below 7/4 Toom-(3,2), below 9/4 Toom-(4,2), beyond that the chunk loop; small
  operands stay schoolbook. Toom-4 joined the squaring dispatcher
  (`squareDispatchToomCook4Cutoff = 512`, provisional). Proofs: `Equiv/Mul/ToomUnbalanced.lean`
  (interpolation lemmas, a length-generic Horner bound `hornerInt64_abs_lt`, the two
  assemble-algebra lemmas, and the three `*_toNat` theorems under the hypothesis that the balanced
  multiplier is correct) and `Equiv/Mul/Dispatch.lean` (`toNat_mul` re-established over the new
  dispatcher). `AzInt.mulUInt64`/`mulInt64` moved to `AzInt/MulSmall.lean` to keep the evaluation
  framework off the dispatcher's import cycle; dispatcher proofs for squaring live in
  `Equiv/Square/Dispatch.lean`. Guards for milestones 1–4 are in `Azurite/AzNat/Tests/ToomCook.lean`.
  Toom-(4,3) and Toom-(5,3) are deferred until the ratio sweep (milestone 5) shows a gap between
  the (3,2)/(4,2) bands and the balanced ladder worth filling.

* **2026-09-27 — Milestone 5 done: thresholds measured.**  New tuners in `Azurite/AzNat/Tune.lean`
  (`tune_aznat_*` in `Benchmark/Main.lean`): per-size A/B crossover tables (`school` vs top-level
  Karatsuba, Karatsuba vs top-level Toom-3, Toom-3 vs top-level Toom-4, for multiplication and
  squaring), 2-D `(schoolbook, toomCook3)` sweeps of the production dispatchers over the
  geometric random distribution, Toom-4 cutoff sweeps of the dispatchers, the ratio-band table
  `tune_aznat_unbalanced` (shorter length × ratio × five strategies), and an old-vs-new
  dispatcher comparison.  Config keys are comma-separated (`"schoolbook:48,toomCook3:256"`).
  Findings on a quiet machine (Apple Silicon, single thread):
  * The lower rungs were stale.  Schoolbook now ties top-level Karatsuba at 48 limbs (the old
    cutoff was 16) and top-level Karatsuba squaring at 96 limbs (old 32); the constant-factor work
    on schoolbook since the earlier tuning moved both crossovers.  Toom-3 ties Karatsuba at
    192–256 limbs and wins from 320 (both kinds); the 2-D sweeps are flat from 128 to 256 for
    multiplication and best at 320 for squaring.
  * Toom-4 at the top level stops losing to Toom-3 at 512 limbs and wins by 3–6 % above 1024
    (squaring similar); the dispatcher sweeps are flat from 384 to 1024.  The gain is small
    because in our cost model the seven evaluations' linear passes cost nearly what a Toom-3
    product saves, as predicted in "Where we are".
  * Unbalanced bands are the same at every shorter length from 96 to 512 limbs: padding to the
    longer length wins up to ratio 5/4, Toom-(3,2) from 11/8 to 7/4, Toom-(4,2) from 15/8 to 5/2,
    the chunk loop from 11/4.  Below 96 limbs schoolbook beats every variant except padding at
    ratios up to 9/8.  Toom-(4,3)/(5,3) stay deferred: the (3,2)/(4,2) bands leave no gap.
  * Final constants: `MulThresholds {schoolbook 48, toomCook3 256, toomCook4 512, unbalanced 96}`;
    `mulLimbsOrdered` bands `≤ 5/4` padded (`≤ 9/8` below `unbalanced`, else schoolbook),
    `< 15/8` Toom-(3,2), `≤ 21/8` Toom-(4,2), else chunks; squaring 96 / 320 / 512.
  * Against the pre-milestone-4 dispatcher on the geometric random distribution the new one
    takes 69 % of the time at 4096 mean bits, 73 % at 16384, 61 % at 65536, 47 % at 262144.

* **2026-09-30 — Constant-factor work on schoolbook: two-row blocking (benchmark pending).**
  The FFT profiling (`docs/fft_plan.md`, 2026-09-29 entry) put the cost of a schoolbook limb
  product at roughly 60–70 % software `wideMul` and the rest boxing of the fresh accumulator limb,
  with every arithmetic pass over `n` limbs costing 10–14 ns per limb.  `schoolbookMulLimbs`
  now consumes two limbs of `b` per pass (`mulAdd2Limbs`, outer loop `schoolbookMulLimbs.go2`):
  each step does two `mulAddWithCarry`s against one `a` limb, keeps a two-limb running carry and
  stores one accumulator limb, so accumulator writes (and the per-row `set` of the carry limb,
  now two limbs per fused row) are halved against two single rows; an odd final row goes through
  the old `schoolbookMulLimbs.go`.  Correctness: `mulAdd2Limbs_toNat` (two uses of
  `UInt64.mulAddWithCarry_eq` per step) and `schoolbookMulLimbs.go2_correct`, which reduces the
  fused step to a window lemma (`toNatLimbsList_take_window`: lists agreeing outside
  `[j, j + lenA + 2)` differ in value only by that window) and the zero-tail invariant of the
  single-row proof; `schoolbookMulLimbs_toNat` is unchanged in statement.  Not yet benchmarked
  (the machine was busy); the schoolbook / Karatsuba crossover (48) and the squaring constant
  may move once it is.  The remaining lever per the cost model, an `@[extern]` 64×64→128
  multiply, is a policy decision for the user, not taken here.

* **2026-10-01 — Two-row passes measured and extended to squaring; thresholds retuned.**  The
  user ruled out `@[extern]` primitives: Azurite stays pure Lean.  Measured against the
  pre-change binary on a quiet machine (µs per operation, top level only):
  * Schoolbook multiplication: 7 → 4 at 32 limbs, 27 → 16 at 64, 106 → 63 at 128,
    416 → 244 at 256 (about 40 % less).  Top-level Karatsuba, whose base case is schoolbook,
    88 → 55 at 128 and 330 → 202 at 256.  The schoolbook / Karatsuba tie moved from 48 limbs to
    64–80 (the 2-D ladder sweeps are best at 64 at mean 16384 and 65536 bits, flat 64–80 at
    4096); top-level Toom-3 now ties Karatsuba at 320 (3 % slower at 256); the FFT is 3 %
    slower than the Toom ladder at 5120 limbs and 3 % faster at 6144.  `fftMul` at 16384 limbs:
    90.5 → 76.7 ms (pointwise products 49.0 → 34.5 ms), Toom ladder 132 → 105 ms.
  * Squaring did not move in that run (`schoolbookSquareLimbs` has its own loop), so the
    off-diagonal accumulation got the same treatment: `schoolbookSquareLimbs.offDiag.go2`
    takes rows `i` and `i + 1` together (the lone product `a_{i+1} a_i` seeds the two-row pass
    `mulAdd2Limbs.go` over the shared slice `a[i+2 ..]`, with the two-limb carry landing where
    the single rows would have put theirs); proof `offDiag.go2_correct` via the window lemma
    and two `partialOffDiagSum_step`s.  Schoolbook squaring: 5 → 3 at 32 limbs, 16 → 10 at 64,
    57 → 37 at 128, 218 → 133 at 256 (about 35 % less); the schoolbook / Karatsuba tie moved
    from 96 to 160 limbs (2-D sweeps best at 96–128), Toom-3 squaring wins from 384 (loses by
    3–8 % at 192–320).  The squaring FFT crossover table is noisy around 4096 (FFT wins at
    3072 and 5120, loses at 4096); the cutoff stays.
  * New constants: `MulThresholds {schoolbook 64, toomCook3 320, toomCook4 512, unbalanced 96,
    fft 6144}`; squaring 128 / 384 / 512 / 4096.  The unbalanced bands were not re-measured;
    they depend on ratios of the same ladder and should be re-swept with `tune_aznat_unbalanced`
    when convenient.
