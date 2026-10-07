# AzNat GCD plan (MCA §1.6)

Source: Brent & Zimmermann, *Modern Computer Arithmetic*, §1.6 (text supplied by the author in
chunks; algorithms implemented from that text and first principles — no GMP/Malachite code).

## Provenance rules

- Algorithms 1.16 (Euclid), 1.18 (binary GCD), 1.21 (BinaryDivide), 1.22 (HalfBinaryGcd) from MCA.
- The plain-GCD driver (half-gcd with `k = n/2`, one binary division, recurse) follows MCA's
  cost discussion for `G(n)`; the "make the first operand odd and the second even" preparation and
  the word-level base case are first principles.
- Correctness proofs are independent of MCA's Theorem 1.9 / Lemma 7 of Stehlé–Zimmermann: they
  rest on the determinant invariant only (see below).

## Design

- `Azurite/AzNat/Gcd/Binary.lean`: `gcdUInt64` (Euclid, constant fuel 130), `gcdBinary`
  (Stein, bulk `trailingZerosLimbs` shifts using the hardware `UInt64.trailingZeros`).
- `Azurite/AzNat/Gcd/HalfBinary.lean`: `Mat2` (2×2 `AzInt` matrices), `WordMat` (`Int64`
  cofactors), `Word2` (128-bit progress-only operands), `binaryDivide` (quotient via
  `AzZModPow2.invOdd`), `halfBinaryGcdWord` (base case for `k ≤ 63` on two-word operands with
  `Int64` cofactors, stopping early when a cofactor would exceed `2^{61 − j₀}`), `halfBinaryGcd`
  (structural recursion on fuel `k + 1`), `halfBinaryGcdDriver` with two regimes — **quadratic
  word rounds** (the LSB analogue of MCA Alg. 1.17 DoubleDigitGcd: one base case on the low 127
  bits, then `fusedCombine?` per output — one `linCombShift` pass computing the signed
  combination in two's complement with the shift by `2j` folded in (a low phase that only checks
  the discarded limbs, then a branch-free emission phase with hoisted shift words), plus a short
  `negLimbs` two's-complement fix-up when the difference is negative; ≈ 57 bits per round) up
  to
  `halfBinaryGcdQuadraticThreshold`, the `k = n/2` recursion above — checked exact shifts,
  binary-GCD fallback; `gcdHalfBinaryWith threshold quadThreshold`, `gcdHalfBinary`.
- `Azurite/AzNat/Gcd.lean`: `gcd` dispatches at `halfBinaryGcdThreshold` bits (64, tuned
  2026-10-05) to `gcdHalfBinary`; `halfBinaryGcdQuadraticThreshold = 65536` (tuned 2026-10-05
  with the two-word base case and the fused round).

## Correctness architecture

`natAbs_detInt_halfBinaryGcd`: every returned matrix has `|det| = 2^{2j}`.  The `Int64` base case
is exact because the loop checks before each step that every cofactor is at most `2^{61 − j₀}`
in magnitude (`abs_toInt_le_of_check`, `wordStep_exact`, `wordStep_quotient_bound`); nothing
about the 128-bit operand arithmetic (`Word2`) enters the proofs.  The fused pass is specified
by `linCombLimbs.go_spec_sub`/`_add` (induction on the limb count with all carries, closed by
`linear_combination` from the word-level carry identities), lifted to arrays by
`linCombLimbs.go_acc`.  The shift fold is proved by refinement: a pure `emitShift` on the raw
limbs equals the phased loop (`linCombShift.goLow_eq`/`goHigh_eq`) and has a value lemma in two
phases (`emitShift_val_high` = the shift-stream identity, `emitShift_val_low` = exactness as
divisibility); `negLimbs` has `toNatLimbsList_negLimbs`; `linCombShift_spec` packages value,
exactness flag, borrow and length, and `toInt_fusedCombine?` does the sign algebra on top.  `OddEquiv m n`
(same odd divisors) is preserved by applying such a matrix with exact division by `2^{2j}`
(`oddEquiv_gcd_of_mat`), by a binary-division step with *any* quotient
(`oddEquiv_gcd_binaryStep`), and by exact division of one operand by a power of two
(`oddEquiv_gcd_div_pow`).  The driver returns the odd part of the GCD
(`toNat_halfBinaryGcdDriver`); since its first operand is odd, that is the GCD
(`toNat_gcdHalfBinary`, `toNat_gcd`).  MCA Theorem 1.9 (remainder-sequence semantics) is used
only to argue progress and is not formalized.

## Status log

- 2026-10-04: profile showed gcd ≈ 100 % of AzRat cost.  Root causes fixed: `BitVec.ctz` on
  the hot path (→ `UInt64.trailingZeros`), bignum fuel in `gcdUInt64` (→ constant 130).
- 2026-10-05: half-binary GCD implemented and proven; textbook example (MCA p. 1.6.3,
  `a = 1889826700059`, `b = 421872857844`) reproduced; random cross-checks against `gcdBinary`
  up to 300 limbs.
- 2026-10-05: `az_nat_gcd` (random pairs, planted factor ≈ bits/3, so operands ≈ 4/3 of the
  listed bits): half-binary overtakes binary near 1024 operand bits; µs at 512/1024/2048/4096/
  16384/65536 listed bits: binary 78/232/787/2961/43897/689774, half-binary 75/209/493/1107/6636/
  49106.  Thresholds 768–1536 within 10 %; set `halfBinaryGcdThreshold := 1024`.  The word
  base-case bound 31 is fixed by `2k + 1 ≤ 63`.

- 2026-10-05 (middle layer): quadratic word rounds added to the driver.  First version (generic
  `AzInt` matrix path + binary division per round) was no faster than Stein; the lean round
  (`lowWord`, `applyWord`, two exact shifts) still lost because the base case cost 2.1 µs — all of
  it machine-size `Int` arithmetic and Nat-side helpers (`Int` matrix 2082 ns vs `Int64` 156 ns;
  `Nat` shift/`toUInt64` helpers 1695 ns vs pure `UInt64` 203 ns).  Final base case 0.13–0.16 µs.
  `az_nat_gcd` (µs, listed bits ≈ 3/4 of operand bits): 64: 2.2 (Stein 4.7); 128: 3.7 (10.0);
  256: 8.0 (28.7); 512: 20 (79); 1024: 54 (263); 2048: 172 (846; recursion alone 380);
  4096: 554 (3010; recursion 886); 8192: 1986; 65536: 45826.  `az_rat_profile` gcd µs at
  128/256/1024/4096/65536 bits: 2.2/5.2/38.5/367/33195 (before the arc: 1154/2160/9145/37730/
  986564).

- 2026-10-05 (two-word base case): `halfBinaryGcdWord` now takes `Word2` operands with
  `k ≤ 63`; cofactors stay `Int64` with a runtime magnitude check (mean `j` per call 57 of 63,
  0.8 µs per call).  `az_nat_gcd` (µs, listed bits ≈ 3/4 of operand bits): 64: 2.2; 128: 3.7;
  256: 7.5; 512: 17; 1024: 42; 2048: 109; 4096: 337; 8192: 1139; 16384: 4434; 65536: 42000
  (one-word rounds: 2.2/3.7/8.0/20/54/172/554/1986/5749/45826).  Threshold sweep: 16384 best or
  within noise everywhere; 32768+ loses from 44000 operand bits.  `az_rat_profile` gcd µs at
  128/256/1024/4096/16384/65536 bits: 2.7/5.7/31.5/237/2874/31025.

- 2026-10-05 (fused round): `fusedCombine?` replaces four `mulInt64` products, two sums and two
  exact shifts per round by two fused passes (one per output) plus a shift and, for a negative
  difference, a short `pow2 − T` fix-up.  Cost attribution at 4 limbs (ns): pass 140, trailing
  zeros 46, shift 93, fix-up 171 (half the time), one output ≈ 310 — about 20–25 % off the round;
  a first version using `Int64.toInt` for the magnitudes was slower (word-only `int64Abs`
  fixed it).  The quadratic rounds now beat the recursion to ≈ 80000 operand bits
  (`halfBinaryGcdQuadraticThreshold := 65536`).  `az_nat_gcd` (µs, listed bits ≈ 3/4 of operand
  bits): 256: 6.7; 1024: 34.5; 4096: 267; 8192: 849; 16384: 3144; 32768: 11794; 65536: 41000.
  `az_rat_profile` gcd µs at 256/1024/4096/16384/65536 bits: 5.0/27.5/193/2018/28471.

- 2026-10-05 (folded shift + in-place negation): `linCombShift` emits the shifted limbs directly
  and `negLimbs` replaces the `pow2 − T` fix-up.  A first single-loop version (phase tests and
  shift amounts recomputed per limb) measured no better than the separate shift; splitting into a
  low phase and a branch-free emission phase with hoisted word shift amounts won.  A/B against the
  single-loop binary (alternating runs, 12 inputs): 1024 listed bits 33 vs 37 µs, 4096: 250 vs
  327, 16384: 2770 vs 3880.  Lesson: these microbenchmarks vary 20–30 % between runs; compare
  binaries alternately in one session, and never time a binary without checking it rebuilt (an
  executable depends on the proof modules, so a stale `Equiv` build leaves the old binary in
  place).  Final `az_nat_gcd` (µs, listed bits ≈ 3/4 of operand bits): 256: 6.0; 1024: 32;
  2048: 85; 4096: 246; 8192: 790; 16384: 2822; 32768: 10498; 65536: 39532.  `az_rat_profile`
  gcd µs at 256/1024/4096/16384/65536 bits: 5.0/26.5/187/1827/26115.

- 2026-10-07 (extended GCD): `AzInt.egcd` was still the single-bit HAC 14.61 loop (now
  `egcdBinary`, `AzInt/ExtendedGcd/Binary.lean`).  New `AzInt/ExtendedGcd/HalfBinary.lean`:
  `egcdDriver` runs the plain driver's rounds (same checks and fallbacks) and pulls a Bézout row
  back through each round on return — `pullBack` (`Mat2`: four products), `pullBackWord` (word
  matrix: two `fusedCombine?` passes with `sh = 0`), `pullBackStep` (binary division: two shifts
  and one small product) — ending in `egcdBase` (`egcdBinary` on the magnitudes, signs folded in,
  gcd split as `2^e · odd`).  The row satisfies `s x + t y = 2^e g`; `fixUp` strips `2^e` with
  `k ≡ −t x⁻¹ (mod 2^e)` from `AzZModPow2.invOdd` (`x` odd), two products and two exact shifts —
  `O(M(n))`, no per-bit corrections.  `egcdHalfBinaryWith`/`egcdHalfBinary` prepare as
  `gcdHalfBinaryWith`; `egcd` dispatches at `egcdHalfBinaryThreshold` (= 64 bits, untuned).
  Proofs in `AzInt/Equiv/ExtendedGcd/HalfBinary.lean` (`ScaledBezout.Spec`/`GcdSpec` invariants,
  `egcdDriver_spec`, `fixUp_spec`, `egcdHalfBinaryWith_spec`); `egcd_bezout`/`egcd_gcd` keep
  their statements.  Cost per round relative to the plain gcd: ≈ 2× in the quadratic layer (two
  extra passes over the growing coefficients), ≈ 1.5× in the recursion (four balanced
  half-size products).  Not timed.  Possible follow-ups: a word-level extended Euclid base case
  (the 64-bit `egcdBinary` call is the fixed overhead), tuning `egcdHalfBinaryThreshold`.

## Open

- The round is now one fused pass per output plus a short negation half the time; the remaining
  cost is the pass itself (two `mulWithCarry` and a borrow per limb) and the base case (0.8 µs).
  A 3-word base case (`k ≤ 95`) would need 192-bit remainder arithmetic and cofactors that no
  longer fit `Int64`; not planned.
- (Resolved 2026-10-05.)  Scaling 65536 → 262144 bits was 8.4×; `az_nat_gcd_breakdown` (one
  top-level driver step, compiled timings) shows the gcd simply tracks multiplication in the
  Toom-4 range (1024 → 4096 limbs): half-gcd 18.9 → 149.6 ms (7.9×), matrix application
  4.8 → 40.4 ms (8.5×, = 4 unbalanced products with no overhead), balanced product
  1.75 → 14.4 ms (8.2×), full gcd 37.7 → 305 ms (8.1×); truncation, shifts and the binary
  division are negligible (< 0.1 ms).  The ~5× expectation assumed FFT-range multiplication,
  which only starts at `fft := 6144` limbs.  Nothing gcd-specific to fix; any gain would come
  from the multiplication ladder itself.
- Optional: formalize Theorem 1.9 to prove the runtime exactness checks never fail.
- (Resolved 2026-10-07.)  Extended GCD: see the status entry; half-gcd matrix outputs for rational
  reconstruction are still not exposed (the extended driver pulls back a row, not a matrix).
