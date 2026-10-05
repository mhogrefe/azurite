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
- `Azurite/AzNat/Gcd/HalfBinary.lean`: `Mat2` (2×2 `AzInt` matrices), `binaryDivide`
  (quotient via `AzZModPow2.invOdd`), `halfBinaryGcdWord` (base case for `k ≤ 31`: words and
  machine-size `Int` cofactors), `halfBinaryGcd` (structural recursion on fuel `k + 1`),
  `halfBinaryGcdDriver` (checked exact shifts, binary-GCD fallback), `gcdHalfBinary`.
- `Azurite/AzNat/Gcd.lean`: `gcd` dispatches at `halfBinaryGcdThreshold` bits (1024, tuned
  2026-10-05); `gcdHalfBinaryWith` exposes the threshold for benchmarking.

## Correctness architecture

`natAbs_detInt_halfBinaryGcd`: every returned matrix has `|det| = 2^{2j}`.  `OddEquiv m n`
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

## Open

- Mid sizes (300–1000 bits) still cost about what the binary GCD costs; a quadratic middle
  layer (MCA Alg. 1.17 DoubleDigitGcd or an LSB word-level analogue) could help there.
- Scaling 65536 → 262144 bits was 8.4× (49 ms → 417 ms), above the expected ~5×; check whether
  the `n/2 × n`-bit matrix products reach the FFT range and whether `lowBits`/`apply` allocate
  more than needed.
- Optional: formalize Theorem 1.9 to prove the runtime exactness checks never fail.
- Extended / half-gcd outputs (cofactors) for rational reconstruction, if needed later.
