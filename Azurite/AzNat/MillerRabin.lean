/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  The Miller–Rabin strong probable-prime test, as a PROVEN-SOUND
  compositeness filter.

  For odd `n ≥ 3` write `n − 1 = 2^s·d` with `d` odd.  A base `a` PASSES if
  `a ≡ 0, ±1 (mod n)` (no information), or `a^d ≡ ±1`, or
  `a^(2^i·d) ≡ −1` for some `1 ≤ i ≤ s − 1`.  Primes pass EVERY base
  (`millerRabin_eq_true_of_prime` in `Azurite/AzNat/Equiv/MillerRabin.lean`
  — Fermat plus the `±1` square-root dichotomy in the field `F_n`), so a
  `false` verdict is a PROOF of compositeness.  A `true` verdict proves
  nothing and is never trusted: it routes the candidate to a deterministic
  confirmation (today `isPrime`; the planned Lucas–Pratt certificate
  checker for large primes).  The probabilistic aspect of Miller–Rabin —
  a composite survives a random base with probability `≤ 1/4` — is only a
  statement about how often the filter is USEFUL, and never enters the
  trusted path.

  All arithmetic is limb-level: the powering is `AzZMod.powAzNat`
  (sliding-window, exponent read by bits), the `2^s·d` split is
  `trailingZeros`/`shiftRight`.

  The driver tests the first twelve primes as fixed bases (a strong
  deterministic filter in practice) plus `rounds` SplitMix64-seeded
  pseudorandom bases.
-/
import Azurite.AzZMod.Instances
import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Sub
import Azurite.Random.Gen

namespace Azurite

namespace AzNat

/-- The `−1`-hunting squaring chain: does some `x^(2^i)`, `0 ≤ i < fuel`,
equal `negOne`? -/
def mrChain (m : AzNat) [NeZero m.toNat] (negOne : AzZMod m) :
    ℕ → AzZMod m → Bool
  | 0, _ => false
  | fuel + 1, x => if x = negOne then true else mrChain m negOne fuel (x * x)

/-- One Miller–Rabin round at base `a` (`true` = passed).  Bases reducing
to `0, ±1 (mod n)` pass vacuously; `n ≤ 1` fails. -/
def millerRabinBase (n a : AzNat) : Bool :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    let s := ((n - 1).trailingZeros).getD 0
    let d := (n - 1).shiftRight s
    let a' := AzZMod.ofAzNat n a
    let negOne := AzZMod.ofAzNat n (n - 1)
    if a' = 0 ∨ a' = 1 ∨ a' = negOne then true
    else
      let x := a'.powAzNat d
      if x = 1 ∨ x = negOne then true
      else mrChain n negOne (s - 1) (x * x)
  else false

/-- All bases pass. -/
def millerRabinBases (n : AzNat) (bases : List AzNat) : Bool :=
  bases.all (millerRabinBase n)

/-- The first twelve primes, as fixed bases. -/
def mrSmallBases : List AzNat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37].map ofNat

/-- `rounds` pseudorandom bases from a `SplitMix64` stream. -/
def mrRandomBases : ℕ → Random.SplitMix64 → List AzNat
  | 0, _ => []
  | rounds + 1, g =>
    let (u, g') := (Random.RandomGen.next g : UInt64 × Random.SplitMix64)
    ofNat u.toNat :: mrRandomBases rounds g'

/-- **The Miller–Rabin compositeness filter**: twelve fixed prime bases
plus `rounds` pseudorandom ones.  `false` verdicts are PROVEN composite
(`millerRabin_eq_false_imp_not_prime`); `true` verdicts are "probably
prime" and must be confirmed deterministically. -/
def millerRabin (n : AzNat) (rounds : ℕ) (seed : UInt64) : Bool :=
  millerRabinBases n
    (mrSmallBases ++ mrRandomBases rounds (Random.mkSplitMix64 seed))

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! ### Primes pass, composites fail

Small primes and composites; a Carmichael number (`561`, a Fermat liar
for every coprime base, caught by the strong test); a large prime
(`2^61 − 1`, Mersenne) and its neighbors; and a strong-pseudoprime
example (`2047 = 23·89` passes base 2 alone but not the full driver). -/

section Tests

open Azurite Azurite.AzNat

private def mr (n : ℕ) : Bool :=
  millerRabin (AzNat.ofNat n) 8 0

#guard mr 2 && mr 3 && mr 5 && mr 7 && mr 97 && mr 1009
#guard !(mr 0) && !(mr 1) && !(mr 4) && !(mr 9) && !(mr 91) && !(mr 1001)
-- Carmichael numbers (Fermat liars for all coprime bases)
#guard !(mr 561) && !(mr 1105) && !(mr 41041)
-- 2047 = 23·89 passes base 2 alone…
#guard millerRabinBases (AzNat.ofNat 2047) [AzNat.ofNat 2]
-- …but not the driver
#guard !(mr 2047)
-- Mersenne prime 2^61 − 1 and neighbors
#guard mr 2305843009213693951
#guard !(mr 2305843009213693949) && !(mr 2305843009213693953)

end Tests
