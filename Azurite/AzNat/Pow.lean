/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.SlidingWindowPow
import Azurite.AzNat.Instances
import Azurite.AzNat.ToStringBase

/-!
# Exponentiation for AzNat

Computable exponentiation `a ^ n` for multi-limb naturals, in `O(log n)` `AzNat`
multiplications. Two named variants are provided so they can be benchmarked against each other:

- `AzNat.pow` — **sliding-window** exponentiation (`Azurite.slidingWindowPow`). This is also the
  `npow` of the `CommSemiring` instance (`Instances.lean`), so `a.pow n = a ^ n` definitionally
  and `(a : AzNat) ^ n` runs the sliding-window algorithm.
- `AzNat.powBinary` — **right-to-left binary** exponentiation (`Azurite.fastPow`), the older
  algorithm, kept as a benchmarking baseline.

Both route their squarings through AzNat's dedicated three-way `square` (schoolbook / Karatsuba /
Toom-Cook 3) via the `instSquareAzNat` instance (`Instances.lean`), so a squaring costs a single
subquadratic squaring rather than a general multiplication.

## Main definitions

- `Azurite.AzNat.pow a n`, `Azurite.AzNat.powBinary a n`.

The `ℕ`-equivalence proofs live in `Azurite.AzNat.Equiv.Pow` (`toNat_pow`, `toNat_powBinary`,
`pow_eq_powBinary`, `ofNat_pow`, `ofNat_powBinary`).
-/

namespace Azurite.AzNat

/-- Exponentiation for `AzNat` via **sliding-window** exponentiation, in `O(log n)`
multiplications (with a small precomputed table of odd powers). Definitionally equal to
`a ^ n`, since it is the `CommSemiring`'s `npow`. -/
def pow (a : AzNat) (n : ℕ) : AzNat :=
  Azurite.slidingWindowPow a n

/-- Exponentiation for `AzNat` via **right-to-left binary** exponentiation (exponentiation by
squaring) — the older algorithm, kept for benchmarking against `pow`. -/
def powBinary (a : AzNat) (n : ℕ) : AzNat :=
  Azurite.fastPow a n

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard AzNat.toString ((AzNat.ofNat 3).pow 4) == "81"
#guard AzNat.toString ((AzNat.ofNat 2).pow 10) == "1024"
#guard AzNat.toString ((AzNat.ofNat 7).pow 0) == "1"
#guard AzNat.toString ((AzNat.ofNat 7).pow 1) == "7"
#guard AzNat.toString ((AzNat.ofNat 5).pow 3) == "125"
#guard AzNat.toString ((AzNat.ofNat 2).pow 64) == "18446744073709551616"
-- huge targets (48- and 302-digit numerals): kept as algorithm-level equality
-- against `AzNat.ofNat`, for readability, rather than a giant string literal
#guard (AzNat.ofNat 3).pow 100 = AzNat.ofNat (3 ^ 100)
#guard (AzNat.ofNat 2).pow 1000 = AzNat.ofNat (2 ^ 1000)

-- The sliding-window and binary algorithms agree across a range of exponents.
#guard (List.range 60).all (fun n => (AzNat.ofNat 3).pow n = (AzNat.ofNat 3).powBinary n)
#guard (List.range 40).all (fun n => (AzNat.ofNat 12345).pow n = (AzNat.ofNat 12345).powBinary n)

end Tests

end Azurite.AzNat
