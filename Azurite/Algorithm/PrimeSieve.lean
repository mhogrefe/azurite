/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  The sieve of Eratosthenes — with the table BITPACKED into an `AzNat`.

  `primeSieve n : AzNat` is the primality table for `[0, n]` as a bitset:
  bit `j` is set iff `j` is prime.  The table starts as
  `lowMask (n+1)` with bits `0` and `1` cleared, and for each
  `d = 2, 3, …` with `d² ≤ n`, if bit `d` is still set (which at `d`'s
  turn happens exactly when `d` is prime — a composite's least prime
  factor has already cleared it), the multiples `d², d² + d, …` are
  cleared.  The classical `O(n log log n)` sieve; correctness —
  `(primeSieve n).testBit j = true ↔ Nat.Prime j` for `j ≤ n` — is
  `Azurite.primeSieve_testBit_iff` in
  `Azurite/Algorithm/Equiv/PrimeSieve.lean`, by the invariant "bit `j` is
  set iff `2 ≤ j ≤ n` and every prime `p < d` dividing `j` has `p² > j`".

  The `AzNat` bitset is 8× denser than an `Array Bool`, mutates in place
  under linear use (`clearBit` is a limb write), and its bit-access API
  comes with proven `toNat` bridges — exactly what the invariant proof
  consumes.  Loop indices are plain `ℕ`: sieve ranges are memory-bound
  long before any index approaches word size.

  `primesUpTo n` extracts the sorted prime list; `smallPrimes` is the
  first hundred primes as a literal (guarded against the sieve), for use
  as trial-division bases, Miller–Rabin bases, and Pratt certificate
  leaves without re-sieving.
-/
import Azurite.AzNat.TestBit
import Azurite.AzNat.ClearBit
import Azurite.AzNat.LowMask
import Azurite.AzNat.Conversion

namespace Azurite

namespace AzNat

/-- Clear bits `j₀, j₀ + d, j₀ + 2d, …` (while `≤ n`). -/
def sieveMark (n d : Nat) : Nat → Nat → AzNat → AzNat
  | 0, _, s => s
  | fuel + 1, j, s =>
    if j ≤ n then sieveMark n d fuel (j + d) (s.clearBit j) else s

/-- The main loop: process `d = d₀, d₀ + 1, …` while `d² ≤ n`, clearing
the multiples of each still-set `d` from `d²` on. -/
def sieveLoop (n : Nat) : Nat → Nat → AzNat → AzNat
  | 0, _, s => s
  | fuel + 1, d, s =>
    if d * d ≤ n then
      sieveLoop n fuel (d + 1)
        (if s.testBit d then sieveMark n d (n + 1) (d * d) s else s)
    else s

/-- **The sieve of Eratosthenes**, bitpacked: bit `j` of the result is set
iff `j` is prime (for `j ≤ n`). -/
def primeSieve (n : Nat) : AzNat :=
  sieveLoop n (n + 1) 2 (((lowMask (n + 1)).clearBit 0).clearBit 1)

/-- The primes up to `n`, in increasing order. -/
def primesUpTo (n : Nat) : Array Nat :=
  let table := primeSieve n
  (Array.range (n + 1)).filter (fun j => table.testBit j)

/-- **The first 100 primes** (up through `541`), as a literal — the shared
small-prime table for trial division, Miller–Rabin bases, and Pratt
certificate leaves.  Guarded against the sieve below; each entry's
primality is a theorem (`smallPrimes_prime`). -/
def smallPrimes : Array Nat :=
  #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
    67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
    139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211,
    223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
    293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461,
    463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541]

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

-- the bitset at `n = 10`: bits 2, 3, 5, 7 ⟹ 4 + 8 + 32 + 128 = 172
#guard (primeSieve 10).toNat == 172
#guard primesUpTo 30 == #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

-- the cache IS the sieve's first hundred primes
#guard smallPrimes == primesUpTo 541
#guard smallPrimes.size == 100

-- π(10^4) = 1229, π(10^5) = 9592 (classic checkpoints)
#guard (primesUpTo 10000).size == 1229
#guard (primesUpTo 100000).size == 9592

-- degenerate ranges
#guard primesUpTo 0 == #[]
#guard primesUpTo 1 == #[]
#guard primesUpTo 2 == #[2]

end Tests
