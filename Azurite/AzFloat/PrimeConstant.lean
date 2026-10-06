/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Parity
import Azurite.AzNat.ShiftRight

/-!
# The prime constant

`ρ = Σ_{n prime} 2^(−n) = 0.011010100010100010…₂ ≈ 0.4146825099`: bit `n` of the expansion is
`1` exactly when `n` is prime.  The first `64 N` bits are therefore the prime sieve up to
`64 N` read backwards: `primeConstantLimbs N` fills `N` words from the sieve's bitmap
(`primeSieve`, one `testBit` per bit, `wordOfBits`), bit `m` of the integer being
`1` iff `64 N − m` is prime.  As for the Prouhet–Thue–Morse constant, rounding to `p` bits
uses the first `p + 1` significant bits (the expansion starts `0.01`) and `roundFromFloor`;
the truncation is never exact and the value never a midpoint because there are infinitely many
primes and infinitely many composites.  `Equiv/PrimeConstant.lean` defines the real number
`primeConstantReal` and proves `primeConstantPrecRound p mode = liftVal₀ (some
primeConstantReal) p mode`.
-/

namespace Azurite.AzFloat

/-- The word `Σ_{l<64} [f l] · 2^l`, assembled bit by bit. -/
def wordOfBits (f : ℕ → Bool) : UInt64 :=
  (List.range 64).foldl
    (fun acc l => if f l then acc + ((1 : UInt64) <<< UInt64.ofNat l) else acc) 0

/-- The first `64 N` bits of the prime constant as an integer: bit `m` is `1` iff `64 N − m` is
prime, read off the prime sieve up to `64 N`. -/
def primeConstantLimbs (N : ℕ) : AzNat :=
  let K := 64 * N
  let S := AzNat.primeSieve K
  AzNat.ofLimbs (Array.ofFn fun i : Fin N => wordOfBits fun l => S.testBit (K - (64 * i + l)))

/-- The prime constant rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def primeConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else
    let N := (p + 2) / 64 + 1
    -- the first `p + 1` significant bits: the floor at `p` bits and the round bit
    let Y := (primeConstantLimbs N).shiftRight (64 * N - (p + 2))
    let r := roundFromFloor (Y.shiftRight 1) false (if Y.isOdd then .gt else .lt) mode
    (normalizeCarry (AzInt.mkNorm true r.1) (AzInt.ofInt (-1)) p, r.2)

/-- The prime constant rounded to nearest at precision `p`. -/
def primeConstant (p : Nat) : AzFloat := (primeConstantPrecRound p .Nearest).1

end Azurite.AzFloat
