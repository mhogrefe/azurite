/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.SumProduct
import Azurite.AzNat.Conversion
import Azurite.AzNat.ToStringBase
import Mathlib.Data.Nat.Log

/-!
## Primorials

`primorial n = n# = ∏_{p ≤ n prime} p` and `productOfFirstNPrimes n = p₁ p₂ ⋯ pₙ`, both as
balanced product trees (`product`) over the primes from the sieve.

For the first `n` primes the sieve needs a bound on `pₙ`.  `firstPrimes n` sieves up to
`n (⌊log₂ n⌋ + 2)` — already enough for every `n` in practice, since
`pₙ < n (ln n + ln ln n)` — and doubles the bound while fewer than `n` primes are found; `n + 1`
doublings from a bound of at least `2` reach `2^(n+1)`, below which Bertrand's postulate
guarantees at least `n + 1` primes, so the loop always ends with enough primes
(`firstPrimes_spec`, proven with Mathlib's `Nat.exists_prime_lt_and_le_two_mul`).  The result is
the array of the first `n` primes, `(firstPrimes n)[i] = Nat.nth Nat.Prime i`.
-/

namespace Azurite.AzNat

/-- **Primorial** `n# = ∏_{p ≤ n prime} p`. -/
def primorial (n : Nat) : AzNat := product ((primesUpTo n).toList.map ofNat)

/-- Sieve up to `B`, doubling `B` while fewer than `n` primes are found (`fuel` doublings). -/
def firstPrimes.go (n : Nat) : Nat → Nat → Array Nat
  | 0, B => primesUpTo B
  | fuel + 1, B =>
    let ps := primesUpTo B
    if n ≤ ps.size then ps else firstPrimes.go n fuel (2 * B)

/-- **The first `n` primes**, `#[2, 3, 5, …]`. -/
def firstPrimes (n : Nat) : Array Nat :=
  (firstPrimes.go n (n + 1) (max 2 (n * (Nat.log 2 n + 2)))).extract 0 n

/-- **The product of the first `n` primes** `p₁ p₂ ⋯ pₙ`. -/
def productOfFirstNPrimes (n : Nat) : AzNat := product ((firstPrimes n).toList.map ofNat)

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def Pm (n : Nat) : String := AzNat.toString (primorial n)
private def Pf (n : Nat) : String := AzNat.toString (productOfFirstNPrimes n)

#guard (List.range 14).map Pm == ["1", "1", "2", "6", "6", "30", "30", "210", "210", "210", "210",
  "2310", "2310", "30030"]
#guard Pm 30 == "6469693230"
#guard Pm 97 == "2305567963945518424753102147331756070"
#guard Pm 100 == "2305567963945518424753102147331756070"
#guard (Pm 1000).length == 416
#guard (Pm 1000).take 20 == "19590340644999083431"
#guard (List.range 10).map Pf == ["1", "2", "6", "30", "210", "2310", "30030", "510510",
  "9699690", "223092870"]
#guard Pf 20 == "557940830126698960967415390"
#guard (Pf 1000).length == 3393
#guard (Pf 1000).take 20 == "67862960841975551495"
#guard (Pf 1000).drop (3393 - 20) == "10943137983635951570"
#guard firstPrimes 0 == #[]
#guard firstPrimes 1 == #[2]
#guard firstPrimes 10 == #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
#guard (firstPrimes 100).size == 100 && (firstPrimes 100).back! == 541
#guard (firstPrimes 1000).size == 1000 && (firstPrimes 1000).back! == 7919
-- `p₁ ⋯ pₙ = pₙ#`, and agreement with plain folds
#guard (List.range 200).all fun n =>
  productOfFirstNPrimes (n + 1) == primorial (firstPrimes (n + 1)).back!
#guard (List.range 300).all fun n =>
  primorial n == (primesUpTo n).foldl (fun acc p => acc * ofNat p) 1

end Tests
