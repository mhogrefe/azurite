/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-!
# Primality of a number below `2^32` in one machine word

`isPrimeWord n`: trial division by `2` and by the odd numbers up to `√n`, in `UInt64`
arithmetic (the squares `d²` of the divisors tried stay below `2^34`).  `some b` is the
verdict for an `n < 2^32`; `none` if `n` is larger or the fuel runs out (which it does not:
at most `2^15` odd numbers are tried).  Proven (`Azurite/AzNat/Equiv/IsPrimeWord.lean`):
`isPrimeWord n = some b → (b = true ↔ Nat.Prime n.toNat)`.

At most about `32768` divisions of machine words — some tens of microseconds for a prime
near `2^32`, against a millisecond for the same loop on `AzNat`.
-/

namespace Azurite.AzNat

/-- Trial division of `n` by `d, d + 2, d + 4, …` while `d² ≤ n`: `some true` if none
divides, `some false` at the first that does, `none` if the fuel runs out. -/
def trialOddWord (n : UInt64) : Nat → UInt64 → Option Bool
  | 0, _ => none
  | fuel + 1, d =>
    if n < d * d then some true
    else if n % d = 0 then some false
    else trialOddWord n fuel (d + 2)

/-- **Primality of `n < 2^32`** by trial division in machine words; `none` for larger `n`. -/
def isPrimeWord (n : UInt64) : Option Bool :=
  if 4294967296 ≤ n then none
  else if n < 2 then some false
  else if n < 4 then some true
  else if n % 2 = 0 then some false
  else trialOddWord n 32770 3

end Azurite.AzNat

section Tests

open Azurite.AzNat

#guard isPrimeWord 0 == some false && isPrimeWord 1 == some false && isPrimeWord 2 == some true
#guard isPrimeWord 3 == some true && isPrimeWord 4 == some false && isPrimeWord 9 == some false
#guard isPrimeWord 25 == some false && isPrimeWord 97 == some true
#guard isPrimeWord 4294967291 == some true     -- the largest prime below 2^32
#guard isPrimeWord 4294836225 == some false    -- 65535²
#guard isPrimeWord 4294049777 == some false    -- 65521 · 65537
#guard isPrimeWord 4294967295 == some false && isPrimeWord 4294967296 == none
#guard ((List.range 100).filter fun k => isPrimeWord k.toUInt64 == some true) ==
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

end Tests
