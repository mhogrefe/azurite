/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Factorial

/-!
## Double factorial

`doubleFactorial n = n‼ = n (n − 2) (n − 4) ⋯`.  For even `n = 2k`, `n‼ = 2^k k!`: the factorial
shifted.  For odd `n = 2k + 1`, `n‼ = n! / (2k)‼ = n! / (2^k k!)` is odd, and its prime
factorization has `v_p(n‼) = v_p(n!) − v_p(k!)` for every odd prime `p ≤ n`, so it is assembled
exactly as the odd part of the factorial (`prodPrimePowers`), from the differences of the
Legendre exponents.  No division is performed.
-/

namespace Azurite.AzNat

/-- The odd primes up to the odd `n = 2k + 1` with their exponents in `n‼`,
`v_p(n!) − v_p(k!)`. -/
def oddDoubleFactorialExps (n : Nat) : List (Nat × Nat) :=
  ((primesUpTo n).toList.filter (· ≠ 2)).map fun p =>
    (p, legendreExp p n n - legendreExp p (n / 2) (n / 2))

/-- **Double factorial** `n‼`. -/
def doubleFactorial (n : Nat) : AzNat :=
  if n % 2 = 0 then factorial (n / 2) <<< (n / 2)
  else prodPrimePowers (oddDoubleFactorialExps n) (Nat.log 2 n + 1)

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def D (n : Nat) : String := AzNat.toString (doubleFactorial n)

#guard D 0 == "1"
#guard D 1 == "1"
#guard D 2 == "2"
#guard D 3 == "3"
#guard D 7 == "105"
#guard D 8 == "384"
#guard D 9 == "945"
#guard D 10 == "3840"
#guard D 15 == "2027025"
#guard D 16 == "10321920"
#guard D 20 == "3715891200"
#guard D 25 == "7905853580625"
#guard D 30 == "42849873690624000"
#guard D 49 == "58435841445947272053455474390625"
#guard D 50 == "520469842636666622693081088000000"
#guard D 51 == "2980227913743310874726229193921875"
#guard D 101 == "27526460611482367980105203778549278196237042938512614478716"
  ++ "7211167753726318359375"
-- `1001‼` has 1287 digits
#guard (D 1001).length == 1287
#guard (D 1001).take 20 == "10084907809351460485"
#guard (D 1001).drop (1287 - 20) == "22149753570556640625"
-- agreement with the plain product `n (n − 2) ⋯`
private def naive : Nat → AzNat
  | 0 => 1
  | 1 => 1
  | n + 2 => ofNat (n + 2) * naive n
#guard (List.range 400).all fun n => doubleFactorial n == naive n
#guard doubleFactorial 2501 == naive 2501
#guard doubleFactorial 2500 == naive 2500

end Tests
