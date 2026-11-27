/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Conversion
import Azurite.AzNat.IsPrimeAprcl
import Azurite.AzNat.IsPrimeWord
import Azurite.ECPP.Gen.Search

/-!
# The production primality test

`isPrime n`, with `isPrime n = true ↔ Nat.Prime n.toNat` (`isPrime_eq_true_iff`,
`Azurite/AzNat/Equiv/IsPrime.lean`):

* up to 32 bits, trial division in machine words (`isPrimeWord`); up to 80 bits, the twelve Miller–Rabin bases and the APR-CL
  verdict.  If APR-CL gives up (never observed), `ecppOrNaive`: an elliptic curve
  certificate when `n` has more than `ecppFallbackBits` bits, trial division otherwise or
  when no certificate is found;
* above, the twelve fixed Miller–Rabin bases first (`false` proves compositeness), then
  elliptic curve primality proving (`ECPP.provePrime`: an unproven search for a certificate and
  the proven checker `ECPP.check`, so `true` proves primality), and, only if no certificate is
  found, the APR-CL verdict with its trial-division fallback (`aprclOrNaive`).

Measured 2026-11-25 (ten probable primes above `10^D`, ms per prime, elliptic curves
(search and check) / APR-CL): 20 digits 7.5 / 7.6; 25: 11.6 / 18.5; 30: 14.0 / 45.6;
40: 19.1 / 131; 50: 31.7 / 204; 70: 66.9 / 574; 100: 206 / 1391; 150: 595 / 4855.
-/

namespace Azurite

namespace AzNat

/-- The parameters of the certificate search for an `n` of at most 80 bits: the small set of
discriminants, and a chain that goes down to 32 bits (where the checker's base case is trial
division). -/
def ecppFallbackParams : ECPP.GenParams := { ECPP.smallParams with baseBits := 32 }

/-- Above this many bits a certificate search is faster than trial division.  Measured
2026-11-26 (five primes each, ms per prime, trial division / certificate): 34 bits
2.9 / 7.6; 36: 5.4–5.9 / 5.9–6.2; 38: 11 / 5.7; 40: 22 / 6.7; 48: 356 / 6.2; 56: 5800 / 6.2;
64: 92600 / 7.7. -/
def ecppFallbackBits : Nat := 36

/-- **Primality without APR-CL** (for the inputs on which it gives up): a checked elliptic
curve certificate when `n` is long enough for that to be faster than trial division, and
trial division otherwise or when no certificate is found. -/
def ecppOrNaive (n : AzNat) : Bool :=
  (decide (ecppFallbackBits < n.size) && ECPP.provePrime n ecppFallbackParams) ||
    isPrimeNaive n

/-- The APR-CL verdict, with `ecppOrNaive` when it gives up. -/
def aprclOrEcpp (n : AzNat) : Bool :=
  match APRCL.aprclTestSel n with
  | some b => b
  | none => ecppOrNaive n

/-- **Primality test**: trial division (in machine words) up to 32 bits; up to 80 bits, Miller–Rabin rejection
and the APR-CL verdict (an elliptic curve certificate or trial division if it gives up);
above, Miller–Rabin rejection, then a checked elliptic curve certificate, then APR-CL if none
was found.  Proven: `isPrime n = true ↔ Nat.Prime n.toNat`. -/
def isPrime (n : AzNat) : Bool :=
  if n.size ≤ 32 then
    match isPrimeWord n.toUInt64 with
    | some b => b
    | none => isPrimeNaive n
  else if n.size ≤ 80 then millerRabin n 0 0 && aprclOrEcpp n
  else millerRabin n 0 0 && (ECPP.provePrime n || aprclOrNaive n)

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def parse' (s : String) : AzNat := (AzNat.parse s).get!

#guard isPrime (parse' "0") == false
#guard isPrime (parse' "1") == false
#guard isPrime (parse' "2") == true
#guard isPrime (parse' "97") == true
#guard isPrime (parse' "104729") == true
#guard isPrime (parse' "104730") == false
#guard isPrime (parse' "2147483647") == true          -- 2^31 − 1
#guard isPrime (parse' "825265") == false             -- Carmichael, 5 factors
#guard isPrime (parse' "18446744073709551617") == false
#guard isPrime (parse' "2305843009213693951") == true -- 2^61 − 1
-- strong pseudoprimes to the twelve bases: the certificate search gives up, APR-CL decides
#guard isPrime (parse' "3317044064679887385961981") == false
#guard isPrime (parse' "318665857834031151167461") == false
-- above 80 bits: by elliptic curve certificates
#guard isPrime (parse' "1000000000000000000000007") == true
#guard isPrime (ofNat (2 ^ 127 - 1)) == true
#guard isPrime (ofNat (10 ^ 50 + 151)) == true
#guard isPrime (ofNat (10 ^ 100 + 267)) == true
#guard isPrime (ofNat ((10 ^ 50 + 151) * (10 ^ 50 + 447))) == false
#guard isPrime (ofNat (10 ^ 100 + 269)) == false
-- the fallback of APR-CL, directly
#guard ecppOrNaive (parse' "34359738421") == true            -- 36 bits: trial division
#guard ecppOrNaive (parse' "1000000000039") == true          -- 40 bits: certificate
#guard ECPP.provePrime (parse' "1000000000039") ecppFallbackParams
#guard ECPP.provePrime (parse' "1125899906842679") ecppFallbackParams   -- 51 bits
#guard ecppOrNaive (parse' "1125899906842679") == true
#guard ecppOrNaive (parse' "1000000000000000000000007") == true
#guard ecppOrNaive (parse' "1125899906842681") == false

end Tests
