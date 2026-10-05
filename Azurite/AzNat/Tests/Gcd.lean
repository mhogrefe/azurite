/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd
import Azurite.AzNat.ParseBase

/-!
# Tests for the GCD: the single-limb Euclidean path and the binary GCD
-/

namespace Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def G (a b : String) : String := toString (gcd (N a) (N b))

-- single limb (Euclid on `UInt64`)
#guard G "12" "18" == "6"
#guard G "18" "12" == "6"
#guard G "0" "5" == "5"
#guard G "5" "0" == "5"
#guard G "0" "0" == "0"
#guard G "1" "123456789" == "1"
#guard G "18446744073709551615" "18446744073709551615" == "18446744073709551615"
#guard G "18446744073709551615" "4294967295" == "4294967295"            -- 2^64−1 and 2^32−1
#guard G "18446744073709551614" "6" == "2"
#guard G "9223372036854775808" "6917529027641081856" == "2305843009213693952" -- 2^63, 3·2^61
#guard gcdUInt64 0 0 == 0
#guard gcdUInt64 7 0 == 7
#guard gcdUInt64 0 7 == 7
#guard gcdUInt64 1071 462 == 21
-- consecutive Fibonacci numbers F₉₃, F₉₂: the worst case for Euclid on 64 bits (91 steps)
#guard gcdUInt64 12200160415121876738 7540113804746346429 == 1
#guard G "12200160415121876738" "7540113804746346429" == "1"

-- across the one-limb boundary (binary GCD)
#guard G "18446744073709551616" "4" == "4"                              -- 2^64 and 4
#guard G "36893488147419103232" "18446744073709551616" == "18446744073709551616"
#guard G "340282366920938463463374607431768211455" "18446744073709551615"
  == "18446744073709551615"                                               -- 2^128−1, 2^64−1
#guard G "1000000000000000000000000000000000000" "1000000000000000000000" ==
  "1000000000000000000000"
#guard coprime (N "18446744073709551616") (N "3") == true
#guard coprime (N "18446744073709551616") (N "6") == false
#guard coprime (N "35") (N "64") == true
#guard coprime (N "35") (N "63") == false

-- half-binary GCD (MCA §1.6.3); the worked example of MCA Algorithm 1.22
private def ex := halfBinaryGcd 21 (N "1889826700059").toAzInt (N "421872857844").toAzInt 20
#guard ex.1 == 20
#guard ex.2.a = (N "1444544").toAzInt
#guard ex.2.b = (N "1086512").toAzInt
#guard ex.2.c = (N "349084").toAzInt
#guard ex.2.d = (N "1023711").toAzInt
-- the driver with a tiny fallback threshold, so the recursion really runs
private def H (a b : String) : String := toString (gcdHalfBinaryWith 8 (N a) (N b))
#guard H "1889826700059" "421872857844" == "3"
#guard H "935" "714" == "17"                                            -- MCA BinaryDivide example
#guard H "19" "2" == "1"
#guard H "0" "12" == "12"
#guard H "12" "0" == "12"
#guard H "18446744073709551615" "4294967295" == "4294967295"
#guard H "340282366920938463463374607431768211455" "18446744073709551615"
  == "18446744073709551615"
private def big : AzNat := (N "123456789012345678901234567890123456789") <<< 200
#guard gcdHalfBinaryWith 8 (big * N "1000003") (big * N "1000004") = big
#guard gcdHalfBinaryWith 8 (N "3" <<< 300) (N "9" <<< 280) = N "3" <<< 280
-- the dispatcher above its threshold: `gcd (n k) (n (k + 1)) = n`, powers of two, neighbours
private def huge : AzNat := big <<< 900
#guard gcd (huge * N "1000003") (huge * N "1000004") = huge
#guard gcd (huge * N "6") (huge * N "4") = huge * N "2"
#guard gcd (N "7" <<< 1500) (N "5" <<< 1500) = N "1" <<< 1500
#guard toString (gcd (N "1" <<< 1400) ((N "1" <<< 1400) + N "1")) == "1"
#guard coprime ((N "1" <<< 1300) + N "3") ((N "1" <<< 1300) + N "4") == true

end Azurite.AzNat
