/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.PowRat
import Azurite.AzFloat.RatPow
import Azurite.AzFloat.RatPowRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `q^r` with rational base and exponent

The special values (`q^0 = 1`, `0^r`, `1^r`, `(−1)^n`, negative bases with non-integer
exponents, `p = 0`), the exact powers (`8^(1/3) = 2`, `(27/8)^(2/3) = 9/4`,
`(32/243)^(3/5) = 8/27` rounded, `(1/8)^(−2/3) = 4`, `1024^(−7/10) = 1/128`, `(3/2)^10`, `(−3/2)^3`,
`2^100` at 1 bit), the integer powers through the bracket (`3^40`, `(−3)^41` at 20 bits,
`(1 + 10^−6)^(10^6)`), the correctly rounded irrational powers `(1/3)^(1/3)`, `(2/3)^(5/7)`,
`(10/3)^(−7/3)`, `(22/7)^(355/113)`, `(3/2)^(1/3)`, `7^(−401/6)` in the three modes (references
from a 150-digit evaluation of `exp (r ln q)`), agreement with `ratPowPrecRound` and
`powRatPrecRound`, and `(1/3)^(1/3)` at 200 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (q r : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  ratPowRatPrecRound (Q q) (Q r) p m
private def pinf : AzFloat := infinity true

-- special values
#guard P "0" "0" 53 == (F "1" 53, .eq)
#guard P "5" "0" 53 == (F "1" 53, .eq)
#guard P "-7/3" "0" 53 == (F "1" 53, .eq)
#guard P "0" "2" 53 == (zero, .eq)
#guard P "0" "1/2" 53 == (zero, .eq)
#guard P "0" "-2" 53 == (pinf, .eq)
#guard P "0" "-1/2" 53 == (pinf, .eq)
#guard P "1" "-5/2" 53 == (F "1" 53, .eq)
#guard P "1" "1000000000000" 53 == (F "1" 53, .eq)
#guard P "-1" "4" 53 == (F "1" 53, .eq)
#guard P "-1" "3" 53 == (F "-1" 53, .eq)
#guard P "-1" "1/2" 53 == (nan, .eq)
#guard P "-8" "1/3" 53 == (nan, .eq)
#guard P "-27/8" "2/3" 53 == (nan, .eq)
#guard P "2" "3" 0 == (nan, .eq)
#guard P "0" "3" 0 == (zero, .eq)
#guard P "0" "-3" 0 == (pinf, .eq)
#guard P "0" "0" 0 == (nan, .eq)

-- exact powers
#guard P "8" "1/3" 53 == (F "2" 53, .eq)
#guard P "27/8" "2/3" 53 == (F "9/4" 53, .eq)
#guard P "32/243" "3/5" 53 == (F "8/27" 53, .lt)
#guard P "1/8" "-2/3" 53 == (F "4" 53, .eq)
#guard P "4" "3/2" 53 == (F "8" 53, .eq)
#guard P "1/4" "-1/2" 53 == (F "2" 53, .eq)
#guard P "1024" "-7/10" 53 == (F "1/128" 53, .eq)
#guard P "3/2" "10" 53 == (F "59049/1024" 53, .eq)
#guard P "-3/2" "3" 53 == (F "-27/8" 53, .eq)
#guard P "-3/2" "4" 53 == (F "81/16" 53, .eq)
#guard P "2" "100" 1 == (F "1267650600228229401496703205376" 1, .eq)
#guard P "1/3" "2" 53 == (F "1/9" 53, .lt)
#guard P "-1/3" "3" 53 == (F "-1/27" 53, .gt)

-- integer powers through the bracket
#guard P "3" "40" 20 == (F "12157660708133142528" 20, .lt)
#guard P "-3" "41" 20 == (F "-36472999716585472000" 20, .lt)
#guard P "1000001/1000000" "1000000" 53 == (F "6121023454357621/2251799813685248" 53, .lt)
#guard P "1000001/1000000" "1000000" 53 .Ceiling == (F "3060511727178811/1125899906842624" 53, .gt)
#guard (P "3" "1000000000" 10).1 == (ratPowPrecRound (Q "3") (F "1000000000" 53) 10 .Nearest).1

-- correctly rounded irrational powers
#guard P "1/3" "1/3" 53 == (F "6245243153597301/9007199254740992" 53, .lt)
#guard P "1/3" "1/3" 53 .Floor == (F "6245243153597301/9007199254740992" 53, .lt)
#guard P "1/3" "1/3" 53 .Ceiling == (F "3122621576798651/4503599627370496" 53, .gt)
#guard P "2/3" "5/7" 53 == (F "3371167285277805/4503599627370496" 53, .lt)
#guard P "2/3" "5/7" 53 .Ceiling == (F "6742334570555611/9007199254740992" 53, .gt)
#guard P "10/3" "-7/3" 53 == (F "8682790995474021/144115188075855872" 53, .gt)
#guard P "10/3" "-7/3" 53 .Floor == (F "2170697748868505/36028797018963968" 53, .lt)
#guard P "22/7" "355/113" 53 == (F "2569042986886897/70368744177664" 53, .lt)
#guard P "22/7" "355/113" 53 .Ceiling == (F "5138085973773795/140737488355328" 53, .gt)
#guard P "3/2" "1/3" 53 == (F "5155334636208885/4503599627370496" 53, .gt)
#guard P "3/2" "1/3" 53 .Floor == (F "1288833659052221/1125899906842624" 53, .lt)
#guard P "7" "-401/6" 53
  == (F ("2920451216048091/"
      ++ "883423532389192164791648750371459257913741948437809479060803100646309888") 53, .gt)

-- agreement with the one-sided rational powers
#guard P "3/2" "1/3" 53 == powRatPrecRound (F "3/2" 53) (Q "1/3") 53 .Nearest
#guard P "10" "2/7" 53 .Floor == powRatPrecRound (F "10" 53) (Q "2/7") 53 .Floor
#guard P "7" "-401/6" 53 == powRatPrecRound (F "7" 53) (Q "-401/6") 53 .Nearest
#guard P "1/3" "1/2" 53 == ratPowPrecRound (Q "1/3") (F "1/2" 53) 53 .Nearest
#guard P "22/7" "-3/4" 53 .Ceiling == ratPowPrecRound (Q "22/7") (F "-3/4" 53) 53 .Ceiling
#guard P "-5/3" "7" 53 == ratPowPrecRound (Q "-5/3") (F "7" 53) 53 .Nearest

-- 200 bits
#guard toString (ratPowRat (Q "1/3") (Q "1/3") 200)
  == "0.693361274350634704843352274785961795445935113457754036565864"

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := F "4503599627370497/4503599627370496" 53
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53
#guard ratPowRatPrecRound (Q "7/3") tinyQ 53 .Nearest == (F "1" 53, .lt)
#guard ratPowRatPrecRound (Q "7/3") tinyQ 53 .Floor == (F "1" 53, .lt)
#guard ratPowRatPrecRound (Q "7/3") tinyQ 53 .Ceiling == (aboveOne, .gt)
#guard ratPowRatPrecRound (Q "7/3") (-tinyQ) 53 .Nearest == (F "1" 53, .gt)
#guard ratPowRatPrecRound (Q "7/3") (-tinyQ) 53 .Floor == (belowOne, .lt)
#guard ratPowRatPrecRound (Q "7/3") (-tinyQ) 53 .Ceiling == (F "1" 53, .gt)
#guard ratPowRatPrecRound (Q "3/7") tinyQ 53 .Nearest == (F "1" 53, .gt)
