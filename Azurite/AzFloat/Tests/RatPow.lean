/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow
import Azurite.AzFloat.RatPow
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `q^y` with a rational base

The special values (as for `x^y`: `q^0 = 1`, `1^y = 1` even for `NaN`, the infinite exponents
against `|q|`, `0^y`, negative bases), the exact powers (`(4/9)^(1/2) = 2/3` rounded,
`(1/4)^(−1/2) = 2`, `(9/4)^(3/2) = 27/8`, `(3/2)^10`, `(−2/3)^3`), the integer powers through the
bracket (`3^40`, `(1/3)^40` at 20 bits), the correctly rounded `(2/3)^(5/4)`, `(22/7)^(−7/8)`,
`(1/3)^(1/3)` (the last within `1/30` ulp of a rounding boundary at 53 bits), `10^(1/2)`
(references from an 80- and 100-digit evaluation of `exp (y ln q)` at the float exponent),
`(1/3)^(1/3)` at 200 bits, agreement with `pow` on float bases, and `(2/3)^(10^9)` at 10 bits
through the bracket.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (q : String) (y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  ratPowPrecRound (Q q) y p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard P "1/3" zero 53 == (F "1" 53, .eq)
#guard P "0" zero 53 == (F "1" 53, .eq)
#guard P "1" nan 53 == (F "1" 53, .eq)
#guard P "1" ninf 53 == (F "1" 53, .eq)
#guard P "1" (F "-7/2" 53) 53 == (F "1" 53, .eq)
#guard P "2/3" nan 53 == (nan, .eq)
#guard P "3/2" pinf 53 == (pinf, .eq)
#guard P "2/3" pinf 53 == (zero, .eq)
#guard P "3/2" ninf 53 == (zero, .eq)
#guard P "2/3" ninf 53 == (pinf, .eq)
#guard P "-5/2" pinf 53 == (pinf, .eq)
#guard P "-1" pinf 53 == (F "1" 53, .eq)
#guard P "-1" ninf 53 == (F "1" 53, .eq)
#guard P "0" pinf 53 == (zero, .eq)
#guard P "0" ninf 53 == (pinf, .eq)
#guard P "0" (F "1/2" 53) 53 == (zero, .eq)
#guard P "0" (F "-2" 53) 53 == (pinf, .eq)
#guard P "-1" (F "4" 53) 53 == (F "1" 53, .eq)
#guard P "-1" (F "3" 53) 53 == (F "-1" 53, .eq)
#guard P "-2/3" (F "3/2" 53) 53 == (nan, .eq)
#guard P "-1" (F "1/2" 53) 53 == (nan, .eq)
#guard P "2/3" (F "3" 53) 0 == (nan, .eq)
#guard P "0" (F "3" 53) 0 == (zero, .eq)

-- exact and rational powers
#guard P "4/9" (F "1/2" 53) 53 == (F "2/3" 53, .lt)
#guard P "1/4" (F "-1/2" 53) 53 == (F "2" 53, .eq)
#guard P "9/4" (F "3/2" 53) 53 == (F "27/8" 53, .eq)
#guard P "16/81" (F "3/4" 53) 53 == ofAzRatRound (Q "8/27") 53 .Nearest
#guard P "3/2" (F "10" 53) 53 == (F "59049/1024" 53, .eq)
#guard P "-2/3" (F "3" 53) 53 == (F "-8/27" 53, .gt)
#guard P "-2/3" (F "2" 53) 53 == (F "4/9" 53, .lt)
#guard P "2" (F "100" 53) 1 == (F "1267650600228229401496703205376" 1, .eq)

-- integer powers through the bracket
#guard P "3" (F "40" 20) 20 == (F "12157660708133142528" 20, .lt)
#guard P "1/3" (F "40" 20) 20 == (F "795499/9671406556917033397649408" 20, .gt)
#guard P "3" (F "40" 20) 20 == powPrecRound (F "3" 20) (F "40" 20) 20 .Nearest
#guard P "-3" (F "41" 20) 20 == powPrecRound (F "-3" 20) (F "41" 20) 20 .Nearest
#guard (P "2/3" (F "1000000000" 53) 10).2 == .lt

-- correctly rounded irrational powers
#guard P "2/3" (F "5/4" 53) 53 == (F "2712974431165687/4503599627370496" 53, .lt)
#guard P "2/3" (F "5/4" 53) 53 .Ceiling == (F "5425948862331375/9007199254740992" 53, .gt)
#guard P "22/7" (F "-7/8" 53) 53 == (F "6613946919566801/18014398509481984" 53, .gt)
#guard P "22/7" (F "-7/8" 53) 53 .Floor == (F "413371682472925/1125899906842624" 53, .lt)
#guard P "1/3" (F "1/3" 53) 53 == (F "3122621576798651/4503599627370496" 53, .gt)
#guard P "1/3" (F "1/3" 53) 53 .Floor == (F "6245243153597301/9007199254740992" 53, .lt)
#guard P "10" (F "1/2" 53) 53 == (F "7120816245988179/2251799813685248" 53, .gt)
#guard toString (ratPowFloat (Q "1/3") (F "1/3" 200) 200)
  == "0.693361274350634704843352274785961795445935113457754036565864"
#guard P "3" (F "7/4" 53) 53 == powPrecRound (F "3" 53) (F "7/4" 53) 53 .Nearest
#guard P "3/2" (F "5/4" 53) 53 .Floor == powPrecRound (F "3/2" 53) (F "5/4" 53) 53 .Floor
#guard P "3/2" (F "-11/4" 53) 53 == powPrecRound (F "3/2" 53) (F "-11/4" 53) 53 .Nearest

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
private def aboveOne : AzFloat := F "4503599627370497/4503599627370496" 53
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53
#guard ratPowPrecRound (Q "7/3") tinyX 53 .Nearest == (F "1" 53, .lt)
#guard ratPowPrecRound (Q "7/3") tinyX 53 .Floor == (F "1" 53, .lt)
#guard ratPowPrecRound (Q "7/3") tinyX 53 .Ceiling == (aboveOne, .gt)
#guard ratPowPrecRound (Q "7/3") (-tinyX) 53 .Nearest == (F "1" 53, .gt)
#guard ratPowPrecRound (Q "7/3") (-tinyX) 53 .Floor == (belowOne, .lt)
#guard ratPowPrecRound (Q "7/3") (-tinyX) 53 .Ceiling == (F "1" 53, .gt)
#guard ratPowPrecRound (Q "3/7") tinyX 53 .Nearest == (F "1" 53, .gt)
