/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow
import Azurite.AzFloat.Pow2
import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseM1
import Azurite.AzFloat.PowBaseM1Rat
import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `x^y`

The special values of IEEE 754 (Malachite's table, without negative zero), the exact dyadic
powers (`4^(1/2) = 2`, `4^(3/2) = 8`, `(9/4)^(3/2) = 27/8`, `(1/4)^(−1/2) = 2`, `16^(1/4) = 2`,
`(3/2)^10`, `(−3/2)^3 = −27/8`), the integer powers through the bracket (`3^40`, `(−3)^41`,
`3^(−40)` at 20 bits), the correctly rounded `2^(1/2)` (against `√2`), `(3/2)^(5/4)`,
`10^(−1/8)`, `(123456789/1024)^(77/64)`, `3^(7/4)` (against `powBase`), `(1/3)^(1/3)` at 200 bits
(references from an 80-digit evaluation of `exp (y ln x)`), the directed modes, and agreement with
`pow2` and `powBase`.  The natural-base powers `powBase`, `powBaseRat`, `powBaseM1`,
`powBaseM1Rat` share the cheapness test, so `3^(10^9)` (and `3^(10^9) − 1`) at 10 bits are
computed through the bracket in milliseconds instead of forming the exact power.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := powPrecRound x y p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- `x^0 = 1` and `1^y = 1`, even for `NaN`
#guard P nan zero 53 == (F "1" 53, .eq)
#guard P pinf zero 53 == (F "1" 53, .eq)
#guard P (F "-7/3" 53) zero 53 == (F "1" 53, .eq)
#guard P (F "1" 53) nan 53 == (F "1" 53, .eq)
#guard P (F "1" 53) pinf 53 == (F "1" 53, .eq)
#guard P (F "1" 53) (F "-5/2" 53) 53 == (F "1" 53, .eq)
-- `NaN` otherwise
#guard P nan (F "2" 53) 53 == (nan, .eq)
#guard P (F "2" 53) nan 53 == (nan, .eq)
#guard P nan pinf 53 == (nan, .eq)
-- infinite exponents
#guard P (F "2" 53) pinf 53 == (pinf, .eq)
#guard P (F "1/2" 53) pinf 53 == (zero, .eq)
#guard P (F "2" 53) ninf 53 == (zero, .eq)
#guard P (F "1/2" 53) ninf 53 == (pinf, .eq)
#guard P (F "-3" 53) pinf 53 == (pinf, .eq)
#guard P (F "-1/3" 53) ninf 53 == (pinf, .eq)
#guard P (F "-1" 53) pinf 53 == (F "1" 53, .eq)
#guard P (F "-1" 53) ninf 53 == (F "1" 53, .eq)
#guard P zero pinf 53 == (zero, .eq)
#guard P zero ninf 53 == (pinf, .eq)
#guard P pinf pinf 53 == (pinf, .eq)
#guard P pinf ninf 53 == (zero, .eq)
#guard P ninf pinf 53 == (pinf, .eq)
#guard P ninf ninf 53 == (zero, .eq)
-- `(−1)^y`
#guard P (F "-1" 53) (F "4" 53) 53 == (F "1" 53, .eq)
#guard P (F "-1" 53) (F "3" 53) 53 == (F "-1" 53, .eq)
#guard P (F "-1" 53) (F "1/2" 53) 53 == (nan, .eq)
-- infinite bases
#guard P pinf (F "2" 53) 53 == (pinf, .eq)
#guard P pinf (F "1/2" 53) 53 == (pinf, .eq)
#guard P pinf (F "-2" 53) 53 == (zero, .eq)
#guard P ninf (F "3" 53) 53 == (ninf, .eq)
#guard P ninf (F "2" 53) 53 == (pinf, .eq)
#guard P ninf (F "1/2" 53) 53 == (pinf, .eq)
#guard P ninf (F "-3" 53) 53 == (zero, .eq)
#guard P ninf (F "-2" 53) 53 == (zero, .eq)
-- zero bases
#guard P zero (F "2" 53) 53 == (zero, .eq)
#guard P zero (F "1/2" 53) 53 == (zero, .eq)
#guard P zero (F "-2" 53) 53 == (pinf, .eq)
#guard P zero (F "-3" 53) 53 == (pinf, .eq)
-- negative base, non-integer exponent
#guard P (F "-2" 53) (F "3/2" 53) 53 == (nan, .eq)
#guard P (F "-8" 53) (F "1/2" 53) 53 == (nan, .eq)
-- precision `0`
#guard P (F "2" 53) (F "3" 53) 0 == (nan, .eq)
#guard P (F "2" 53) zero 0 == (nan, .eq)
#guard P zero (F "3" 53) 0 == (zero, .eq)

-- exact dyadic powers
#guard P (F "4" 53) (F "1/2" 53) 53 == (F "2" 53, .eq)
#guard P (F "4" 53) (F "3/2" 53) 53 == (F "8" 53, .eq)
#guard P (F "9/4" 53) (F "3/2" 53) 53 == (F "27/8" 53, .eq)
#guard P (F "1/4" 53) (F "-1/2" 53) 53 == (F "2" 53, .eq)
#guard P (F "16" 53) (F "1/4" 53) 53 == (F "2" 53, .eq)
#guard P (F "16" 53) (F "-3/4" 53) 53 == (F "1/8" 53, .eq)
#guard P (F "3/2" 53) (F "10" 53) 53 == (F "59049/1024" 53, .eq)
#guard P (F "-3/2" 53) (F "3" 53) 53 == (F "-27/8" 53, .eq)
#guard P (F "-3/2" 53) (F "-2" 53) 53 == (F "4/9" 53, .lt)
#guard P (F "2" 53) (F "100" 53) 1 == (F "1267650600228229401496703205376" 1, .eq)
#guard P (F "2" 53) (F "-100" 53) 1 == (F "1/1267650600228229401496703205376" 1, .eq)

-- integer powers through the bracket (`|n| (size m' − 1) > p + 1`)
#guard P (F "3" 20) (F "40" 20) 20 == (F "12157660708133142528" 20, .lt)
#guard P (F "3" 20) (F "40" 20) 20 .Ceiling == (F "12157678300319186944" 20, .gt)
#guard P (F "-3" 20) (F "41" 20) 20 == (F "-36472999716585472000" 20, .lt)
#guard P (F "-3" 20) (F "41" 20) 20 .Ceiling == (F "-36472964532213383168" 20, .gt)
#guard P (F "3" 20) (F "-40" 20) 20 == (F "795499/9671406556917033397649408" 20, .gt)
#guard P (F "3" 20) (F "-40" 20) 20 .Floor == (F "397749/4835703278458516698824704" 20, .lt)
#guard P (F "3" 20) (F "40" 20) 20 == powIntPrecRound (F "3" 20) (AzInt.ofInt 40) 20 .Nearest
#guard P (F "-3" 20) (F "41" 20) 20 == powIntPrecRound (F "-3" 20) (AzInt.ofInt 41) 20 .Nearest

-- correctly rounded irrational powers
#guard P (F "2" 53) (F "1/2" 53) 53 == sqrt2PrecRound 53 .Nearest
#guard P (F "2" 53) (F "1/2" 53) 53 .Floor == sqrt2PrecRound 53 .Floor
#guard P (F "2" 53) (F "1/2" 53) 53 .Ceiling == sqrt2PrecRound 53 .Ceiling
#guard P (F "3/2" 53) (F "5/4" 53) 53 == (F "3738039210885025/2251799813685248" 53, .lt)
#guard P (F "3/2" 53) (F "5/4" 53) 53 .Ceiling == (F "7476078421770051/4503599627370496" 53, .gt)
#guard P (F "10" 53) (F "-1/8" 53) 53 == (F "3377223281716941/4503599627370496" 53, .gt)
#guard P (F "10" 53) (F "-1/8" 53) 53 .Floor == (F "6754446563433881/9007199254740992" 53, .lt)
#guard P (F "123456789/1024" 53) (F "77/64" 53) 53 == (F "5575665134221977/4294967296" 53, .gt)
#guard P (F "123456789/1024" 53) (F "77/64" 53) 53 .Floor == (F "696958141777747/536870912" 53, .lt)
#guard P (F "3" 53) (F "7/4" 53) 53 == (F "962436293652183/140737488355328" 53, .lt)
#guard P (F "3" 53) (F "7/4" 53) 53 == powBasePrecRound 3 (F "7/4" 53) 53 .Nearest
#guard P (F "2" 53) (F "7/4" 53) 53 == pow2PrecRound (F "7/4" 53) 53 .Nearest
#guard P (F "2" 53) (F "-11/4" 53) 53 .Floor == pow2PrecRound (F "-11/4" 53) 53 .Floor
#guard toString (pow (F "1/3" 200) (F "1/3" 200))
  == "0.693361274350634704843352274785961795445935113457754036565864"
#guard P (F "1/3" 200) (F "1/3" 200) 200 .Floor
  == (F ("278547152542482532563422671618708116702897587785882603583841/"
      ++ "401734511064747568885490523085290650630550748445698208825344") 200, .lt)
#guard toString (pow (F "3/2" 53) (F "5/4" 53)) == "1.6600228795504823"

-- the natural-base powers on huge exponents: the bracket path, in agreement with `pow`
#guard powBasePrecRound 3 (F "1000000000" 53) 10 .Nearest
  == P (F "3" 53) (F "1000000000" 53) 10
#guard powBaseRatPrecRound 3 (Q "1000000000") 10 .Nearest == P (F "3" 53) (F "1000000000" 53) 10
#guard powBasePrecRound 3 (F "-1000000000" 53) 10 .Floor
  == P (F "3" 53) (F "-1000000000" 53) 10 .Floor
#guard (powBaseM1PrecRound 3 (F "1000000000" 53) 10 .Nearest).1
  == (P (F "3" 53) (F "1000000000" 53) 10).1
#guard (powBaseM1RatPrecRound 3 (Q "1000000000") 10 .Nearest).1
  == (P (F "3" 53) (F "1000000000" 53) 10).1
#guard powBaseM1PrecRound 3 (F "-1000000000" 53) 10 .Nearest == (F "-1" 10, .lt)
#guard powBaseM1PrecRound 3 (F "40" 20) 20 .Nearest == (F "12157660708133142528" 20, .lt)
#guard powBaseM1RatPrecRound 3 (Q "40") 20 .Nearest == (F "12157660708133142528" 20, .lt)
#guard powBaseM1PrecRound 3 (F "-40" 20) 20 .Nearest == (F "-1" 20, .lt)
#guard (powBasePrecRound 10 (F "1000000" 53) 53 .Nearest).1 == (P (F "10" 53) (F "1000000" 53) 53).1

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
private def aboveOne : AzFloat := F "4503599627370497/4503599627370496" 53
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53
#guard powPrecRound (F "3" 53) tinyX 53 .Nearest == (F "1" 53, .lt)
#guard powPrecRound (F "3" 53) tinyX 53 .Floor == (F "1" 53, .lt)
#guard powPrecRound (F "3" 53) tinyX 53 .Ceiling == (aboveOne, .gt)
#guard powPrecRound (F "3" 53) (-tinyX) 53 .Nearest == (F "1" 53, .gt)
#guard powPrecRound (F "3" 53) (-tinyX) 53 .Floor == (belowOne, .lt)
#guard powPrecRound (F "3" 53) (-tinyX) 53 .Ceiling == (F "1" 53, .gt)
-- a base below `1` reverses the side
#guard powPrecRound (F "1/3" 53) tinyX 53 .Nearest == (F "1" 53, .gt)
#guard powPrecRound (F "1/3" 53) (-tinyX) 53 .Ceiling == (aboveOne, .gt)
-- a huge or a tiny base: `(3·2^(±2N))^(1/2) = √3 · 2^(±N)`, `N = 2^29` (the starting precision
-- is logarithmic in the exponent of the base)
private def bigN : AzInt := AzInt.ofInt (2 ^ 29)
#guard powPrecRound ((F "3" 53) <<< AzInt.ofInt (2 ^ 30)) (F "1/2" 53) 53 .Nearest
  == ((powPrecRound (F "3" 53) (F "1/2" 53) 53 .Nearest).1 <<< bigN,
    (powPrecRound (F "3" 53) (F "1/2" 53) 53 .Nearest).2)
#guard powPrecRound ((F "3" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) (F "1/2" 53) 53 .Floor
  == ((powPrecRound (F "3" 53) (F "1/2" 53) 53 .Floor).1 <<< (-bigN),
    (powPrecRound (F "3" 53) (F "1/2" 53) 53 .Floor).2)
