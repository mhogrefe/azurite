/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatFloat
import Azurite.AzFloat.LogBaseRat
import Azurite.AzFloat.LogBasePow2Rat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b q` with a float base

Special values, exact cases (including rationals with odd denominators), agreement with the
natural, power-of-two and float-argument versions, and
`log₃ 7 = 1.7712437491614222600679283070824577180664713345942434793689925…`,
`log_{3/2} 2 = 1.7095112913514547769761902621740141406150037352361072230744539…`,
`log₁₀ (1/3) = −0.4771212547196624372950279032551153092001288641906958648298656…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (q : String) (b : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatFloatPrecRound (Q q) b p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard L "2" nan 10 == (nan, .eq)
#guard L "-2" (F "2" 53) 10 == (nan, .eq)
#guard L "2" (F "-2" 53) 10 == (nan, .eq)
#guard L "2" ninf 10 == (nan, .eq)
#guard L "2" (F "2" 53) 0 == (nan, .eq)                      -- precision 0
#guard L "0" (F "2" 53) 10 == (infinity false, .eq)
#guard L "0" (F "1/2" 53) 10 == (infinity true, .eq)
#guard L "0" one 10 == (infinity false, .eq)
#guard L "0" pinf 10 == (nan, .eq)
#guard L "0" zero 10 == (nan, .eq)
#guard L "1" (F "2" 53) 10 == (zero, .eq)
#guard L "1" one 10 == (nan, .eq)
#guard L "1" pinf 10 == (zero, .eq)
#guard L "1" zero 10 == (zero, .eq)
#guard L "2" pinf 10 == (zero, .eq)
#guard L "1/3" zero 10 == (zero, .eq)
#guard L "2" one 10 == (infinity true, .eq)
#guard L "1/3" one 10 == (infinity false, .eq)
#guard L "7/4" one 10 == (infinity true, .eq)

-- exact cases: a common rational root
#guard L "8" (F "4" 53) 53 == (F "3/2" 53, .eq)
#guard L "1/8" (F "4" 53) 53 == (F "-3/2" 53, .eq)
#guard L "1/8" (F "1/4" 53) 53 == (F "3/2" 53, .eq)
#guard L "27" (F "9" 53) 53 == (F "3/2" 53, .eq)
#guard L "1/27" (F "9" 53) 53 == (F "-3/2" 53, .eq)           -- an odd denominator
#guard L "1/3" (F "9" 53) 53 == (F "-1/2" 53, .eq)
#guard L "1/243" (F "3" 53) 53 == (F "-5" 53, .eq)
#guard L "9/4" (F "3/2" 53) 53 == (F "2" 53, .eq)
#guard L "4/9" (F "3/2" 53) 53 == (F "-2" 53, .eq)            -- `(3/2)^(−2)`
#guard L "8/27" (F "3/2" 53) 53 == (F "-3" 53, .eq)
#guard L "2/3" (F "9/4" 53) 53 == (F "-1/2" 53, .eq)
#guard L "1/1000" (F "10" 53) 53 == (F "-3" 53, .eq)
#guard L "1000" (F "10" 53) 53 == (F "3" 53, .eq)
#guard L "1/10" (F "1000" 53) 53 == ofAzRatRound (Q "-1/3") 53 .Nearest
#guard L "1/10" (F "1000" 53) 53 .Floor == ofAzRatRound (Q "-1/3") 53 .Floor
#guard L "1000" (F "10" 53) 1 == (F "4" 1, .gt)
#guard (L "2/3" (F "4" 53) 53).2 != .eq                       -- `n, d > 1`: never exact
#guard (L "3/5" (F "3" 53) 53).2 != .eq
#guard (L "2" (F "10" 53) 53).2 != .eq

-- agreement with the natural, power-of-two and float versions
#guard L "7/4" (F "3" 53) 150 == logBaseRatPrecRound (Q "7/4") 3 150 .Nearest
#guard L "1/3" (F "10" 53) 150 .Floor == logBaseRatPrecRound (Q "1/3") 10 150 .Floor
#guard L "10" (F "8" 53) 150 == logBasePow2RatPrecRound (Q "10") (K 3) 150 .Nearest
#guard L "1/10" (F "1/8" 53) 150 .Up == logBasePow2RatPrecRound (Q "1/10") (K (-3)) 150 .Up
#guard L "2" (F "3/2" 53) 150 == logBaseFloatPrecRound (F "2" 53) (F "3/2" 53) 150 .Nearest
#guard L "5/8" (F "9/4" 53) 150 .Ceiling
  == logBaseFloatPrecRound (F "5/8" 53) (F "9/4" 53) 150 .Ceiling

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard (L "7" (F "3" 53) 150).1 == ofAzRat ref37 150
#guard (L "1/7" (F "3" 53) 150).1 == ofAzRat (-ref37) 150
#guard (L "7" (F "1/3" 53) 150).2 != .eq                      -- `1/3` rounded is not exact
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard (L "2" (F "3/2" 53) 150).1 == ofAzRat ref32 150
#guard (L "2" (F "3/2" 53) 150 .Floor).1 == (ofAzRatRound ref32 150 .Floor).1
-- `log₁₀ (1/3)`
private def ref103 : AzRat :=
  Q ("-477121254719662437295027903255115309200128864190695864829865/1"
    ++ "".pushn '0' 60)
#guard (L "1/3" (F "10" 53) 150).1 == ofAzRat ref103 150
#guard (L "3" (F "10" 53) 150 .Up).1 == (ofAzRatRound (-ref103) 150 .Up).1
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard (L "2" (F "1048577/1048576" 53) 100).1 == ofAzRat refUp 100
#guard (L "1/2" (F "1048577/1048576" 53) 100).1 == ofAzRat (-refUp) 100

-- default rounding
#guard logBaseRatFloat (Q "8") (F "4" 53) 10 == F "3/2" 10
#guard logBaseRatFloat (Q "7") (F "3" 53) 53 == ofAzRat ref37 53
#guard logBaseRatFloat (Q "1/3") (F "10" 53) 60 == logBaseRat (Q "1/3") 10 60
