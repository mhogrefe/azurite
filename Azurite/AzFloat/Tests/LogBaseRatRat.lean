/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LogBasePow2Rat
import Azurite.AzFloat.LogBaseRat
import Azurite.AzFloat.LogBaseRatBase
import Azurite.AzFloat.LogBaseRatRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b q` with rationals

Special values, exact cases (bases and arguments with odd numerators and denominators), agreement
with the natural, power-of-two, float-base and float-argument versions, and
`log₃ 7 = 1.7712437491614222600679283070824577180664713345942434793689925…`,
`log_{3/2} 2 = 1.7095112913514547769761902621740141406150037352361072230744539…`,
`log₁₀ (1/3) = −0.4771212547196624372950279032551153092001288641906958648298656…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (q b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatRatPrecRound (Q q) (Q b) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L "-2" "2" 10) == ("NaN", .eq)
#guard D (L "2" "-2" 10) == ("NaN", .eq)
#guard D (L "2" "2" 0) == ("NaN", .eq) -- precision 0
#guard D (L "2" "0" 10) == ("0.0", .eq)
#guard D (L "0" "0" 10) == ("NaN", .eq)
#guard D (L "1" "1" 10) == ("NaN", .eq)
#guard D (L "2" "1" 10) == ("Infinity", .eq)
#guard D (L "1/2" "1" 10) == ("-Infinity", .eq)
#guard D (L "0" "1" 10) == ("-Infinity", .eq)
#guard D (L "0" "2" 10) == ("-Infinity", .eq)
#guard D (L "0" "2/3" 10) == ("Infinity", .eq)
#guard D (L "1" "2" 10) == ("0.0", .eq)
#guard D (L "1" "2/3" 10) == ("0.0", .eq)

-- exact cases: float-like and genuinely rational
#guard D (L "8" "4" 53) == ("1.5", .eq)
#guard D (L "1/8" "1/4" 53) == ("1.5", .eq)
#guard D (L "9/4" "3/2" 53) == ("2.0", .eq)
#guard D (L "9/4" "2/3" 53) == ("-2.0", .eq)
#guard D (L "8/27" "3/2" 53) == ("-3.0", .eq) -- `n₁ = 1`
#guard D (L "27/8" "9/4" 53) == ("1.5", .eq) -- `d₁ = 1`
#guard D (L "8/27" "4/9" 53) == ("1.5", .eq)
#guard D (L "2/3" "4/9" 53) == ("0.5", .eq)
#guard D (L "125/27" "25/9" 53) == ("1.5", .eq) -- all odd parts above `1`
#guard D (L "27/125" "25/9" 53) == ("-1.5", .eq) -- the crosswise case
#guard D (L "2500/81" "50/9" 53) == ("2.0", .eq) -- with 2-exponents
#guard D (L "81/2500" "50/9" 53) == ("-2.0", .eq)
#guard D (L "25/9" "125/27" 53) == ("0.6666666666666666", .lt)
#guard D (L "9/25" "125/27" 53 .Floor) == ("-0.6666666666666667", .lt)
#guard D (L "1000" "10" 53) == ("3.0", .eq)
#guard D (L "1/1000" "1/10" 53) == ("3.0", .eq)
#guard D (L "1000" "10" 1) == ("4.0", .gt)
#guard (L "250/27" "50/9" 53).2 != .eq                       -- the odd parts disagree
#guard (L "3/5" "7/11" 53).2 != .eq
#guard (L "2/3" "4/5" 53).2 != .eq
#guard (L "2" "10" 53).2 != .eq

-- agreement with the natural, power-of-two, float-base and float-argument versions
#guard L "7/4" "3" 150 == logBaseRatPrecRound (Q "7/4") 3 150 .Nearest
#guard L "1/3" "10" 150 .Floor == logBaseRatPrecRound (Q "1/3") 10 150 .Floor
#guard L "10" "8" 150 == logBasePow2RatPrecRound (Q "10") (K 3) 150 .Nearest
#guard L "1/10" "1/8" 150 .Up == logBasePow2RatPrecRound (Q "1/10") (K (-3)) 150 .Up
#guard L "7/4" "3/2" 150 == logBaseRatFloatPrecRound (Q "7/4") (X "1.5" 53) 150 .Nearest
#guard L "5/8" "9/4" 150 .Ceiling == logBaseRatBasePrecRound (X "0.625" 53) (Q "9/4") 150 .Ceiling
#guard L "5/8" "2/3" 150 == logBaseRatBasePrecRound (X "0.625" 53) (Q "2/3") 150 .Nearest

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard toString ((L "7" "3" 150).1) == "1.771243749161422260067928307082457718066471335"
#guard toString ((L "1/7" "3" 150).1) == "-1.771243749161422260067928307082457718066471335"
#guard toString ((L "7" "1/3" 150).1) == "-1.771243749161422260067928307082457718066471335"
#guard toString ((L "1/7" "1/3" 150 .Floor).1) == "1.771243749161422260067928307082457718066471333"
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard toString ((L "2" "3/2" 150).1) == "1.709511291351454776976190262174014140615003736"
#guard toString ((L "1/2" "2/3" 150).1) == "1.709511291351454776976190262174014140615003736"
#guard toString ((L "2" "2/3" 150 .Ceiling).1) == "-1.709511291351454776976190262174014140615003734"
-- `log₁₀ (1/3)`
private def ref103 : AzRat :=
  Q ("-477121254719662437295027903255115309200128864190695864829865/1"
    ++ "".pushn '0' 60)
#guard toString ((L "1/3" "10" 150).1) == "-0.477121254719662437295027903255115309200128864"
#guard toString ((L "3" "1/10" 150).1) == "-0.477121254719662437295027903255115309200128864"
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard toString ((L "2" "1048577/1048576" 100).1) == "726817.844576360406377773066637"
#guard toString ((L "1/2" "1048577/1048576" 100).1) == "-726817.844576360406377773066637"

-- default rounding
#guard toString (logBaseRatRat (Q "8") (Q "4") 10) == "1.5"
#guard toString (logBaseRatRat (Q "7") (Q "3") 53) == "1.7712437491614224"
#guard logBaseRatRat (Q "1/3") (Q "10") 60 == logBaseRat (Q "1/3") 10 60
