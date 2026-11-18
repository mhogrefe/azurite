/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LogBasePow2Rat
import Azurite.AzFloat.LogBaseRat
import Azurite.AzFloat.LogBaseRatFloat
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (q : String) (b : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatFloatPrecRound (Q q) b p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard D (L "2" nan 10) == ("NaN", .eq)
#guard D (L "-2" (X "2" 53) 10) == ("NaN", .eq)
#guard D (L "2" (X "-2" 53) 10) == ("NaN", .eq)
#guard D (L "2" ninf 10) == ("NaN", .eq)
#guard D (L "2" (X "2" 53) 0) == ("NaN", .eq)  -- precision 0
#guard D (L "0" (X "2" 53) 10) == ("-Infinity", .eq)
#guard D (L "0" (X "0.5" 53) 10) == ("Infinity", .eq)
#guard D (L "0" one 10) == ("-Infinity", .eq)
#guard D (L "0" pinf 10) == ("NaN", .eq)
#guard D (L "0" zero 10) == ("NaN", .eq)
#guard D (L "1" (X "2" 53) 10) == ("0.0", .eq)
#guard D (L "1" one 10) == ("NaN", .eq)
#guard D (L "1" pinf 10) == ("0.0", .eq)
#guard D (L "1" zero 10) == ("0.0", .eq)
#guard D (L "2" pinf 10) == ("0.0", .eq)
#guard D (L "1/3" zero 10) == ("0.0", .eq)
#guard D (L "2" one 10) == ("Infinity", .eq)
#guard D (L "1/3" one 10) == ("-Infinity", .eq)
#guard D (L "7/4" one 10) == ("Infinity", .eq)

-- exact cases: a common rational root
#guard D (L "8" (X "4" 53) 53) == ("1.5", .eq)
#guard D (L "1/8" (X "4" 53) 53) == ("-1.5", .eq)
#guard D (L "1/8" (X "0.25" 53) 53) == ("1.5", .eq)
#guard D (L "27" (X "9" 53) 53) == ("1.5", .eq)
#guard D (L "1/27" (X "9" 53) 53) == ("-1.5", .eq)  -- an odd denominator
#guard D (L "1/3" (X "9" 53) 53) == ("-0.5", .eq)
#guard D (L "1/243" (X "3" 53) 53) == ("-5.0", .eq)
#guard D (L "9/4" (X "1.5" 53) 53) == ("2.0", .eq)
#guard D (L "4/9" (X "1.5" 53) 53) == ("-2.0", .eq)  -- `(3/2)^(−2)`
#guard D (L "8/27" (X "1.5" 53) 53) == ("-3.0", .eq)
#guard D (L "2/3" (X "2.25" 53) 53) == ("-0.5", .eq)
#guard D (L "1/1000" (X "10" 53) 53) == ("-3.0", .eq)
#guard D (L "1000" (X "10" 53) 53) == ("3.0", .eq)
#guard D (L "1/10" (X "1000" 53) 53) == ("-0.3333333333333333", .gt)
#guard D (L "1/10" (X "1000" 53) 53 .Floor) == ("-0.33333333333333337", .lt)
#guard D (L "1000" (X "10" 53) 1) == ("4.0", .gt)
#guard (L "2/3" (X "4" 53) 53).2 != .eq                       -- `n, d > 1`: never exact
#guard (L "3/5" (X "3" 53) 53).2 != .eq
#guard (L "2" (X "10" 53) 53).2 != .eq

-- agreement with the natural, power-of-two and float versions
#guard L "7/4" (X "3" 53) 150 == logBaseRatPrecRound (Q "7/4") 3 150 .Nearest
#guard L "1/3" (X "10" 53) 150 .Floor == logBaseRatPrecRound (Q "1/3") 10 150 .Floor
#guard L "10" (X "8" 53) 150 == logBasePow2RatPrecRound (Q "10") (K 3) 150 .Nearest
#guard L "1/10" (X "0.125" 53) 150 .Up == logBasePow2RatPrecRound (Q "1/10") (K (-3)) 150 .Up
#guard L "2" (X "1.5" 53) 150 == logBaseFloatPrecRound (X "2" 53) (X "1.5" 53) 150 .Nearest
#guard L "5/8" (X "2.25" 53) 150 .Ceiling
  == logBaseFloatPrecRound (X "0.625" 53) (X "2.25" 53) 150 .Ceiling

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard toString ((L "7" (X "3" 53) 150).1) == "1.771243749161422260067928307082457718066471335"
#guard toString ((L "1/7" (X "3" 53) 150).1) == "-1.771243749161422260067928307082457718066471335"
#guard (L "7" (X "0.333333333333333\
  3" 53) 150).2 != .eq                      -- `1/3` rounded is not exact
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard toString ((L "2" (X "1.5" 53) 150).1) == "1.709511291351454776976190262174014140615003736"
#guard toString ((L "2" (X "1.5" 53) 150 .Floor).1)
  == "1.709511291351454776976190262174014140615003734"
-- `log₁₀ (1/3)`
private def ref103 : AzRat :=
  Q ("-477121254719662437295027903255115309200128864190695864829865/1"
    ++ "".pushn '0' 60)
#guard toString ((L "1/3" (X "10" 53) 150).1) == "-0.477121254719662437295027903255115309200128864"
#guard toString ((L "3" (X "10" 53) 150 .Up).1)
  == "0.4771212547196624372950279032551153092001288644"
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard toString ((L "2" (X "1.00000095367431640625" 53) 100).1) == "726817.844576360406377773066637"
#guard toString ((L "1/2" (X "1.00000095367431640625" 53) 100).1) == "-726817.844576360406377773066\
  637"

-- default rounding
#guard toString (logBaseRatFloat (Q "8") (X "4" 53) 10) == "1.5"
#guard toString (logBaseRatFloat (Q "7") (X "3" 53) 53) == "1.7712437491614224"
#guard logBaseRatFloat (Q "1/3") (X "10" 53) 60 == logBaseRat (Q "1/3") 10 60
