/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LogBase
import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.LogBaseRatBase
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b x` with a rational base

Special values, exact cases (including bases with odd denominators), agreement with the natural,
power-of-two and float-base versions, and
`log₃ 7 = 1.7712437491614222600679283070824577180664713345942434793689925…`,
`log_{3/2} 2 = 1.7095112913514547769761902621740141406150037352361072230744539…`,
`log_{1 + 2^(−20)} 2 = 726817.84457636040637777306663695374104317457331197399796360…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatBasePrecRound x (Q b) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L nan "2" 10) == ("NaN", .eq)
#guard D (L (X "2" 53) "-2" 10) == ("NaN", .eq)
#guard D (L (X "-2" 53) "2" 10) == ("NaN", .eq)
#guard D (L ninf "2" 10) == ("NaN", .eq)
#guard D (L (X "8" 53) "2" 0) == ("NaN", .eq)  -- precision 0
-- base `0`
#guard D (L (X "2" 53) "0" 10) == ("0.0", .eq)
#guard D (L (X "0.5" 53) "0" 10) == ("0.0", .eq)
#guard D (L pinf "0" 10) == ("NaN", .eq)
#guard D (L zero "0" 10) == ("NaN", .eq)
-- base `1`
#guard D (L one "1" 10) == ("NaN", .eq)
#guard D (L (X "2" 53) "1" 10) == ("Infinity", .eq)
#guard D (L (X "0.5" 53) "1" 10) == ("-Infinity", .eq)
#guard D (L pinf "1" 10) == ("Infinity", .eq)
#guard D (L zero "1" 10) == ("-Infinity", .eq)
-- `x = ∞`, `x = 0`, `x = 1`
#guard D (L pinf "2" 10) == ("Infinity", .eq)
#guard D (L pinf "2/3" 10) == ("-Infinity", .eq)
#guard D (L zero "2" 10) == ("-Infinity", .eq)
#guard D (L zero "2/3" 10) == ("Infinity", .eq)
#guard D (L one "2" 10) == ("0.0", .eq)
#guard D (L one "2/3" 10) == ("0.0", .eq)

-- exact cases: a common rational root
#guard D (L (X "8" 53) "4" 53) == ("1.5", .eq)
#guard D (L (X "8" 53) "1/2" 53) == ("-3.0", .eq)
#guard D (L (X "0.125" 53) "1/4" 53) == ("1.5", .eq)
#guard D (L (X "27" 53) "9" 53) == ("1.5", .eq)
#guard D (L (X "27" 53) "1/3" 53) == ("-3.0", .eq)  -- an odd denominator
#guard D (L (X "3" 53) "1/9" 53) == ("-0.5", .eq)
#guard D (L (X "243" 53) "1/3" 53) == ("-5.0", .eq)
#guard D (L (X "2.25" 53) "3/2" 53) == ("2.0", .eq)
#guard D (L (X "2.25" 53) "2/3" 53) == ("-2.0", .eq)  -- `(2/3)^(−2)`
#guard D (L (X "3.375" 53) "2/3" 53) == ("-3.0", .eq)
#guard D (L (X "1.5" 53) "4/9" 53) == ("-0.5", .eq)
#guard D (L (X "0.5625" 53) "3/4" 53) == ("2.0", .eq)
#guard D (L (X "1000" 53) "10" 53) == ("3.0", .eq)
#guard D (L (X "1000" 53) "1/10" 53) == ("-3.0", .eq)
#guard D (L (X "10" 53) "1000" 53) == ("0.3333333333333333", .lt)
#guard D (L (X "10" 53) "1/1000" 53 .Floor) == ("-0.33333333333333337", .lt)
#guard D (L (X "1000" 53) "10" 1) == ("4.0", .gt)
#guard (L (X "4" 53) "2/3" 53).2 != .eq                       -- `n, d > 1`: never exact
#guard (L (X "2" 53) "3/5" 53).2 != .eq
#guard (L (X "2" 53) "10" 53).2 != .eq

-- agreement with the natural, power-of-two and float-base versions
#guard L (X "1.75" 53) "3" 150 == logBasePrecRound (X "1.75" 53) 3 150 .Nearest
#guard L (X "2" 53) "10" 150 .Floor == logBasePrecRound (X "2" 53) 10 150 .Floor
#guard L (X "10" 53) "8" 150 == logBasePow2PrecRound (X "10" 53) (K 3) 150 .Nearest
#guard L (X "10" 53) "1/8" 150 .Up == logBasePow2PrecRound (X "10" 53) (K (-3)) 150 .Up
#guard L (X "2" 53) "3/2" 150 == logBaseFloatPrecRound (X "2" 53) (X "1.5" 53) 150 .Nearest
#guard L (X "0.625" 53) "9/4" 150 .Ceiling
  == logBaseFloatPrecRound (X "0.625" 53) (X "2.25" 53) 150 .Ceiling

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard toString (L (X "7" 53) "3" 150).1 == "1.771243749161422260067928307082457718066471335"
-- an exact `1/3` base
#guard toString (L (X "7" 53) "1/3" 150).1 == "-1.771243749161422260067928307082457718066471335"
#guard toString (L (X "7" 53) "3" 150 .Floor).1 == "1.771243749161422260067928307082457718066471333"
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard toString (L (X "2" 53) "3/2" 150).1 == "1.709511291351454776976190262174014140615003736"
-- an exact `2/3` base
#guard toString (L (X "2" 53) "2/3" 150).1 == "-1.709511291351454776976190262174014140615003736"
#guard toString (L (X "2" 53) "2/3" 150 .Ceiling).1 == "-1.7095112913514547769761902621740141406150\
  03734"
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard toString (L (X "2" 53) "1048577/1048576" 100).1 == "726817.844576360406377773066637"
#guard toString (L (X "0.5" 53) "1048577/1048576" 100).1 == "-726817.844576360406377773066637"
#guard (L (X "2" 53) "1048575/1048576" 100).2 != .eq

-- default precision
#guard toString (logBaseRatBase (X "8" 10) (Q "4")) == "1.5"
#guard toString (logBaseRatBase (X "7" 53) (Q "3")) == "1.7712437491614224"
#guard logBaseRatBase (X "2" 53) (Q "10") == logBase (X "2" 53) 10

-- exponents far beyond memory: the work does not depend on the exponent
#guard (L ((X "3" 53) <<< K (2 ^ 60)) "10/7" 53).2 != .eq
#guard (L ((X "3" 53) <<< K (-(2 ^ 60))) "12" 53).2 != .eq
#guard (L ((X "1" 53) <<< K (2 ^ 60)) "5/4" 53).2 != .eq
