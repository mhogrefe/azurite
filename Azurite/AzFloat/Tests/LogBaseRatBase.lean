/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatBase
import Azurite.AzFloat.LogBase
import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.Conversion
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatBasePrecRound x (Q b) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard L nan "2" 10 == (nan, .eq)
#guard L (F "2" 53) "-2" 10 == (nan, .eq)
#guard L (F "-2" 53) "2" 10 == (nan, .eq)
#guard L ninf "2" 10 == (nan, .eq)
#guard L (F "8" 53) "2" 0 == (nan, .eq)                      -- precision 0
-- base `0`
#guard L (F "2" 53) "0" 10 == (zero, .eq)
#guard L (F "1/2" 53) "0" 10 == (zero, .eq)
#guard L pinf "0" 10 == (nan, .eq)
#guard L zero "0" 10 == (nan, .eq)
-- base `1`
#guard L one "1" 10 == (nan, .eq)
#guard L (F "2" 53) "1" 10 == (infinity true, .eq)
#guard L (F "1/2" 53) "1" 10 == (infinity false, .eq)
#guard L pinf "1" 10 == (infinity true, .eq)
#guard L zero "1" 10 == (infinity false, .eq)
-- `x = ∞`, `x = 0`, `x = 1`
#guard L pinf "2" 10 == (infinity true, .eq)
#guard L pinf "2/3" 10 == (infinity false, .eq)
#guard L zero "2" 10 == (infinity false, .eq)
#guard L zero "2/3" 10 == (infinity true, .eq)
#guard L one "2" 10 == (zero, .eq)
#guard L one "2/3" 10 == (zero, .eq)

-- exact cases: a common rational root
#guard L (F "8" 53) "4" 53 == (F "3/2" 53, .eq)
#guard L (F "8" 53) "1/2" 53 == (F "-3" 53, .eq)
#guard L (F "1/8" 53) "1/4" 53 == (F "3/2" 53, .eq)
#guard L (F "27" 53) "9" 53 == (F "3/2" 53, .eq)
#guard L (F "27" 53) "1/3" 53 == (F "-3" 53, .eq)             -- an odd denominator
#guard L (F "3" 53) "1/9" 53 == (F "-1/2" 53, .eq)
#guard L (F "243" 53) "1/3" 53 == (F "-5" 53, .eq)
#guard L (F "9/4" 53) "3/2" 53 == (F "2" 53, .eq)
#guard L (F "9/4" 53) "2/3" 53 == (F "-2" 53, .eq)            -- `(2/3)^(−2)`
#guard L (F "27/8" 53) "2/3" 53 == (F "-3" 53, .eq)
#guard L (F "3/2" 53) "4/9" 53 == (F "-1/2" 53, .eq)
#guard L (F "9/16" 53) "3/4" 53 == (F "2" 53, .eq)
#guard L (F "1000" 53) "10" 53 == (F "3" 53, .eq)
#guard L (F "1000" 53) "1/10" 53 == (F "-3" 53, .eq)
#guard L (F "10" 53) "1000" 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "10" 53) "1/1000" 53 .Floor == ofAzRatRound (Q "-1/3") 53 .Floor
#guard L (F "1000" 53) "10" 1 == (F "4" 1, .gt)
#guard (L (F "4" 53) "2/3" 53).2 != .eq                       -- `n, d > 1`: never exact
#guard (L (F "2" 53) "3/5" 53).2 != .eq
#guard (L (F "2" 53) "10" 53).2 != .eq

-- agreement with the natural, power-of-two and float-base versions
#guard L (F "7/4" 53) "3" 150 == logBasePrecRound (F "7/4" 53) 3 150 .Nearest
#guard L (F "2" 53) "10" 150 .Floor == logBasePrecRound (F "2" 53) 10 150 .Floor
#guard L (F "10" 53) "8" 150 == logBasePow2PrecRound (F "10" 53) (K 3) 150 .Nearest
#guard L (F "10" 53) "1/8" 150 .Up == logBasePow2PrecRound (F "10" 53) (K (-3)) 150 .Up
#guard L (F "2" 53) "3/2" 150 == logBaseFloatPrecRound (F "2" 53) (F "3/2" 53) 150 .Nearest
#guard L (F "5/8" 53) "9/4" 150 .Ceiling
  == logBaseFloatPrecRound (F "5/8" 53) (F "9/4" 53) 150 .Ceiling

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard (L (F "7" 53) "3" 150).1 == ofAzRat ref37 150
#guard (L (F "7" 53) "1/3" 150).1 == ofAzRat (-ref37) 150     -- an exact `1/3` base
#guard (L (F "7" 53) "3" 150 .Floor).1 == (ofAzRatRound ref37 150 .Floor).1
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard (L (F "2" 53) "3/2" 150).1 == ofAzRat ref32 150
#guard (L (F "2" 53) "2/3" 150).1 == ofAzRat (-ref32) 150     -- an exact `2/3` base
#guard (L (F "2" 53) "2/3" 150 .Ceiling).1 == (ofAzRatRound (-ref32) 150 .Ceiling).1
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard (L (F "2" 53) "1048577/1048576" 100).1 == ofAzRat refUp 100
#guard (L (F "1/2" 53) "1048577/1048576" 100).1 == ofAzRat (-refUp) 100
#guard (L (F "2" 53) "1048575/1048576" 100).2 != .eq

-- default precision
#guard logBaseRatBase (F "8" 10) (Q "4") == F "3/2" 10
#guard logBaseRatBase (F "7" 53) (Q "3") == ofAzRat ref37 53
#guard logBaseRatBase (F "2" 53) (Q "10") == logBase (F "2" 53) 10
