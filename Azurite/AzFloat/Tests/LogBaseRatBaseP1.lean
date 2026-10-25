/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRatBaseP1
import Azurite.AzFloat.LogBaseP1
import Azurite.AzFloat.LogBasePow2P1
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b (1 + x)` with a rational base

Special values, exact cases (including bases with odd denominators), agreement with the natural,
power-of-two and float-base `log_b (1 + x)` and with `log_b` on the exact `1 + x`, and
`log₃ (1 + 6) = 1.7712437491614222600679283070824577180664713345942434793689925…`,
`log_{3/2} (1 + 1) = 1.7095112913514547769761902621740141406150037352361072230744539…`,
`log₁₀ (1 + 2^(−30)) = 4.0446825483908662596994682583423467366992942764363982162…·10^(−10)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatBaseP1PrecRound x (Q b) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard L nan "2" 10 == (nan, .eq)
#guard L (F "1" 53) "-2" 10 == (nan, .eq)
#guard L ninf "2" 10 == (nan, .eq)
#guard L (F "-2" 53) "2" 10 == (nan, .eq)                     -- `1 + x < 0`
#guard L (F "-3/2" 53) "2/3" 10 == (nan, .eq)
#guard L (F "1" 53) "2" 0 == (nan, .eq)                      -- precision 0
-- base `0` and base `1`
#guard L (F "1" 53) "0" 10 == (zero, .eq)
#guard L pinf "0" 10 == (nan, .eq)
#guard L (F "-1" 53) "0" 10 == (nan, .eq)
#guard L (F "1" 53) "1" 10 == (infinity true, .eq)
#guard L (F "-1/2" 53) "1" 10 == (infinity false, .eq)
#guard L zero "1" 10 == (nan, .eq)
#guard L pinf "1" 10 == (infinity true, .eq)
-- `x = ∞`, `x = 0`, `x = −1`
#guard L pinf "2" 10 == (infinity true, .eq)
#guard L pinf "2/3" 10 == (infinity false, .eq)
#guard L zero "2" 10 == (zero, .eq)
#guard L zero "2/3" 10 == (zero, .eq)
#guard L (F "-1" 53) "2" 10 == (infinity false, .eq)
#guard L (F "-1" 53) "2/3" 10 == (infinity true, .eq)

-- exact cases
#guard L (F "7" 53) "4" 53 == (F "3/2" 53, .eq)
#guard L (F "7" 53) "1/2" 53 == (F "-3" 53, .eq)
#guard L (F "-7/8" 53) "1/4" 53 == (F "3/2" 53, .eq)
#guard L (F "26" 53) "9" 53 == (F "3/2" 53, .eq)
#guard L (F "26" 53) "1/3" 53 == (F "-3" 53, .eq)             -- an odd denominator
#guard L (F "2" 53) "1/9" 53 == (F "-1/2" 53, .eq)
#guard L (F "5/4" 53) "3/2" 53 == (F "2" 53, .eq)             -- `9/4`
#guard L (F "5/4" 53) "2/3" 53 == (F "-2" 53, .eq)
#guard L (F "19/8" 53) "2/3" 53 == (F "-3" 53, .eq)           -- `27/8`
#guard L (F "1/2" 53) "4/9" 53 == (F "-1/2" 53, .eq)          -- `3/2`
#guard L (F "-7/16" 53) "3/4" 53 == (F "2" 53, .eq)           -- `9/16`
#guard L (F "999" 53) "10" 53 == (F "3" 53, .eq)
#guard L (F "999" 53) "1/10" 53 == (F "-3" 53, .eq)
#guard L (F "9" 53) "1000" 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "9" 53) "1/1000" 53 .Floor == ofAzRatRound (Q "-1/3") 53 .Floor
#guard L (F "999" 53) "10" 1 == (F "4" 1, .gt)
#guard (L (F "3" 53) "2/3" 53).2 != .eq                       -- `n, d > 1`: never exact
#guard (L (F "1" 53) "10" 53).2 != .eq
#guard (L (F "-1/2" 53) "3" 53).2 != .eq

-- agreement with the natural, power-of-two and float-base `log_b (1 + x)`, and with `log_b`
#guard L (F "1" 53) "10" 150 == logBaseP1PrecRound (F "1" 53) 10 150 .Nearest
#guard L (F "-1/2" 53) "10" 150 .Floor == logBaseP1PrecRound (F "-1/2" 53) 10 150 .Floor
#guard L (F "9" 53) "8" 150 == logBasePow2P1PrecRound (F "9" 53) (K 3) 150 .Nearest
#guard L (F "9" 53) "1/8" 150 .Up == logBasePow2P1PrecRound (F "9" 53) (K (-3)) 150 .Up
#guard L (F "9" 53) "3/2" 150 == logBaseFloatP1PrecRound (F "9" 53) (F "3/2" 53) 150 .Nearest
#guard L (F "9" 53) "3/2" 150 .Ceiling == logBaseRatBasePrecRound (F "10" 53) (Q "3/2") 150 .Ceiling
#guard L (F "-3/8" 53) "2/3" 150 == logBaseRatBasePrecRound (F "5/8" 53) (Q "2/3") 150 .Nearest

-- `log₃ (1 + 6)`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard (L (F "6" 53) "3" 150).1 == ofAzRat ref37 150
#guard (L (F "6" 53) "1/3" 150).1 == ofAzRat (-ref37) 150
#guard (L (F "6" 53) "3" 150 .Floor).1 == (ofAzRatRound ref37 150 .Floor).1
-- `log_{3/2} (1 + 1)`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard (L (F "1" 53) "3/2" 150).1 == ofAzRat ref32 150
#guard (L (F "1" 53) "2/3" 150).1 == ofAzRat (-ref32) 150
#guard (L (F "1" 53) "2/3" 150 .Ceiling).1 == (ofAzRatRound (-ref32) 150 .Ceiling).1
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard (L (F "1" 53) "1048577/1048576" 100).1 == ofAzRat refUp 100
#guard (L (F "-1/2" 53) "1048577/1048576" 100).1 == ofAzRat (-refUp) 100
-- a tiny argument: `log₁₀ (1 + 2^(−30))`
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)
#guard (L (F "1/1073741824" 53) "10" 100).1 == ofAzRat refTiny 100
#guard (L (F "1/1073741824" 53) "1/10" 100).1 == ofAzRat (-refTiny) 100

-- default precision
#guard logBaseRatBaseP1 (F "7" 10) (Q "4") == F "3/2" 10
#guard logBaseRatBaseP1 (F "6" 53) (Q "3") == ofAzRat ref37 53
#guard logBaseRatBaseP1 (F "1" 53) (Q "10") == logBaseP1 (F "1" 53) 10
