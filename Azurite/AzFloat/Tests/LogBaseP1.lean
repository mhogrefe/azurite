/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseP1
import Azurite.AzFloat.LogBase
import Azurite.AzFloat.Log2P1
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b (1 + x)`

Special values, exact cases (`1 + x = c^r` for the primitive root `c` of the base, and
`1 + x = 2^j` for power-of-two bases), agreement with `log2P1` and with `log_b` on `1 + x`, and
`log₁₀ (1 + 2^(−30)) = 4.044682548390866259699468258342346736699294276436398216273…·10^(−10)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def L (x : AzFloat) (b : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseP1PrecRound x b p m

-- special values
#guard L nan 10 10 == (nan, .eq)
#guard L one 0 10 == (nan, .eq)                              -- base 0
#guard L one 1 10 == (nan, .eq)                              -- base 1
#guard L (infinity true) 10 10 == (infinity true, .eq)
#guard L (infinity false) 10 10 == (nan, .eq)
#guard L zero 10 10 == (zero, .eq)
#guard L (F "-1" 53) 10 10 == (infinity false, .eq)
#guard L (F "-2" 53) 10 10 == (nan, .eq)
#guard L (F "-3/2" 53) 10 10 == (nan, .eq)
#guard L (F "8" 53) 10 0 == (nan, .eq)                       -- precision 0

-- exact cases: `1 + x = c^r` for `b = c^s` gives `r / s`, rounded once
#guard L (F "9" 53) 10 53 == (F "1" 53, .eq)
#guard L (F "99" 53) 10 53 == (F "2" 53, .eq)
#guard L (F "999" 53) 10 53 == (F "3" 53, .eq)
#guard L (F "35" 53) 6 53 == (F "2" 53, .eq)
#guard L (F "5" 53) 36 53 == (F "1/2" 53, .eq)
#guard L (F "26" 53) 9 53 == (F "3/2" 53, .eq)
#guard L (F "2" 53) 27 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "2" 53) 27 53 .Up == ofAzRatRound (Q "1/3") 53 .Up
#guard L (F "8" 53) 27 53 .Floor == ofAzRatRound (Q "2/3") 53 .Floor
#guard L (F "999" 53) 10 1 == (F "4" 1, .gt)                 -- 3 rounded to 1 bit
#guard L (F "99999999999999999999" 100) 10 100 == (F "20" 100, .eq)
#guard (L (F "1/2" 53) 10 53).2 != .eq                        -- 3/2 is not a power of 10
#guard (L (F "-1/2" 53) 10 53).2 != .eq                       -- 1/2 is not a power of 10

-- power-of-two bases: `1 + x = 2^j` gives `j / k`
#guard L (F "7" 53) 8 53 == (F "1" 53, .eq)
#guard L (F "3" 53) 16 53 == (F "1/2" 53, .eq)
#guard L (F "-1/2" 53) 4 53 == (F "-1/2" 53, .eq)
#guard L (F "-7/8" 53) 8 53 == (F "-1" 53, .eq)
#guard L (F "1" 53) 8 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "-3/4" 53) 8 53 .Floor == ofAzRatRound (Q "-2/3") 53 .Floor
#guard L (F "1267650600228229401496703205375" 110) 1024 110 == (F "10" 110, .eq)
#guard L (F "10" 53) 2 53 == log2P1PrecRound (F "10" 53) 53 .Nearest
#guard L (F "-1/3" 53) 2 20 .Floor == log2P1PrecRound (F "-1/3" 53) 20 .Floor
#guard L (F "1/1073741824" 53) 2 100 == log2P1PrecRound (F "1/1073741824" 53) 100 .Nearest

-- agreement with `log_b` on the exact `1 + x`
#guard L (F "1" 53) 10 150 == logBasePrecRound (F "2" 53) 10 150 .Nearest
#guard L (F "2" 53) 10 150 .Floor == logBasePrecRound (F "3" 53) 10 150 .Floor
#guard L (F "3/4" 53) 3 150 == logBasePrecRound (F "7/4" 53) 3 150 .Nearest
#guard L (F "-1/2" 53) 10 150 .Up == logBasePrecRound (F "1/2" 53) 10 150 .Up
#guard L (F "-3/4" 53) 7 150 == logBasePrecRound (F "1/4" 53) 7 150 .Nearest

-- `log₁₀ (1 + 2^(−30))`: a tiny argument
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)
#guard (L (F "1/1073741824" 53) 10 100).1 == ofAzRat refTiny 100
#guard (L (F "1/1073741824" 53) 10 100 .Floor).1 == (ofAzRatRound refTiny 100 .Floor).1
#guard (L (F "1/1073741824" 53) 10 100 .Ceiling).1 == (ofAzRatRound refTiny 100 .Ceiling).1
#guard (L (F "-1/1073741824" 53) 10 60).2 != .eq

-- default precision
#guard logBaseP1 (F "999" 10) 10 == F "3" 10
#guard logBaseP1 (F "7" 53) 8 == F "1" 53
#guard logBaseP1 (F "10" 53) 2 == log2P1 (F "10" 53)
#guard logBaseP1 (F "1" 53) 10 == logBase (F "2" 53) 10
