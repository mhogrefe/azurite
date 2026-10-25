/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBasePow2P1
import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.Log2P1
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_{2^k} (1 + x)`

Special values, exact cases `1 + x = 2^j` (value `j / k`), agreement with `log2P1` for `k = 1`
and with `log_{2^k}` on the exact `1 + x`, and
`log₁₆ (1 + 9) = 0.830482023721840586967579857372347543966207848256145153013…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (k : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePow2P1PrecRound x (K k) p m

-- special values
#guard L nan 4 10 == (nan, .eq)
#guard L one 0 10 == (nan, .eq)                              -- base 1
#guard L (infinity true) 4 10 == (infinity true, .eq)
#guard L (infinity true) (-4) 10 == (infinity false, .eq)
#guard L (infinity false) 4 10 == (nan, .eq)
#guard L zero 4 10 == (zero, .eq)
#guard L zero (-4) 10 == (zero, .eq)
#guard L (F "-1" 53) 4 10 == (infinity false, .eq)
#guard L (F "-1" 53) (-4) 10 == (infinity true, .eq)
#guard L (F "-2" 53) 4 10 == (nan, .eq)
#guard L (F "-3/2" 53) 4 10 == (nan, .eq)
#guard L (F "8" 53) 4 0 == (nan, .eq)                        -- precision 0

-- exact cases: `1 + x = 2^j` gives `j / k`, rounded once
#guard L (F "7" 53) 3 53 == (F "1" 53, .eq)
#guard L (F "3" 53) 4 53 == (F "1/2" 53, .eq)
#guard L (F "15" 53) 4 53 == (F "1" 53, .eq)
#guard L (F "15" 53) (-4) 53 == (F "-1" 53, .eq)
#guard L (F "-1/2" 53) 2 53 == (F "-1/2" 53, .eq)
#guard L (F "-3/4" 53) 4 53 .Ceiling == (F "-1/2" 53, .eq)
#guard L (F "-7/8" 53) (-3) 53 == (F "1" 53, .eq)
#guard L (F "1" 53) 3 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "1" 53) 3 53 .Up == ofAzRatRound (Q "1/3") 53 .Up
#guard L (F "3" 53) 3 53 .Floor == ofAzRatRound (Q "2/3") 53 .Floor
#guard L (F "-3/4" 53) 3 53 == ofAzRatRound (Q "-2/3") 53 .Nearest
#guard L (F "1023" 53) 10 1 == (F "1" 1, .eq)
#guard L (F "1267650600228229401496703205375" 110) 10 110 == (F "10" 110, .eq)
#guard (L (F "1/2" 53) 4 53).2 != .eq                         -- 3/2 is not a power of two

-- `k = 1` agrees with `log2P1`
#guard L (F "10" 53) 1 53 == log2P1PrecRound (F "10" 53) 53 .Nearest
#guard L (F "-1/3" 53) 1 20 .Floor == log2P1PrecRound (F "-1/3" 53) 20 .Floor
#guard L (F "1/1073741824" 53) 1 100 == log2P1PrecRound (F "1/1073741824" 53) 100 .Nearest

-- agreement with `log_{2^k}` on the exact `1 + x`
#guard L (F "9" 53) 4 150 == logBasePow2PrecRound (F "10" 53) (K 4) 150 .Nearest
#guard L (F "9" 53) 4 150 .Floor == logBasePow2PrecRound (F "10" 53) (K 4) 150 .Floor
#guard L (F "9" 53) (-4) 150 == logBasePow2PrecRound (F "10" 53) (K (-4)) 150 .Nearest
#guard L (F "-3/8" 53) 4 150 .Ceiling == logBasePow2PrecRound (F "5/8" 53) (K 4) 150 .Ceiling
#guard L (F "10" 53) (-1) 53 == logBasePow2PrecRound (F "11" 53) (K (-1)) 53 .Nearest
#guard L (F "2" 53) 1000 100 == logBasePow2PrecRound (F "3" 53) (K 1000) 100 .Nearest

-- `log₁₆ (1 + 9)`
private def ref16 : AzRat :=
  Q ("830482023721840586967579857372347543966207848256145153013/1"
    ++ "".pushn '0' 57)
#guard (L (F "9" 53) 4 150).1 == ofAzRat ref16 150
#guard (L (F "9" 53) 4 150 .Floor).1 == (ofAzRatRound ref16 150 .Floor).1
#guard (L (F "9" 53) (-4) 150).1 == ofAzRat (-ref16) 150
-- a tiny argument: `log₁₆ (1 + 2^(−30))` is not exact
#guard (L (F "1/1073741824" 53) 4 100).2 != .eq
#guard (L (F "-1/1073741824" 53) 4 100).2 != .eq

-- default precision
#guard logBasePow2P1 (F "7" 10) (K 3) == F "1" 10
#guard logBasePow2P1 (F "10" 53) (K 1) == log2P1 (F "10" 53)
#guard logBasePow2P1 (F "9" 53) (K 4) == ofAzRat ref16 53
