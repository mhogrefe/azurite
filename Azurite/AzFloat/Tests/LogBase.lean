/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBase
import Azurite.AzFloat.Log2
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b`

Special values, exact cases (integer powers of the primitive root of the base), agreement with
`log_{2^k}` for power-of-two bases, and
`log₁₀ 2 = 0.301029995663981195213738894724493026768189881462108541310427…`,
`log₃ (7/4) = 0.509384242018507385868874078396936009467300054330482623627682…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (b : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePrecRound x b p m

-- special values
#guard L nan 10 10 == (nan, .eq)
#guard L one 0 10 == (nan, .eq)                              -- base 0
#guard L one 1 10 == (nan, .eq)                              -- base 1
#guard L (infinity true) 10 10 == (infinity true, .eq)
#guard L (infinity false) 10 10 == (nan, .eq)
#guard L zero 10 10 == (infinity false, .eq)
#guard L (F "-8" 53) 10 10 == (nan, .eq)
#guard L (F "8" 53) 10 0 == (nan, .eq)                       -- precision 0

-- exact cases: `x = c^r` for `b = c^s` gives `r / s`, rounded once
#guard L (F "1" 53) 10 53 == (zero, .eq)
#guard L (F "1000" 53) 10 53 == (F "3" 53, .eq)
#guard L (F "36" 53) 6 53 == (F "2" 53, .eq)
#guard L (F "6" 53) 36 53 == (F "1/2" 53, .eq)
#guard L (F "144" 53) 12 53 == (F "2" 53, .eq)
#guard L (F "3" 53) 9 53 == (F "1/2" 53, .eq)
#guard L (F "27" 53) 9 53 == (F "3/2" 53, .eq)
#guard L (F "3" 53) 27 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "3" 53) 27 53 .Up == ofAzRatRound (Q "1/3") 53 .Up
#guard L (F "9" 53) 27 53 .Floor == ofAzRatRound (Q "2/3") 53 .Floor
#guard L (F "1000" 53) 10 1 == (F "4" 1, .gt)                -- 3 rounded to 1 bit
#guard L (F "1000" 53) 10 1 .Floor == (F "2" 1, .lt)
#guard L (F "10" 53) 1000 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "1/1000" 53) 10 53 == (F "-3" 53, .lt)            -- 1/1000 is not a float

-- power-of-two bases agree with `log_{2^k}`
#guard L (F "10" 53) 2 53 == log2PrecRound (F "10" 53) 53 .Nearest
#guard L (F "10" 53) 8 53 == logBasePow2PrecRound (F "10" 53) (K 3) 53 .Nearest
#guard L (F "10" 53) 16 20 .Floor == logBasePow2PrecRound (F "10" 53) (K 4) 20 .Floor
#guard L (F "2" 53) 8 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "1/2" 53) 4 53 == (F "-1/2" 53, .eq)
#guard L (F "3" 53) ((1 : UInt64) <<< 63) 53 == logBasePow2PrecRound (F "3" 53) (K 63) 53 .Nearest

-- `log₁₀ 2`
private def ref102 : AzRat :=
  Q ("301029995663981195213738894724493026768189881462108541310427/1"
    ++ "".pushn '0' 60)
#guard (L (F "2" 53) 10 150).1 == ofAzRat ref102 150
#guard (L (F "2" 53) 10 150 .Floor).1 == (ofAzRatRound ref102 150 .Floor).1
#guard (L (F "2" 53) 10 150 .Ceiling).1 == (ofAzRatRound ref102 150 .Ceiling).1
#guard (L (F "2" 53) 10 150).2 == .lt
#guard (L (F "1/2" 53) 10 150).1 == ofAzRat (-ref102) 150
-- `log₃ (7/4)`
private def ref374 : AzRat :=
  Q ("509384242018507385868874078396936009467300054330482623627682/1"
    ++ "".pushn '0' 60)
#guard (L (F "7/4" 53) 3 150).1 == ofAzRat ref374 150
#guard (L (F "7/4" 53) 3 150 .Up).1 == (ofAzRatRound ref374 150 .Up).1
-- the largest base: `log_{2^64 − 1} 2` is just above `1/64`
#guard L (F "2" 53) (UInt64.ofNat (2 ^ 64 - 1)) 64 == (ofAzRat (Q "1/64") 64, .lt)

-- default precision
#guard logBase (F "1000" 10) 10 == F "3" 10
#guard logBase (F "10" 53) 2 == log2 (F "10" 53)
#guard logBase (F "2" 53) 10 == ofAzRat ref102 53
