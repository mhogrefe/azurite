/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseRat
import Azurite.AzFloat.LogBase
import Azurite.AzFloat.Log2Rat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b` of a rational

Special values, exact cases (integer powers, possibly negative, of the primitive root of the
base), agreement with `log_{2^k}` for power-of-two bases and with the float version on floats,
and `log₁₀ 2`, `log₁₀ (1/3) = −0.477121254719662437295027903255115309200128864190695864829865…`,
`log₃ (7/4)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (q : String) (b : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatPrecRound (Q q) b p m

-- special values
#guard L "1" 0 10 == (nan, .eq)                              -- base 0
#guard L "1" 1 10 == (nan, .eq)                              -- base 1
#guard L "0" 10 10 == (infinity false, .eq)
#guard L "-8" 10 10 == (nan, .eq)
#guard L "-1/8" 10 10 == (nan, .eq)
#guard L "8" 10 0 == (nan, .eq)                              -- precision 0

-- exact cases: `q = c^r` for `b = c^s` gives `r / s`, rounded once
#guard L "1" 10 53 == (zero, .eq)
#guard L "1000" 10 53 == (F "3" 53, .eq)
#guard L "1/1000" 10 53 == (F "-3" 53, .eq)
#guard L "36" 6 53 == (F "2" 53, .eq)
#guard L "1/36" 6 53 == (F "-2" 53, .eq)
#guard L "6" 36 53 == (F "1/2" 53, .eq)
#guard L "1/6" 36 53 == (F "-1/2" 53, .eq)
#guard L "27" 9 53 == (F "3/2" 53, .eq)
#guard L "1/27" 9 53 == (F "-3/2" 53, .eq)
#guard L "3" 27 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L "1/3" 27 53 .Up == ofAzRatRound (Q "-1/3") 53 .Up
#guard L "1/9" 27 53 .Floor == ofAzRatRound (Q "-2/3") 53 .Floor
#guard L "1000" 10 1 == (F "4" 1, .gt)                       -- 3 rounded to 1 bit
#guard L "1/1000" 10 1 .Ceiling == (F "-2" 1, .gt)
#guard L "10" 1000 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard (L "2/3" 36 53).2 != .eq                               -- not a power of 6

-- power-of-two bases agree with `log_{2^k}`
#guard L "10" 2 53 == log2RatPrecRound (Q "10") 53 .Nearest
#guard L "10" 8 53 == logBasePow2RatPrecRound (Q "10") (K 3) 53 .Nearest
#guard L "1/10" 16 20 .Floor == logBasePow2RatPrecRound (Q "1/10") (K 4) 20 .Floor
#guard L "2" 8 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L "1/2" 4 53 == (F "-1/2" 53, .eq)

-- floats agree with the float version
#guard L "7/4" 3 150 == logBasePrecRound (F "7/4" 53) 3 150 .Nearest
#guard L "2" 10 150 .Floor == logBasePrecRound (F "2" 53) 10 150 .Floor
#guard L "1000" 10 53 == logBasePrecRound (F "1000" 53) 10 53 .Nearest

-- `log₁₀ 2`
private def ref102 : AzRat :=
  Q ("301029995663981195213738894724493026768189881462108541310427/1"
    ++ "".pushn '0' 60)
#guard (L "2" 10 150).1 == ofAzRat ref102 150
#guard (L "2" 10 150 .Ceiling).1 == (ofAzRatRound ref102 150 .Ceiling).1
#guard (L "2" 10 150).2 == .lt
#guard (L "1/2" 10 150).1 == ofAzRat (-ref102) 150
-- `log₁₀ (1/3)`
private def ref103 : AzRat :=
  Q ("-477121254719662437295027903255115309200128864190695864829865/1"
    ++ "".pushn '0' 60)
#guard (L "1/3" 10 150).1 == ofAzRat ref103 150
#guard (L "1/3" 10 150 .Up).1 == (ofAzRatRound ref103 150 .Up).1
#guard (L "1/3" 10 150 .Down).1 == (ofAzRatRound ref103 150 .Down).1
#guard (L "3" 10 150).1 == ofAzRat (-ref103) 150
-- `log₃ (7/4)`
private def ref374 : AzRat :=
  Q ("509384242018507385868874078396936009467300054330482623627682/1"
    ++ "".pushn '0' 60)
#guard (L "7/4" 3 150).1 == ofAzRat ref374 150
#guard (L "4/7" 3 150).1 == ofAzRat (-ref374) 150
-- the largest base: `log_{2^64 − 1} 2` is just above `1/64`
#guard L "2" (UInt64.ofNat (2 ^ 64 - 1)) 64 == (ofAzRat (Q "1/64") 64, .lt)

-- default rounding
#guard logBaseRat (Q "1000") 10 10 == F "3" 10
#guard logBaseRat (Q "10") 2 53 == log2Rat (Q "10") 53
#guard logBaseRat (Q "2") 10 53 == ofAzRat ref102 53
