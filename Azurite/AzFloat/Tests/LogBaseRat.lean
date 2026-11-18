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
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln

/-!
# Tests for `log_b` of a rational

Special values, exact cases (integer powers, possibly negative, of the primitive root of the
base), agreement with `log_{2^k}` for power-of-two bases and with the float version on floats,
and `log₁₀ 2`, `log₁₀ (1/3) = −0.477121254719662437295027903255115309200128864190695864829865…`,
`log₃ (7/4)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (q : String) (b : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatPrecRound (Q q) b p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L "1" 0 10) == ("NaN", .eq) -- base 0
#guard D (L "1" 1 10) == ("NaN", .eq) -- base 1
#guard D (L "0" 10 10) == ("-Infinity", .eq)
#guard D (L "-8" 10 10) == ("NaN", .eq)
#guard D (L "-1/8" 10 10) == ("NaN", .eq)
#guard D (L "8" 10 0) == ("NaN", .eq) -- precision 0

-- exact cases: `q = c^r` for `b = c^s` gives `r / s`, rounded once
#guard D (L "1" 10 53) == ("0.0", .eq)
#guard D (L "1000" 10 53) == ("3.0", .eq)
#guard D (L "1/1000" 10 53) == ("-3.0", .eq)
#guard D (L "36" 6 53) == ("2.0", .eq)
#guard D (L "1/36" 6 53) == ("-2.0", .eq)
#guard D (L "6" 36 53) == ("0.5", .eq)
#guard D (L "1/6" 36 53) == ("-0.5", .eq)
#guard D (L "27" 9 53) == ("1.5", .eq)
#guard D (L "1/27" 9 53) == ("-1.5", .eq)
#guard D (L "3" 27 53) == ("0.3333333333333333", .lt)
#guard D (L "1/3" 27 53 .Up) == ("-0.33333333333333337", .lt)
#guard D (L "1/9" 27 53 .Floor) == ("-0.6666666666666667", .lt)
#guard D (L "1000" 10 1) == ("4.0", .gt) -- 3 rounded to 1 bit
#guard D (L "1/1000" 10 1 .Ceiling) == ("-2.0", .gt)
#guard D (L "10" 1000 53) == ("0.3333333333333333", .lt)
#guard (L "2/3" 36 53).2 != .eq                               -- not a power of 6

-- power-of-two bases agree with `log_{2^k}`
#guard L "10" 2 53 == log2RatPrecRound (Q "10") 53 .Nearest
#guard L "10" 8 53 == logBasePow2RatPrecRound (Q "10") (K 3) 53 .Nearest
#guard L "1/10" 16 20 .Floor == logBasePow2RatPrecRound (Q "1/10") (K 4) 20 .Floor
#guard D (L "2" 8 53) == ("0.3333333333333333", .lt)
#guard D (L "1/2" 4 53) == ("-0.5", .eq)

-- floats agree with the float version
#guard L "7/4" 3 150 == logBasePrecRound (X "1.75" 53) 3 150 .Nearest
#guard L "2" 10 150 .Floor == logBasePrecRound (X "2" 53) 10 150 .Floor
#guard L "1000" 10 53 == logBasePrecRound (X "1000" 53) 10 53 .Nearest

-- `log₁₀ 2`
private def ref102 : AzRat :=
  Q ("301029995663981195213738894724493026768189881462108541310427/1"
    ++ "".pushn '0' 60)
#guard toString ((L "2" 10 150).1) == "0.3010299956639811952137388947244930267681898814"
#guard toString ((L "2" 10 150 .Ceiling).1) == "0.3010299956639811952137388947244930267681898817"
#guard (L "2" 10 150).2 == .lt
#guard toString ((L "1/2" 10 150).1) == "-0.3010299956639811952137388947244930267681898814"
-- `log₁₀ (1/3)`
private def ref103 : AzRat :=
  Q ("-477121254719662437295027903255115309200128864190695864829865/1"
    ++ "".pushn '0' 60)
#guard toString ((L "1/3" 10 150).1) == "-0.477121254719662437295027903255115309200128864"
#guard toString ((L "1/3" 10 150 .Up).1) == "-0.4771212547196624372950279032551153092001288644"
#guard toString ((L "1/3" 10 150 .Down).1) == "-0.477121254719662437295027903255115309200128864"
#guard toString ((L "3" 10 150).1) == "0.477121254719662437295027903255115309200128864"
-- `log₃ (7/4)`
private def ref374 : AzRat :=
  Q ("509384242018507385868874078396936009467300054330482623627682/1"
    ++ "".pushn '0' 60)
#guard toString ((L "7/4" 3 150).1) == "0.509384242018507385868874078396936009467300055"
#guard toString ((L "4/7" 3 150).1) == "-0.509384242018507385868874078396936009467300055"
-- the largest base: `log_{2^64 − 1} 2` is just above `1/64`
#guard L "2" (UInt64.ofNat (2 ^ 64 - 1)) 64 == (ofAzRat (Q "1/64") 64, .lt)

-- default rounding
#guard toString (logBaseRat (Q "1000") 10 10) == "3.0"
#guard logBaseRat (Q "10") 2 53 == log2Rat (Q "10") 53
#guard toString (logBaseRat (Q "2") 10 53) == "0.3010299956639812"

-- precomputed constants: the same results
#guard logBaseRatWith (LogBaseConsts.forPrecision 10 53) (Q "7") 53 == logBaseRat (Q "7") 10 53
#guard logBaseRatWith (LogBaseConsts.forPrecision 3 53) (Q "1/7") 53 == logBaseRat (Q "1/7") 3 53
#guard logBaseRatWith (LogBaseConsts.forPrecision 4 53) (Q "7") 53 == logBaseRat (Q "7") 4 53
#guard logBaseRatWith (LogBaseConsts.forPrecision 10 53) (Q "100") 53 == logBaseRat (Q "100") 10 53
