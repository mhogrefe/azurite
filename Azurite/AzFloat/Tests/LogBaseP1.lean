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
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln

/-!
# Tests for `log_b (1 + x)`

Special values, exact cases (`1 + x = c^r` for the primitive root `c` of the base, and
`1 + x = 2^j` for power-of-two bases), agreement with `log2P1` and with `log_b` on `1 + x`, and
`log₁₀ (1 + 2^(−30)) = 4.044682548390866259699468258342346736699294276436398216273…·10^(−10)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def L (x : AzFloat) (b : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseP1PrecRound x b p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L nan 10 10) == ("NaN", .eq)
#guard D (L one 0 10) == ("NaN", .eq) -- base 0
#guard D (L one 1 10) == ("NaN", .eq) -- base 1
#guard D (L (infinity true) 10 10) == ("Infinity", .eq)
#guard D (L (infinity false) 10 10) == ("NaN", .eq)
#guard D (L zero 10 10) == ("0.0", .eq)
#guard D (L (X "-1" 53) 10 10) == ("-Infinity", .eq)
#guard D (L (X "-2" 53) 10 10) == ("NaN", .eq)
#guard D (L (X "-1.5" 53) 10 10) == ("NaN", .eq)
#guard D (L (X "8" 53) 10 0) == ("NaN", .eq) -- precision 0

-- exact cases: `1 + x = c^r` for `b = c^s` gives `r / s`, rounded once
#guard D (L (X "9" 53) 10 53) == ("1.0", .eq)
#guard D (L (X "99" 53) 10 53) == ("2.0", .eq)
#guard D (L (X "999" 53) 10 53) == ("3.0", .eq)
#guard D (L (X "35" 53) 6 53) == ("2.0", .eq)
#guard D (L (X "5" 53) 36 53) == ("0.5", .eq)
#guard D (L (X "26" 53) 9 53) == ("1.5", .eq)
#guard D (L (X "2" 53) 27 53) == ("0.3333333333333333", .lt)
#guard D (L (X "2" 53) 27 53 .Up) == ("0.33333333333333337", .gt)
#guard D (L (X "8" 53) 27 53 .Floor) == ("0.6666666666666666", .lt)
#guard D (L (X "999" 53) 10 1) == ("4.0", .gt) -- 3 rounded to 1 bit
#guard D (L (X "99999999999999999999" 100) 10 100) == ("2.0e1", .eq)
#guard (L (X "0.5" 53) 10 53).2 != .eq                        -- 3/2 is not a power of 10
#guard (L (X "-0.5" 53) 10 53).2 != .eq                       -- 1/2 is not a power of 10

-- power-of-two bases: `1 + x = 2^j` gives `j / k`
#guard D (L (X "7" 53) 8 53) == ("1.0", .eq)
#guard D (L (X "3" 53) 16 53) == ("0.5", .eq)
#guard D (L (X "-0.5" 53) 4 53) == ("-0.5", .eq)
#guard D (L (X "-0.875" 53) 8 53) == ("-1.0", .eq)
#guard D (L (X "1" 53) 8 53) == ("0.3333333333333333", .lt)
#guard D (L (X "-0.75" 53) 8 53 .Floor) == ("-0.6666666666666667", .lt)
#guard D (L (X "1267650600228229401496703205375" 110) 1024 110) == ("1.0e1", .eq)
#guard L (X "10" 53) 2 53 == log2P1PrecRound (X "10" 53) 53 .Nearest
#guard L (X "-0.3333333333333333" 53) 2 20 .Floor == log2P1PrecRound (X "-0.3333333333333333" 53)
    20 .Floor
#guard L (X "0.000000000931322574615478515625" 53) 2 100 == log2P1PrecRound (X
    "0.000000000931322574615478515625" 53) 100 .Nearest

-- agreement with `log_b` on the exact `1 + x`
#guard L (X "1" 53) 10 150 == logBasePrecRound (X "2" 53) 10 150 .Nearest
#guard L (X "2" 53) 10 150 .Floor == logBasePrecRound (X "3" 53) 10 150 .Floor
#guard L (X "0.75" 53) 3 150 == logBasePrecRound (X "1.75" 53) 3 150 .Nearest
#guard L (X "-0.5" 53) 10 150 .Up == logBasePrecRound (X "0.5" 53) 10 150 .Up
#guard L (X "-0.75" 53) 7 150 == logBasePrecRound (X "0.25" 53) 7 150 .Nearest

-- `log₁₀ (1 + 2^(−30))`: a tiny argument
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)
#guard toString ((L (X "0.000000000931322574615478515625" 53) 10 100).1) ==
    "4.044682548390866259699468258343e-10"
#guard toString ((L (X "0.000000000931322574615478515625" 53) 10 100 .Floor).1) ==
    "4.04468254839086625969946825834e-10"
#guard toString ((L (X "0.000000000931322574615478515625" 53) 10 100 .Ceiling).1) ==
    "4.044682548390866259699468258343e\
  -10"
#guard (L (X "-0.000000000931322574615478515625" 53) 10 60).2 != .eq

-- default precision
#guard toString (logBaseP1 (X "999" 10) 10) == "3.0"
#guard toString (logBaseP1 (X "7" 53) 8) == "1.0"
#guard logBaseP1 (X "10" 53) 2 == log2P1 (X "10" 53)
#guard logBaseP1 (X "1" 53) 10 == logBase (X "2" 53) 10

-- precomputed constants: the same results
#guard logBaseP1With (LogBaseConsts.forPrecision 10 53) (X "0.5" 53) == logBaseP1 (X "0.5" 53) 10
#guard logBaseP1With (LogBaseConsts.forPrecision 3 53) (X "-0.5" 53) == logBaseP1 (X "-0.5" 53) 3
#guard logBaseP1With (LogBaseConsts.forPrecision 4 53) (X "3" 53) == logBaseP1 (X "3" 53) 4
#guard logBaseP1With (LogBaseConsts.forPrecision 10 53) (X "9" 53) == logBaseP1 (X "9" 53) 10

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
-- `log₁₀ (1 + x) ≈ x / ln 10`
#guard L tinyX 10 53 == ((X "0.4342944819032518" 53) <<< tinyE, .lt)
#guard (L (-tinyX) 10 53).2 == .gt

-- a huge power of two, `x = 2^K` with `K = 2^30 − 98`: `log₂ (1 + x) = K + ε`, `ε ≈ 2^(−K)`;
-- the side of `K` is decided without `K` bits of working precision
private def bigX : AzFloat := (X "1" 52) <<< AzInt.ofInt (2 ^ 30 - 98)
#guard L bigX 4 52 .Floor == (X "536870863" 52, .lt)
#guard L bigX 2 52 == (X "1073741726" 52, .lt)
#guard (L bigX 8 52).2 == .lt

-- huge integers with a base that is not a power of two: the exactness test rejects them by the
-- 2-adic guard of `checkedLogBase` instead of computing a power of about `2^30` bits
#guard (L bigX 10 52).2 == .gt

-- exponents far beyond memory: `logBaseP1ExactSkip` decides from the exponent and the
-- significand that `1 + x` is not a power of the base; nothing of that size is built
private def hugeX : AzFloat := (X "1" 53) <<< AzInt.ofInt (2 ^ 50)
#guard (L hugeX 10 53).2 != .eq
#guard (L hugeX 3 53 .Floor).2 == .lt
#guard (L ((X "3" 53) <<< AzInt.ofInt (2 ^ 50)) 7 53).2 != .eq
#guard (L ((X "1" 53) <<< AzInt.ofInt (-(2 ^ 50 : Int))) 10 53).2 != .eq
-- exact cases with an exponent above the precision: `1 + 8 = 3^2`, `1 + 80 = 3^4 = 9^2`
#guard D (L (X "8" 1) 3 53) == ("2.0", .eq)
#guard D (L (X "80" 3) 3 53) == ("4.0", .eq)
#guard D (L (X "80" 3) 9 53) == ("2.0", .eq)
#guard D (L (X "80" 3) 27 53) == ("1.3333333333333333", .lt)
#guard (L (X "88" 4) 3 53).2 != .eq
