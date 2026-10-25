/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBasePow2Rat
import Azurite.AzFloat.Log2Rat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_{2^k}` of a rational

Exact cases, agreement with `log₂` for `k = ±1`, and
`log₁₆ 10 = 0.830482023721840586967579857372347543966207848256145153013…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (q : String) (k : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePow2RatPrecRound (Q q) (K k) p m

-- special values
#guard L "1" 0 10 == (nan, .eq)                      -- base 1
#guard L "0" 4 10 == (infinity false, .eq)
#guard L "0" (-4) 10 == (infinity true, .eq)
#guard L "-8" 3 10 == (nan, .eq)
#guard L "-1/8" (-3) 10 == (nan, .eq)

-- exact powers of two: `j / k`, rounded once
#guard L "1" 4 53 == (zero, .eq)
#guard L "16" 4 53 == (F "1" 53, .eq)
#guard L "1/16" 4 53 == (F "-1" 53, .eq)
#guard L "256" (-4) 53 == (F "-2" 53, .eq)
#guard L "8" 4 53 == (F "3/4" 53, .eq)
#guard L "1/8" (-4) 53 == (F "3/4" 53, .eq)
#guard L "2" 3 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L "2" 3 53 .Up == ofAzRatRound (Q "1/3") 53 .Up
#guard L "1/4" 3 53 .Floor == ofAzRatRound (Q "-2/3") 53 .Floor
#guard L "1024" 10 1 == (F "1" 1, .eq)

-- `k = ±1` agrees with `log₂`
#guard L "10" 1 53 == log2RatPrecRound (Q "10") 53 .Nearest
#guard L "1/3" 1 20 .Floor == log2RatPrecRound (Q "1/3") 20 .Floor
#guard L "10" (-1) 53 == (-(log2RatPrecRound (Q "10") 53 .Nearest).1, .gt)
#guard L "3" (-1) 20 .Ceiling == log2RatPrecRound (Q "1/3") 20 .Ceiling

-- `log₁₆ 10` and `log₁₆ (1/10) = −log₁₆ 10`
private def ref16 : AzRat :=
  Q ("830482023721840586967579857372347543966207848256145153013/1"
    ++ "".pushn '0' 57)
#guard (L "10" 4 150).1 == ofAzRat ref16 150
#guard (L "10" 4 150 .Floor).1 == (ofAzRatRound ref16 150 .Floor).1
#guard (L "1/10" 4 150).1 == ofAzRat (-ref16) 150
#guard (L "10" (-4) 150).1 == ofAzRat (-ref16) 150
#guard (L "1/10" (-4) 150).1 == ofAzRat ref16 150
-- a non-dyadic rational with a non-dyadic base exponent: `log₈ (7/3) = log₂ (7/3) / 3`,
-- `log₂ (7/3) = 1.22239242133644792598823037328401429988…`
private def ref73 : AzRat :=
  Q ("12223924213364479259882303732840142998812122182736/3" ++ "".pushn '0' 49)
#guard (L "7/3" 3 60).1 == ofAzRat ref73 60
-- a large base
private def ref1000 : AzRat :=
  Q ("332192809488736234787031942948939017586483139302458061205/1" ++ "".pushn '0' 59)
#guard (L "10" 1000 100).1 == ofAzRat ref1000 100

-- nearest at precision `p`
#guard logBasePow2Rat (Q "256") (K 4) 10 == F "2" 10
#guard logBasePow2Rat (Q "10") (K 1) 53 == log2Rat (Q "10") 53
