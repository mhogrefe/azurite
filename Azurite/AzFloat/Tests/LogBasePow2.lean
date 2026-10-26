/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Log2
import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_{2^k}`

Exact cases, agreement with `log₂` for `k = ±1`, and `log₁₆ 10 = log₂ 10 / 4`,
`log₂ 10 = 3.32192809488736234787031942948939017586483139302458061205…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (k : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePow2PrecRound x (K k) p m

-- special values
#guard L nan 4 10 == (nan, .eq)
#guard L one 0 10 == (nan, .eq)                              -- base 1
#guard L (infinity true) 4 10 == (infinity true, .eq)
#guard L (infinity true) (-4) 10 == (infinity false, .eq)
#guard L (infinity false) 4 10 == (nan, .eq)
#guard L zero 4 10 == (infinity false, .eq)
#guard L zero (-4) 10 == (infinity true, .eq)
#guard L (F "-8" 53) 3 10 == (nan, .eq)

-- exact powers of two: `(e − 1) / k`, rounded once
#guard L (F "1" 53) 4 53 == (zero, .eq)
#guard L (F "16" 53) 4 53 == (F "1" 53, .eq)
#guard L (F "256" 53) 4 53 == (F "2" 53, .eq)
#guard L (F "2" 53) 4 53 == (F "1/4" 53, .eq)
#guard L (F "8" 53) 4 53 == (F "3/4" 53, .eq)
#guard L (F "8" 53) (-4) 53 == (F "-3/4" 53, .eq)
#guard L (F "1/8" 53) (-4) 53 == (F "3/4" 53, .eq)
#guard L (F "2" 53) 3 53 == ofAzRatRound (Q "1/3") 53 .Nearest  -- 1/3 rounded
#guard L (F "2" 53) 3 53 .Up == ofAzRatRound (Q "1/3") 53 .Up
#guard L (F "4" 53) 3 53 .Floor == ofAzRatRound (Q "2/3") 53 .Floor
#guard L (F "1024" 53) 10 1 == (F "1" 1, .eq)
#guard L (F "1024" 53) 1 53 == log2PrecRound (F "1024" 53) 53 .Nearest

-- `k = ±1` agrees with `log₂`
#guard L (F "10" 53) 1 53 == log2PrecRound (F "10" 53) 53 .Nearest
#guard L (F "3" 53) 1 20 .Floor == log2PrecRound (F "3" 53) 20 .Floor
#guard L (F "10" 53) (-1) 53 == (-(log2PrecRound (F "10" 53) 53 .Nearest).1, .gt)
#guard L (F "1/3" 53) (-1) 20 .Ceiling == log2PrecRound (F "3" 53) 20 .Ceiling

-- `log₁₆ 10 = 0.830482023721840586967579857372347543966207848256145153013…`
private def ref16 : AzRat :=
  Q ("830482023721840586967579857372347543966207848256145153013/1"
    ++ "".pushn '0' 57)
#guard (L (F "10" 53) 4 150).1 == ofAzRat ref16 150
#guard (L (F "10" 53) 4 150 .Floor).1 == (ofAzRatRound ref16 150 .Floor).1
#guard (L (F "10" 53) (-4) 150).1 == ofAzRat (-ref16) 150
-- `log₁₆ (5/8) = (log₂ 10 − 4) / 4`
private def ref58 : AzRat :=
  Q ("-13561438102252753042593611410212196482703372139508387759/8" ++ "".pushn '0' 55)
#guard (L (F "5/8" 53) 4 150).1 == ofAzRat ref58 150
#guard (L (F "10" 53) 4 150).2 == .lt ∨ (L (F "10" 53) 4 150).2 == .gt
-- `log_{2^1000} 10`: a large base
private def ref1000 : AzRat :=
  Q ("332192809488736234787031942948939017586483139302458061205/1" ++ "".pushn '0' 59)
#guard (L (F "10" 53) 1000 100).1 == ofAzRat ref1000 100

-- default precision
#guard logBasePow2 (F "256" 10) (K 4) == F "2" 10
#guard logBasePow2 (F "10" 53) (K 1) == log2 (F "10" 53)
