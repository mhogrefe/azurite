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
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln

/-!
# Tests for `log_{2^k}`

Exact cases, agreement with `log₂` for `k = ±1`, and `log₁₆ 10 = log₂ 10 / 4`,
`log₂ 10 = 3.32192809488736234787031942948939017586483139302458061205…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (k : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePow2PrecRound x (K k) p m

-- special values
#guard D (L nan 4 10) == ("NaN", .eq)
#guard D (L one 0 10) == ("NaN", .eq)  -- base 1
#guard D (L (infinity true) 4 10) == ("Infinity", .eq)
#guard D (L (infinity true) (-4) 10) == ("-Infinity", .eq)
#guard D (L (infinity false) 4 10) == ("NaN", .eq)
#guard D (L zero 4 10) == ("-Infinity", .eq)
#guard D (L zero (-4) 10) == ("Infinity", .eq)
#guard D (L (X "-8" 53) 3 10) == ("NaN", .eq)

-- exact powers of two: `(e − 1) / k`, rounded once
#guard D (L (X "1" 53) 4 53) == ("0.0", .eq)
#guard D (L (X "16" 53) 4 53) == ("1.0", .eq)
#guard D (L (X "256" 53) 4 53) == ("2.0", .eq)
#guard D (L (X "2" 53) 4 53) == ("0.25", .eq)
#guard D (L (X "8" 53) 4 53) == ("0.75", .eq)
#guard D (L (X "8" 53) (-4) 53) == ("-0.75", .eq)
#guard D (L (X "0.125" 53) (-4) 53) == ("0.75", .eq)
#guard D (L (X "2" 53) 3 53) == ("0.3333333333333333", .lt)  -- 1/3 rounded
#guard D (L (X "2" 53) 3 53 .Up) == ("0.33333333333333337", .gt)
#guard D (L (X "4" 53) 3 53 .Floor) == ("0.6666666666666666", .lt)
#guard D (L (X "1024" 53) 10 1) == ("1.0", .eq)
#guard L (X "1024" 53) 1 53 == log2PrecRound (X "1024" 53) 53 .Nearest

-- `k = ±1` agrees with `log₂`
#guard L (X "10" 53) 1 53 == log2PrecRound (X "10" 53) 53 .Nearest
#guard L (X "3" 53) 1 20 .Floor == log2PrecRound (X "3" 53) 20 .Floor
#guard L (X "10" 53) (-1) 53 == (-(log2PrecRound (X "10" 53) 53 .Nearest).1, .gt)
#guard L (X "0.3333333333333333" 53) (-1) 20 .Ceiling == log2PrecRound (X "3" 53) 20 .Ceiling

-- `log₁₆ 10 = 0.830482023721840586967579857372347543966207848256145153013…`
private def ref16 : AzRat :=
  Q ("830482023721840586967579857372347543966207848256145153013/1"
    ++ "".pushn '0' 57)
#guard toString ((L (X "10" 53) 4 150).1) == "0.830482023721840586967579857372347543966207848"
#guard toString ((L (X "10" 53) 4 150 .Floor).1)
  == "0.830482023721840586967579857372347543966207848"
#guard toString ((L (X "10" 53) (-4) 150).1) == "-0.830482023721840586967579857372347543966207848"
-- `log₁₆ (5/8) = (log₂ 10 − 4) / 4`
private def ref58 : AzRat :=
  Q ("-13561438102252753042593611410212196482703372139508387759/8" ++ "".pushn '0' 55)
#guard toString ((L (X "0.625" 53) 4 150).1) == "-0.1695179762781594130324201426276524560337921517"
#guard (L (X "10" 53) 4 150).2 == .lt ∨ (L (X "10" 53) 4 150).2 == .gt
-- `log_{2^1000} 10`: a large base
private def ref1000 : AzRat :=
  Q ("332192809488736234787031942948939017586483139302458061205/1" ++ "".pushn '0' 59)
#guard toString ((L (X "10" 53) 1000 100).1) == "0.00332192809488736234787031942949"

-- default precision
#guard toString (logBasePow2 (X "256" 10) (K 4)) == "2.0"
#guard logBasePow2 (X "10" 53) (K 1) == log2 (X "10" 53)

-- precomputed constants: the same results
#guard logBasePow2With (LnConsts.forPrecision 53) (X "10" 53) (K 3) == logBasePow2 (X "10" 53) (K 3)
#guard logBasePow2With (LnConsts.forPrecision 53) (X "10" 53) (K (-2))
  == logBasePow2 (X "10" 53) (K (-2))
#guard logBasePow2With (LnConsts.forPrecision 53) (X "8" 53) (K 3) == logBasePow2 (X "8" 53) (K 3)
#guard logBasePow2With (LnConsts.forPrecision 53) (X "10" 53) (K 0) == logBasePow2 (X "10" 53) (K 0)
