/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Log2P1
import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.LogBasePow2P1
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln

/-!
# Tests for `log_{2^k} (1 + x)`

Special values, exact cases `1 + x = 2^j` (value `j / k`), agreement with `log2P1` for `k = 1`
and with `log_{2^k}` on the exact `1 + x`, and
`log₁₆ (1 + 9) = 0.830482023721840586967579857372347543966207848256145153013…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (k : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePow2P1PrecRound x (K k) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L nan 4 10) == ("NaN", .eq)
#guard D (L one 0 10) == ("NaN", .eq)  -- base 1
#guard D (L (infinity true) 4 10) == ("Infinity", .eq)
#guard D (L (infinity true) (-4) 10) == ("-Infinity", .eq)
#guard D (L (infinity false) 4 10) == ("NaN", .eq)
#guard D (L zero 4 10) == ("0.0", .eq)
#guard D (L zero (-4) 10) == ("0.0", .eq)
#guard D (L (X "-1" 53) 4 10) == ("-Infinity", .eq)
#guard D (L (X "-1" 53) (-4) 10) == ("Infinity", .eq)
#guard D (L (X "-2" 53) 4 10) == ("NaN", .eq)
#guard D (L (X "-1.5" 53) 4 10) == ("NaN", .eq)
#guard D (L (X "8" 53) 4 0) == ("NaN", .eq)  -- precision 0

-- exact cases: `1 + x = 2^j` gives `j / k`, rounded once
#guard D (L (X "7" 53) 3 53) == ("1.0", .eq)
#guard D (L (X "3" 53) 4 53) == ("0.5", .eq)
#guard D (L (X "15" 53) 4 53) == ("1.0", .eq)
#guard D (L (X "15" 53) (-4) 53) == ("-1.0", .eq)
#guard D (L (X "-0.5" 53) 2 53) == ("-0.5", .eq)
#guard D (L (X "-0.75" 53) 4 53 .Ceiling) == ("-0.5", .eq)
#guard D (L (X "-0.875" 53) (-3) 53) == ("1.0", .eq)
#guard D (L (X "1" 53) 3 53) == ("0.3333333333333333", .lt)
#guard D (L (X "1" 53) 3 53 .Up) == ("0.33333333333333337", .gt)
#guard D (L (X "3" 53) 3 53 .Floor) == ("0.6666666666666666", .lt)
#guard D (L (X "-0.75" 53) 3 53) == ("-0.6666666666666666", .gt)
#guard D (L (X "1023" 53) 10 1) == ("1.0", .eq)
#guard D (L (X "1267650600228229401496703205375" 110) 10 110) == ("1.0e1", .eq)
#guard (L (X "0.5" 53) 4 53).2 != .eq                         -- 3/2 is not a power of two

-- `k = 1` agrees with `log2P1`
#guard L (X "10" 53) 1 53 == log2P1PrecRound (X "10" 53) 53 .Nearest
#guard L (X "-0.3333333333333333" 53) 1 20 .Floor
  == log2P1PrecRound (X "-0.3333333333333333" 53) 20 .Floor
#guard L (X "0.000000000931322574615478515625" 53) 1 100
  == log2P1PrecRound (X "0.000000000931322574615478515625" 53) 100 .Nearest

-- agreement with `log_{2^k}` on the exact `1 + x`
#guard L (X "9" 53) 4 150 == logBasePow2PrecRound (X "10" 53) (K 4) 150 .Nearest
#guard L (X "9" 53) 4 150 .Floor == logBasePow2PrecRound (X "10" 53) (K 4) 150 .Floor
#guard L (X "9" 53) (-4) 150 == logBasePow2PrecRound (X "10" 53) (K (-4)) 150 .Nearest
#guard L (X "-0.375" 53) 4 150 .Ceiling == logBasePow2PrecRound (X "0.625" 53) (K 4) 150 .Ceiling
#guard L (X "10" 53) (-1) 53 == logBasePow2PrecRound (X "11" 53) (K (-1)) 53 .Nearest
#guard L (X "2" 53) 1000 100 == logBasePow2PrecRound (X "3" 53) (K 1000) 100 .Nearest

-- `log₁₆ (1 + 9)`
private def ref16 : AzRat :=
  Q ("830482023721840586967579857372347543966207848256145153013/1"
    ++ "".pushn '0' 57)
#guard toString (L (X "9" 53) 4 150).1 == "0.830482023721840586967579857372347543966207848"
#guard toString (L (X "9" 53) 4 150 .Floor).1 == "0.830482023721840586967579857372347543966207848"
#guard toString (L (X "9" 53) (-4) 150).1 == "-0.830482023721840586967579857372347543966207848"
-- a tiny argument: `log₁₆ (1 + 2^(−30))` is not exact
#guard (L (X "0.000000000931322574615478515625" 53) 4 100).2 != .eq
#guard (L (X "-0.000000000931322574615478515625" 53) 4 100).2 != .eq

-- default precision
#guard toString (logBasePow2P1 (X "7" 10) (K 3)) == "1.0"
#guard logBasePow2P1 (X "10" 53) (K 1) == log2P1 (X "10" 53)
#guard toString (logBasePow2P1 (X "9" 53) (K 4)) == "0.8304820237218405"

-- precomputed constants: the same results
#guard logBasePow2P1With (LnConsts.forPrecision 53) (X "0.5" 53) (K 3)
  == logBasePow2P1 (X "0.5" 53) (K 3)
#guard logBasePow2P1With (LnConsts.forPrecision 53) (X "-0.5" 53) (K 2)
  == logBasePow2P1 (X "-0.5" 53) (K 2)

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
-- `log₁₆ (1 + x) ≈ x / (4 ln 2)`
#guard L tinyX 4 53
  == ((X "1.4426950408889634" 53) <<< (tinyE - AzInt.ofInt 2), .lt)

-- a huge power of two, `x = 2^K` with `K = 2^30 − 98`: `log₂ (1 + x) = K + ε`, `ε ≈ 2^(−K)`;
-- the side of `K` is decided without `K` bits of working precision
private def bigX : AzFloat := (X "1" 52) <<< AzInt.ofInt (2 ^ 30 - 98)
#guard D (L bigX 2 52) == ("536870863.0", .lt)
#guard D (L bigX (-2) 52) == ("-536870863.0", .gt)
#guard D (L bigX 1 52 .Floor) == ("1073741726.0", .lt)
#guard D (L bigX (-1) 52 .Floor) == ("-1073741726.0000002", .lt)
#guard (L bigX 3 52).2 != .eq
