/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Pow
import Azurite.AzFloat.Pow2
import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseM1
import Azurite.AzFloat.PowBaseM1Rat
import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `x^y`

The special values of IEEE 754 (Malachite's table, without negative zero), the exact dyadic
powers (`4^(1/2) = 2`, `4^(3/2) = 8`, `(9/4)^(3/2) = 27/8`, `(1/4)^(−1/2) = 2`, `16^(1/4) = 2`,
`(3/2)^10`, `(−3/2)^3 = −27/8`), the integer powers through the bracket (`3^40`, `(−3)^41`,
`3^(−40)` at 20 bits), the correctly rounded `2^(1/2)` (against `√2`), `(3/2)^(5/4)`,
`10^(−1/8)`, `(123456789/1024)^(77/64)`, `3^(7/4)` (against `powBase`), `(1/3)^(1/3)` at 200 bits
(references from an 80-digit evaluation of `exp (y ln x)`), the directed modes, and agreement with
`pow2` and `powBase`.  The natural-base powers `powBase`, `powBaseRat`, `powBaseM1`,
`powBaseM1Rat` share the cheapness test, so `3^(10^9)` (and `3^(10^9) − 1`) at 10 bits are
computed through the bracket in milliseconds instead of forming the exact power; `(−1)^y` and
`(−∞)^y` for `y = ±2^(2^30)` and `y = 3 · 2^(2^30)` take the parity from the exponent.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 200 bits. -/
private def third200 : AzFloat :=
  X "0.3333333333333333333333333333333333333333333333333333333333334" 200
private def P (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := powPrecRound x y p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `x^0 = 1` and `1^y = 1`, even for `NaN`
#guard D (P nan zero 53) == ("1.0", .eq)
#guard D (P pinf zero 53) == ("1.0", .eq)
#guard D (P (X "-2.3333333333333335" 53) zero 53) == ("1.0", .eq)
#guard D (P (X "1" 53) nan 53) == ("1.0", .eq)
#guard D (P (X "1" 53) pinf 53) == ("1.0", .eq)
#guard D (P (X "1" 53) (X "-2.5" 53) 53) == ("1.0", .eq)
-- `NaN` otherwise
#guard D (P nan (X "2" 53) 53) == ("NaN", .eq)
#guard D (P (X "2" 53) nan 53) == ("NaN", .eq)
#guard D (P nan pinf 53) == ("NaN", .eq)
-- infinite exponents
#guard D (P (X "2" 53) pinf 53) == ("Infinity", .eq)
#guard D (P (X "0.5" 53) pinf 53) == ("0.0", .eq)
#guard D (P (X "2" 53) ninf 53) == ("0.0", .eq)
#guard D (P (X "0.5" 53) ninf 53) == ("Infinity", .eq)
#guard D (P (X "-3" 53) pinf 53) == ("Infinity", .eq)
#guard D (P (X "-0.3333333333333333" 53) ninf 53) == ("Infinity", .eq)
#guard D (P (X "-1" 53) pinf 53) == ("1.0", .eq)
#guard D (P (X "-1" 53) ninf 53) == ("1.0", .eq)
#guard D (P zero pinf 53) == ("0.0", .eq)
#guard D (P zero ninf 53) == ("Infinity", .eq)
#guard D (P pinf pinf 53) == ("Infinity", .eq)
#guard D (P pinf ninf 53) == ("0.0", .eq)
#guard D (P ninf pinf 53) == ("Infinity", .eq)
#guard D (P ninf ninf 53) == ("0.0", .eq)
-- `(−1)^y`
#guard D (P (X "-1" 53) (X "4" 53) 53) == ("1.0", .eq)
#guard D (P (X "-1" 53) (X "3" 53) 53) == ("-1.0", .eq)
#guard D (P (X "-1" 53) (X "0.5" 53) 53) == ("NaN", .eq)
-- infinite bases
#guard D (P pinf (X "2" 53) 53) == ("Infinity", .eq)
#guard D (P pinf (X "0.5" 53) 53) == ("Infinity", .eq)
#guard D (P pinf (X "-2" 53) 53) == ("0.0", .eq)
#guard D (P ninf (X "3" 53) 53) == ("-Infinity", .eq)
#guard D (P ninf (X "2" 53) 53) == ("Infinity", .eq)
#guard D (P ninf (X "0.5" 53) 53) == ("Infinity", .eq)
#guard D (P ninf (X "-3" 53) 53) == ("0.0", .eq)
#guard D (P ninf (X "-2" 53) 53) == ("0.0", .eq)
-- zero bases
#guard D (P zero (X "2" 53) 53) == ("0.0", .eq)
#guard D (P zero (X "0.5" 53) 53) == ("0.0", .eq)
#guard D (P zero (X "-2" 53) 53) == ("Infinity", .eq)
#guard D (P zero (X "-3" 53) 53) == ("Infinity", .eq)
-- negative base, non-integer exponent
#guard D (P (X "-2" 53) (X "1.5" 53) 53) == ("NaN", .eq)
#guard D (P (X "-8" 53) (X "0.5" 53) 53) == ("NaN", .eq)
-- precision `0`
#guard D (P (X "2" 53) (X "3" 53) 0) == ("NaN", .eq)
#guard D (P (X "2" 53) zero 0) == ("NaN", .eq)
#guard D (P zero (X "3" 53) 0) == ("0.0", .eq)

-- exact dyadic powers
#guard D (P (X "4" 53) (X "0.5" 53) 53) == ("2.0", .eq)
#guard D (P (X "4" 53) (X "1.5" 53) 53) == ("8.0", .eq)
#guard D (P (X "2.25" 53) (X "1.5" 53) 53) == ("3.375", .eq)
#guard D (P (X "0.25" 53) (X "-0.5" 53) 53) == ("2.0", .eq)
#guard D (P (X "16" 53) (X "0.25" 53) 53) == ("2.0", .eq)
#guard D (P (X "16" 53) (X "-0.75" 53) 53) == ("0.125", .eq)
#guard D (P (X "1.5" 53) (X "10" 53) 53) == ("57.6650390625", .eq)
#guard D (P (X "-1.5" 53) (X "3" 53) 53) == ("-3.375", .eq)
#guard D (P (X "-1.5" 53) (X "-2" 53) 53) == ("0.4444444444444444", .lt)
#guard D (P (X "2" 53) (X "100" 53) 1) == ("1.0e30", .eq)
#guard D (P (X "2" 53) (X "-100" 53) 1) == ("8.0e-31", .eq)

-- integer powers through the bracket (`|n| (size m' − 1) > p + 1`)
#guard D (P (X "3" 20) (X "40" 20) 20) == ("1.215766e19", .lt)
#guard D (P (X "3" 20) (X "40" 20) 20 .Ceiling) == ("1.215768e19", .gt)
#guard D (P (X "-3" 20) (X "41" 20) 20) == ("-3.6473e19", .lt)
#guard D (P (X "-3" 20) (X "41" 20) 20 .Ceiling) == ("-3.647296e19", .gt)
#guard D (P (X "3" 20) (X "-40" 20) 20) == ("8.22527e-20", .gt)
#guard D (P (X "3" 20) (X "-40" 20) 20 .Floor) == ("8.22526e-20", .lt)
#guard P (X "3" 20) (X "40" 20) 20 == powIntPrecRound (X "3" 20) (AzInt.ofInt 40) 20 .Nearest
#guard P (X "-3" 20) (X "41" 20) 20 == powIntPrecRound (X "-3" 20) (AzInt.ofInt 41) 20 .Nearest

-- correctly rounded irrational powers
#guard P (X "2" 53) (X "0.5" 53) 53 == sqrt2PrecRound 53 .Nearest
#guard P (X "2" 53) (X "0.5" 53) 53 .Floor == sqrt2PrecRound 53 .Floor
#guard P (X "2" 53) (X "0.5" 53) 53 .Ceiling == sqrt2PrecRound 53 .Ceiling
#guard D (P (X "1.5" 53) (X "1.25" 53) 53) == ("1.6600228795504823", .lt)
#guard D (P (X "1.5" 53) (X "1.25" 53) 53 .Ceiling) == ("1.6600228795504826", .gt)
#guard D (P (X "10" 53) (X "-0.125" 53) 53) == ("0.7498942093324559", .gt)
#guard D (P (X "10" 53) (X "-0.125" 53) 53 .Floor) == ("0.7498942093324558", .lt)
#guard D (P (X "120563.2705078125" 53) (X "1.203125" 53) 53) == ("1298185.7019993423", .gt)
#guard D (P (X "120563.2705078125" 53) (X "1.203125" 53) 53 .Floor) == ("1298185.701999342", .lt)
#guard D (P (X "3" 53) (X "1.75" 53) 53) == ("6.8385211708643325", .lt)
#guard P (X "3" 53) (X "1.75" 53) 53 == powBasePrecRound 3 (X "1.75" 53) 53 .Nearest
#guard P (X "2" 53) (X "1.75" 53) 53 == pow2PrecRound (X "1.75" 53) 53 .Nearest
#guard P (X "2" 53) (X "-2.75" 53) 53 .Floor == pow2PrecRound (X "-2.75" 53) 53 .Floor
#guard toString (pow third200 third200)
  == "0.693361274350634704843352274785961795445935113457754036565864"
#guard D (P third200 third200 200 .Floor) ==
  ("0.693361274350634704843352274785961795445935113457754036565863", .lt)
#guard toString (pow (X "1.5" 53) (X "1.25" 53)) == "1.6600228795504823"

-- the natural-base powers on huge exponents: the bracket path, in agreement with `pow`
#guard powBasePrecRound 3 (X "1000000000" 53) 10 .Nearest
  == P (X "3" 53) (X "1000000000" 53) 10
#guard powBaseRatPrecRound 3 (Q "1000000000") 10 .Nearest == P (X "3" 53) (X "1000000000" 53) 10
#guard powBasePrecRound 3 (X "-1000000000" 53) 10 .Floor
  == P (X "3" 53) (X "-1000000000" 53) 10 .Floor
#guard (powBaseM1PrecRound 3 (X "1000000000" 53) 10 .Nearest).1
  == (P (X "3" 53) (X "1000000000" 53) 10).1
#guard (powBaseM1RatPrecRound 3 (Q "1000000000") 10 .Nearest).1
  == (P (X "3" 53) (X "1000000000" 53) 10).1
#guard D (powBaseM1PrecRound 3 (X "-1000000000" 53) 10 .Nearest) == ("-1.0", .lt)
#guard D (powBaseM1PrecRound 3 (X "40" 20) 20 .Nearest) == ("1.215766e19", .lt)
#guard D (powBaseM1RatPrecRound 3 (Q "40") 20 .Nearest) == ("1.215766e19", .lt)
#guard D (powBaseM1PrecRound 3 (X "-40" 20) 20 .Nearest) == ("-1.0", .lt)
#guard (powBasePrecRound 10 (X "1000000" 53) 53 .Nearest).1 == (P (X "10" 53) (X "1000000" 53) 53).1

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (powPrecRound (X "3" 53) tinyX 53 .Nearest) == ("1.0", .lt)
#guard D (powPrecRound (X "3" 53) tinyX 53 .Floor) == ("1.0", .lt)
#guard D (powPrecRound (X "3" 53) tinyX 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (powPrecRound (X "3" 53) (-tinyX) 53 .Nearest) == ("1.0", .gt)
#guard D (powPrecRound (X "3" 53) (-tinyX) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (powPrecRound (X "3" 53) (-tinyX) 53 .Ceiling) == ("1.0", .gt)
-- a base below `1` reverses the side
#guard D (powPrecRound (X "0.3333333333333333" 53) tinyX 53 .Nearest) == ("1.0", .gt)
#guard D (powPrecRound (X "0.3333333333333333" 53) (-tinyX) 53 .Ceiling)
  == ("1.0000000000000002", .gt)
-- a huge or a tiny base: `(3·2^(±2N))^(1/2) = √3 · 2^(±N)`, `N = 2^29` (the starting precision
-- is logarithmic in the exponent of the base)
private def bigN : AzInt := AzInt.ofInt (2 ^ 29)
#guard powPrecRound ((X "3" 53) <<< AzInt.ofInt (2 ^ 30)) (X "0.5" 53) 53 .Nearest
  == ((powPrecRound (X "3" 53) (X "0.5" 53) 53 .Nearest).1 <<< bigN,
    (powPrecRound (X "3" 53) (X "0.5" 53) 53 .Nearest).2)
#guard powPrecRound ((X "3" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) (X "0.5" 53) 53 .Floor
  == ((powPrecRound (X "3" 53) (X "0.5" 53) 53 .Floor).1 <<< (-bigN),
    (powPrecRound (X "3" 53) (X "0.5" 53) 53 .Floor).2)

-- `(−1)^y` and `(−∞)^y` for a huge integer `y = ±2^(2^30)`: the parity from the exponent and the
-- trailing zeros, without converting `y` to an `AzInt`
private def hugeY (s : Bool) (k : Int) : AzFloat :=
  (X (if s then "1" else "-1") 1) <<< AzInt.ofInt k
#guard D (P (X "-1" 1) (hugeY true (2 ^ 30)) 10) == ("1.0", .eq)
#guard D (P (X "-1" 1) (hugeY false (2 ^ 30)) 10 .Floor) == ("1.0", .eq)
#guard D (P (X "-1" 1) ((X "3" 2) <<< AzInt.ofInt (2 ^ 30)) 10) == ("1.0", .eq)
#guard D (P (X "-1" 2) (X "-7" 3) 10 .Ceiling) == ("-1.0", .eq)
#guard D (P (infinity false) (hugeY true (2 ^ 30)) 10) == ("Infinity", .eq)
#guard D (P (infinity false) (X "7" 3) 10) == ("-Infinity", .eq)
