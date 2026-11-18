/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriod
import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `atan2 (y, x) u / (2π)`

The whole table of special values in degrees (`NaN`; `±45`, `±135`, `±90` for `y = ±∞`; `0` and
`±180` for `x = ±∞`; `y = 0`; `x = 0`; the diagonals `|y| = |x|`, also at unequal precisions;
`u = 0`; `p = 0`), with roundings of the rational values that do not fit; the correctly rounded
53-bit values in all eight octants, at inexact and very unequal arguments; other periods (`1`,
`7`, `400`, `2^64 − 1`); agreement with `atanWithPeriod` for `x = 1`; the directed modes; 1-,
20- and 113-bit results; a 200-bit string; and extreme ratios (`2⁻²⁰⁰`, `2^(±2^30)`).
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def D (y x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2WithPeriodPrecRound y x u p m
private def inf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def one' : AzFloat := X "1" 53
/-- A result as its decimal output and its comparison tag. -/
private def Dd (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `NaN`
#guard Dd (D nan one' 360 53) == ("NaN", .eq)
#guard Dd (D one' nan 360 53) == ("NaN", .eq)
#guard Dd (D inf nan 360 53) == ("NaN", .eq)
#guard Dd (D nan zero 0 53) == ("NaN", .eq)
-- `y = ±∞`
#guard Dd (D inf inf 360 53) == ("45.0", .eq)
#guard Dd (D ninf inf 360 53) == ("-45.0", .eq)
#guard Dd (D inf ninf 360 53) == ("135.0", .eq)
#guard Dd (D ninf ninf 360 53) == ("-135.0", .eq)
#guard Dd (D inf (X "5" 53) 360 53) == ("9.0e1", .eq)
#guard Dd (D ninf zero 360 53) == ("-9.0e1", .eq)
#guard Dd (D inf ninf 7 2) == ("3.0", .gt)
#guard Dd (D ninf ninf 7 2 .Ceiling) == ("-2.0", .gt)
#guard Dd (D inf ninf 1 53) == ("0.375", .eq)
-- `x = ±∞`, finite `y`
#guard Dd (D (X "5" 53) inf 360 53) == ("0.0", .eq)
#guard Dd (D (X "-5" 53) inf 360 53) == ("0.0", .eq)
#guard Dd (D zero inf 360 53) == ("0.0", .eq)
#guard Dd (D (X "5" 53) ninf 360 53) == ("1.8e2", .eq)
#guard Dd (D (X "-5" 53) ninf 360 53) == ("-1.8e2", .eq)
#guard Dd (D zero ninf 360 53) == ("1.8e2", .eq)
-- `y = 0`, `x = 0`
#guard Dd (D zero zero 360 53) == ("0.0", .eq)
#guard Dd (D zero (X "3" 53) 360 53) == ("0.0", .eq)
#guard Dd (D zero (X "-3" 53) 360 53) == ("1.8e2", .eq)
#guard Dd (D (X "2" 53) zero 360 53) == ("9.0e1", .eq)
#guard Dd (D (X "-2" 53) zero 360 53) == ("-9.0e1", .eq)
#guard Dd (D (X "-2" 53) zero 1 53) == ("-0.25", .eq)
-- the diagonals
#guard Dd (D (X "3" 53) (X "3" 53) 360 53) == ("45.0", .eq)
#guard Dd (D (X "-3" 53) (X "3" 53) 360 53) == ("-45.0", .eq)
#guard Dd (D (X "3" 53) (X "-3" 53) 360 53) == ("135.0", .eq)
#guard Dd (D (X "-3" 53) (X "-3" 53) 360 53) == ("-135.0", .eq)
#guard Dd (D (X "0.3333333333333333" 53) (X "0.3333333333333333" 53) 360 53) == ("45.0", .eq)
#guard Dd (D (X "3" 200) (X "-3" 53) 360 2) == ("1.3e2", .lt)
#guard Dd (D (X "3" 53) (X "-3" 53) 360 2 .Ceiling) == ("2.0e2", .gt)
-- `u = 0`, `p = 0`
#guard Dd (D one' (X "2" 53) 0 53) == ("0.0", .eq)
#guard Dd (D inf ninf 0 53) == ("0.0", .eq)
#guard Dd (D (X "-5" 53) ninf 0 53) == ("0.0", .eq)
#guard Dd (D (X "3" 53) (X "3" 53) 0 53) == ("0.0", .eq)
#guard Dd (D one' (X "2" 53) 360 0) == ("NaN", .eq)

-- correctly rounded values
#guard Dd (D (X "1" 53) (X "2" 53) 360 53) == ("26.56505117707799", .gt)
#guard Dd (D (X "2" 53) (X "1" 53) 360 53) == ("63.43494882292201", .lt)
#guard Dd (D (X "1" 53) (X "-2" 53) 360 53) == ("153.43494882292202", .gt)
#guard Dd (D (X "2" 53) (X "-1" 53) 360 53) == ("116.56505117707799", .gt)
#guard Dd (D (X "-1" 53) (X "2" 53) 360 53) == ("-26.56505117707799", .lt)
#guard Dd (D (X "-2" 53) (X "1" 53) 360 53) == ("-63.43494882292201", .gt)
#guard Dd (D (X "-1" 53) (X "-2" 53) 360 53) == ("-153.43494882292202", .lt)
#guard Dd (D (X "-2" 53) (X "-1" 53) 360 53) == ("-116.56505117707799", .lt)
#guard Dd (D (X "0.3333333333333333" 53) (X "1.4" 53) 360 53) == ("13.392497753751098", .lt)
#guard Dd (D (X "-1.4" 53) (X "0.3333333333333333" 53) 360 53) == ("-76.6075022462489", .gt)
#guard Dd (D (X "3.142857142857143" 53) (X "-0.001" 53) 360 53) == ("90.0182304746844", .lt)
#guard Dd (D (X "0.001" 53) (X "-3.142857142857143" 53) 360 53) == ("179.9817695253156", .gt)
#guard Dd (D (X "1000000000000" 53) (X "3" 53) 360 53) == ("89.99999999982812", .gt)
#guard Dd (D (X "3" 53) (X "-1000000000000" 53) 360 53) == ("179.9999999998281", .lt)
#guard Dd (D (X "1" 53) (X "2" 53) 1 53) == ("0.07379180882521663", .lt)
#guard Dd (D (X "1" 53) (X "-2" 53) 400 53) == ("170.48327646991333", .lt)
#guard Dd (D (X "-2" 53) (X "1" 53) 7 53) == ("-1.2334573382234835", .gt)
#guard Dd (D (X "2" 53) (X "-1" 53) 18446744073709551615 53) == ("5.972904630562261e18", .lt)
#guard Dd (D (X "1" 53) (X "2" 53) 360 53 .Floor) == ("26.565051177077986", .lt)
#guard Dd (D (X "-2" 53) (X "-1" 53) 360 53 .Floor) == ("-116.56505117707799", .lt)
#guard Dd (D (X "2" 53) (X "-1" 53) 360 53 .Floor) == ("116.56505117707798", .lt)
#guard Dd (D (X "1" 53) (X "2" 53) 360 53 .Ceiling) == ("26.56505117707799", .gt)
#guard Dd (D (X "-2" 53) (X "-1" 53) 360 53 .Ceiling) == ("-116.56505117707798", .gt)
#guard Dd (D (X "2" 53) (X "-1" 53) 360 53 .Ceiling) == ("116.56505117707799", .gt)
#guard Dd (D (X "1" 53) (X "2" 53) 360 20) == ("26.56506", .gt)
#guard Dd (D (X "1" 53) (X "-2" 53) 360 1) == ("1.0e2", .lt)
#guard Dd (D (X "-2" 53) (X "1" 53) 360 113) == ("-63.434948822922010648427806279546704", .gt)

-- agreement with `atanWithPeriod` for `x = 1`
#guard D (X "0.3333333333333333\
  " 53) one' 360 53 == atanWithPeriodPrecRound (X "0.3333333333333333" 53) 360 53 .Nearest
#guard D (X "-3.142857142857143\
  " 53) one' 7 53 .Floor == atanWithPeriodPrecRound (X "-3.142857142857143" 53) 7 53 .Floor
#guard atan2WithPeriod (X "1" 53) (X "2" 53) 360 == (D (X "1" 53) (X "2" 53) 360 53).1
#guard toString (atan2WithPeriodPrecRound (X "1" 200) (X "-2" 200) 360 200 .Nearest).1
  == "153.434948822922010648427806279546705328795785700354778972014"

-- extreme ratios
private def t : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard Dd (D t one' 360 53) == ("3.565525112668747e-59", .gt)
#guard Dd (D one' t 360 53) == ("9.0e1", .gt)
#guard Dd (D one' t 360 53 .Floor) == ("89.99999999999999", .lt)
#guard Dd (D t (-one') 360 53) == ("1.8e2", .gt)
#guard Dd (D t (-one') 360 53 .Floor) == ("179.99999999999997", .lt)
#guard Dd (D (-t) (-one') 360 53) == ("-1.8e2", .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard (D tiny one' 360 53).1
  == (X "57.29577951308232" 53) <<< AzInt.ofInt (-1073741824)
#guard (D tiny one' 360 53).2 == .gt
#guard (D (-tiny) huge 360 53 .Floor).2 == .lt
#guard Dd (D huge tiny 360 53) == ("9.0e1", .gt)
#guard Dd (D tiny (-huge) 360 53) == ("1.8e2", .gt)
#guard Dd (D (-huge) (-tiny) 360 53) == ("-9.0e1", .gt)
#guard Dd (D (-huge) tiny 360 53) == ("-9.0e1", .lt)
#guard (D huge tiny 360 53 .Floor).2 == .lt
