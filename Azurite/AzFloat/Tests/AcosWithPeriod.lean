/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccos (x) u / (2π)`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`, also for `u = 0`; `u/4` at `0`;
`u = 0`; `0` at `1`; `u/2` at `−1`; `u/6` at `1/2` and `u/3` at `−1/2` — exact for `u = 360`,
the correctly rounded rationals for `u = 7`, `1`, `2` in all modes; `p = 0`), the correctly
rounded 53-bit values in degrees, other periods (`1`, `7`, `400`, `2^64 − 1`), the directed
modes, 1-, 20- and 113-bit results, a 200-bit string, the neighbours `±(1 − 2^(−53))` of `±1`,
and tiny arguments `±2⁻²⁰⁰`, `±2^(−2^30)`: values next to the float `u/4`, at no extra cost.
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosWithPeriodPrecRound x u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("NaN", .eq)
#guard D (W (infinity false) 0 53) == ("NaN", .eq)
#guard D (W (X "2" 53) 360 53) == ("NaN", .eq)
#guard D (W (X "-1.5" 53) 0 53) == ("NaN", .eq)
#guard D (W (X "0.75" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-1" 53) 0 53) == ("0.0", .eq)
#guard D (W zero 0 53) == ("0.0", .eq)
#guard D (W (X "0.75" 53) 360 0) == ("NaN", .eq)
#guard D (W zero 360 53) == ("9.0e1", .eq)
#guard D (W zero 1 53) == ("0.25", .eq)
#guard D (W zero 7 53) == ("1.75", .eq)
#guard D (W zero 7 1) == ("2.0", .gt)
#guard D (W (X "1" 53) 360 53) == ("0.0", .eq)
#guard D (W (X "1" 200) 360 0) == ("0.0", .eq)
#guard D (W (X "-1" 53) 360 53) == ("1.8e2", .eq)
#guard D (W (X "-1" 53) 7 53) == ("3.5", .eq)
#guard D (W (X "-1" 53) 7 1) == ("4.0", .gt)
-- a sixth and a third of a turn
#guard D (W (X "0.5" 53) 360 53) == ("6.0e1", .eq)
#guard D (W (X "-0.5" 200) 360 53) == ("1.2e2", .eq)
#guard D (W (X "0.5" 53) 3 53) == ("0.5", .eq)
#guard D (W (X "0.5" 53) 7 53) == ("1.1666666666666667", .gt)
#guard D (W (X "0.5" 53) 7 53 .Floor) == ("1.1666666666666665", .lt)
#guard D (W (X "0.5" 53) 7 1) == ("1.0", .lt)
#guard D (W (X "0.5" 53) 7 3) == ("1.2", .gt)
#guard D (W (X "-0.5" 53) 7 53) == ("2.3333333333333335", .gt)
#guard D (W (X "-0.5" 53) 7 53 .Floor) == ("2.333333333333333", .lt)
#guard D (W (X "0.5" 53) 1 53) == ("0.16666666666666666", .lt)
#guard D (W (X "0.5" 53) 1 53 .Ceiling) == ("0.16666666666666669", .gt)
#guard D (W (X "-0.5" 53) 1 53) == ("0.3333333333333333", .lt)
#guard D (W (X "-0.5" 53) 2 53 .Ceiling) == ("0.6666666666666667", .gt)

-- correctly rounded values
#guard D (W (X "0.3333333333333333" 53) 360 53) == ("70.52877936550931", .lt)
#guard D (W (X "-0.3333333333333333" 53) 360 53) == ("109.47122063449069", .gt)
#guard D (W (X "-0.7" 53) 360 53) == ("134.4270040008057", .gt)
#guard D (W (X "0.75" 53) 360 53) == ("41.409622109270856", .lt)
#guard D (W (X "0.9" 53) 360 53) == ("25.841932763167126", .gt)
#guard D (W (X "0.0009765625" 53) 360 53) == ("89.94404708142578", .gt)
#guard D (W (X "-0.0009765625" 53) 360 53) == ("90.05595291857422", .lt)
#guard D (W (X "0.999999" 53) 360 53) == ("0.08102847520767845", .lt)
#guard D (W (X "-0.999999" 53) 360 53) == ("179.9189715247923", .lt)
#guard D (W (X "0.7142857142857143" 53) 360 53) == ("44.415308597192976", .gt)
#guard D (W (X "0.75" 53) 1 53) == ("0.11502672808130794", .lt)
#guard D (W (X "-0.25" 53) 1 53) == ("0.29021531162758313", .gt)
#guard D (W (X "0.75" 53) 7 53) == ("0.8051870965691555", .lt)
#guard D (W (X "-0.25" 53) 7 53) == ("2.031507181393082", .lt)
#guard D (W (X "0.75" 53) 400 53) == ("46.01069123252318", .gt)
#guard D (W (X "-0.25" 53) 400 53) == ("116.08612465103324", .lt)
#guard D (W (X "0.75" 53) 18446744073709551615 53) == ("2.1218686145520673e18", .lt)
#guard D (W (X "-0.25" 53) 18446744073709551615 53) == ("5.35352757986589e18", .gt)
#guard D (W (X "0.75" 53) 360 53 .Floor) == ("41.409622109270856", .lt)
#guard D (W (X "-0.25" 53) 360 53 .Floor) == ("104.47751218592991", .lt)
#guard D (W (X "0.75" 53) 360 53 .Ceiling) == ("41.40962210927086", .gt)
#guard D (W (X "-0.25" 53) 360 53 .Ceiling) == ("104.47751218592992", .gt)
#guard D (W (X "0.75" 53) 360 20) == ("41.4096", .lt)
#guard D (W (X "-0.25" 53) 360 1) == ("1.0e2", .gt)
#guard D (W (X "0.75" 53) 360 113) == ("41.40962210927085933848050218692572", .gt)
#guard acosWithPeriod (X "0.75" 53) 360 == (W (X "0.75" 53) 360 53).1
#guard toString (acosWithPeriodPrecRound (X "0.75" 200) 360 200 .Nearest).1 == "41.4096221092708593\
  3848050218692572074178405114872853837005748"

-- next to `±1`
#guard D (W (X "0.9999999999999999" 53) 360 53) == ("8.537736462515939e-7", .gt)
#guard D (W (X "-0.9999999999999999" 53) 360 53) == ("179.99999914622634", .lt)
#guard D (W (X "-0.9999999999999999" 53) 360 53 .Ceiling) ==
  ("179.99999914622637", .gt)

-- tiny arguments: next to the float `u/4`
private def t200 : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard D (W t200 360 53) == ("9.0e1", .gt)
#guard D (W t200 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (W (-t200) 360 53) == ("9.0e1", .lt)
#guard D (W (-t200) 360 53 .Ceiling) == ("90.00000000000001", .gt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard D (W tiny 360 53) == ("9.0e1", .gt)
#guard D (W tiny 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (W (-tiny) 360 53) == ("9.0e1", .lt)
#guard D (W (-tiny) 360 53 .Ceiling) == ("90.00000000000001", .gt)
#guard D (W (-tiny) 360 53 .Floor) == ("9.0e1", .lt)
