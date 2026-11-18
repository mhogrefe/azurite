/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arctan (x) u / (2π)`

The special values (`NaN`; a quarter turn `±u/4` at `±∞`; `0` at `x = 0` and for `u = 0`; an
eighth of a turn `±u/8` at `x = ±1`, exact when the precision holds it and rounded otherwise;
`p = 0`), the correctly rounded 53-bit values in degrees (`u = 360`) at `1/2`, `3`, `−1000`,
the floats nearest `1/3` and `−7/5`, `1/1024`, `10¹²`, other periods (`1`, `7`, `400`,
`2^64 − 1`), the directed modes, 1-, 20- and 113-bit results, 200-bit strings, a small
argument `2⁻⁴⁰`, the tiny arguments `2⁻²⁰⁰` and `±2^(−2^30)` (no cost in the exponent) and the
huge `2^1000` (just below a quarter turn).  References: an independent 1400-bit fixed-point
evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanWithPeriodPrecRound x u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("9.0e1", .eq)
#guard D (W (infinity false) 360 53) == ("-9.0e1", .eq)
#guard D (W (infinity true) 1 53) == ("0.25", .eq)
#guard D (W (infinity true) 7 1) == ("2.0", .gt)
#guard D (W (infinity false) 7 1 .Ceiling) == ("-1.0", .gt)
#guard D (W (infinity true) 0 53) == ("0.0", .eq)
#guard D (W (infinity false) 0 53) == ("0.0", .eq)
#guard D (W zero 360 53) == ("0.0", .eq)
#guard D (W zero 360 0) == ("0.0", .eq)
#guard D (W (X "3" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-1" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "3" 53) 360 0) == ("NaN", .eq)
-- an eighth of a turn
#guard D (W (X "1" 53) 360 53) == ("45.0", .eq)
#guard D (W (X "-1" 53) 360 53) == ("-45.0", .eq)
#guard D (W (X "1" 200) 1 53) == ("0.125", .eq)
#guard D (W (X "1" 53) 360 2) == ("5.0e1", .gt)
#guard D (W (X "1" 53) 360 2 .Floor) == ("3.0e1", .lt)
#guard D (W (X "-1" 53) 360 2 .Floor) == ("-5.0e1", .lt)
#guard D (W (X "1" 53) 18446744073709551615 53) == ("2.305843009213694e18", .gt)

-- correctly rounded values
#guard D (W (X "0.5" 53) 360 53) == ("26.56505117707799", .gt)
#guard D (W (X "3" 53) 360 53) == ("71.56505117707799", .gt)
#guard D (W (X "-1000" 53) 360 53) == ("-89.9427042395855", .gt)
#guard D (W (X "0.3333333333333333" 53) 360 53) == ("18.43494882292201", .gt)
#guard D (W (X "-1.4" 53) 360 53) == ("-54.46232220802562", .lt)
#guard D (W (X "0.0009765625" 53) 360 53) == ("0.05595289189380367", .lt)
#guard D (W (X "1000000000000" 53) 360 53) == ("89.9999999999427", .lt)
#guard D (W (X "0.5" 53) 1 53) == ("0.07379180882521663", .lt)
#guard D (W (X "0.5" 53) 400 53) == ("29.516723530086654", .lt)
#guard D (W (X "3" 53) 18446744073709551615 53) == ("3.667061621348567e18", .lt)
#guard D (W (X "-0.3333333333333333" 53) 7 53) == ("-0.3584573382234835", .lt)
#guard D (W (X "0.5" 53) 360 53 .Floor) == ("26.565051177077986", .lt)
#guard D (W (X "-3" 53) 360 53 .Floor) == ("-71.56505117707799", .lt)
#guard D (W (X "0.5" 53) 360 53 .Ceiling) == ("26.56505117707799", .gt)
#guard D (W (X "-3" 53) 360 53 .Ceiling) == ("-71.56505117707798", .gt)
#guard D (W (X "3" 53) 360 20) == ("71.5651", .gt)
#guard D (W (X "3" 53) 360 1) == ("6.0e1", .lt)
#guard D (W (X "0.5" 53) 360 113) == ("26.565051177077989351572193720453296", .gt)
#guard toString (atanWithPeriodPrecRound (X "0.5" 200) 360 200 .Nearest).1 == "26.56505117707798935\
  157219372045329467120421429964522102798602"
#guard toString (atanWithPeriodPrecRound (X "3" 200) 360 200 .Nearest).1 == "71.5650511770779893515\
  72193720453294671204214299645221027986"
#guard toString (atanWithPeriod (X "0.5" 53) 360) == "26.56505117707799"

-- small, tiny and huge arguments
#guard D (W (powerOf2 (AzInt.ofInt (-40))) 360 53) == ("5.211020790109826e-11", .gt)
#guard D (W (powerOf2 (AzInt.ofInt (-200))) 360 53) == ("3.565525112668747e-59", .gt)
#guard D (W (powerOf2 (AzInt.ofInt 1000)) 360 53) == ("9.0e1", .gt)
#guard D (W (powerOf2 (AzInt.ofInt 1000)) 360 53 .Floor) == ("89.99999999999999", .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard (W tiny 360 53).1 == (X "57.29577951308232" 53) <<< AzInt.ofInt (-1073741824)
#guard (W tiny 360 53).2 == .gt
#guard (W (-tiny) 360 53 .Floor).2 == .lt
-- a huge argument: within `2^(−2^30)` of a quarter turn, at no extra cost
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard D (W huge 360 53) == ("9.0e1", .gt)
#guard D (W huge 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (W (-huge) 360 53) == ("-9.0e1", .lt)
#guard D (W (-huge) 7 53 .Ceiling) == ("-1.7499999999999998", .gt)
