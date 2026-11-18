/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin (x) u / (2π)`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`, also for `u = 0`; `0`; `u = 0`; a
quarter turn `±u/4` at `±1`; a twelfth of a turn `±u/12` at `±1/2` — exact for `u = 360`, the
correctly rounded rational for `u = 7`, `1`, `10` in all modes; `p = 0`), the correctly rounded
53-bit values in degrees, other periods (`1`, `7`, `400`, `2^64 − 1`), the directed modes, 1-,
20- and 113-bit results, a 200-bit string, the neighbour `1 − 2^(−53)` of `1`, and tiny
arguments `2⁻²⁰⁰`, `±2^(−2^30)` (no cost in the exponent).  References: an independent 1400-bit
fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinWithPeriodPrecRound x u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("NaN", .eq)
#guard D (W (infinity false) 0 53) == ("NaN", .eq)
#guard D (W (X "2" 53) 360 53) == ("NaN", .eq)
#guard D (W (X "-1.5" 53) 0 53) == ("NaN", .eq)
#guard D (W zero 360 53) == ("0.0", .eq)
#guard D (W zero 360 0) == ("0.0", .eq)
#guard D (W (X "0.75" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-1" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "0.5" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "0.75" 53) 360 0) == ("NaN", .eq)
-- a quarter turn
#guard D (W (X "1" 53) 360 53) == ("9.0e1", .eq)
#guard D (W (X "-1" 200) 360 53) == ("-9.0e1", .eq)
#guard D (W (X "1" 53) 1 53) == ("0.25", .eq)
#guard D (W (X "1" 53) 7 1) == ("2.0", .gt)
#guard D (W (X "-1" 53) 7 1 .Ceiling) == ("-1.0", .gt)
-- a twelfth of a turn
#guard D (W (X "0.5" 53) 360 53) == ("3.0e1", .eq)
#guard D (W (X "-0.5" 200) 360 53) == ("-3.0e1", .eq)
#guard D (W (X "0.5" 53) 3 53) == ("0.25", .eq)
#guard D (W (X "0.5" 53) 7 53) == ("0.5833333333333334", .gt)
#guard D (W (X "0.5" 53) 7 53 .Floor) == ("0.5833333333333333", .lt)
#guard D (W (X "-0.5" 53) 7 53) == ("-0.5833333333333334", .lt)
#guard D (W (X "-0.5" 53) 7 53 .Ceiling) == ("-0.5833333333333333", .gt)
#guard D (W (X "0.5" 53) 1 53) == ("0.08333333333333333", .lt)
#guard D (W (X "0.5" 53) 1 53 .Ceiling) == ("0.08333333333333334", .gt)
#guard D (W (X "-0.5" 53) 10 53 .Floor) == ("-0.8333333333333334", .lt)

-- correctly rounded values
#guard D (W (X "0.3333333333333333" 53) 360 53) == ("19.47122063449069", .gt)
#guard D (W (X "-0.7" 53) 360 53) == ("-44.4270040008057", .lt)
#guard D (W (X "0.75" 53) 360 53) == ("48.590377890729144", .gt)
#guard D (W (X "0.9" 53) 360 53) == ("64.15806723683288", .gt)
#guard D (W (X "0.0009765625" 53) 360 53) == ("0.05595291857422375", .lt)
#guard D (W (X "0.999999" 53) 360 53) == ("89.91897152479233", .gt)
#guard D (W (X "0.7142857142857143" 53) 360 53) == ("45.584691402807024", .lt)
#guard D (W (X "0.75" 53) 1 53) == ("0.13497327191869204", .lt)
#guard D (W (X "0.75" 53) 7 53) == ("0.9448129034308445", .gt)
#guard D (W (X "0.75" 53) 400 53) == ("53.98930876747682", .lt)
#guard W (X "0.75" 53) 18446744073709551615 53 == (X "2489817403875320320" 53, .lt)
#guard D (W (X "0.75" 53) 360 53 .Floor) == ("48.59037789072914", .lt)
#guard D (W (X "-0.3333333333333333" 53) 360 53 .Floor) == ("-19.47122063449069", .lt)
#guard D (W (X "0.75" 53) 360 53 .Ceiling) == ("48.590377890729144", .gt)
#guard D (W (X "-0.3333333333333333" 53) 360 53 .Ceiling) == ("-19.471220634490688", .gt)
#guard D (W (X "0.75" 53) 360 20) == ("48.5904", .gt)
#guard D (W (X "0.75" 53) 360 1) == ("6.0e1", .gt)
#guard D (W (X "0.75" 53) 360 113) == ("48.59037789072914066151949781307428", .lt)
#guard asinWithPeriod (X "0.75" 53) 360 == (W (X "0.75" 53) 360 53).1
#guard toString (asinWithPeriodPrecRound (X "0.75" 200) 360 200 .Nearest).1
  == "48.59037789072914066151949781307427925821594885127146162994252"

-- next to `1`, small and tiny arguments
#guard D (W (X "0.9999999999999999" 53) 360 53) == ("89.99999914622636", .gt)
#guard D (W (powerOf2 (AzInt.ofInt (-200))) 360 53) == ("3.565525112668747e-59", .gt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard (W tiny 360 53).1 == (X "57.29577951308232" 53) <<< AzInt.ofInt (-1073741824)
#guard (W tiny 360 53).2 == .gt
#guard (W (-tiny) 360 53 .Floor).2 == .lt
