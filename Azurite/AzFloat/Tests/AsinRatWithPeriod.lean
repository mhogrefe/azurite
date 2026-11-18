/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin (q) u / (2π)` of a rational

The special values (`0`; `|q| > 1` gives `NaN`, also for `u = 0`; `u = 0`; `±u/4` at `±1`;
`±u/12` at `±1/2`, also for an unreduced input, exact or correctly rounded; `p = 0`), the
correctly rounded 53-bit values in degrees at exact rationals, other periods, agreement with the
float function at representable arguments, the directed modes, 20- and 113-bit results, a
200-bit string, and the tiny argument `±1/(3·2^1000)`.  References: an independent 1400-bit
fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinRatWithPeriodPrecRound (Q q) u p m

-- special values
#guard D (R "0" 360 53) == ("0.0", .eq)
#guard D (R "0" 360 0) == ("0.0", .eq)
#guard D (R "3/2" 360 53) == ("NaN", .eq)
#guard D (R "-22/7" 0 53) == ("NaN", .eq)
#guard D (R "1/3" 0 53) == ("0.0", .eq)
#guard D (R "-1" 0 53) == ("0.0", .eq)
#guard D (R "1/3" 360 0) == ("NaN", .eq)
#guard D (R "1" 360 53) == ("9.0e1", .eq)
#guard D (R "-1" 360 53) == ("-9.0e1", .eq)
#guard D (R "1" 7 1) == ("2.0", .gt)
#guard D (R "1/2" 360 53) == ("3.0e1", .eq)
#guard D (R "-3/6" 360 53) == ("-3.0e1", .eq)
#guard D (R "1/2" 7 53) == ("0.5833333333333334", .gt)
#guard D (R "-1/2" 7 53 .Ceiling) == ("-0.5833333333333333", .gt)
#guard D (R "1/2" 1 53 .Ceiling) == ("0.08333333333333334", .gt)

-- correctly rounded values at exact rationals
#guard D (R "1/3" 360 53) == ("19.47122063449069", .gt)
#guard D (R "-7/10" 360 53) == ("-44.4270040008057", .gt)
#guard D (R "3/4" 360 53) == ("48.590377890729144", .gt)
#guard D (R "-22/23" 360 53) == ("-73.04257370582768", .gt)
#guard D (R "999999/1000000" 360 53) == ("89.91897152479349", .gt)
#guard D (R "1/1000000007" 360 53) == ("5.7295779112011867e-8", .lt)
#guard D (R "355/452" 360 53) == ("51.757524689159325", .gt)
#guard D (R "1/3" 1 53) == ("0.05408672398469636", .lt)
#guard D (R "1/3" 7 53) == ("0.37860706789287457", .gt)
#guard D (R "1/3" 400 53) == ("21.634689593878544", .lt)
#guard D (R "1/3" 360 53 .Floor) == ("19.471220634490688", .lt)
#guard D (R "1/3" 360 53 .Ceiling) == ("19.47122063449069", .gt)
#guard D (R "1/3" 360 20) == ("19.47122", .gt)
#guard D (R "1/3" 360 113) == ("19.471220634490691369245999339962437", .gt)

-- agreement with the float function at representable arguments
#guard R "3/4" 360 53 == asinWithPeriodPrecRound (X "0.75" 53) 360 53 .Nearest
#guard R "-1/1024" 7 53 .Floor == asinWithPeriodPrecRound (X "-0.0009765625" 53) 7 53 .Floor
#guard asinRatWithPeriod (Q "1/3") 360 53 == (R "1/3" 360 53).1
#guard toString (asinRatWithPeriod (Q "1/3") 360 200)
  == "19.4712206344906913692459993399624359630068431009079482881711"

-- tiny arguments (`±1/(3·2^1000)`)
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard D (asinRatWithPeriodPrecRound tinyQ 360 53 .Nearest) == ("1.7824022171113933e-300", .lt)
#guard (asinRatWithPeriodPrecRound (-tinyQ) 360 53 .Floor).2 == .lt
