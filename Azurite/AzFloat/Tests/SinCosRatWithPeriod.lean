/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosRatWithPeriod
import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.CosWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinCosRatWithPeriod`

The special values (`u = 0`, `q = 0`, `p = 0`), the exact values in degrees (the delegated
denominators), `45°` (`sin = cos = √2/2`), `1/3°` at 200 bits against the float function at the
exact argument `1°` with period `1080`, and the agreement with `sinRatWithPeriodPrecRound` and
`cosRatWithPeriodPrecRound` over every third of a degree of a turn, both signs, several
periods, modes and precisions, a huge numerator and denominator, and a tiny rational
(delegated).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def SC (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinCosRatWithPeriodPrecRound (Q q) u p m
private def agrees (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosRatWithPeriodPrecRound (Q q) u p m
    == (sinRatWithPeriodPrecRound (Q q) u p m, cosRatWithPeriodPrecRound (Q q) u p m)
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A pair of results as decimal output. -/
private def D2 (r : (AzFloat × Ordering) × (AzFloat × Ordering)) :
    (String × Ordering) × (String × Ordering) := (D r.1, D r.2)

-- special values
#guard D2 (SC "1/3" 0 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC "0" 360 53) == (("0.0", .eq), ("1.0", .eq))
#guard D2 (SC "0" 360 0) == (("0.0", .eq), ("NaN", .eq))
#guard D2 (SC "1/3" 360 0) == (("NaN", .eq), ("NaN", .eq))

-- exact values
#guard D (SC "30" 360 53).1 == ("0.5", .eq)
#guard D (SC "60" 360 53).2 == ("0.5", .eq)
#guard D2 (SC "90" 360 53) == (("1.0", .eq), ("0.0", .eq))
#guard D2 (SC "-90" 360 53) == (("-1.0", .eq), ("0.0", .eq))
#guard D2 (SC "1/2" 1 53) == (("0.0", .eq), ("-1.0", .eq))
#guard D (SC "1/12" 1 53).1 == ("0.5", .eq)
#guard D (SC "-5/12" 1 53).1 == ("-0.5", .eq)
#guard D (SC "1/3" 1 53).2 == ("-0.5", .eq)

-- `45°`, and `1/3°` against the float function at `1` with period `1080`
#guard D (SC "45" 360 53).1 == ("0.7071067811865476", .gt)
#guard (SC "1/8" 1 53).1 == (SC "1/8" 1 53).2
#guard SC "1/3" 360 200 == (sinWithPeriodPrecRound (X "1" 200) 1080 200 .Nearest,
  cosWithPeriodPrecRound (X "1" 200) 1080 200 .Nearest)
#guard sinCosRatWithPeriod (Q "1/3") 360 53
  == (sinWithPeriod (X "1" 53) 1080, cosWithPeriod (X "1" 53) 1080)

-- agreement with the separate functions
#guard (List.range 1081).all fun i => agrees s!"{i}/3" 360 53
#guard (List.range 400).all fun i => agrees s!"-{i + 1}/7" 360 53 .Floor
#guard (List.range 60).all fun i => agrees s!"{i + 1}/11" 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees s!"-{2 * i + 1}/13" 1 40 .Down
#guard (List.range 60).all fun i => agrees s!"{2 * i + 1}/5" 400 100 .Up
#guard agrees "1/7" 360 1
#guard agrees "1/7" 18446744073709551615 53
#guard agrees "12345678901234567890123456789/1000000007" 360 300
#guard agrees "1/7" 360 2000
#guard agrees ("314159265358979323846264338327950288419716939937510/"
  ++ "100000000000000000000000000000000000000000000000001") 2 64

-- tiny rationals (delegated) and a small one on the ordinary path
#guard agrees "1/1267650600228229401496703205376" 360 20
#guard agrees "-1/1267650600228229401496703205376" 360 20 .Floor
#guard agrees "1/1099511627776" 360 53
