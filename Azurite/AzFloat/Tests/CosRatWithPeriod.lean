/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.CosWithPeriod
import Azurite.AzFloat.CosRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `cos (2π q / u)` of a rational `q`

The special values (`u = 0`, `p = 0`, `q = 0`), the exact rational values — including arguments
no float can hit, such as `1/3` of a turn (`−1/2`), `1/6` (`1/2`), `7/3` of `7`, `1001/7` of `13`
(`1`) and `45/2` of `90` (`0`) —, the correctly rounded irrational values (`1/3` of `7`,
`(±22/7)°`, `1/10` of a turn, `(10³⁰ + 1/3)°`), the directed modes, agreement with the float
variant at representable arguments, and a tiny argument.  References: a 240-digit evaluation
with exact reduction, rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def C (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cosRatWithPeriodPrecRound (Q q) u p m
private def belowOne : AzFloat := X "0.9999999999999999" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (C "1/3" 0 53) == ("NaN", .eq)
#guard D (C "1/3" 360 0) == ("NaN", .eq)
#guard D (C "0" 360 0) == ("NaN", .eq)
#guard D (C "0" 360 53) == ("1.0", .eq)

-- exact values
#guard D (C "1/3" 1 53) == ("-0.5", .eq)
#guard D (C "-2/3" 1 53) == ("-0.5", .eq)
#guard D (C "1/6" 1 53) == ("0.5", .eq)
#guard D (C "5/6" 1 53) == ("0.5", .eq)
#guard D (C "1/2" 1 53) == ("-1.0", .eq)
#guard D (C "7/3" 7 53) == ("-0.5", .eq)
#guard D (C "1001/7" 13 53) == ("1.0", .eq)
#guard D (C "45/2" 90 53) == ("0.0", .eq)
#guard D (C "60" 360 53) == ("0.5", .eq)
#guard D (C "-1260" 360 53) == ("-1.0", .eq)
#guard D (C "1/3" 1 7 .Floor) == ("-0.5", .eq)

-- correctly rounded irrational values
#guard D (C "1/3" 7 53) == ("0.9555728057861407", .lt)
#guard D (C "1/3" 7 53 .Ceiling) == ("0.9555728057861408", .gt)
#guard D (C "22/7" 360 53) == ("0.9984959401311517", .lt)
#guard D (C "-22/7" 360 53) == ("0.9984959401311517", .lt)
#guard D (C "22/7" 360 53 .Ceiling) == ("0.9984959401311518", .gt)
#guard D (C "1/10" 1 53) == ("0.8090169943749475", .gt)
#guard D (C "1/10" 1 53 .Floor) == ("0.8090169943749473", .lt)
#guard D (C "3000000000000000000000000000001/3" 360 53) == ("0.17937458593745736", .lt)
#guard toString (cosRatWithPeriod (Q "22/7") 360 200)
  == "0.9984959401311517674613121977046275966008758908100819199996446"

-- agreement with the float variant at representable arguments
#guard C "45" 360 53 == cosWithPeriodPrecRound (X "45" 53) 360 53 .Nearest
#guard C "5/2" 7 53 == cosWithPeriodPrecRound (X "2.5" 53) 7 53 .Nearest
#guard C "1" 1000 53 .Floor == cosWithPeriodPrecRound (X "1" 53) 1000 53 .Floor

-- a tiny argument (`1/(3·2^1000)`): rounded without touching the argument
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard D (cosRatWithPeriodPrecRound tinyQ 360 53 .Nearest) == ("1.0", .gt)
#guard D (cosRatWithPeriodPrecRound (-tinyQ) 1 53 .Floor) == ("0.9999999999999999", .lt)
