/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.SinRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sin (2π q / u)` of a rational `q`

The special values (`u = 0`, `p = 0`, `q = 0`), the exact rational values — including arguments
no float can hit, such as `1/12` of a turn (`1/2`), `±5/12`, `7/12`, `11/12`, `7/12` of `7`,
`1001/7` of `13` (`0`) and `±45/2` of `90` (`±1`) —, the correctly rounded irrational values
(`1/3` of `7`, `(±22/7)°`, `1/10`, `1/3`, `−2/3` and `1/7` of a turn, `(10³⁰ + 1/3)°`), the
directed modes, agreement with the float variant at representable arguments, and the tiny path
at `±1/(3·2^1000)`.  References: a 300-digit evaluation with exact reduction, rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinRatWithPeriodPrecRound (Q q) u p m
private def half : AzFloat := X "0.5" 53
private def nhalf : AzFloat := X "-0.5" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (S "1/3" 0 53) == ("NaN", .eq)
#guard D (S "0" 0 53) == ("NaN", .eq)
#guard D (S "1/3" 360 0) == ("NaN", .eq)
#guard D (S "0" 360 0) == ("0.0", .eq)
#guard D (S "0" 360 53) == ("0.0", .eq)

-- exact values
#guard D (S "1/12" 1 53) == ("0.5", .eq)
#guard D (S "5/12" 1 53) == ("0.5", .eq)
#guard D (S "7/12" 1 53) == ("-0.5", .eq)
#guard D (S "11/12" 1 53) == ("-0.5", .eq)
#guard D (S "-1/12" 1 53) == ("-0.5", .eq)
#guard D (S "-7/12" 1 53) == ("0.5", .eq)
#guard D (S "1/4" 1 53) == ("1.0", .eq)
#guard D (S "-1/4" 1 53) == ("-1.0", .eq)
#guard D (S "3/4" 1 53) == ("-1.0", .eq)
#guard D (S "1/2" 1 53) == ("0.0", .eq)
#guard D (S "7/12" 7 53) == ("0.5", .eq)
#guard D (S "1001/7" 13 53) == ("0.0", .eq)
#guard D (S "45/2" 90 53) == ("1.0", .eq)
#guard D (S "-45/2" 90 53) == ("-1.0", .eq)
#guard D (S "30" 360 53) == ("0.5", .eq)
#guard D (S "-1350" 360 53) == ("1.0", .eq)
#guard D (S "1/12" 1 7 .Floor) == ("0.5", .eq)

-- correctly rounded irrational values
#guard D (S "1/3" 7 53) == ("0.2947551744109042", .lt)
#guard D (S "1/3" 7 53 .Ceiling) == ("0.29475517441090426", .gt)
#guard D (S "22/7" 360 53) == ("0.05482570146936002", .gt)
#guard D (S "-22/7" 360 53) == ("-0.05482570146936002", .lt)
#guard D (S "22/7" 360 53 .Floor) == ("0.054825701469360014", .lt)
#guard D (S "-22/7" 360 53 .Floor) == ("-0.05482570146936002", .lt)
#guard D (S "1/10" 1 53) == ("0.5877852522924731", .gt)
#guard D (S "1/10" 1 53 .Floor) == ("0.587785252292473", .lt)
#guard D (S "1/3" 1 53) == ("0.8660254037844386", .lt)
#guard D (S "-2/3" 1 53) == ("0.8660254037844386", .lt)
#guard D (S "1/7" 1 53) == ("0.7818314824680298", .lt)
#guard D (S "3000000000000000000000000000001/3" 360 53) == ("-0.9837808485225588", .gt)
#guard toString (sinRatWithPeriod (Q "1/7") 1 200)
  == "0.781831482468029808708444526674057750232334518708687528980635"

-- agreement with the float variant at representable arguments
#guard S "45" 360 53 == sinWithPeriodPrecRound (X "45" 53) 360 53 .Nearest
#guard S "-5/2" 7 53 == sinWithPeriodPrecRound (X "-2.5" 53) 7 53 .Nearest
#guard S "1" 1000 53 .Floor == sinWithPeriodPrecRound (X "1" 53) 1000 53 .Floor

-- the tiny path (`±1/(3·2^1000)`): `sin y` rounds like a value just below `y = 2πq/u`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyE : AzInt := AzInt.ofInt (-1000)
private def degLo : AzFloat := (X "0.005817764173314432" 53) <<< tinyE
private def degHi : AzFloat := (X "0.005817764173314433" 53) <<< tinyE
private def turnLo : AzFloat := (X "2.0943951023931953" 53) <<< tinyE
private def turnHi : AzFloat := (X "2.0943951023931957" 53) <<< tinyE
#guard D (sinRatWithPeriodPrecRound tinyQ 360 53 .Nearest) == ("5.4295076439858145e-304", .lt)
#guard D (sinRatWithPeriodPrecRound tinyQ 360 53 .Ceiling) == ("5.429507643985815e-304", .gt)
#guard D (sinRatWithPeriodPrecRound (-tinyQ) 360 53 .Nearest) == ("-5.4295076439858145e-304", .gt)
#guard D (sinRatWithPeriodPrecRound (-tinyQ) 360 53 .Floor) == ("-5.429507643985815e-304", .lt)
#guard D (sinRatWithPeriodPrecRound tinyQ 1 53 .Nearest) == ("1.9546227518348934e-301", .gt)
#guard D (sinRatWithPeriodPrecRound tinyQ 1 53 .Floor) == ("1.954622751834893e-301", .lt)
#guard (sinPeriodTiny? false tinyQ.num (tinyQ.den * AzNat.ofNat 360) (AzInt.ofInt 0)
  (ratExpBound tinyQ + AzInt.ofInt 2) 53 .Nearest).isSome
