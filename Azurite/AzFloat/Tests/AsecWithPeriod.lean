/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsec (x) u / (2π)`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and for `u = 0`; `u/4` at `±∞`;
`u = 0`; `0` at `1`; `u/2` at `−1`; `u/6` at `2` and `u/3` at `−2` — exact for `u = 360`, the
correctly rounded rationals for `u = 7`, `1` in several modes; `p = 0`), the correctly rounded
53-bit values in degrees, other periods (`1`, `7`, `400`, `2^64 − 1`), the directed modes, 1-,
20- and 113-bit results, a 200-bit string, the neighbours `±(1 + 2^(−52))` of `±1`, and huge
arguments `±2^1000`, `±2^(2^30)`: values next to the float `u/4`, at no extra cost.
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecWithPeriodPrecRound x u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W zero 360 53) == ("NaN", .eq)
#guard D (W zero 0 53) == ("NaN", .eq)
#guard D (W (X "0.5" 53) 360 53) == ("NaN", .eq)
#guard D (W (X "-0.75" 53) 0 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("9.0e1", .eq)
#guard D (W (infinity false) 360 53) == ("9.0e1", .eq)
#guard D (W (infinity true) 7 1) == ("2.0", .gt)
#guard D (W (infinity false) 0 53) == ("0.0", .eq)
#guard D (W (X "3" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-1" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "3" 53) 360 0) == ("NaN", .eq)
#guard D (W (X "1" 53) 360 53) == ("0.0", .eq)
#guard D (W (X "1" 200) 360 0) == ("0.0", .eq)
#guard D (W (X "-1" 53) 360 53) == ("1.8e2", .eq)
#guard D (W (X "-1" 53) 7 1) == ("4.0", .gt)
-- a sixth and a third of a turn
#guard D (W (X "2" 53) 360 53) == ("6.0e1", .eq)
#guard D (W (X "-2" 200) 360 53) == ("1.2e2", .eq)
#guard D (W (X "2" 53) 3 53) == ("0.5", .eq)
#guard D (W (X "2" 53) 7 53) == ("1.1666666666666667", .gt)
#guard D (W (X "2" 53) 7 53 .Floor) == ("1.1666666666666665", .lt)
#guard D (W (X "-2" 53) 7 53) == ("2.3333333333333335", .gt)
#guard D (W (X "2" 53) 1 53) == ("0.16666666666666666", .lt)
#guard D (W (X "-2" 53) 1 53 .Ceiling) == ("0.33333333333333337", .gt)

-- correctly rounded values
#guard D (W (X "3" 53) 360 53) == ("70.52877936550931", .lt)
#guard D (W (X "-3" 53) 360 53) == ("109.47122063449069", .gt)
#guard D (W (X "1.5" 53) 360 53) == ("48.189685104221404", .gt)
#guard D (W (X "-1.4" 53) 360 53) == ("135.58469140280704", .gt)
#guard D (W (X "1.25" 53) 360 53) == ("36.86989764584402", .lt)
#guard D (W (X "100" 53) 360 53) == ("89.42703265514285", .gt)
#guard D (W (X "-1000" 53) 360 53) == ("90.05729578906238", .lt)
#guard D (W (X "1.000001" 53) 360 53) == ("0.0810284346889665", .gt)
#guard D (W (X "-1.000001" 53) 360 53) == ("179.91897156531104", .gt)
#guard D (W (X "3.142857142857143" 53) 360 53) == ("71.44699546497934", .lt)
#guard D (W (X "1.5" 53) 1 53) == ("0.133860236400615", .gt)
#guard D (W (X "-4" 53) 1 53) == ("0.29021531162758313", .gt)
#guard D (W (X "1.5" 53) 7 53) == ("0.937021654804305", .lt)
#guard D (W (X "-4" 53) 7 53) == ("2.031507181393082", .lt)
#guard D (W (X "1.5" 53) 400 53) == ("53.544094560246", .lt)
#guard D (W (X "-4" 53) 400 53) == ("116.08612465103324", .lt)
#guard D (W (X "1.5" 53) 18446744073709551615 53) == ("2.4692855225284045e18", .gt)
#guard D (W (X "-4" 53) 18446744073709551615 53) == ("5.35352757986589e18", .gt)
#guard D (W (X "1.5" 53) 360 53 .Floor) == ("48.1896851042214", .lt)
#guard D (W (X "-4" 53) 360 53 .Floor) == ("104.47751218592991", .lt)
#guard D (W (X "1.5" 53) 360 53 .Ceiling) == ("48.189685104221404", .gt)
#guard D (W (X "-4" 53) 360 53 .Ceiling) == ("104.47751218592992", .gt)
#guard D (W (X "1.5" 53) 360 20) == ("48.1897", .gt)
#guard D (W (X "-4" 53) 360 1) == ("1.0e2", .gt)
#guard D (W (X "1.5" 53) 360 113) == ("48.18968510422140193414208326942174", .gt)
#guard asecWithPeriod (X "1.5" 53) 360 == (W (X "1.5" 53) 360 53).1
#guard toString (asecWithPeriodPrecRound (X "1.5" 200) 360 200 .Nearest).1 == "48.18968510422140193\
  414208326942174046898588046409865224662722"

-- next to `±1`
#guard D (W (X "1.0000000000000002" 53) 360 53) == ("1.2074182697257331e-6", .gt)
#guard D (W (X "-1.0000000000000002" 53) 360 53) == ("179.99999879258172", .lt)
#guard D (W (X "-1.0000000000000002" 53) 360 53 .Ceiling) ==
  ("179.99999879258175", .gt)

-- huge arguments: next to the float `u/4`
private def T : AzFloat := powerOf2 (AzInt.ofInt 1000)
#guard D (W T 360 53) == ("9.0e1", .gt)
#guard D (W T 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (W (-T) 360 53) == ("9.0e1", .lt)
#guard D (W (-T) 360 53 .Ceiling) == ("90.00000000000001", .gt)
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard D (W huge 360 53) == ("9.0e1", .gt)
#guard D (W huge 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (W (-huge) 360 53) == ("9.0e1", .lt)
#guard D (W (-huge) 360 53 .Ceiling) == ("90.00000000000001", .gt)
#guard D (W (-huge) 360 53 .Floor) == ("9.0e1", .lt)
