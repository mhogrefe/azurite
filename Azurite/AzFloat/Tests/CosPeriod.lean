/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.CosPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cos (2π x / u)`

The special values (`u = 0`, `NaN`, `±∞`, `x = 0`, `p = 0`), the exact rational values in
degrees (`u = 360`: `0°, 60°, 90°, 120°, 180°, 240°, 270°, 300°, 360°, 720°, −60°`) and in
turns (`u = 1`: `1/2, 1/4, 3/4`; `u = 3, 4, 6, 7/4`), the correctly rounded irrational values
(`45°`, `30°`, `1°`, `359°`, `−1°`, `(10¹⁵ + 1)°`, `1/12`, `1/8`, `1/7`, `5/2` of `7`,
`1/1000` of a turn, the 53-bit float nearest `1/3` of a turn — whose cosine is one ulp away from
`−1/2` —, `2⁻¹⁰⁰` of a turn and `1/(2⁶⁴ − 1)` of a turn — both round to `1`), the directed
modes, a 20-bit result, agreement with `cos`, and 200-bit `cos (2π/7)` and `cos 1°`.  References:
a 240-digit evaluation (Machin `π`, exact reduction of `x/u`) rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def C (x : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cosWithPeriodPrecRound (F x 53) u p m
private def half : AzFloat := F "1/2" 53
private def nhalf : AzFloat := F "-1/2" 53

-- special values
#guard cosWithPeriodPrecRound (F "1" 53) 0 53 .Nearest == (nan, .eq)
#guard cosWithPeriodPrecRound nan 360 53 .Nearest == (nan, .eq)
#guard cosWithPeriodPrecRound (infinity true) 360 53 .Nearest == (nan, .eq)
#guard cosWithPeriodPrecRound (infinity false) 360 53 .Nearest == (nan, .eq)
#guard cosWithPeriodPrecRound zero 360 53 .Nearest == (F "1" 53, .eq)
#guard cosWithPeriodPrecRound zero 360 0 .Nearest == (nan, .eq)
#guard cosWithPeriodPrecRound zero 0 53 .Nearest == (nan, .eq)
#guard C "1" 360 0 == (nan, .eq)

-- exact values
#guard C "0" 360 53 == (F "1" 53, .eq)
#guard C "60" 360 53 == (half, .eq)
#guard C "90" 360 53 == (zero, .eq)
#guard C "120" 360 53 == (nhalf, .eq)
#guard C "180" 360 53 == (F "-1" 53, .eq)
#guard C "240" 360 53 == (nhalf, .eq)
#guard C "270" 360 53 == (zero, .eq)
#guard C "300" 360 53 == (half, .eq)
#guard C "360" 360 53 == (F "1" 53, .eq)
#guard C "720" 360 53 == (F "1" 53, .eq)
#guard C "-60" 360 53 == (half, .eq)
#guard C "1/2" 1 53 == (F "-1" 53, .eq)
#guard C "1/4" 1 53 == (zero, .eq)
#guard C "3/4" 1 53 == (zero, .eq)
#guard C "1" 3 53 == (nhalf, .eq)
#guard C "1" 4 53 == (zero, .eq)
#guard C "5" 6 53 == (half, .eq)
#guard C "7/4" 1 53 == (zero, .eq)
#guard C "60" 360 7 == (F "1/2" 7, .eq)

-- correctly rounded irrational values
#guard C "45" 360 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard C "30" 360 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard C "1" 360 53 == (F "4502913707333573/4503599627370496" 53, .gt)
#guard C "359" 360 53 == (F "4502913707333573/4503599627370496" 53, .gt)
#guard C "-1" 360 53 == (F "4502913707333573/4503599627370496" 53, .gt)
#guard C "1000000000000001" 360 53 == (F "6874618563813967/36028797018963968" 53, .lt)
#guard C "1" 12 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard C "1" 8 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard C "1" 7 53 == (F "5615896878640593/9007199254740992" 53, .lt)
#guard C "5/2" 7 53 == (F "-5615896878640593/9007199254740992" 53, .gt)
#guard C "1" 1000 53 == (F "9007021460339101/9007199254740992" 53, .lt)
#guard C "1/3" 1 53 == (F "-4503599627370495/9007199254740992" 53, .gt)
#guard C "1/1267650600228229401496703205376" 1 53 == (F "1" 53, .gt)
#guard C "1" 18446744073709551615 53 == (F "1" 53, .gt)

-- directed modes, other precisions, agreement with `cos`
#guard C "45" 360 53 .Floor == (F "1592262918131443/2251799813685248" 53, .lt)
#guard C "45" 360 53 .Ceiling == (F "6369051672525773/9007199254740992" 53, .gt)
#guard C "1" 360 53 .Floor == (F "9005827414667145/9007199254740992" 53, .lt)
#guard C "1" 360 53 .Ceiling == (F "4502913707333573/4503599627370496" 53, .gt)
#guard C "1" 360 20 == (F "32763/32768" 20, .lt)
#guard cosWithPeriod (F "45" 53) 360 == F "6369051672525773/9007199254740992" 53
#guard toString (cosWithPeriod (F "1" 200) 7)
  == "0.6234898018587335305250048840042398106322747308964021053655496"
#guard toString (cosWithPeriod (F "1" 200) 360)
  == "0.999847695156391239157011558813914851692740310583185939658321"

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53
#guard cosWithPeriodPrecRound tinyX 360 53 .Nearest == (F "1" 53, .gt)
#guard cosWithPeriodPrecRound tinyX 360 53 .Floor == (belowOne, .lt)
#guard cosWithPeriodPrecRound (-tinyX) 1 53 .Ceiling == (F "1" 53, .gt)
#guard cosWithPeriodPrecRound tinyX 18446744073709551615 53 .Floor == (belowOne, .lt)
