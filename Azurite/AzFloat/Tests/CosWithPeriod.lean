/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.CosWithPeriod
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def C (x : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cosWithPeriodPrecRound (F x 53) u p m
private def half : AzFloat := X "0.5" 53
private def nhalf : AzFloat := X "-0.5" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (cosWithPeriodPrecRound (X "1" 53) 0 53 .Nearest) == ("NaN", .eq)
#guard D (cosWithPeriodPrecRound nan 360 53 .Nearest) == ("NaN", .eq)
#guard D (cosWithPeriodPrecRound (infinity true) 360 53 .Nearest) == ("NaN", .eq)
#guard D (cosWithPeriodPrecRound (infinity false) 360 53 .Nearest) == ("NaN", .eq)
#guard D (cosWithPeriodPrecRound zero 360 53 .Nearest) == ("1.0", .eq)
#guard D (cosWithPeriodPrecRound zero 360 0 .Nearest) == ("NaN", .eq)
#guard D (cosWithPeriodPrecRound zero 0 53 .Nearest) == ("NaN", .eq)
#guard D (C "1" 360 0) == ("NaN", .eq)

-- exact values
#guard D (C "0" 360 53) == ("1.0", .eq)
#guard D (C "60" 360 53) == ("0.5", .eq)
#guard D (C "90" 360 53) == ("0.0", .eq)
#guard D (C "120" 360 53) == ("-0.5", .eq)
#guard D (C "180" 360 53) == ("-1.0", .eq)
#guard D (C "240" 360 53) == ("-0.5", .eq)
#guard D (C "270" 360 53) == ("0.0", .eq)
#guard D (C "300" 360 53) == ("0.5", .eq)
#guard D (C "360" 360 53) == ("1.0", .eq)
#guard D (C "720" 360 53) == ("1.0", .eq)
#guard D (C "-60" 360 53) == ("0.5", .eq)
#guard D (C "1/2" 1 53) == ("-1.0", .eq)
#guard D (C "1/4" 1 53) == ("0.0", .eq)
#guard D (C "3/4" 1 53) == ("0.0", .eq)
#guard D (C "1" 3 53) == ("-0.5", .eq)
#guard D (C "1" 4 53) == ("0.0", .eq)
#guard D (C "5" 6 53) == ("0.5", .eq)
#guard D (C "7/4" 1 53) == ("0.0", .eq)
#guard D (C "60" 360 7) == ("0.5", .eq)

-- correctly rounded irrational values
#guard D (C "45" 360 53) == ("0.7071067811865476", .gt)
#guard D (C "30" 360 53) == ("0.8660254037844386", .lt)
#guard D (C "1" 360 53) == ("0.9998476951563913", .gt)
#guard D (C "359" 360 53) == ("0.9998476951563913", .gt)
#guard D (C "-1" 360 53) == ("0.9998476951563913", .gt)
#guard D (C "1000000000000001" 360 53) == ("0.1908089953765448", .lt)
#guard D (C "1" 12 53) == ("0.8660254037844386", .lt)
#guard D (C "1" 8 53) == ("0.7071067811865476", .gt)
#guard D (C "1" 7 53) == ("0.6234898018587335", .lt)
#guard D (C "5/2" 7 53) == ("-0.6234898018587335", .gt)
#guard D (C "1" 1000 53) == ("0.9999802608561371", .lt)
#guard D (C "1/3" 1 53) == ("-0.4999999999999999", .gt)
#guard D (C "1/1267650600228229401496703205376" 1 53) == ("1.0", .gt)
#guard C "1" 18446744073709551615 53 == (X "1" 53, .gt)

-- directed modes, other precisions, agreement with `cos`
#guard D (C "45" 360 53 .Floor) == ("0.7071067811865475", .lt)
#guard D (C "45" 360 53 .Ceiling) == ("0.7071067811865476", .gt)
#guard D (C "1" 360 53 .Floor) == ("0.9998476951563912", .lt)
#guard D (C "1" 360 53 .Ceiling) == ("0.9998476951563913", .gt)
#guard D (C "1" 360 20) == ("0.999847", .lt)
#guard toString (cosWithPeriod (X "45" 53) 360) == "0.7071067811865476"
#guard toString (cosWithPeriod (X "1" 200) 7)
  == "0.6234898018587335305250048840042398106322747308964021053655496"
#guard toString (cosWithPeriod (X "1" 200) 360)
  == "0.999847695156391239157011558813914851692740310583185939658321"

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard cosWithPeriodPrecRound tinyX 360 53 .Nearest == (X "1" 53, .gt)
#guard cosWithPeriodPrecRound tinyX 360 53 .Floor == (belowOne, .lt)
#guard cosWithPeriodPrecRound (-tinyX) 1 53 .Ceiling == (X "1" 53, .gt)
#guard cosWithPeriodPrecRound tinyX 18446744073709551615 53 .Floor == (belowOne, .lt)

-- huge arguments: `m 2^E mod u` through `2^E mod u` (`3·2^(2^28) ≡ 6 mod 7`, `≡ 48 mod 360`,
-- `≡ 0 mod 3`, `≡ 3 mod 2^64 − 1`), never building the `2^28`-bit number
private def hugeX : AzFloat := (X "3" 53) <<< AzInt.ofInt (2 ^ 28)
#guard cosWithPeriodPrecRound hugeX 7 53 .Nearest ==
  cosWithPeriodPrecRound (X "6" 53) 7 53 .Nearest
#guard cosWithPeriodPrecRound hugeX 360 53 .Floor ==
  cosWithPeriodPrecRound (X "48" 53) 360 53 .Floor
#guard cosWithPeriodPrecRound (-hugeX) 360 30 .Ceiling ==
  cosWithPeriodPrecRound (X "48" 53) 360 30 .Ceiling
#guard cosWithPeriodPrecRound hugeX 3 53 .Nearest == (X "1" 53, .eq)
#guard cosWithPeriodPrecRound hugeX 18446744073709551615 53 .Nearest ==
  cosWithPeriodPrecRound (X "3" 53) 18446744073709551615 53 .Nearest
