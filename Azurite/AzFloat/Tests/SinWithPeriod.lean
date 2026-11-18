/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Sin
import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `sin (2π x / u)`

The special values (`u = 0`, `NaN`, `±∞`, `x = 0`, `p = 0`), the exact rational values in
degrees (`u = 360`: `0°, 30°, 90°, 150°, 180°, 210°, 270°, 330°, 360°, 720°, −30°, −90°`) and
in turns (`u = 1`: `1/2, 1/4, 3/4, 7/4`; `u = 4, 12`), the correctly rounded irrational values
(`45°`, `60°`, `1°`, `359°`, `−1°`, `−200°`, `(10¹⁵ + 1)°`, `1/8`, `1/7`, `5/2` of `7`,
`1/1000` of a turn, the 53-bit floats nearest `1/3` and `1/12` of a turn — the latter rounds to
`1/2` inexactly —, the float next above `180°` (`sin ≈ −5·10⁻¹⁶`), `2⁻¹⁰⁰` of a turn and
`1/(2⁶⁴ − 1)` of a turn), the directed modes, a 20-bit result, and 200-bit `sin (2π/7)` and
`sin 1°`; the tiny path at `±2^(−2^30)` (immediate).  References: a 300-digit evaluation
(Machin `π`, exact reduction of `x/u`) rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (x : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinWithPeriodPrecRound (F x 53) u p m
private def half : AzFloat := X "0.5" 53
private def nhalf : AzFloat := X "-0.5" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (sinWithPeriodPrecRound (X "1" 53) 0 53 .Nearest) == ("NaN", .eq)
#guard D (sinWithPeriodPrecRound nan 360 53 .Nearest) == ("NaN", .eq)
#guard D (sinWithPeriodPrecRound (infinity true) 360 53 .Nearest) == ("NaN", .eq)
#guard D (sinWithPeriodPrecRound (infinity false) 360 53 .Nearest) == ("NaN", .eq)
#guard D (sinWithPeriodPrecRound zero 360 53 .Nearest) == ("0.0", .eq)
#guard D (sinWithPeriodPrecRound zero 360 0 .Nearest) == ("0.0", .eq)
#guard D (sinWithPeriodPrecRound zero 0 53 .Nearest) == ("NaN", .eq)
#guard D (S "1" 360 0) == ("NaN", .eq)

-- exact values
#guard D (S "30" 360 53) == ("0.5", .eq)
#guard D (S "90" 360 53) == ("1.0", .eq)
#guard D (S "150" 360 53) == ("0.5", .eq)
#guard D (S "180" 360 53) == ("0.0", .eq)
#guard D (S "210" 360 53) == ("-0.5", .eq)
#guard D (S "270" 360 53) == ("-1.0", .eq)
#guard D (S "330" 360 53) == ("-0.5", .eq)
#guard D (S "360" 360 53) == ("0.0", .eq)
#guard D (S "720" 360 53) == ("0.0", .eq)
#guard D (S "-30" 360 53) == ("-0.5", .eq)
#guard D (S "-90" 360 53) == ("-1.0", .eq)
#guard D (S "-210" 360 53) == ("0.5", .eq)
#guard D (S "-270" 360 53) == ("1.0", .eq)
#guard D (S "1/2" 1 53) == ("0.0", .eq)
#guard D (S "1/4" 1 53) == ("1.0", .eq)
#guard D (S "3/4" 1 53) == ("-1.0", .eq)
#guard D (S "7/4" 1 53) == ("-1.0", .eq)
#guard D (S "1" 4 53) == ("1.0", .eq)
#guard D (S "-1" 4 53) == ("-1.0", .eq)
#guard D (S "1" 12 53) == ("0.5", .eq)
#guard D (S "5" 12 53) == ("0.5", .eq)
#guard D (S "7" 12 53) == ("-0.5", .eq)
#guard D (S "11" 12 53) == ("-0.5", .eq)
#guard D (S "30" 360 7) == ("0.5", .eq)

-- correctly rounded irrational values
#guard D (S "45" 360 53) == ("0.7071067811865476", .gt)
#guard D (S "60" 360 53) == ("0.8660254037844386", .lt)
#guard D (S "1" 360 53) == ("0.01745240643728351", .lt)
#guard D (S "359" 360 53) == ("-0.01745240643728351", .gt)
#guard D (S "-1" 360 53) == ("-0.01745240643728351", .gt)
#guard D (S "-200" 360 53) == ("0.3420201433256687", .lt)
#guard D (S "1000000000000001" 360 53) == ("-0.981627183447664", .lt)
#guard D (S "1" 8 53) == ("0.7071067811865476", .gt)
#guard D (S "1" 7 53) == ("0.7818314824680298", .lt)
#guard D (S "5/2" 7 53) == ("0.7818314824680298", .lt)
#guard D (S "1" 1000 53) == ("0.006283143965558951", .lt)
#guard D (S "1/3" 1 53) == ("0.8660254037844387", .gt)
#guard D (S "1/12" 1 53) == ("0.5", .gt)
#guard D (S "1/12" 1 53 .Floor) == ("0.49999999999999994", .lt)
#guard D (S "6333186975989761/35184372088832" 360 53) == ("-4.960524086056721e-16", .gt)
#guard D (S "1/1267650600228229401496703205376" 1 53) == ("4.9565592490930495e-30", .lt)
#guard D (S "1" 18446744073709551615 53) == ("3.4061215800865545e-19", .lt)

-- directed modes, other precisions
#guard D (S "45" 360 53 .Floor) == ("0.7071067811865475", .lt)
#guard D (S "45" 360 53 .Ceiling) == ("0.7071067811865476", .gt)
#guard D (S "1" 360 53 .Floor) == ("0.01745240643728351", .lt)
#guard D (S "1" 360 53 .Ceiling) == ("0.017452406437283515", .gt)
#guard D (S "-1" 360 53 .Floor) == ("-0.017452406437283515", .lt)
#guard D (S "-1" 360 53 .Ceiling) == ("-0.01745240643728351", .gt)
#guard D (S "1" 360 20) == ("0.01745242", .gt)
#guard toString (sinWithPeriod (X "45" 53) 360) == "0.7071067811865476"
#guard toString (sinWithPeriod (X "1" 200) 7)
  == "0.781831482468029808708444526674057750232334518708687528980635"
#guard toString (sinWithPeriod (X "1" 200) 360)
  == "0.01745240643728351281941897851631619247225272030713964268361243"

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate);
-- `sin y` rounds like a value just below `y = 2π 2^(−2^30) / u`
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def degLo : AzFloat := (X "0.017453292519943295" 53) <<< tinyE
private def degHi : AzFloat := (X "0.0174532925199433" 53) <<< tinyE
private def maxLo : AzFloat :=
  (X "3.4061215800865545e-19" 53) <<< tinyE
#guard sinWithPeriodPrecRound tinyX 360 53 .Nearest == (degLo, .lt)
#guard sinWithPeriodPrecRound tinyX 360 53 .Floor == (degLo, .lt)
#guard sinWithPeriodPrecRound tinyX 360 53 .Ceiling == (degHi, .gt)
#guard sinWithPeriodPrecRound (-tinyX) 360 53 .Nearest == (-degLo, .gt)
#guard sinWithPeriodPrecRound (-tinyX) 360 53 .Floor == (-degHi, .lt)
#guard sinWithPeriodPrecRound (-tinyX) 360 53 .Ceiling == (-degLo, .gt)
#guard sinWithPeriodPrecRound tinyX 18446744073709551615 53 .Nearest == (maxLo, .lt)

-- huge arguments: `m 2^E mod u` through `2^E mod u` (`3·2^(2^28) ≡ 6 mod 7`, `≡ 48 mod 360`,
-- `≡ 0 mod 3`, `≡ 3 mod 2^64 − 1`), never building the `2^28`-bit number
private def hugeX : AzFloat := (X "3" 53) <<< AzInt.ofInt (2 ^ 28)
#guard sinWithPeriodPrecRound hugeX 7 53 .Nearest ==
  sinWithPeriodPrecRound (X "6" 53) 7 53 .Nearest
#guard sinWithPeriodPrecRound hugeX 360 53 .Floor
  == sinWithPeriodPrecRound (X "48" 53) 360 53 .Floor
#guard sinWithPeriodPrecRound (-hugeX) 360 30 .Ceiling ==
  sinWithPeriodPrecRound (X "-48" 53) 360 30 .Ceiling
#guard D (sinWithPeriodPrecRound hugeX 3 53 .Nearest) == ("0.0", .eq)
#guard sinWithPeriodPrecRound hugeX 18446744073709551615 53 .Nearest ==
  sinWithPeriodPrecRound (X "3" 53) 18446744073709551615 53 .Nearest
