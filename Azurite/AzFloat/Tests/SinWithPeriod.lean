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
private def S (x : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinWithPeriodPrecRound (F x 53) u p m
private def half : AzFloat := F "1/2" 53
private def nhalf : AzFloat := F "-1/2" 53

-- special values
#guard sinWithPeriodPrecRound (F "1" 53) 0 53 .Nearest == (nan, .eq)
#guard sinWithPeriodPrecRound nan 360 53 .Nearest == (nan, .eq)
#guard sinWithPeriodPrecRound (infinity true) 360 53 .Nearest == (nan, .eq)
#guard sinWithPeriodPrecRound (infinity false) 360 53 .Nearest == (nan, .eq)
#guard sinWithPeriodPrecRound zero 360 53 .Nearest == (zero, .eq)
#guard sinWithPeriodPrecRound zero 360 0 .Nearest == (zero, .eq)
#guard sinWithPeriodPrecRound zero 0 53 .Nearest == (nan, .eq)
#guard S "1" 360 0 == (nan, .eq)

-- exact values
#guard S "30" 360 53 == (half, .eq)
#guard S "90" 360 53 == (F "1" 53, .eq)
#guard S "150" 360 53 == (half, .eq)
#guard S "180" 360 53 == (zero, .eq)
#guard S "210" 360 53 == (nhalf, .eq)
#guard S "270" 360 53 == (F "-1" 53, .eq)
#guard S "330" 360 53 == (nhalf, .eq)
#guard S "360" 360 53 == (zero, .eq)
#guard S "720" 360 53 == (zero, .eq)
#guard S "-30" 360 53 == (nhalf, .eq)
#guard S "-90" 360 53 == (F "-1" 53, .eq)
#guard S "-210" 360 53 == (half, .eq)
#guard S "-270" 360 53 == (F "1" 53, .eq)
#guard S "1/2" 1 53 == (zero, .eq)
#guard S "1/4" 1 53 == (F "1" 53, .eq)
#guard S "3/4" 1 53 == (F "-1" 53, .eq)
#guard S "7/4" 1 53 == (F "-1" 53, .eq)
#guard S "1" 4 53 == (F "1" 53, .eq)
#guard S "-1" 4 53 == (F "-1" 53, .eq)
#guard S "1" 12 53 == (half, .eq)
#guard S "5" 12 53 == (half, .eq)
#guard S "7" 12 53 == (nhalf, .eq)
#guard S "11" 12 53 == (nhalf, .eq)
#guard S "30" 360 7 == (F "1/2" 7, .eq)

-- correctly rounded irrational values
#guard S "45" 360 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard S "60" 360 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard S "1" 360 53 == (F "2515156836085391/144115188075855872" 53, .lt)
#guard S "359" 360 53 == (F "-2515156836085391/144115188075855872" 53, .gt)
#guard S "-1" 360 53 == (F "-2515156836085391/144115188075855872" 53, .gt)
#guard S "-200" 360 53 == (F "6161287160138741/18014398509481984" 53, .lt)
#guard S "1000000000000001" 360 53 == (F "-4420855817591649/4503599627370496" 53, .lt)
#guard S "1" 8 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard S "1" 7 53 == (F "7042111946219083/9007199254740992" 53, .lt)
#guard S "5/2" 7 53 == (F "7042111946219083/9007199254740992" 53, .lt)
#guard S "1" 1000 53 == (F "7243971794433657/1152921504606846976" 53, .lt)
#guard S "1/3" 1 53 == (F "7800463371553963/9007199254740992" 53, .gt)
#guard S "1/12" 1 53 == (half, .gt)
#guard S "1/12" 1 53 .Floor == (F "9007199254740991/18014398509481984" 53, .lt)
#guard S "6333186975989761/35184372088832" 360 53
  == (F "-5030569068109113/10141204801825835211973625643008" 53, .gt)
#guard S "1/1267650600228229401496703205376" 1 53
  == (F "884279719003555/178405961588244985132285746181186892047843328" 53, .lt)
#guard S "1" 18446744073709551615 53
  == (F "884279719003555/2596148429267413814265248164610048" 53, .lt)

-- directed modes, other precisions
#guard S "45" 360 53 .Floor == (F "1592262918131443/2251799813685248" 53, .lt)
#guard S "45" 360 53 .Ceiling == (F "6369051672525773/9007199254740992" 53, .gt)
#guard S "1" 360 53 .Floor == (F "2515156836085391/144115188075855872" 53, .lt)
#guard S "1" 360 53 .Ceiling == (F "5030313672170783/288230376151711744" 53, .gt)
#guard S "-1" 360 53 .Floor == (F "-5030313672170783/288230376151711744" 53, .lt)
#guard S "-1" 360 53 .Ceiling == (F "-2515156836085391/144115188075855872" 53, .gt)
#guard S "1" 360 20 == (F "292803/16777216" 20, .gt)
#guard sinWithPeriod (F "45" 53) 360 == F "6369051672525773/9007199254740992" 53
#guard toString (sinWithPeriod (F "1" 200) 7)
  == "0.781831482468029808708444526674057750232334518708687528980635"
#guard toString (sinWithPeriod (F "1" 200) 360)
  == "0.01745240643728351281941897851631619247225272030713964268361243"

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate);
-- `sin y` rounds like a value just below `y = 2π 2^(−2^30) / u`
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
private def degLo : AzFloat := (F "5030569068109113/288230376151711744" 53) <<< tinyE
private def degHi : AzFloat := (F "2515284534054557/144115188075855872" 53) <<< tinyE
private def maxLo : AzFloat :=
  (F "884279719003555/2596148429267413814265248164610048" 53) <<< tinyE
#guard sinWithPeriodPrecRound tinyX 360 53 .Nearest == (degLo, .lt)
#guard sinWithPeriodPrecRound tinyX 360 53 .Floor == (degLo, .lt)
#guard sinWithPeriodPrecRound tinyX 360 53 .Ceiling == (degHi, .gt)
#guard sinWithPeriodPrecRound (-tinyX) 360 53 .Nearest == (-degLo, .gt)
#guard sinWithPeriodPrecRound (-tinyX) 360 53 .Floor == (-degHi, .lt)
#guard sinWithPeriodPrecRound (-tinyX) 360 53 .Ceiling == (-degLo, .gt)
#guard sinWithPeriodPrecRound tinyX 18446744073709551615 53 .Nearest == (maxLo, .lt)

-- huge arguments: `m 2^E mod u` through `2^E mod u` (`3·2^(2^28) ≡ 6 mod 7`, `≡ 48 mod 360`,
-- `≡ 0 mod 3`, `≡ 3 mod 2^64 − 1`), never building the `2^28`-bit number
private def hugeX : AzFloat := (F "3" 53) <<< AzInt.ofInt (2 ^ 28)
#guard sinWithPeriodPrecRound hugeX 7 53 .Nearest ==
  sinWithPeriodPrecRound (F "6" 53) 7 53 .Nearest
#guard sinWithPeriodPrecRound hugeX 360 53 .Floor == sinWithPeriodPrecRound (F "48" 53) 360 53 .Floor
#guard sinWithPeriodPrecRound (-hugeX) 360 30 .Ceiling ==
  sinWithPeriodPrecRound (F "-48" 53) 360 30 .Ceiling
#guard sinWithPeriodPrecRound hugeX 3 53 .Nearest == (zero, .eq)
#guard sinWithPeriodPrecRound hugeX 18446744073709551615 53 .Nearest ==
  sinWithPeriodPrecRound (F "3" 53) 18446744073709551615 53 .Nearest
