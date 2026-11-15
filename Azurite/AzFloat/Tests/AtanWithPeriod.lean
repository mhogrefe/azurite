/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arctan (x) u / (2π)`

The special values (`NaN`; a quarter turn `±u/4` at `±∞`; `0` at `x = 0` and for `u = 0`; an
eighth of a turn `±u/8` at `x = ±1`, exact when the precision holds it and rounded otherwise;
`p = 0`), the correctly rounded 53-bit values in degrees (`u = 360`) at `1/2`, `3`, `−1000`,
the floats nearest `1/3` and `−7/5`, `1/1024`, `10¹²`, other periods (`1`, `7`, `400`,
`2^64 − 1`), the directed modes, 1-, 20- and 113-bit results, 200-bit strings, a small
argument `2⁻⁴⁰`, the tiny arguments `2⁻²⁰⁰` and `±2^(−2^30)` (no cost in the exponent) and the
huge `2^1000` (just below a quarter turn).  References: an independent 1400-bit fixed-point
evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanWithPeriodPrecRound x u p m

-- special values
#guard W nan 360 53 == (nan, .eq)
#guard W (infinity true) 360 53 == (F "90" 53, .eq)
#guard W (infinity false) 360 53 == (F "-90" 53, .eq)
#guard W (infinity true) 1 53 == (F "1/4" 53, .eq)
#guard W (infinity true) 7 1 == (F "2" 1, .gt)
#guard W (infinity false) 7 1 .Ceiling == (F "-1" 1, .gt)
#guard W (infinity true) 0 53 == (zero, .eq)
#guard W (infinity false) 0 53 == (zero, .eq)
#guard W zero 360 53 == (zero, .eq)
#guard W zero 360 0 == (zero, .eq)
#guard W (F "3" 53) 0 53 == (zero, .eq)
#guard W (F "-1" 53) 0 53 == (zero, .eq)
#guard W (F "3" 53) 360 0 == (nan, .eq)
-- an eighth of a turn
#guard W (F "1" 53) 360 53 == (F "45" 53, .eq)
#guard W (F "-1" 53) 360 53 == (F "-45" 53, .eq)
#guard W (F "1" 200) 1 53 == (F "1/8" 53, .eq)
#guard W (F "1" 53) 360 2 == (F "48" 2, .gt)
#guard W (F "1" 53) 360 2 .Floor == (F "32" 2, .lt)
#guard W (F "-1" 53) 360 2 .Floor == (F "-48" 2, .lt)
#guard W (F "1" 53) 18446744073709551615 53 == (F "2305843009213693952" 53, .gt)

-- correctly rounded values
#guard W (F "1/2" 53) 360 53 == (F "1869349290346353/70368744177664" 53, .gt)
#guard W (F "3" 53) 360 53 == (F "5035942778341233/70368744177664" 53, .gt)
#guard W (F "-1000" 53) 360 53 == (F "-6329155145282687/70368744177664" 53, .gt)
#guard W (F "1/3" 53) 360 53 == (F "1297244197648527/70368744177664" 53, .gt)
#guard W (F "-7/5" 53) 360 53 == (F "-7664890437556127/140737488355328" 53, .lt)
#guard W (F "1/1024" 53) 360 53 == (F "8063661538663547/144115188075855872" 53, .lt)
#guard W (F "1000000000000" 53) 360 53 == (F "98956046499777/1099511627776" 53, .lt)
#guard W (F "1/2" 53) 1 53 == (F "664657525456481/9007199254740992" 53, .lt)
#guard W (F "1/2" 53) 400 53 == (F "8308219068206013/281474976710656" 53, .lt)
#guard W (F "3" 53) 18446744073709551615 53 == (F "3667061621348567040" 53, .lt)
#guard W (F "-1/3" 53) 7 53 == (F "-6457393339406001/18014398509481984" 53, .lt)
#guard W (F "1/2" 53) 360 53 .Floor == (F "7477397161385411/281474976710656" 53, .lt)
#guard W (F "-3" 53) 360 53 .Floor == (F "-5035942778341233/70368744177664" 53, .lt)
#guard W (F "1/2" 53) 360 53 .Ceiling == (F "1869349290346353/70368744177664" 53, .gt)
#guard W (F "-3" 53) 360 53 .Ceiling == (F "-314746423646327/4398046511104" 53, .gt)
#guard W (F "3" 53) 360 20 == (F "586261/8192" 20, .gt)
#guard W (F "3" 53) 360 1 == (F "64" 1, .lt)
#guard W (F "1/2" 53) 360 113
  == (F "2155212996461858891468025780715179/81129638414606681695789005144064" 113, .gt)
#guard (toString (atanWithPeriodPrecRound (F "1/2" 200) 360 200 .Nearest).1).startsWith
  "26.565051177077989351572193720453294671204214299645221027"
#guard (toString (atanWithPeriodPrecRound (F "3" 200) 360 200 .Nearest).1).startsWith
  "71.565051177077989351572193720453294671204214299645221027"
#guard atanWithPeriod (F "1/2" 53) 360 == F "1869349290346353/70368744177664" 53

-- small, tiny and huge arguments
#guard W (powerOf2 (AzInt.ofInt (-40))) 360 53
  == (F "1007958012753983/19342813113834066795298816" 53, .gt)
#guard W (powerOf2 (AzInt.ofInt (-200))) 360 53
  == (F ("1007958012753983/"
    ++ "28269553036454149273332760011886696253239742350009903329945699220681916416") 53, .gt)
#guard W (powerOf2 (AzInt.ofInt 1000)) 360 53 == (F "90" 53, .gt)
#guard W (powerOf2 (AzInt.ofInt 1000)) 360 53 .Floor
  == (F "6333186975989759/70368744177664" 53, .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard (W tiny 360 53).1 == (F "1007958012753983/17592186044416" 53) <<< AzInt.ofInt (-1073741824)
#guard (W tiny 360 53).2 == .gt
#guard (W (-tiny) 360 53 .Floor).2 == .lt
-- a huge argument: within `2^(−2^30)` of a quarter turn, at no extra cost
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard W huge 360 53 == (F "90" 53, .gt)
#guard W huge 360 53 .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard W (-huge) 360 53 == (F "-90" 53, .lt)
#guard W (-huge) 7 53 .Ceiling == (F "-7881299347898367/4503599627370496" 53, .gt)
