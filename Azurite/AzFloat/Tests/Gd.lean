/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Gudermannian `gd x`

The special values (`NaN`, `±∞ ↦ ±π/2`, `0`, `p = 0`); the correctly rounded 53-bit values on
every path — the alternating series for a small argument (`1/1024`, `3/8`), the general path
(`3/4`, `1`, `5/4`), the alternating series of `e^(−x)` (`2`, `7/2`, `20`, `45`) and the huge
path (`200`, `100000`, `2^(2^30)`), where the value is `π/2` rounded with the comparison of a
number just below it; 200-, 300- and 1000-bit results; directed rounding; oddness; tiny
arguments (`±2^(−1000)`, `±2^(−2^30)`: the value is just inside `x`, at no cost); and the
agreement of the three paths of the bracket.  References: a 400-digit evaluation of
`2 arctan ((e^x − 1)/(e^x + 1))` (argument halving and the series) rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := gdPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == piDiv2PrecRound 53 .Nearest
#guard A (infinity true) 53 .Floor == piDiv2PrecRound 53 .Floor
#guard (A (infinity false) 53 .Floor).1 == -(piDiv2PrecRound 53 .Ceiling).1
#guard (A (infinity false) 53 .Floor).2 == .lt
#guard A (infinity true) 0 == (nan, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "1" 53) 0 == (nan, .eq)

-- correctly rounded 53-bit values on every path
#guard A (F "1/1024" 53) 53 == (F "8796091624107/9007199254740992" 53, .gt)
#guard A (F "3/8" 53) 53 == (F "1650604576534915/4503599627370496" 53, .lt)
#guard A (F "3/4" 53) 53 == (F "6198766695064517/9007199254740992" 53, .lt)
#guard A (F "1" 53) 53 == (F "7798158244213747/9007199254740992" 53, .gt)
#guard A (F "5/4" 53) 53 == (F "4560955735412077/4503599627370496" 53, .lt)
#guard A (F "-2" 53) 53 == (F "-5862607364342525/4503599627370496" 53, .gt)
#guard A (F "7/2" 53) 53 == (F "6802326532795795/4503599627370496" 53, .gt)
#guard A (F "20" 53) 53 == (F "7074237733463219/4503599627370496" 53, .gt)
#guard A (F "45" 53) 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A (F "200" 53) 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A (F "100000" 53) 53 == (F "884279719003555/562949953421312" 53, .lt)

-- a huge argument: `π/2` rounded, with the comparison of a number just below `π/2`
private def huge : AzFloat := h (F "3" 53) (2 ^ 30)
#guard (A huge 53).1 == (piDiv2PrecRound 53 .Nearest).1
#guard (A huge 53 .Floor) == piDiv2PrecRound 53 .Floor
#guard (A huge 53 .Ceiling) == piDiv2PrecRound 53 .Ceiling
#guard (A (-huge) 53 .Ceiling).1 == -(piDiv2PrecRound 53 .Floor).1

-- directed rounding and oddness
#guard A (F "1" 53) 53 .Floor == (F "3899079122106873/4503599627370496" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "7798158244213747/9007199254740992" 53, .gt)
#guard A (F "-3/4" 53) 53 == (F "-6198766695064517/9007199254740992" 53, .gt)
#guard (A (F "-1" 53) 53 .Floor).1 == -(A (F "1" 53) 53 .Ceiling).1

-- other precisions
#guard A (F "1" 53) 200 == (F ("1391237920176253689963724998890889512640847220755539751705113"
  ++ "/1606938044258990275541962092341162602522202993782792835301376") 200, .gt)
#guard A (F "30" 53) 300 == (F ("7999421572937213664891602802477721614953836017510164060302611"
  ++ "80768607098942482562552613807/50925899408362152156711142210234454026286709841648406265"
  ++ "9035112338595324940834176545849344") 300, .lt)
#guard A (F "1/64" 53) 300 == (F ("203695309418709261793874874002220643327251531252941789717943"
  ++ "5755455859109371507420941901159/1303703024854071095211805240582002023072939771946199200"
  ++ "40712988758680403184853549195737432064") 300, .lt)
#guard A (F "3/4" 53) 1000 == (F ("184353417745397661167963670497771353723122348286355821811970"
  ++ "13266792462473134880684112196849940368757334928406466142549028677492563515990229576953"
  ++ "51490863489280441148172424393538023654836218531898543256156116907707298345502470387112"
  ++ "580131304569314927628291421000233275776837995723207517742075478924083/2678771517965668"
  ++ "30237106262265000452640351202926383401860937597092587762781234030623299594703923964531"
  ++ "89866822938828670629678632142307851089961443936746437009836419437060577463552686512655"
  ++ "92785469488545538261618745895485316849691889791385986519265728642799119421635541915107"
  ++ "457913156096709301417017344") 1000, .gt)
#guard toString (gd (F "1" 200))
  == "0.8657694832396586242896018461918444413796791992487600996118485"
#guard (A (F "1" 53) 1).1 == F "1" 1 && (A (F "1" 53) 2).1 == F "3/4" 2

-- tiny arguments: the value is just inside `x`
#guard A (h (F "1" 53) (-1000)) 53 == (h (F "1" 53) (-1000), .gt)
#guard A (h (F "-1" 53) (-1000)) 53 == (h (F "-1" 53) (-1000), .lt)
#guard A (h (F "1" 53) (-(2 ^ 30))) 53 .Floor
  == (h (F "9007199254740991/9007199254740992" 53) (-(2 ^ 30)), .lt)

-- the paths of the bracket agree
private def overlap (a b : Encl) : Bool := le a.1 b.2 && le b.1 a.2
private def x3 : AzFloat := F "3" 53
private def e3 : AzInt := AzInt.ofInt 2
#guard (gdLargeSeries? x3 e3 117).isSome
#guard ((gdLargeSeries? x3 e3 117).map (overlap (gdCore x3 e3 117))) == some true
#guard (gdLargeSeries? x3 e3 1000).isNone
private def xs : AzFloat := F "3/8" 53
private def es : AzInt := AzInt.ofInt (-1)
#guard ((gdSmallSeries? xs es 117).map (overlap (gdCore xs es 117))) == some true
#guard (gdSmallSeries? (F "3/4" 53) (AzInt.ofInt 0) 117).isNone
#guard overlap (gdHuge 128 117) (gdCore (F "200" 53) (AzInt.ofInt 8) 117)
#guard (enclNarrow? (F "1" 8, F "5/4" 8) 2).isSome && (enclNarrow? (F "1" 8, F "5/4" 8) 3).isNone
