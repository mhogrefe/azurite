/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asin
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asin`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`; `±1` give `±π/2` in every mode; `0`;
`p = 0`), the correctly rounded 53-bit values at `±1/2`, the floats nearest `1/3`, `−7/10`,
`3/4`, `9/10`, `99/100`, `1 − 10⁻⁶`, `1/√2`, `5/7`, small arguments, and the neighbour
`1 − 2^(−53)` of `1`; the directed modes; 1-, 2-, 20- and 113-bit results; 200-bit strings;
`2⁻⁴⁰`, `2⁻¹⁰⁰` at 200 bits, `1 − 2^(−190)` at 200 bits; and the tiny arguments `±2^(−2^30)`
(no cost in the exponent).  References: an independent 1400-bit fixed-point evaluation of
`arctan (x/√(1 − x²))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asinPrecRound x p m
private def piN : AzFloat := F "884279719003555/562949953421312" 53
private def piC : AzFloat := F "7074237752028441/4503599627370496" 53

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (nan, .eq)
#guard A (infinity false) 53 == (nan, .eq)
#guard A (F "2" 53) 53 == (nan, .eq)
#guard A (F "-3/2" 53) 53 == (nan, .eq)
#guard A (F "9007199254740993/9007199254740992" 54) 53 == (nan, .eq)
#guard A (powerOf2 (AzInt.ofInt 1073741824)) 53 == (nan, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "1/2" 53) 0 == (nan, .eq)
#guard A (F "1" 53) 53 == (piN, .lt)
#guard A (F "1" 200) 53 .Ceiling == (piC, .gt)
#guard A (F "-1" 53) 53 == (-piN, .gt)
#guard A (F "-1" 53) 53 .Floor == (-piC, .lt)

-- correctly rounded values
#guard A (F "1/2" 53) 53 == (F "2358079250676147/4503599627370496" 53, .gt)
#guard A (F "-1/2" 53) 53 == (F "-2358079250676147/4503599627370496" 53, .lt)
#guard A (F "1/3" 53) 53 == (F "3060978757568649/9007199254740992" 53, .gt)
#guard A (F "-7/10" 53) 53 == (F "-6984159753600405/9007199254740992" 53, .gt)
#guard A (F "3/4" 53) 53 == (F "1909666031444023/2251799813685248" 53, .lt)
#guard A (F "9/10" 53) 53 == (F "2521496785244345/2251799813685248" 53, .lt)
#guard A (F "99/100" 53) 53 == (F "6436800632706333/4503599627370496" 53, .lt)
#guard A (F "999999/1000000" 53) 53 == (F "7067868699825069/4503599627370496" 53, .gt)
#guard A (F "1/1024" 53) 53 == (F "2251800171599343/2305843009213693952" 53, .gt)
#guard A (F "1/1000" 53) 53 == (F "2305843393521035/2305843009213693952" 53, .lt)
#guard A (F "-1/1000000000" 53) 53 == (F "-4835703278458517/4835703278458516698824704" 53, .gt)
#guard A (F "707106781186547/1000000000000000" 53) 53
  == (F "3537118876014217/4503599627370496" 53, .gt)
#guard A (F "5/7" 53) 53 == (F "7166154329695639/9007199254740992" 53, .gt)
-- the neighbour `1 − 2^(−53)` of `1`
#guard A (F "9007199254740991/9007199254740992" 53) 53
  == (F "884279710614947/562949953421312" 53, .lt)
#guard A (F "-9007199254740991/9007199254740992" 53) 53 .Floor
  == (F "-7074237684919577/4503599627370496" 53, .lt)

-- directed modes and other precisions
#guard A (F "1/2" 53) 53 .Floor == (F "4716158501352293/9007199254740992" 53, .lt)
#guard A (F "-3/4" 53) 53 .Floor == (F "-7638664125776093/9007199254740992" 53, .lt)
#guard A (F "1/2" 53) 53 .Ceiling == (F "2358079250676147/4503599627370496" 53, .gt)
#guard A (F "-3/4" 53) 53 .Ceiling == (F "-1909666031444023/2251799813685248" 53, .gt)
#guard A (F "1/2" 53) 20 == (F "549033/1048576" 20, .lt)
#guard A (F "1/2" 53) 1 == (F "1/2" 1, .lt)
#guard A (F "3/4" 53) 113
  == (F "4403390068538058708848283552344817/5192296858534827628530496329220096" 113, .gt)
#guard A (F "1/2" 53) 2 == (F "1/2" 2, .lt)
#guard asin (F "1/2" 53) == (A (F "1/2" 53) 53).1
#guard (toString (asinPrecRound (F "1/2" 200) 200 .Nearest).1).startsWith
  "0.52359877559829887307710723054658381403286156656251763"
#guard (toString (asinPrecRound (F "3/4" 200) 200 .Nearest).1).startsWith
  "0.84806207898148100805294433899841808007336621326311264"

-- small arguments, arguments next to `1`, tiny arguments
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) (p : Nat) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some p
#guard same (A (powerOf2 (AzInt.ofInt (-40))) 53) (powerOf2 (AzInt.ofInt (-40))) .lt 53
#guard A (powerOf2 (AzInt.ofInt (-40))) 53 .Ceiling
  == (F "4503599627370497/4951760157141521099596496896" 53, .gt)
#guard same (A (powerOf2 (AzInt.ofInt (-100))) 200) (powerOf2 (AzInt.ofInt (-100))) .lt 200
#guard A (F ("1569275433846670190958947355801916604025588861116008628223/"
    ++ "1569275433846670190958947355801916604025588861116008628224") 200) 200
  == (F ("1262086188654498467993352535281925550314570351733774990511383/"
    ++ "803469022129495137770981046170581301261101496891396417650688") 200, .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard same (A tiny 53) tiny .lt 53
#guard (A tiny 53 .Ceiling).2 == .gt
#guard same (A (-tiny) 53) (-tiny) .gt 53
#guard (A (-tiny) 53 .Floor).2 == .lt
#guard (asinTiny? true tiny (AzInt.ofInt (-1073741823)) 1 53 .Nearest).isSome
