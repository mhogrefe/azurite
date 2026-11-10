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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def C (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cosRatWithPeriodPrecRound (Q q) u p m
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53

-- special values
#guard C "1/3" 0 53 == (nan, .eq)
#guard C "1/3" 360 0 == (nan, .eq)
#guard C "0" 360 0 == (nan, .eq)
#guard C "0" 360 53 == (F "1" 53, .eq)

-- exact values
#guard C "1/3" 1 53 == (F "-1/2" 53, .eq)
#guard C "-2/3" 1 53 == (F "-1/2" 53, .eq)
#guard C "1/6" 1 53 == (F "1/2" 53, .eq)
#guard C "5/6" 1 53 == (F "1/2" 53, .eq)
#guard C "1/2" 1 53 == (F "-1" 53, .eq)
#guard C "7/3" 7 53 == (F "-1/2" 53, .eq)
#guard C "1001/7" 13 53 == (F "1" 53, .eq)
#guard C "45/2" 90 53 == (zero, .eq)
#guard C "60" 360 53 == (F "1/2" 53, .eq)
#guard C "-1260" 360 53 == (F "-1" 53, .eq)
#guard C "1/3" 1 7 .Floor == (F "-1/2" 7, .eq)

-- correctly rounded irrational values
#guard C "1/3" 7 53 == (F "8607034664127685/9007199254740992" 53, .lt)
#guard C "1/3" 7 53 .Ceiling == (F "4303517332063843/4503599627370496" 53, .gt)
#guard C "22/7" 360 53 == (F "562103242988201/562949953421312" 53, .lt)
#guard C "-22/7" 360 53 == (F "562103242988201/562949953421312" 53, .lt)
#guard C "22/7" 360 53 .Ceiling == (F "8993651887811217/9007199254740992" 53, .gt)
#guard C "1/10" 1 53 == (F "910872158600853/1125899906842624" 53, .gt)
#guard C "1/10" 1 53 .Floor == (F "7286977268806823/9007199254740992" 53, .lt)
#guard C "3000000000000000000000000000001/3" 360 53
  == (F "403915659193835/2251799813685248" 53, .lt)
#guard toString (cosRatWithPeriod (Q "22/7") 360 200)
  == "0.9984959401311517674613121977046275966008758908100819199996446"

-- agreement with the float variant at representable arguments
#guard C "45" 360 53 == cosWithPeriodPrecRound (F "45" 53) 360 53 .Nearest
#guard C "5/2" 7 53 == cosWithPeriodPrecRound (F "5/2" 53) 7 53 .Nearest
#guard C "1" 1000 53 .Floor == cosWithPeriodPrecRound (F "1" 53) 1000 53 .Floor

-- a tiny argument (`1/(3·2^1000)`): rounded without touching the argument
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard cosRatWithPeriodPrecRound tinyQ 360 53 .Nearest == (F "1" 53, .gt)
#guard cosRatWithPeriodPrecRound (-tinyQ) 1 53 .Floor == (belowOne, .lt)
