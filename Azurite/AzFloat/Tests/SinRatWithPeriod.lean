/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def S (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinRatWithPeriodPrecRound (Q q) u p m
private def half : AzFloat := F "1/2" 53
private def nhalf : AzFloat := F "-1/2" 53

-- special values
#guard S "1/3" 0 53 == (nan, .eq)
#guard S "0" 0 53 == (nan, .eq)
#guard S "1/3" 360 0 == (nan, .eq)
#guard S "0" 360 0 == (zero, .eq)
#guard S "0" 360 53 == (zero, .eq)

-- exact values
#guard S "1/12" 1 53 == (half, .eq)
#guard S "5/12" 1 53 == (half, .eq)
#guard S "7/12" 1 53 == (nhalf, .eq)
#guard S "11/12" 1 53 == (nhalf, .eq)
#guard S "-1/12" 1 53 == (nhalf, .eq)
#guard S "-7/12" 1 53 == (half, .eq)
#guard S "1/4" 1 53 == (F "1" 53, .eq)
#guard S "-1/4" 1 53 == (F "-1" 53, .eq)
#guard S "3/4" 1 53 == (F "-1" 53, .eq)
#guard S "1/2" 1 53 == (zero, .eq)
#guard S "7/12" 7 53 == (half, .eq)
#guard S "1001/7" 13 53 == (zero, .eq)
#guard S "45/2" 90 53 == (F "1" 53, .eq)
#guard S "-45/2" 90 53 == (F "-1" 53, .eq)
#guard S "30" 360 53 == (half, .eq)
#guard S "-1350" 360 53 == (F "1" 53, .eq)
#guard S "1/12" 1 7 .Floor == (F "1/2" 7, .eq)

-- correctly rounded irrational values
#guard S "1/3" 7 53 == (F "5309837174569895/18014398509481984" 53, .lt)
#guard S "1/3" 7 53 .Ceiling == (F "663729646821237/2251799813685248" 53, .gt)
#guard S "22/7" 360 53 == (F "7901216278647547/144115188075855872" 53, .gt)
#guard S "-22/7" 360 53 == (F "-7901216278647547/144115188075855872" 53, .lt)
#guard S "22/7" 360 53 .Floor == (F "3950608139323773/72057594037927936" 53, .lt)
#guard S "-22/7" 360 53 .Floor == (F "-7901216278647547/144115188075855872" 53, .lt)
#guard S "1/10" 1 53 == (F "2647149443198255/4503599627370496" 53, .gt)
#guard S "1/10" 1 53 .Floor == (F "5294298886396509/9007199254740992" 53, .lt)
#guard S "1/3" 1 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard S "-2/3" 1 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard S "1/7" 1 53 == (F "7042111946219083/9007199254740992" 53, .lt)
#guard S "3000000000000000000000000000001/3" 360 53
  == (F "-2215277531410213/2251799813685248" 53, .gt)
#guard toString (sinRatWithPeriod (Q "1/7") 1 200)
  == "0.781831482468029808708444526674057750232334518708687528980635"

-- agreement with the float variant at representable arguments
#guard S "45" 360 53 == sinWithPeriodPrecRound (F "45" 53) 360 53 .Nearest
#guard S "-5/2" 7 53 == sinWithPeriodPrecRound (F "-5/2" 53) 7 53 .Nearest
#guard S "1" 1000 53 .Floor == sinWithPeriodPrecRound (F "1" 53) 1000 53 .Floor

-- the tiny path (`±1/(3·2^1000)`): `sin y` rounds like a value just below `y = 2πq/u`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyE : AzInt := AzInt.ofInt (-1000)
private def degLo : AzFloat := (F "1676856356036371/288230376151711744" 53) <<< tinyE
private def degHi : AzFloat := (F "6707425424145485/1152921504606846976" 53) <<< tinyE
private def turnLo : AzFloat := (F "4716158501352293/2251799813685248" 53) <<< tinyE
private def turnHi : AzFloat := (F "2358079250676147/1125899906842624" 53) <<< tinyE
#guard sinRatWithPeriodPrecRound tinyQ 360 53 .Nearest == (degLo, .lt)
#guard sinRatWithPeriodPrecRound tinyQ 360 53 .Ceiling == (degHi, .gt)
#guard sinRatWithPeriodPrecRound (-tinyQ) 360 53 .Nearest == (-degLo, .gt)
#guard sinRatWithPeriodPrecRound (-tinyQ) 360 53 .Floor == (-degHi, .lt)
#guard sinRatWithPeriodPrecRound tinyQ 1 53 .Nearest == (turnHi, .gt)
#guard sinRatWithPeriodPrecRound tinyQ 1 53 .Floor == (turnLo, .lt)
#guard (sinPeriodTiny? false tinyQ.num (tinyQ.den * AzNat.ofNat 360) (AzInt.ofInt 0)
  (ratExpBound tinyQ + AzInt.ofInt 2) 53 .Nearest).isSome
