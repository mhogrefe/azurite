/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin (x) u / (2π)`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`, also for `u = 0`; `0`; `u = 0`; a
quarter turn `±u/4` at `±1`; a twelfth of a turn `±u/12` at `±1/2` — exact for `u = 360`, the
correctly rounded rational for `u = 7`, `1`, `10` in all modes; `p = 0`), the correctly rounded
53-bit values in degrees, other periods (`1`, `7`, `400`, `2^64 − 1`), the directed modes, 1-,
20- and 113-bit results, a 200-bit string, the neighbour `1 − 2^(−53)` of `1`, and tiny
arguments `2⁻²⁰⁰`, `±2^(−2^30)` (no cost in the exponent).  References: an independent 1400-bit
fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinWithPeriodPrecRound x u p m

-- special values
#guard W nan 360 53 == (nan, .eq)
#guard W (infinity true) 360 53 == (nan, .eq)
#guard W (infinity false) 0 53 == (nan, .eq)
#guard W (F "2" 53) 360 53 == (nan, .eq)
#guard W (F "-3/2" 53) 0 53 == (nan, .eq)
#guard W zero 360 53 == (zero, .eq)
#guard W zero 360 0 == (zero, .eq)
#guard W (F "3/4" 53) 0 53 == (zero, .eq)
#guard W (F "-1" 53) 0 53 == (zero, .eq)
#guard W (F "1/2" 53) 0 53 == (zero, .eq)
#guard W (F "3/4" 53) 360 0 == (nan, .eq)
-- a quarter turn
#guard W (F "1" 53) 360 53 == (F "90" 53, .eq)
#guard W (F "-1" 200) 360 53 == (F "-90" 53, .eq)
#guard W (F "1" 53) 1 53 == (F "1/4" 53, .eq)
#guard W (F "1" 53) 7 1 == (F "2" 1, .gt)
#guard W (F "-1" 53) 7 1 .Ceiling == (F "-1" 1, .gt)
-- a twelfth of a turn
#guard W (F "1/2" 53) 360 53 == (F "30" 53, .eq)
#guard W (F "-1/2" 200) 360 53 == (F "-30" 53, .eq)
#guard W (F "1/2" 53) 3 53 == (F "1/4" 53, .eq)
#guard W (F "1/2" 53) 7 53 == (F "5254199565265579/9007199254740992" 53, .gt)
#guard W (F "1/2" 53) 7 53 .Floor == (F "2627099782632789/4503599627370496" 53, .lt)
#guard W (F "-1/2" 53) 7 53 == (F "-5254199565265579/9007199254740992" 53, .lt)
#guard W (F "-1/2" 53) 7 53 .Ceiling == (F "-2627099782632789/4503599627370496" 53, .gt)
#guard W (F "1/2" 53) 1 53 == (F "6004799503160661/72057594037927936" 53, .lt)
#guard W (F "1/2" 53) 1 53 .Ceiling == (F "3002399751580331/36028797018963968" 53, .gt)
#guard W (F "-1/2" 53) 10 53 .Floor == (F "-7505999378950827/9007199254740992" 53, .lt)

-- correctly rounded values
#guard W (F "1/3" 53) 360 53 == (F "42817666989229/2199023255552" 53, .gt)
#guard W (F "-7/10" 53) 360 53 == (F "-6252544958225503/140737488355328" 53, .lt)
#guard W (F "3/4" 53) 360 53 == (F "854810967822185/17592186044416" 53, .gt)
#guard W (F "9/10" 53) 360 53 == (F "4514722620322059/70368744177664" 53, .gt)
#guard W (F "1/1024" 53) 360 53 == (F "8063665383717305/144115188075855872" 53, .lt)
#guard W (F "999999/1000000" 53) 360 53 == (F "6327485103946765/70368744177664" 53, .gt)
#guard W (F "5/7" 53) 360 53 == (F "3207737487741887/70368744177664" 53, .lt)
#guard W (F "3/4" 53) 1 53 == (F "4862924616943985/36028797018963968" 53, .lt)
#guard W (F "3/4" 53) 7 53 == (F "8510118079651975/9007199254740992" 53, .gt)
#guard W (F "3/4" 53) 400 53 == (F "7598319713974977/140737488355328" 53, .lt)
#guard W (F "3/4" 53) 18446744073709551615 53 == (F "2489817403875320320" 53, .lt)
#guard W (F "3/4" 53) 360 53 .Floor == (F "6838487742577479/140737488355328" 53, .lt)
#guard W (F "-1/3" 53) 360 53 .Floor == (F "-42817666989229/2199023255552" 53, .lt)
#guard W (F "3/4" 53) 360 53 .Ceiling == (F "854810967822185/17592186044416" 53, .gt)
#guard W (F "-1/3" 53) 360 53 .Ceiling == (F "-5480661374621311/281474976710656" 53, .gt)
#guard W (F "3/4" 53) 360 20 == (F "796105/16384" 20, .gt)
#guard W (F "3/4" 53) 360 1 == (F "64" 1, .gt)
#guard W (F "3/4" 53) 360 113
  == (F "3942119788703954077539797759335803/81129638414606681695789005144064" 113, .lt)
#guard asinWithPeriod (F "3/4" 53) 360 == (W (F "3/4" 53) 360 53).1
#guard (toString (asinWithPeriodPrecRound (F "3/4" 200) 360 200 .Nearest).1).startsWith
  "48.59037789072914066151949781307427925821594885127146162"

-- next to `1`, small and tiny arguments
#guard W (F "9007199254740991/9007199254740992" 53) 360 53
  == (F "6333186915910781/70368744177664" 53, .gt)
#guard W (powerOf2 (AzInt.ofInt (-200))) 360 53 == (F ("1007958012753983/"
  ++ "28269553036454149273332760011886696253239742350009903329945699220681916416") 53, .gt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard (W tiny 360 53).1 == (F "1007958012753983/17592186044416" 53) <<< AzInt.ofInt (-1073741824)
#guard (W tiny 360 53).2 == .gt
#guard (W (-tiny) 360 53 .Floor).2 == .lt
