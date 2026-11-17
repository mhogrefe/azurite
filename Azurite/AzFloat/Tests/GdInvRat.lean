/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GdInv
import Azurite.AzFloat.GdInvRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the inverse Gudermannian of a rational

`gd⁻¹ 0 = 0`, `p = 0`; the domain test on either side of `π/2` (`157/100`, `1570796/10^6`
inside; `1570797/10^6`, `355/226`, `11/7`, `2`, `−100` outside); the correctly rounded 53-bit
values from `1/1000` to `1570796/10^6`; 200- and 300-bit results; directed rounding and
oddness; a tiny argument; agreement with the float function on dyadic arguments.  References:
a 500-digit evaluation of `ln ((1 + sin q)/cos q)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  gdInvRatPrecRound (Q q) p m

-- special values
#guard A "0" 53 == (zero, .eq)
#guard A "0" 0 == (zero, .eq)
#guard A "1/3" 0 == (nan, .eq)

-- the domain `|q| < π/2`
#guard gdInvRatInDomain (Q "1/3") && gdInvRatInDomain (Q "-1") && gdInvRatInDomain (Q "3/2")
#guard gdInvRatInDomain (Q "157/100") && gdInvRatInDomain (Q "-1570796/1000000")
#guard !gdInvRatInDomain (Q "1570797/1000000") && !gdInvRatInDomain (Q "355/226")
#guard !gdInvRatInDomain (Q "-11/7") && !gdInvRatInDomain (Q "2") && !gdInvRatInDomain (Q "5")
#guard A "1570797/1000000" 53 == (nan, .eq)
#guard A "355/226" 53 == (nan, .eq)
#guard A "11/7" 53 == (nan, .eq)
#guard A "-11/7" 53 == (nan, .eq)
#guard A "2" 53 == (nan, .eq)
#guard A "-100" 53 == (nan, .eq)
#guard A "100000000000000000000000000000000000000000000000000/3" 53 == (nan, .eq)

-- correctly rounded 53-bit values
#guard A "1/1000" 53 == (F "1152921696760479/1152921504606846976" 53, .lt)
#guard A "1/3" 53 == (F "3059595851913389/9007199254740992" 53, .gt)
#guard A "-2/3" 53 == (F "-3253225987630997/4503599627370496" 53, .gt)
#guard A "7/5" 53 == (F "5534914012441035/2251799813685248" 53, .lt)
#guard A "157/100" 53 == (F "8814274096388059/1125899906842624" 53, .lt)
#guard A "-157/100" 53 == (F "-8814274096388059/1125899906842624" 53, .gt)
#guard A "1570796/1000000" 53 == (F "2199316027648309/140737488355328" 53, .lt)

-- other precisions, directed rounding, oddness
#guard A "1/3" 200 == (F ("1091700280064027489452961987697949026146073660203580064022519"
  ++ "/3213876088517980551083924184682325205044405987565585670602752") 200, .gt)
#guard A "157/100" 300 == (F ("199340471236548975226151166404321340264102644485421478935181"
  ++ "3134356351476933956428390206617/2546294970418107607835557110511722701314335492082420313"
  ++ "29517556169297662470417088272924672") 300, .gt)
#guard A "1/3" 53 .Floor == (F "6119191703826777/18014398509481984" 53, .lt)
#guard (A "-7/5" 53 .Ceiling).1 == -(A "7/5" 53 .Floor).1

-- a tiny argument: the value is just outside `q`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard (gdInvRatPrecRound tinyQ 53 .Floor) == ofAzRatRound tinyQ 53 .Floor
#guard (gdInvRatPrecRound tinyQ 53 .Ceiling).2 == .gt

-- agreement with the float function on dyadic arguments
#guard A "3/8" 53 == gdInvPrecRound (F "3/8" 53) 53 .Nearest
#guard A "1" 53 == gdInvPrecRound (F "1" 53) 53 .Nearest
#guard A "-5/4" 53 .Floor == gdInvPrecRound (F "-5/4" 53) 53 .Floor
#guard A "3/2" 100 == gdInvPrecRound (F "3/2" 53) 100 .Nearest
#guard A "201/128" 53 .Ceiling == gdInvPrecRound (F "201/128" 53) 53 .Ceiling
