/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccos (x) u / (2π)`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`, also for `u = 0`; `u/4` at `0`;
`u = 0`; `0` at `1`; `u/2` at `−1`; `u/6` at `1/2` and `u/3` at `−1/2` — exact for `u = 360`,
the correctly rounded rationals for `u = 7`, `1`, `2` in all modes; `p = 0`), the correctly
rounded 53-bit values in degrees, other periods (`1`, `7`, `400`, `2^64 − 1`), the directed
modes, 1-, 20- and 113-bit results, a 200-bit string, the neighbours `±(1 − 2^(−53))` of `±1`,
and tiny arguments `±2⁻²⁰⁰`, `±2^(−2^30)`: values next to the float `u/4`, at no extra cost.
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosWithPeriodPrecRound x u p m

-- special values
#guard W nan 360 53 == (nan, .eq)
#guard W (infinity true) 360 53 == (nan, .eq)
#guard W (infinity false) 0 53 == (nan, .eq)
#guard W (F "2" 53) 360 53 == (nan, .eq)
#guard W (F "-3/2" 53) 0 53 == (nan, .eq)
#guard W (F "3/4" 53) 0 53 == (zero, .eq)
#guard W (F "-1" 53) 0 53 == (zero, .eq)
#guard W zero 0 53 == (zero, .eq)
#guard W (F "3/4" 53) 360 0 == (nan, .eq)
#guard W zero 360 53 == (F "90" 53, .eq)
#guard W zero 1 53 == (F "1/4" 53, .eq)
#guard W zero 7 53 == (F "7/4" 53, .eq)
#guard W zero 7 1 == (F "2" 1, .gt)
#guard W (F "1" 53) 360 53 == (zero, .eq)
#guard W (F "1" 200) 360 0 == (zero, .eq)
#guard W (F "-1" 53) 360 53 == (F "180" 53, .eq)
#guard W (F "-1" 53) 7 53 == (F "7/2" 53, .eq)
#guard W (F "-1" 53) 7 1 == (F "4" 1, .gt)
-- a sixth and a third of a turn
#guard W (F "1/2" 53) 360 53 == (F "60" 53, .eq)
#guard W (F "-1/2" 200) 360 53 == (F "120" 53, .eq)
#guard W (F "1/2" 53) 3 53 == (F "1/2" 53, .eq)
#guard W (F "1/2" 53) 7 53 == (F "5254199565265579/4503599627370496" 53, .gt)
#guard W (F "1/2" 53) 7 53 .Floor == (F "2627099782632789/2251799813685248" 53, .lt)
#guard W (F "1/2" 53) 7 1 == (F "1" 1, .lt)
#guard W (F "1/2" 53) 7 3 == (F "5/4" 3, .gt)
#guard W (F "-1/2" 53) 7 53 == (F "5254199565265579/2251799813685248" 53, .gt)
#guard W (F "-1/2" 53) 7 53 .Floor == (F "2627099782632789/1125899906842624" 53, .lt)
#guard W (F "1/2" 53) 1 53 == (F "6004799503160661/36028797018963968" 53, .lt)
#guard W (F "1/2" 53) 1 53 .Ceiling == (F "3002399751580331/18014398509481984" 53, .gt)
#guard W (F "-1/2" 53) 1 53 == (F "6004799503160661/18014398509481984" 53, .lt)
#guard W (F "-1/2" 53) 2 53 .Ceiling == (F "3002399751580331/4503599627370496" 53, .gt)

-- correctly rounded values
#guard W (F "1/3" 53) 360 53 == (F "155094426010451/2199023255552" 53, .lt)
#guard W (F "-1/3" 53) 360 53 == (F "240729759988909/2199023255552" 53, .gt)
#guard W (F "-7/10" 53) 360 53 == (F "591216215943907/4398046511104" 53, .gt)
#guard W (F "3/4" 53) 360 53 == (F "728485776175255/17592186044416" 53, .lt)
#guard W (F "9/10" 53) 360 53 == (F "7273857422670805/281474976710656" 53, .gt)
#guard W (F "1/1024" 53) 360 53 == (F "6329249639376617/70368744177664" 53, .gt)
#guard W (F "-1/1024" 53) 360 53 == (F "6337124312602903/70368744177664" 53, .lt)
#guard W (F "999999/1000000" 53) 360 53 == (F "2919358486013601/36028797018963968" 53, .lt)
#guard W (F "-999999/1000000" 53) 360 53 == (F "3165168019984131/17592186044416" 53, .lt)
#guard W (F "5/7" 53) 360 53 == (F "3125449488247873/70368744177664" 53, .gt)
#guard W (F "3/4" 53) 1 53 == (F "8288549275594013/72057594037927936" 53, .lt)
#guard W (F "-1/4" 53) 1 53 == (F "5228054277212783/18014398509481984" 53, .gt)
#guard W (F "3/4" 53) 7 53 == (F "7252480616144761/9007199254740992" 53, .lt)
#guard W (F "-1/4" 53) 7 53 == (F "4574547492561185/2251799813685248" 53, .lt)
#guard W (F "3/4" 53) 400 53 == (F "6475429121557823/140737488355328" 53, .gt)
#guard W (F "-1/4" 53) 400 53 == (F "8168834808144973/70368744177664" 53, .lt)
#guard W (F "3/4" 53) 18446744073709551615 53 == (F "2121868614552067328" 53, .lt)
#guard W (F "-1/4" 53) 18446744073709551615 53 == (F "5353527579865889792" 53, .gt)
#guard W (F "3/4" 53) 360 53 .Floor == (F "728485776175255/17592186044416" 53, .lt)
#guard W (F "-1/4" 53) 360 53 .Floor == (F "7351951327330475/70368744177664" 53, .lt)
#guard W (F "3/4" 53) 360 53 .Ceiling == (F "5827886209402041/140737488355328" 53, .gt)
#guard W (F "-1/4" 53) 360 53 .Ceiling == (F "1837987831832619/17592186044416" 53, .gt)
#guard W (F "3/4" 53) 360 20 == (F "678455/16384" 20, .lt)
#guard W (F "-1/4" 53) 360 1 == (F "128" 1, .gt)
#guard W (F "3/4" 53) 360 113
  == (F "3359547668610647275081212703629957/81129638414606681695789005144064" 113, .gt)
#guard acosWithPeriod (F "3/4" 53) 360 == (W (F "3/4" 53) 360 53).1
#guard (toString (acosWithPeriodPrecRound (F "3/4" 200) 360 200 .Nearest).1).startsWith
  "41.40962210927085933848050218692572074178405114872853837"

-- next to `±1`
#guard W (F "9007199254740991/9007199254740992" 53) 360 53
  == (F "1007958012753983/1180591620717411303424" 53, .gt)
#guard W (F "-9007199254740991/9007199254740992" 53) 360 53
  == (F "3166593472975135/17592186044416" 53, .lt)
#guard W (F "-9007199254740991/9007199254740992" 53) 360 53 .Ceiling
  == (F "6333186945950271/35184372088832" 53, .gt)

-- tiny arguments: next to the float `u/4`
private def t200 : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard W t200 360 53 == (F "90" 53, .gt)
#guard W t200 360 53 .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard W (-t200) 360 53 == (F "90" 53, .lt)
#guard W (-t200) 360 53 .Ceiling == (F "6333186975989761/70368744177664" 53, .gt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard W tiny 360 53 == (F "90" 53, .gt)
#guard W tiny 360 53 .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard W (-tiny) 360 53 == (F "90" 53, .lt)
#guard W (-tiny) 360 53 .Ceiling == (F "6333186975989761/70368744177664" 53, .gt)
#guard W (-tiny) 360 53 .Floor == (F "90" 53, .lt)
