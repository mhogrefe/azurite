/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsc
import Azurite.AzFloat.AcscRat
import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccsc q` of a rational, plain and with a period

`acscRat`: the special values (`arccsc (±1) = ±π/2`; `|q| < 1` gives `NaN`, including `0`;
`p = 0`), the correctly rounded 53-bit values at exact rationals, agreement with the float
`acsc` at representable arguments, oddness, the directed modes, 20- and 113-bit results, a
200-bit string, the rationals `±(1 + 2^(−200))` next to `±1`, and huge rationals `±2^5000`,
`±3·2^5000`.

`acscRatWithPeriod`: the special values (`NaN` for `|q| < 1`, also for `u = 0`; `±u/4` at `±1`;
`u = 0`; `±u/12` at `±2`, exact or correctly rounded; `p = 0`), the correctly rounded 53-bit
values in degrees, other periods, the directed modes, a 20-bit result, a 200-bit string, and
huge rationals.

References: an independent 1400-bit fixed-point evaluation of `arcsin (1/q)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscRatPrecRound (Q q) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscRatWithPeriodPrecRound (Q q) u p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard T "1" 53 == (h piN (-1), .lt)
#guard T "1" 53 .Ceiling == (h piC (-1), .gt)
#guard T "-1" 53 == (-(h piN (-1)), .gt)
#guard T "-1" 53 .Floor == (-(h piC (-1)), .lt)
#guard T "0" 53 == (nan, .eq)
#guard T "1/2" 53 == (nan, .eq)
#guard T "-999999/1000000" 53 == (nan, .eq)
#guard T "3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "3" 53 == (F "3060978757568649/9007199254740992" 53, .lt)
#guard T "-3" 53 == (F "-3060978757568649/9007199254740992" 53, .gt)
#guard T "3/2" 53 == (F "3286401200665711/4503599627370496" 53, .lt)
#guard T "-7/5" 53 == (F "-7166154329695639/9007199254740992" 53, .lt)
#guard T "22/7" 53 == (F "5833260670897689/18014398509481984" 53, .gt)
#guard T "1000001/1000000" 53 == (F "1766967175752421/1125899906842624" 53, .lt)
#guard T "-1000001/1000000" 53 == (F "-1766967175752421/1125899906842624" 53, .gt)
#guard T "1000000007/3" 53 == (F "7253554866912891/2417851639229258349412352" 53, .gt)
#guard T "355/113" 53 == (F "5835693752244025/18014398509481984" 53, .lt)
#guard T "2" 53 == (F "2358079250676147/4503599627370496" 53, .gt)
#guard T "-2" 53 == (F "-2358079250676147/4503599627370496" 53, .lt)
#guard T "3" 53 .Floor == (F "3060978757568649/9007199254740992" 53, .lt)
#guard T "-3/2" 53 .Floor == (F "-6572802401331423/9007199254740992" 53, .lt)
#guard T "3" 53 .Ceiling == (F "6121957515137299/18014398509481984" 53, .gt)
#guard T "-3/2" 53 .Ceiling == (F "-3286401200665711/4503599627370496" 53, .gt)
#guard T "3" 20 == (F "356345/1048576" 20, .gt)
#guard T "3/2" 113
  == (F "7577925234026520191382024829077409/10384593717069655257060992658440192" 113, .gt)

-- agreement with the float `acsc` at representable arguments, oddness
#guard T "2" 53 == acscPrecRound (F "2" 53) 53 .Nearest
#guard T "-3/2" 53 .Floor == acscPrecRound (F "-3/2" 53) 53 .Floor
#guard acscRat (Q "3") 53 == (T "3" 53).1
#guard (T "-22/7" 53 .Floor).1 == -(T "22/7" 53 .Ceiling).1
#guard (toString (acscRat (Q "3") 200)).startsWith
  "0.33983690945412193709639251339176406638824469033245807"

-- rationals next to `±1`, and huge rationals
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 + pw 200
#guard acscRatPrecRound near1 53 .Nearest == (h piN (-1), .lt)
#guard acscRatPrecRound (-near1) 53 .Nearest == (-(h piN (-1)), .gt)
#guard acscRatPrecRound (-near1) 53 .Floor == (-(h piC (-1)), .lt)
#guard acscRatPrecRound (pw 5000)⁻¹ 53 .Nearest == (h (F "1" 53) (-5000), .lt)
#guard acscRatPrecRound (pw 5000)⁻¹ 53 .Ceiling
  == (h (F "4503599627370497/4503599627370496" 53) (-5000), .gt)
#guard acscRatPrecRound (-(pw 5000)⁻¹) 53 .Ceiling == (-(h (F "1" 53) (-5000)), .gt)
#guard acscRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)

-- with a period: special values
#guard R "0" 360 53 == (nan, .eq)
#guard R "1/2" 0 53 == (nan, .eq)
#guard R "3" 0 53 == (zero, .eq)
#guard R "-3" 0 53 == (zero, .eq)
#guard R "3" 360 0 == (nan, .eq)
#guard R "1" 360 53 == (F "90" 53, .eq)
#guard R "-1" 360 53 == (F "-90" 53, .eq)
#guard R "2" 360 53 == (F "30" 53, .eq)
#guard R "-2" 360 53 == (F "-30" 53, .eq)
#guard R "4/2" 7 53 == (F "5254199565265579/9007199254740992" 53, .gt)
#guard R "-2" 7 53 .Floor == (F "-5254199565265579/9007199254740992" 53, .lt)

-- with a period: correctly rounded values
#guard R "3" 360 53 == (F "42817666989229/2199023255552" 53, .gt)
#guard R "-3" 360 53 == (F "-42817666989229/2199023255552" 53, .lt)
#guard R "3/2" 360 53 == (F "5884278705777237/140737488355328" 53, .lt)
#guard R "-7/5" 360 53 == (F "-3207737487741887/70368744177664" 53, .gt)
#guard R "22/7" 360 53 == (F "5222206519407635/281474976710656" 53, .gt)
#guard R "1000000007/3" 360 53 == (F "3246860002661611/18889465931478580854784" 53, .gt)
#guard R "3" 1 53 == (F "7794718399461421/144115188075855872" 53, .lt)
#guard R "3" 7 53 == (F "852547324941093/2251799813685248" 53, .gt)
#guard R "3" 400 53 == (F "6089623749579235/281474976710656" 53, .lt)
#guard R "-3" 360 53 .Floor == (F "-42817666989229/2199023255552" 53, .lt)
#guard R "-3" 360 53 .Ceiling == (F "-5480661374621311/281474976710656" 53, .gt)
#guard R "3" 360 20 == (F "638033/32768" 20, .gt)
#guard R "3/2" 360 53 == acscWithPeriodPrecRound (F "3/2" 53) 360 53 .Nearest
#guard acscRatWithPeriod (Q "3") 360 53 == (R "3" 360 53).1
#guard (toString (acscRatWithPeriod (Q "3") 360 200)).startsWith
  "19.47122063449069136924599933996243596300684310090794828"
#guard acscRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest
  == (h (F "1007958012753983/17592186044416" 53) (-5000), .gt)
#guard acscRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Floor
  == (h (F "8063664102031863/140737488355328" 53) (-5000), .lt)
#guard acscRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Nearest
  == (-(h (F "1007958012753983/17592186044416" 53) (-5000)), .lt)
