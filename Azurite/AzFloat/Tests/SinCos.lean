/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCos
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinCos`

The special values, the correctly rounded 53-bit pairs `(sin x, cos x)` at `1/2`, `±1`, `3`,
`1/1024`, `100`, `−1000`, `10¹²`, `2⁶⁰`, the 53-bit floats nearest `−7/5`, `22/7` and `π`
(reference values of `Tests/Sin.lean` and `Tests/Cos.lean`), the directed modes, a 20-bit result,
200-bit and 2000-bit values, the agreement with `sinPrecRound` and `cosPrecRound` on a sweep of
arguments covering all the octants and both signs, small arguments on the ordinary path, tiny
arguments (delegated), and `2^1000`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def SC (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinCosPrecRound x p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosPrecRound x p m == (sinPrecRound x p m, cosPrecRound x p m)

-- special values
#guard SC nan 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity true) 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity false) 53 == ((nan, .eq), (nan, .eq))
#guard SC zero 53 == ((zero, .eq), (F "1" 53, .eq))
#guard SC zero 0 == ((zero, .eq), (nan, .eq))
#guard SC (F "1" 53) 0 == ((nan, .eq), (nan, .eq))

-- correctly rounded values
#guard SC (F "1/2" 53) 53 == ((F "539785169252447/1125899906842624" 53, .gt),
  (F "494035062339541/562949953421312" 53, .gt))
#guard SC (F "1" 53) 53 == ((F "3789648413623927/4503599627370496" 53, .lt),
  (F "1216652631687587/2251799813685248" 53, .gt))
#guard SC (F "-1" 53) 53 == ((F "-3789648413623927/4503599627370496" 53, .gt),
  (F "1216652631687587/2251799813685248" 53, .gt))
#guard SC (F "3" 53) 53 == ((F "5084384125703515/36028797018963968" 53, .lt),
  (F "-4458529838789353/4503599627370496" 53, .gt))
#guard SC (F "1/1024" 53) 53 == ((F "9007197823085295/9223372036854775808" 53, .gt),
  (F "9007194959774037/9007199254740992" 53, .lt))
#guard SC (F "100" 53) 53 == ((F "-570117028153783/1125899906842624" 53, .gt),
  (F "7767077903818719/9007199254740992" 53, .lt))
#guard SC (F "-1000" 53) 53 == ((F "-7447868781240427/9007199254740992" 53, .gt),
  (F "5065460396847547/9007199254740992" 53, .lt))
#guard SC (F "1000000000000" 53) 53 == ((F "-2752774392258985/4503599627370496" 53, .gt),
  (F "7128714540216867/9007199254740992" 53, .lt))
#guard SC (F "1152921504606846976" 53) 53 == ((F "-1870455753513367/2251799813685248" 53, .gt),
  (F "-5015173257324871/9007199254740992" 53, .gt))
#guard SC (F "-7/5" 53) 53 == ((F "-4438071036768385/4503599627370496" 53, .gt),
  (F "6123711691446027/36028797018963968" 53, .gt))
#guard SC (F "22/7" 53) 53 == ((F "-5831425920677151/4611686018427387904" 53, .lt),
  (F "-4503596026893703/4503599627370496" 53, .lt))

-- directed modes and other precisions
#guard SC (F "1" 53) 53 .Floor == ((F "3789648413623927/4503599627370496" 53, .lt),
  (F "4866610526750347/9007199254740992" 53, .lt))
#guard SC (F "1" 53) 53 .Ceiling == ((F "7579296827247855/9007199254740992" 53, .gt),
  (F "1216652631687587/2251799813685248" 53, .gt))
#guard SC (F "3" 53) 20 == ((F "147975/1048576" 20, .lt), (F "-519041/524288" 20, .gt))
#guard sinCos (F "1" 53) == (F "3789648413623927/4503599627370496" 53,
  F "1216652631687587/2251799813685248" 53)
#guard (toString (sinCos (F "1" 200)).1).startsWith
  "0.84147098480789650665250232163029899962256306079837106567275"
#guard (toString (sinCos (F "1" 200)).2).startsWith
  "0.54030230586813971740093660744297660373231042061792222767"
#guard (toString (sinCos (F "100" 200)).1).startsWith
  "-0.5063656411097587936565576104597854320650327212906573234433"

-- near a multiple of `π`: the 53-bit float nearest `π`
private def pi53 : AzFloat := F "884279719003555/281474976710656" 53
#guard SC pi53 53 == ((F "4967757600021511/40564819207303340847894502572032" 53, .gt),
  (F "-1" 53, .lt))
#guard agrees (-pi53) 53 .Ceiling

-- agreement with the separate functions: all the octants, both signs, several modes
#guard (List.range 26).all fun i => agrees (F s!"{i + 1}/4" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"-{i + 1}/4" 53) 53 .Floor
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 13).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 40 .Down
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (F "1" 53) 1
#guard agrees (F "12345678901234567890/1000000007" 100) 300
#guard agrees (F "1/3" 2000) 2000

-- small arguments on the ordinary path, tiny arguments (delegated) and a huge argument
#guard agrees (F "1/1099511627776" 53) 53
#guard agrees (F "1/1099511627776" 53) 53 .Floor
private def tinyX : AzFloat := (F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard SC tinyX 53 == ((tinyX, .gt), (F "1" 53, .gt))
#guard agrees (-tinyX) 53 .Floor
#guard agrees ((F "1" 53) <<< AzInt.ofInt (-200)) 53
#guard SC ((F "1" 53) <<< AzInt.ofInt 1000) 53 |>.1
  |> (· == (F "-2867922922783799/18014398509481984" 53, .gt))
