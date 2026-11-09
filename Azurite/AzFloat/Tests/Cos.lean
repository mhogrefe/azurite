/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cos`

The special values (`NaN`, `±∞`, `cos 0 = 1`, `p = 0`), the correctly rounded 53-bit values of
`cos (1/2)`, `cos (±1)`, `cos 3`, `cos (1/1024)`, `cos 100`, `cos (−1000)`, `cos 10¹²`,
`cos 2⁶⁰`, `cos` of the 53-bit floats nearest `−7/5`, `22/7` and `π`, and `cos 2⁻¹⁰⁰` (both
round to `±1`), the directed modes, a 20-bit result, and 200-bit values of `cos 1` and `cos 100`.
References: a 240-digit evaluation (Machin `π`, exact reduction, Taylor series) at the exact
float arguments, rounded to 53 bits with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def C (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cosPrecRound x p m

-- special values
#guard C nan 53 == (nan, .eq)
#guard C (infinity true) 53 == (nan, .eq)
#guard C (infinity false) 53 == (nan, .eq)
#guard C zero 53 == (F "1" 53, .eq)
#guard C zero 0 == (nan, .eq)
#guard C (F "1" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard C (F "1/2" 53) 53 == (F "494035062339541/562949953421312" 53, .gt)
#guard C (F "1" 53) 53 == (F "1216652631687587/2251799813685248" 53, .gt)
#guard C (F "-1" 53) 53 == (F "1216652631687587/2251799813685248" 53, .gt)
#guard C (F "3" 53) 53 == (F "-4458529838789353/4503599627370496" 53, .gt)
#guard C (F "1/1024" 53) 53 == (F "9007194959774037/9007199254740992" 53, .lt)
#guard C (F "100" 53) 53 == (F "7767077903818719/9007199254740992" 53, .lt)
#guard C (F "-1000" 53) 53 == (F "5065460396847547/9007199254740992" 53, .lt)
#guard C (F "1000000000000" 53) 53 == (F "7128714540216867/9007199254740992" 53, .lt)
#guard C (F "1152921504606846976" 53) 53 == (F "-5015173257324871/9007199254740992" 53, .gt)
#guard C (F "-7/5" 53) 53 == (F "6123711691446027/36028797018963968" 53, .gt)
#guard C (F "22/7" 53) 53 == (F "-4503596026893703/4503599627370496" 53, .lt)
#guard C (F "884279719003555/281474976710656" 53) 53 == (F "-1" 53, .lt)
#guard C (F "1/1267650600228229401496703205376" 53) 53 == (F "1" 53, .gt)

-- directed modes and other precisions
#guard C (F "1" 53) 53 .Floor == (F "4866610526750347/9007199254740992" 53, .lt)
#guard C (F "1" 53) 53 .Ceiling == (F "1216652631687587/2251799813685248" 53, .gt)
#guard C (F "3" 53) 53 .Floor == (F "-8917059677578707/9007199254740992" 53, .lt)
#guard C (F "3" 53) 53 .Ceiling == (F "-4458529838789353/4503599627370496" 53, .gt)
#guard C (F "3" 53) 20 == (F "-519041/524288" 20, .gt)
#guard cos (F "1" 53) == F "1216652631687587/2251799813685248" 53
#guard toString (cos (F "1" 200))
  == "0.540302305868139717400936607442976603732310420617922227670097"
#guard toString (cos (F "100" 200))
  == "0.862318872287683934101938513950842535510084008535510829280162"
