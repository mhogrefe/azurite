/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Lambert `W` function of a rational

The special values (`0`, below the branch point — `−3678794412/10¹⁰ < −e⁻¹` —, `W₋₁` of a
positive rational, `p = 0`), `W₀` and `W₋₁` at exact rationals (`1/10`, `1/3`, `22/7`, `10¹²`,
`−1/10`, `−1/3`, `−9/25`, `−10⁻³⁰`, and `−3678794411/10¹⁰` just above `−e⁻¹`, `q ≈ 1.9·10⁻¹⁰`) in
the three modes with 120-digit references, agreement with the float versions on exactly
representable arguments, and 200-bit values.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W0 (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lambertW0RatPrecRound (Q q) p m
private def Wm (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lambertWm1RatPrecRound (Q q) p m
private def ninf : AzFloat := infinity false

-- special values
#guard W0 "0" 53 == (zero, .eq)
#guard W0 "0" 0 == (zero, .eq)
#guard W0 "1" 0 == (nan, .eq)
#guard W0 "-1" 53 == (nan, .eq)
#guard W0 "-3678794412/10000000000" 53 == (nan, .eq)
#guard Wm "0" 53 == (ninf, .eq)
#guard Wm "0" 0 == (ninf, .eq)
#guard Wm "-1/4" 0 == (nan, .eq)
#guard Wm "1/2" 53 == (nan, .eq)
#guard Wm "-1" 53 == (nan, .eq)
#guard Wm "-3678794412/10000000000" 53 == (nan, .eq)

-- `W₀`
#guard W0 "1/10" 53 == (F "1644291734837329/18014398509481984" 53, .lt)
#guard W0 "1/10" 53 .Ceiling == (F "6577166939349317/72057594037927936" 53, .gt)
#guard W0 "1/3" 53 == (F "4641007209100519/18014398509481984" 53, .gt)
#guard W0 "1/3" 53 .Ceiling == (F "4641007209100519/18014398509481984" 53, .gt)
#guard W0 "22/7" 53 == (F "604533130441529/562949953421312" 53, .lt)
#guard W0 "22/7" 53 .Ceiling == (F "4836265043532233/4503599627370496" 53, .gt)
#guard W0 "1000000000000" 53 == (F "6877842295803831/281474976710656" 53, .lt)
#guard W0 "-1/10" 53 == (F "-8058385148099113/72057594037927936" 53, .lt)
#guard W0 "-1/10" 53 .Floor == (F "-8058385148099113/72057594037927936" 53, .lt)
#guard W0 "-1/3" 53 == (F "-1394002090131751/2251799813685248" 53, .gt)
#guard W0 "-1/3" 53 .Ceiling == (F "-1394002090131751/2251799813685248" 53, .gt)
#guard W0 "-9/25" 53 == (F "-226892564064711/281474976710656" 53, .gt)
#guard W0 "-9/25" 53 .Ceiling == (F "-226892564064711/281474976710656" 53, .gt)
#guard W0 "-3678794411/10000000000" 53 == (F "-9007021743060493/9007199254740992" 53, .gt)
#guard W0 "-3678794411/10000000000" 53 .Ceiling == (F "-9007021743060493/9007199254740992" 53, .gt)
#guard W0 "-1/1000000000000000000000000000000" 53
  == (F ("-178405961588245/"
      ++ "178405961588244985132285746181186892047843328") 53, .lt)
#guard W0 "-1/1000000000000000000000000000000" 53 .Floor
  == (F ("-178405961588245/"
      ++ "178405961588244985132285746181186892047843328") 53, .lt)

-- `W₋₁`
#guard Wm "-1/10" 53 == (F "-4027515175571421/1125899906842624" 53, .gt)
#guard Wm "-1/10" 53 .Floor == (F "-8055030351142843/2251799813685248" 53, .lt)
#guard Wm "-1/3" 53 == (F "-6810048603380311/4503599627370496" 53, .gt)
#guard Wm "-1/3" 53 .Floor == (F "-851256075422539/562949953421312" 53, .lt)
#guard Wm "-9/25" 53 == (F "-5506867119745371/4503599627370496" 53, .lt)
#guard Wm "-9/25" 53 .Ceiling == (F "-2753433559872685/2251799813685248" 53, .gt)
#guard Wm "-3678794411/10000000000" 53 == (F "-281480524023555/281474976710656" 53, .lt)
#guard Wm "-3678794411/10000000000" 53 .Floor == (F "-281480524023555/281474976710656" 53, .lt)
#guard Wm "-1/1000000000000000000000000000000" 53 == (F "-5163173629192929/70368744177664" 53, .lt)
#guard Wm "-1/1000000000000000000000000000000" 53 .Ceiling
  == (F "-161349175912279/2199023255552" 53, .gt)

-- agreement with the float versions on exactly representable arguments
#guard W0 "1/2" 53 == lambertW0PrecRound (F "1/2" 53) 53 .Nearest
#guard W0 "-1/4" 53 .Floor == lambertW0PrecRound (F "-1/4" 53) 53 .Floor
#guard Wm "-1/4" 53 == lambertWm1PrecRound (F "-1/4" 53) 53 .Nearest
#guard Wm "-1/8" 200 .Ceiling == lambertWm1PrecRound (F "-1/8" 200) 200 .Ceiling

-- 200 bits and the nearest wrappers
#guard W0 "1/10" 200
  == (F ("1173405792341028906139124517580972948113092057743531025989059/"
      ++ "12855504354071922204335696738729300820177623950262342682411008") 200, .lt)
#guard Wm "-1/3" 200
  == (F ("-1214953269548749243227066924998659316131119544475694165847435/"
      ++ "803469022129495137770981046170581301261101496891396417650688") 200, .lt)
#guard lambertW0Rat (Q "1/10") 53 == (W0 "1/10" 53).1
#guard lambertWm1Rat (Q "-1/3") 53 == (Wm "-1/3" 53).1
