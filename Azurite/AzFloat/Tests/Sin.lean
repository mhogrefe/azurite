/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Sin
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sin`

The special values (`NaN`, `±∞`, `sin 0 = 0` at every precision, `p = 0`), the correctly rounded
53-bit values of `sin (1/2)`, `sin (±1)`, `sin 3`, `sin (1/1024)`, `sin 100`, `sin (−1000)`,
`sin 10¹²`, `sin 2⁶⁰`, `sin` of the 53-bit floats nearest `−7/5` and `22/7`, the directed
modes, a 20-bit result, 200-bit values.  Extreme arguments: the 53-bit float nearest `π`
(`sin ≈ 1.2·10⁻¹⁶`: the loop resolves the small result), `2⁻⁴⁰` (the ordinary path next to the
argument), and `±2^(−2^30)`, `(3/2)·2^(−2^30)` at 100 bits (the tiny path, independent of the
exponent), and `2^1000` (a 700-digit `π` for the reference).  References: a 260-digit evaluation
(Machin `π`, exact reduction, Taylor series) at
the exact float arguments, rounded to 53 bits with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def S (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinPrecRound x p m

-- special values
#guard S nan 53 == (nan, .eq)
#guard S (infinity true) 53 == (nan, .eq)
#guard S (infinity false) 53 == (nan, .eq)
#guard S zero 53 == (zero, .eq)
#guard S zero 0 == (zero, .eq)
#guard S (F "1" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard S (F "1/2" 53) 53 == (F "539785169252447/1125899906842624" 53, .gt)
#guard S (F "1" 53) 53 == (F "3789648413623927/4503599627370496" 53, .lt)
#guard S (F "-1" 53) 53 == (F "-3789648413623927/4503599627370496" 53, .gt)
#guard S (F "3" 53) 53 == (F "5084384125703515/36028797018963968" 53, .lt)
#guard S (F "1/1024" 53) 53 == (F "9007197823085295/9223372036854775808" 53, .gt)
#guard S (F "100" 53) 53 == (F "-570117028153783/1125899906842624" 53, .gt)
#guard S (F "-1000" 53) 53 == (F "-7447868781240427/9007199254740992" 53, .gt)
#guard S (F "1000000000000" 53) 53 == (F "-2752774392258985/4503599627370496" 53, .gt)
#guard S (F "1152921504606846976" 53) 53 == (F "-1870455753513367/2251799813685248" 53, .gt)
#guard S (F "-7/5" 53) 53 == (F "-4438071036768385/4503599627370496" 53, .gt)
#guard S (F "22/7" 53) 53 == (F "-5831425920677151/4611686018427387904" 53, .lt)

-- directed modes and other precisions
#guard S (F "1" 53) 53 .Floor == (F "3789648413623927/4503599627370496" 53, .lt)
#guard S (F "1" 53) 53 .Ceiling == (F "7579296827247855/9007199254740992" 53, .gt)
#guard S (F "-1" 53) 53 .Floor == (F "-7579296827247855/9007199254740992" 53, .lt)
#guard S (F "-1" 53) 53 .Ceiling == (F "-3789648413623927/4503599627370496" 53, .gt)
#guard S (F "3" 53) 20 == (F "147975/1048576" 20, .lt)
#guard sin (F "1" 53) == F "3789648413623927/4503599627370496" 53
#guard (toString (sin (F "1" 200))).startsWith
  "0.84147098480789650665250232163029899962256306079837106567275"
#guard (toString (sin (F "100" 200))).startsWith
  "-0.5063656411097587936565576104597854320650327212906573234433"

-- near a multiple of `π`: the 53-bit float nearest `π`
private def pi53 : AzFloat := F "884279719003555/281474976710656" 53
#guard S pi53 53 == (F "4967757600021511/40564819207303340847894502572032" 53, .gt)
#guard S pi53 53 .Floor == (F "2483878800010755/20282409603651670423947251286016" 53, .lt)
#guard S (-pi53) 53 .Ceiling == (F "-2483878800010755/20282409603651670423947251286016" 53, .gt)

-- small arguments on the ordinary path
#guard S (F "1/1099511627776" 53) 53 == (F "1/1099511627776" 53, .gt)
#guard S (F "1/1099511627776" 53) 53 .Floor
  == (F "9007199254740991/9903520314283042199192993792" 53, .lt)

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
#guard S tinyX 53 == (tinyX, .gt)
#guard S tinyX 53 .Ceiling == (tinyX, .gt)
#guard (S tinyX 53 .Floor).2 == .lt
#guard (S tinyX 53 .Floor).1 != tinyX
#guard S (-tinyX) 53 == (-tinyX, .lt)
#guard S (-tinyX) 53 .Floor == (-tinyX, .lt)
#guard (S (-tinyX) 53 .Ceiling).2 == .gt
#guard S ((F "3/2" 100) <<< tinyE) 53 == ((F "3/2" 53) <<< tinyE, .gt)
#guard (S tinyX 200).1 == (F "1" 200) <<< tinyE
#guard sin tinyX == tinyX
-- the tiny path and the loop agree where both apply (`2^(−200)` at 53 and at 150 bits)
#guard S ((F "1" 53) <<< AzInt.ofInt (-200)) 53 .Floor
  == ((S ((F "1" 53) <<< AzInt.ofInt (-200)) 150 .Floor).1 |> fun y => (setPrecRound y 53 .Floor))

-- a huge argument (`2^1000`; reference with a 700-digit `π`): the reduction needs `π` to about
-- 1000 more bits, the series does not
#guard S ((F "1" 53) <<< AzInt.ofInt 1000) 53
  == (F "-2867922922783799/18014398509481984" 53, .gt)
