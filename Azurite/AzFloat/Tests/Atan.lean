/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan`

The special values (`NaN`, `arctan (±∞) = ±π/2` in the three modes, `arctan 0 = 0` at every
precision, `p = 0`), the correctly rounded 53-bit values of `arctan (1/2)`, `arctan (±1)`,
`arctan 3`, `arctan (1/1024)`, `arctan 100`, `arctan (−1000)`, `arctan 10¹²`, `arctan 2⁶⁰`,
`arctan` of the 53-bit floats nearest `−7/5`, `22/7` and `1/3`, the neighbours of `1`, the
directed modes, 1-, 2- and 20-bit results, 200- and 400-bit values.  Extreme arguments: `2⁻⁴⁰`
(the ordinary path next to the argument), `±2^(−2^30)`, `(3/2)·2^(−2^30)` at 100 bits (the tiny
path, independent of the exponent), `2^1000` (next to `π/2`) and `2^(2^30)`.  References: a
1400-bit fixed-point evaluation (forty halvings `t ↦ t/(1 + √(1 + t²))`, Taylor series, Machin
`π`) at the exact float arguments, rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atanPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A (infinity true) 53 .Floor == (F "884279719003555/562949953421312" 53, .lt)
#guard A (infinity true) 53 .Ceiling == (F "7074237752028441/4503599627370496" 53, .gt)
#guard A (infinity false) 53 == (F "-884279719003555/562949953421312" 53, .gt)
#guard A (infinity false) 53 .Floor == (F "-7074237752028441/4503599627370496" 53, .lt)
#guard A (infinity false) 53 .Ceiling == (F "-884279719003555/562949953421312" 53, .gt)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "1" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1/2" 53) 53 == (F "8352332796509007/18014398509481984" 53, .lt)
#guard A (F "1" 53) 53 == (F "884279719003555/1125899906842624" 53, .lt)
#guard A (F "-1" 53) 53 == (F "-884279719003555/1125899906842624" 53, .gt)
#guard A (F "3" 53) 53 == (F "175787564848171/140737488355328" 53, .gt)
#guard A (F "1/1024" 53) 53 == (F "2251799097857775/2305843009213693952" 53, .gt)
#guard A (F "100" 53) 53 == (F "3514601628432273/2251799813685248" 53, .gt)
#guard A (F "-1000" 53) 53 == (F "-7069734153902269/4503599627370496" 53, .lt)
#guard A (F "1000000000000" 53) 53 == (F "7074237752023937/4503599627370496" 53, .gt)
#guard A (F "1152921504606846976" 53) 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "-8561764796158927/9007199254740992" 53, .gt)
#guard A (F "22/7" 53) 53 == (F "1421722840549829/1125899906842624" 53, .gt)
#guard A (F "1/3" 53) 53 == (F "5796142707547873/18014398509481984" 53, .gt)
-- the neighbours of `1`: `1 + 2^(−52)` and `1 − 2^(−53)`
#guard A (F "4503599627370497/4503599627370496" 53) 53
  == (F "7074237752028441/9007199254740992" 53, .lt)
#guard A (F "9007199254740991/9007199254740992" 53) 53
  == (F "884279719003555/1125899906842624" 53, .gt)

-- directed modes and other precisions
#guard A (F "1" 53) 53 .Floor == (F "884279719003555/1125899906842624" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "7074237752028441/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 .Floor == (F "-7074237752028441/9007199254740992" 53, .lt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-884279719003555/1125899906842624" 53, .gt)
#guard A (F "3" 53) 53 .Floor == (F "5625202075141471/4503599627370496" 53, .lt)
#guard A (F "3" 53) 53 .Ceiling == (F "175787564848171/140737488355328" 53, .gt)
#guard A (F "-3" 53) 53 .Floor == (F "-175787564848171/140737488355328" 53, .lt)
#guard A (F "-3" 53) 53 .Ceiling == (F "-5625202075141471/4503599627370496" 53, .gt)
#guard A (F "3" 53) 20 == (F "163715/131072" 20, .gt)
#guard A (F "1/2" 53) 1 == (F "1/2" 1, .gt)
#guard A (F "1/2" 53) 2 == (F "1/2" 2, .gt)
#guard atan (F "1" 53) == F "884279719003555/1125899906842624" 53
#guard (toString (atan (F "1" 200))).startsWith
  "0.78539816339744830961566084581987572104929234984377645524373"
#guard (toString (atan (F "100" 200))).startsWith
  "1.56079666010823138102498157543047189353721534714317627085953"
#guard (toString (atan (F "-1/3" 200))).startsWith
  "-0.3217505543966421934014046143586613190207552955576561914328"
#guard A (F "3/4" 53) 400 == (F ("415420164932562277212025873527013502124066934406946286877252"
  ++ "913667945603875091507966647483758809945330481323919515903069/6455624695217271474139797930"
  ++ "00752968582426448207305878207664839135161905504210298657411338320034457858975792993186873"
  ++ "344") 400, .lt)

-- small arguments on the ordinary path
#guard A (F "1/1099511627776" 53) 53 == (F "1/1099511627776" 53, .gt)
#guard A (F "1/1099511627776" 53) 53 .Floor
  == (F "9007199254740991/9903520314283042199192993792" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 200
  == (F "1/1267650600228229401496703205376" 200, .gt)

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
#guard A tinyX 53 == (tinyX, .gt)
#guard A tinyX 53 .Ceiling == (tinyX, .gt)
#guard (A tinyX 53 .Floor).2 == .lt
#guard (A tinyX 53 .Floor).1 != tinyX
#guard A (-tinyX) 53 == (-tinyX, .lt)
#guard A (-tinyX) 53 .Floor == (-tinyX, .lt)
#guard (A (-tinyX) 53 .Ceiling).2 == .gt
#guard A ((F "3/2" 100) <<< tinyE) 53 == ((F "3/2" 53) <<< tinyE, .gt)
#guard (A tinyX 200).1 == (F "1" 200) <<< tinyE
#guard atan tinyX == tinyX
-- the tiny path and the loop agree where both apply (`2^(−200)` at 53 and at 150 bits)
#guard A ((F "1" 53) <<< AzInt.ofInt (-200)) 53 .Floor
  == ((A ((F "1" 53) <<< AzInt.ofInt (-200)) 150 .Floor).1 |> fun y => (setPrecRound y 53 .Floor))

-- huge arguments: next to `π/2`, at a cost independent of the exponent
#guard A ((F "1" 53) <<< AzInt.ofInt 1000) 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A ((F "1" 53) <<< AzInt.ofInt 1000) 53 .Ceiling
  == (F "7074237752028441/4503599627370496" 53, .gt)
#guard A (-((F "1" 53) <<< AzInt.ofInt 1000)) 53 .Floor
  == (F "-7074237752028441/4503599627370496" 53, .lt)
#guard A ((F "1" 53) <<< AzInt.ofInt (2 ^ 30 : Int)) 53
  == (F "884279719003555/562949953421312" 53, .lt)
