/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atanh
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atanh x`

The special values (`NaN`; `±∞ ↦ NaN`; `NaN` for `|x| > 1`; `atanh (±1) = ±∞`; `0`; `p = 0`),
the correctly rounded 53-bit values from `2^(−200)` to `1 − 2^(−53)` in three modes, 1-, 2-,
20-, 113-, 120- and 200-bit results, 200-bit strings, oddness, and tiny arguments
`±2^(−1000)`, `±2^(−2^30)` (the value is just outside `x`, at no cost).  References: an
independent 6000-bit fixed-point evaluation of `(1/2) ln ((1 + x)/(1 − x))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atanhPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (nan, .eq)
#guard A (infinity false) 53 == (nan, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "1" 53) 53 == (infinity true, .eq)
#guard A (F "-1" 200) 53 == (infinity false, .eq)
#guard A (F "1" 53) 0 == (infinity true, .eq)
#guard A (F "2" 53) 53 == (nan, .eq)
#guard A (F "-3/2" 53) 53 == (nan, .eq)
#guard A (F "4503599627370497/4503599627370496" 53) 53 == (nan, .eq)
#guard A (h (F "1" 53) 1000) 53 == (nan, .eq)
#guard A (F "1/2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1/2" 53) 53 == (F "4947709893870347/9007199254740992" 53, .gt)
#guard A (F "-1/2" 53) 53 == (F "-4947709893870347/9007199254740992" 53, .lt)
#guard A (F "1/3" 53) 53 == (F "6243314768165359/18014398509481984" 53, .gt)
#guard A (F "-2/7" 53) 53 == (F "-5294311610053059/18014398509481984" 53, .gt)
#guard A (F "3/4" 53) 53 == (F "8763600222181975/9007199254740992" 53, .lt)
#guard A (F "99/100" 53) 53 == (F "5959731409046917/2251799813685248" 53, .lt)
#guard A (F "-999999/1000000" 53) 53 == (F "-2041911979154183/281474976710656" 53, .gt)
#guard A (F "9007199254740991/9007199254740992" 53) 53
  == (F "2633898417819761/140737488355328" 53, .gt)
#guard A (F "-9007199254740991/9007199254740992" 53) 53
  == (F "-2633898417819761/140737488355328" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "4611687555656983/4611686018427387904" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53
  == (F "-4951760157141521/4951760157141521099596496896" 53, .gt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "1/1267650600228229401496703205376" 53, .lt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53, .gt)
#guard A (F "1/2" 53) 53 .Floor == (F "2473854946935173/4503599627370496" 53, .lt)
#guard A (F "-1/2" 53) 53 .Floor == (F "-4947709893870347/9007199254740992" 53, .lt)
#guard A (F "99/100" 53) 53 .Floor == (F "5959731409046917/2251799813685248" 53, .lt)
#guard A (F "9007199254740991/9007199254740992" 53) 53 .Floor
  == (F "5267796835639521/281474976710656" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "4611687555656983/4611686018427387904" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "1/1267650600228229401496703205376" 53, .lt)
#guard A (F "1/2" 53) 53 .Ceiling == (F "4947709893870347/9007199254740992" 53, .gt)
#guard A (F "-1/2" 53) 53 .Ceiling == (F "-2473854946935173/4503599627370496" 53, .gt)
#guard A (F "99/100" 53) 53 .Ceiling == (F "2979865704523459/1125899906842624" 53, .gt)
#guard A (F "9007199254740991/9007199254740992" 53) 53 .Ceiling
  == (F "2633898417819761/140737488355328" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "576460944457123/576460752303423488" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "4503599627370497/5708990770823839524233143877797980545530986496" 53, .gt)
#guard A (F "1/2" 53) 20 == (F "575989/1048576" 20, .lt)
#guard A (F "1/2" 53) 1 == (F "1/2" 1, .lt)
#guard A (F "-3/4" 53) 2 == (F "-1" 2, .lt)
#guard A (F "3/4" 53) 113
  == (F "2525935788482735363164199063898503/2596148429267413814265248164610048" 113, .gt)
#guard A (F "1/3" 200) 200
  == (h (F "556922287356315859773128075548773653166636146774545375368901" 200) (-200), .lt)
#guard A (F "1/3" 200) 10 .Floor == (F "709/2048" 10, .lt)
#guard A (F "7/8" 53) 120
  == (F "224976008831001816472384893701114187/166153499473114484112975882535043072" 120, .gt)
#guard atanh (F "1/2" 53) == (A (F "1/2" 53) 53).1
#guard (toString (atanhPrecRound (F "1/2" 200) 200 .Nearest).1).startsWith
  "0.549306144334054845697622618461262852323745278911374725"
#guard (toString (atanhPrecRound (F "-3/4" 200) 200 .Nearest).1).startsWith
  "-0.97295507452765665255267637172158986481854236479093059"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "1/2" 53) 53 .Nearest && odd (F "1/2" 53) 53 .Floor
#guard odd (F "99/100" 53) 20 .Ceiling && odd (F "1/1000" 53) 113 .Floor
#guard odd (h (F "1" 53) (-1000)) 53 .Ceiling

-- tiny arguments: just outside `x`
private def tinyOk (k : Int) : Bool :=
  let x := h (F "1" 53) (-k)
  A x 53 == (x, .lt) && A x 53 .Floor == (x, .lt) && A x 53 .Ceiling == (h up (-k), .gt)
    && A (-x) 53 == (-x, .gt) && A (-x) 53 .Ceiling == (-x, .gt)
    && A (-x) 53 .Floor == (-(h up (-k)), .lt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824
