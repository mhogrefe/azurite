/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asinh
import Azurite.AzFloat.Ln
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asinh x`

The special values (`NaN`, `±∞`, `0`, `p = 0`), the correctly rounded 53-bit values from
`2^(−200)` to `700` in three modes, large arguments up to `2^100`, 1-, 2-, 20-, 113-, 120- and
200-bit results, 200-bit strings, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)` (the value
is just inside `x`, at no cost), and huge arguments `±2^(2^30)` (where `asinh x` rounds like
`ln (2x)`).  References: an independent 6000-bit fixed-point evaluation of
`ln (x + √(x² + 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asinhPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (infinity true, .eq)
#guard A (infinity false) 53 == (infinity false, .eq)
#guard A (infinity false) 0 == (infinity false, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "7938707516150823/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 == (F "-7938707516150823/9007199254740992" 53, .lt)
#guard A (F "2" 53) 53 == (F "6501556188074119/4503599627370496" 53, .lt)
#guard A (F "1/2" 53) 53 == (F "4334370792049413/9007199254740992" 53, .gt)
#guard A (F "-1/3" 53) 53 == (F "-737352187295465/2251799813685248" 53, .lt)
#guard A (F "3/2" 53) 53 == (F "672591897521275/562949953421312" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "-1281253879910281/1125899906842624" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "8388761401176599/4503599627370496" 53, .gt)
#guard A (F "10" 53) 53 == (F "6751397880867803/2251799813685248" 53, .gt)
#guard A (F "-100" 53) 53 == (F "-2982701587930645/562949953421312" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "4611685249813397/4611686018427387904" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53
  == (F "-4951760157141521/4951760157141521099596496896" 53, .lt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53, .lt)
#guard A (F "30" 53) 53 == (F "2305067390464741/562949953421312" 53, .lt)
#guard A (F "-37" 53) 53 == (F "-2423076018725379/562949953421312" 53, .lt)
#guard A (F "700" 53) 53 == (F "4078137829701437/562949953421312" 53, .gt)
#guard A (F "1" 53) 53 .Floor == (F "3969353758075411/4503599627370496" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-7938707516150823/9007199254740992" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "672591897521275/562949953421312" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "-1281253879910281/1125899906842624" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "4611685249813397/4611686018427387904" 53, .lt)
#guard A (F "-100" 53) 53 .Floor == (F "-2982701587930645/562949953421312" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "9007199254740991/11417981541647679048466287755595961091061972992" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "7938707516150823/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-3969353758075411/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "5380735180170201/4503599627370496" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "-5125015519641123/4503599627370496" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "2305842624906699/2305843009213693952" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling == (F "-5965403175861289/1125899906842624" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard A (F "1" 53) 20 == (F "924187/1048576" 20, .lt)
#guard A (F "1" 53) 1 == (F "1" 1, .gt)
#guard A (F "-3/2" 53) 2 == (F "-1" 2, .gt)
#guard A (F "3/2" 53) 113
  == (F "6203565299812821301800075686385929/5192296858534827628530496329220096" 113, .gt)
#guard A (F "1/3" 200) 200
  == (h (F "131548026003643155867851029962187731778678167635124170804961" 200) (-198), .gt)
#guard A (F "1/3" 200) 10 .Floor == (F "335/1024" 10, .lt)
#guard A (F "10" 53) 120
  == (F "249082617696306734545693277949096155/83076749736557242056487941267521536" 120, .gt)
#guard A (F "1000000" 110) 53 == (F "2041912049527027/140737488355328" 53, .gt)
#guard A (F "1000000" 110) 53 .Floor == (F "8167648198108107/562949953421312" 53, .lt)
#guard A (F "-123456789012345678901234567890" 110) 53
  == (F "-4762474689668297/70368744177664" 53, .gt)
#guard A (F "-123456789012345678901234567890" 110) 53 .Floor
  == (F "-2381237344834149/35184372088832" 53, .lt)
#guard A (F "1267650600228229401496703205376" 110) 53
  == (F "4926365559255479/70368744177664" 53, .gt)
#guard A (F "1267650600228229401496703205376" 110) 53 .Floor
  == (F "2463182779627739/35184372088832" 53, .lt)
#guard asinh (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (asinhPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "0.881373587019543025232609324979792309028160328261635410"
#guard (toString (asinhPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "-1.19476321728710930411193082851909052353616207515300542"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor
#guard odd (F "100" 53) 20 .Ceiling && odd (F "1/1000" 53) 113 .Floor
#guard odd (h (F "1" 53) (-1000)) 53 .Ceiling && odd (h (F "1" 53) 1000) 53 .Ceiling

-- tiny arguments: just inside `x`
private def tinyOk (k : Int) : Bool :=
  let x := h (F "1" 53) (-k)
  A x 53 == (x, .gt) && A x 53 .Ceiling == (x, .gt) && A x 53 .Floor == (h dn (-k), .lt)
    && A (-x) 53 == (-x, .lt) && A (-x) 53 .Floor == (-x, .lt)
    && A (-x) 53 .Ceiling == (-(h dn (-k)), .gt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824

-- huge arguments: `asinh x` rounds like `ln (2x)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  A x p m == lnPrecRound (h x 1) p m
#guard big (h (F "1" 53) 1073741824) 53 .Nearest && big (h (F "3" 53) 1073741824) 53 .Floor
#guard big (h (F "5" 53) 100000) 113 .Ceiling && odd (h (F "3" 53) 1073741824) 53 .Floor
