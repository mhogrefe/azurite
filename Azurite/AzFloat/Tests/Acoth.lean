/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acoth
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acoth x`

The special values (`NaN`; `±∞ ↦ 0`; `acoth (±1) = ±∞`; `NaN` for `|x| < 1`, including `0`;
`p = 0`), the correctly rounded 53-bit values from `1 + 2^(−52)` to `3·2^100` of both signs in
three modes — across the switch to the huge-argument enclosure — 1-, 2-, 20-, 113-, 120- and
200-bit results, 200-bit strings, oddness, and huge arguments `±2^1000`, `±2^(2^30)`,
`±3·2^(2^30)` (the value is just outside `1/x`, at no cost).  References: an independent
6000-bit fixed-point evaluation of `(1/2) ln ((x + 1)/(x − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acothPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (zero, .eq)
#guard A (infinity false) 53 == (zero, .eq)
#guard A (infinity false) 0 == (zero, .eq)
#guard A (F "1" 53) 53 == (infinity true, .eq)
#guard A (F "-1" 200) 53 == (infinity false, .eq)
#guard A (F "1" 53) 0 == (infinity true, .eq)
#guard A zero 53 == (nan, .eq)
#guard A (F "1/2" 53) 53 == (nan, .eq)
#guard A (F "-3/4" 53) 53 == (nan, .eq)
#guard A (F "9007199254740991/9007199254740992" 53) 53 == (nan, .eq)
#guard A (h (F "-1" 53) (-1000)) 53 == (nan, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "2" 53) 53 == (F "4947709893870347/9007199254740992" 53, .gt)
#guard A (F "-2" 53) 53 == (F "-4947709893870347/9007199254740992" 53, .lt)
#guard A (F "3" 53) 53 == (F "6243314768165359/18014398509481984" 53, .lt)
#guard A (F "-7/2" 53) 53 == (F "-1323577902513265/4503599627370496" 53, .lt)
#guard A (F "4/3" 53) 53 == (F "1095450027772747/1125899906842624" 53, .lt)
#guard A (F "101/100" 53) 53 == (F "5970990501941743/2251799813685248" 53, .lt)
#guard A (F "-1000001/1000000" 53) 53 == (F "-4083824239814593/562949953421312" 53, .lt)
#guard A (F "4503599627370497/4503599627370496" 53) 53
  == (F "2585122521193469/140737488355328" 53, .lt)
#guard A (F "-4503599627370497/4503599627370496" 53) 53
  == (F "-2585122521193469/140737488355328" 53, .gt)
#guard A (F "1000" 53) 53 == (F "4611687555656983/4611686018427387904" 53, .lt)
#guard A (F "-1000000000000" 53) 53 == (F "-4951760157141521/4951760157141521099596496896" 53, .gt)
#guard A (F "1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .lt)
#guard A (F "35184372088832" 53) 53 == (F "1/35184372088832" 53, .lt)
#guard A (F "3377699720527872" 53) 53
  == (F "6004799503160661/20282409603651670423947251286016" 53, .lt)
#guard A (F "1267650600228229401496703205376" 53) 53
  == (F "1/1267650600228229401496703205376" 53, .lt)
#guard A (F "-3802951800684688204490109616128" 53) 53
  == (F "-6004799503160661/22835963083295358096932575511191922182123945984" 53, .gt)
#guard A (F "2" 53) 53 .Floor == (F "2473854946935173/4503599627370496" 53, .lt)
#guard A (F "-2" 53) 53 .Floor == (F "-4947709893870347/9007199254740992" 53, .lt)
#guard A (F "101/100" 53) 53 .Floor == (F "5970990501941743/2251799813685248" 53, .lt)
#guard A (F "4503599627370497/4503599627370496" 53) 53 .Floor
  == (F "2585122521193469/140737488355328" 53, .lt)
#guard A (F "1000" 53) 53 .Floor == (F "4611687555656983/4611686018427387904" 53, .lt)
#guard A (F "35184372088832" 53) 53 .Floor == (F "1/35184372088832" 53, .lt)
#guard A (F "1125899906842624" 53) 53 .Floor == (F "1/1125899906842624" 53, .lt)
#guard A (F "-3802951800684688204490109616128" 53) 53 .Floor
  == (F "-3002399751580331/11417981541647679048466287755595961091061972992" 53, .lt)
#guard A (F "2" 53) 53 .Ceiling == (F "4947709893870347/9007199254740992" 53, .gt)
#guard A (F "-2" 53) 53 .Ceiling == (F "-2473854946935173/4503599627370496" 53, .gt)
#guard A (F "101/100" 53) 53 .Ceiling == (F "373186906371359/140737488355328" 53, .gt)
#guard A (F "4503599627370497/4503599627370496" 53) 53 .Ceiling
  == (F "5170245042386939/281474976710656" 53, .gt)
#guard A (F "1000" 53) 53 .Ceiling == (F "576460944457123/576460752303423488" 53, .gt)
#guard A (F "35184372088832" 53) 53 .Ceiling
  == (F "4503599627370497/158456325028528675187087900672" 53, .gt)
#guard A (F "1125899906842624" 53) 53 .Ceiling
  == (F "4503599627370497/5070602400912917605986812821504" 53, .gt)
#guard A (F "-3802951800684688204490109616128" 53) 53 .Ceiling
  == (F "-6004799503160661/22835963083295358096932575511191922182123945984" 53, .gt)
#guard A (F "2" 53) 20 == (F "575989/1048576" 20, .lt)
#guard A (F "2" 53) 1 == (F "1/2" 1, .lt)
#guard A (F "-4/3" 53) 2 == (F "-1" 2, .lt)
#guard A (F "4/3" 53) 113
  == (F "631483947120683902554701798484293/649037107316853453566312041152512" 113, .lt)
#guard A (F "3" 200) 200
  == (h (F "556922287356315859773128075548773653166636146774545375368901" 200) (-200), .lt)
#guard A (F "3" 200) 10 .Floor == (F "709/2048" 10, .lt)
#guard A (F "8/7" 53) 120
  == (F "899904035324007403625228658502474769/664613997892457936451903530140172288" 120, .lt)
#guard acoth (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (acothPrecRound (F "2" 200) 200 .Nearest).1).startsWith
  "0.549306144334054845697622618461262852323745278911374725"
#guard (toString (acothPrecRound (F "-4/3" 200) 200 .Nearest).1).startsWith
  "-0.97295507452765665255267637172158986481854236479093059"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor
#guard odd (F "100" 53) 20 .Ceiling && odd (F "1001/1000" 53) 113 .Floor
#guard odd (h (F "1" 53) 1000) 53 .Ceiling && odd (h (F "3" 53) 1073741824) 53 .Floor

-- huge arguments: just outside `1/x`
private def hugeOk (k : Int) : Bool :=
  let x := h (F "1" 53) k
  let y := h (F "1" 53) (-k)
  A x 53 == (y, .lt) && A x 53 .Floor == (y, .lt) && A x 53 .Ceiling == (h up (-k), .gt)
    && A (-x) 53 == (-y, .gt) && A (-x) 53 .Ceiling == (-y, .gt)
    && A (-x) 53 .Floor == (-(h up (-k)), .lt)
#guard hugeOk 60
#guard hugeOk 100
#guard hugeOk 1000
#guard hugeOk 1073741824
private def big3 : AzFloat := h (F "3" 53) 1073741824
#guard A big3 53 == (h (F "6004799503160661/18014398509481984" 53) (-1073741824), .lt)
#guard A big3 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-1073741824), .gt)
#guard A (-big3) 53 .Floor
  == (-(h (F "3002399751580331/9007199254740992" 53) (-1073741824)), .lt)
