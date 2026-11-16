/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acot
import Azurite.AzFloat.Atan
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot x`

The special values (`NaN`; `arccot (±∞) = 0`; `arccot 0 = π/2`, correctly rounded; `p = 0`),
the correctly rounded 53-bit values at `±1` (`±π/4`), `±2`, `3/2`, `1/2`, the floats nearest
`−1/3`, `1/1000`, `−7/5`, `100`, `−1000`, `10^(±12)`, `22/7`, the powers of two `2^50`, `±2^70`,
`2^(−70)` and `3·2^50`; agreement with `atan` of an exactly representable reciprocal; oddness
(`f(−x, m) = −f(x, −m)`); the directed modes; 1-, 2-, 20-, 113- and 120-bit results; 200-bit
strings; huge arguments: `±2^1000`, `±2^(2^30)` (exponentially close to the float `1/x`, from
below: the three modes and both signs) and `±3·2^300`, `±3·2^(2^30)` (the correctly rounded
reciprocal); and tiny arguments `±2^(−1000)`, `±2^(−2^30)` (next to `±π/2`), all at no extra
cost.  References: an independent 1400-bit fixed-point evaluation of `arctan (1/x)` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acotPrecRound x p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (zero, .eq)
#guard A (infinity false) 53 == (zero, .eq)
#guard A (infinity true) 0 == (zero, .eq)
#guard A zero 53 == (h piN (-1), .lt)
#guard A zero 53 .Ceiling == (h piC (-1), .gt)
#guard A (F "2" 53) 0 == (nan, .eq)
#guard A (F "1" 53) 53 == (h piN (-2), .lt)
#guard A (F "-1" 53) 53 .Floor == (-(h piC (-2)), .lt)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "884279719003555/1125899906842624" 53, .lt)
#guard A (F "-1" 53) 53 == (F "-884279719003555/1125899906842624" 53, .gt)
#guard A (F "2" 53) 53 == (F "8352332796509007/18014398509481984" 53, .lt)
#guard A (F "-2" 53) 53 == (F "-8352332796509007/18014398509481984" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "5296256612459413/9007199254740992" 53, .lt)
#guard A (F "1/2" 53) 53 == (F "1246538638225297/1125899906842624" 53, .lt)
#guard A (F "-1/3" 53) 53 == (F "-175787564848171/140737488355328" 53, .gt)
#guard A (F "1/1000" 53) 53 == (F "7069734153902269/4503599627370496" 53, .gt)
#guard A (F "-7/5" 53) 53 == (F "-5586710707897953/9007199254740992" 53, .gt)
#guard A (F "100" 53) 53 == (F "5764415380978525/576460752303423488" 53, .lt)
#guard A (F "-1000" 53) 53 == (F "-4611684481199637/4611686018427387904" 53, .gt)
#guard A (F "1000000000000" 53) 53 == (F "4951760157141521/4951760157141521099596496896" 53, .lt)
#guard A (F "1/1000000000000" 53) 53 == (F "7074237752023937/4503599627370496" 53, .gt)
#guard A (F "22/7" 53) 53 == (F "2774692779658249/9007199254740992" 53, .gt)
#guard A (F "1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .gt)
#guard A (F "3377699720527872" 53) 53
  == (F "6004799503160661/20282409603651670423947251286016" 53, .lt)
#guard A (F "1180591620717411303424" 53) 53 == (F "1/1180591620717411303424" 53, .gt)
#guard A (F "-1180591620717411303424" 53) 53 == (F "-1/1180591620717411303424" 53, .lt)
#guard A (F "1/1180591620717411303424" 53) 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A (F "1" 53) 53 .Floor == (F "884279719003555/1125899906842624" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-7074237752028441/9007199254740992" 53, .lt)
#guard A (F "2" 53) 53 .Floor == (F "8352332796509007/18014398509481984" 53, .lt)
#guard A (F "-3/2" 53) 53 .Floor == (F "-2648128306229707/4503599627370496" 53, .lt)
#guard A (F "1/3" 53) 53 .Floor == (F "175787564848171/140737488355328" 53, .lt)
#guard A (F "1125899906842624" 53) 53 .Floor
  == (F "9007199254740991/10141204801825835211973625643008" 53, .lt)
#guard A (F "-1180591620717411303424" 53) 53 .Floor == (F "-1/1180591620717411303424" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "7074237752028441/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-884279719003555/1125899906842624" 53, .gt)
#guard A (F "2" 53) 53 .Ceiling == (F "522020799781813/1125899906842624" 53, .gt)
#guard A (F "-3/2" 53) 53 .Ceiling == (F "-5296256612459413/9007199254740992" 53, .gt)
#guard A (F "1/3" 53) 53 .Ceiling == (F "5625202075141473/4503599627370496" 53, .gt)
#guard A (F "1125899906842624" 53) 53 .Ceiling == (F "1/1125899906842624" 53, .gt)
#guard A (F "-1180591620717411303424" 53) 53 .Ceiling
  == (F "-9007199254740991/10633823966279326983230456482242756608" 53, .gt)
#guard A (F "2" 53) 20 == (F "243085/524288" 20, .gt)
#guard A (F "2" 53) 1 == (F "1/2" 1, .gt)
#guard A (F "3/2" 53) 113
  == (F "6106168142420669375800887123151837/10384593717069655257060992658440192" 113, .gt)
#guard A (F "-3/2" 53) 2 == (F "-1/2" 2, .gt)
#guard A (F "1/3" 53) 2 == (F "1" 2, .lt)
#guard A (F "1024" 53) 120
  == (F "1329227573234957581826559870628721577/1361129467683753853853498429727072845824" 120, .lt)
#guard A (F "2" 53) 53 == atanPrecRound (F "1/2" 53) 53 .Nearest
#guard A (F "-4" 53) 53 .Floor == atanPrecRound (F "-1/4" 53) 53 .Floor
#guard A (F "1/8" 53) 113 .Ceiling == atanPrecRound (F "8" 53) 113 .Ceiling
#guard A (F "1024" 53) 200 == atanPrecRound (F "1/1024" 53) 200 .Nearest
#guard acot (F "2" 53) == (A (F "2" 53) 53).1

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor && odd (F "3/2" 53) 53 .Ceiling
#guard odd (F "1/1000" 53) 20 .Floor && odd (F "1024" 53) 113 .Ceiling

-- 200-bit strings
#guard (toString (A (F "2" 200) 200).1).startsWith
  "0.46364760900080611621425623146121440202853705428612026381"
#guard (toString (A (F "-3/2" 200) 200).1).startsWith
  "-0.5880026035475675512456110806250854276017072460559243537"

-- huge powers of two: exponentially close to the float `1/x`, from below
private def pred1 : AzFloat := F "9007199254740991/9007199254740992" 53
private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)
private def tiny (k : Int) : AzFloat := h (F "1" 53) (-k)
private def pow2ok (k : Int) : Bool :=
  A (pw k) 53 == (tiny k, .gt) && A (pw k) 53 .Ceiling == (tiny k, .gt)
    && A (pw k) 53 .Floor == (h pred1 (-k), .lt)
    && A (-(pw k)) 53 == (-(tiny k), .lt) && A (-(pw k)) 53 .Floor == (-(tiny k), .lt)
    && A (-(pw k)) 53 .Ceiling == (-(h pred1 (-k)), .gt)
#guard pow2ok 1000
#guard pow2ok 1073741824
#guard pow2ok 60
#guard pow2ok 100

-- huge arguments that are not powers of two: the correctly rounded reciprocal
private def recipOk (x : AzFloat) (p : Nat) : Bool :=
  A x p == divPrecRound one x p .Nearest && A x p .Floor == divPrecRound one x p .Floor
    && A x p .Ceiling == divPrecRound one x p .Ceiling
#guard recipOk (h (F "3" 53) 300) 53
#guard recipOk (h (F "-3" 53) 300) 53
#guard recipOk (h (F "3" 53) 1073741824) 53
#guard recipOk (h (F "-7074237752028441/2251799813685248" 53) 1073741824) 200

-- tiny arguments: next to `±π/2`
private def tinyOk (k : Int) : Bool :=
  A (pw (-k)) 53 == (h piN (-1), .lt) && A (pw (-k)) 53 .Ceiling == (h piC (-1), .gt)
    && A (-(pw (-k))) 53 == (-(h piN (-1)), .gt)
    && A (-(pw (-k))) 53 .Floor == (-(h piC (-1)), .lt)
#guard tinyOk 1000
#guard tinyOk 1073741824
