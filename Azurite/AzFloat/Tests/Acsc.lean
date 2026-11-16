/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsc
import Azurite.AzFloat.Asin
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccsc x`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and tiny arguments;
`arccsc (±∞) = 0`; `arccsc (±1) = ±π/2`, correctly rounded; `p = 0`), the correctly rounded
53-bit values at `±2` (`±π/6`), `3/2`, `5/4`, the float nearest `−7/5`, `100`, `−1000`, `10¹²`,
`±(1 + 10⁻⁶)`, `22/7`, the powers of two `2^50`, `±2^70` and `3·2^50`, and the neighbours
`±(1 + 2^(−52))` of `±1`; agreement with `asin` of an exactly representable reciprocal; oddness
(`f(−x, m) = −f(x, −m)`); the directed modes; 1-, 2-, 20- and 113-bit results; `arccsc 1024` at
120 and 200 bits (the value is `2^(−10) (1 + 2^(−20)/6 + …)`); 200-bit strings; and huge
arguments: `±2^1000`, `±2^(2^30)` (exponentially close to the float `1/x`: the three modes and
both signs) and `±3·2^300`, `±3·2^(2^30)` (the correctly rounded reciprocal), at no extra cost.
References: an independent 1400-bit fixed-point evaluation of `arcsin (1/x)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acscPrecRound x p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard A nan 53 == (nan, .eq)
#guard A zero 53 == (nan, .eq)
#guard A (F "1/2" 53) 53 == (nan, .eq)
#guard A (F "-9007199254740991/9007199254740992" 53) 53 == (nan, .eq)
#guard A (powerOf2 (AzInt.ofInt (-1073741824))) 53 == (nan, .eq)
#guard A (infinity true) 53 == (zero, .eq)
#guard A (infinity false) 53 == (zero, .eq)
#guard A (infinity true) 0 == (zero, .eq)
#guard A (F "1" 53) 53 == (h piN (-1), .lt)
#guard A (F "1" 53) 53 .Ceiling == (h piC (-1), .gt)
#guard A (F "-1" 53) 53 == (-(h piN (-1)), .gt)
#guard A (F "-1" 53) 53 .Floor == (-(h piC (-1)), .lt)
#guard A (F "-1" 53) 53 .Ceiling == (-(h piN (-1)), .gt)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "2" 53) 53 == (F "2358079250676147/4503599627370496" 53, .gt)
#guard A (F "-2" 53) 53 == (F "-2358079250676147/4503599627370496" 53, .lt)
#guard A (F "3/2" 53) 53 == (F "3286401200665711/4503599627370496" 53, .lt)
#guard A (F "5/4" 53) 53 == (F "8352332796509007/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "-7166154329695639/9007199254740992" 53, .gt)
#guard A (F "100" 53) 53 == (F "2882351802074999/288230376151711744" 53, .lt)
#guard A (F "-1000" 53) 53 == (F "-2305843393521035/2305843009213693952" 53, .gt)
#guard A (F "1000000000000" 53) 53 == (F "4951760157141521/4951760157141521099596496896" 53, .lt)
#guard A (F "1000001/1000000" 53) 53 == (F "3533934351504973/2251799813685248" 53, .lt)
#guard A (F "-1000001/1000000" 53) 53 == (F "-3533934351504973/2251799813685248" 53, .gt)
#guard A (F "22/7" 53) 53 == (F "5833260670897689/18014398509481984" 53, .gt)
#guard A (F "1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .lt)
#guard A (F "3377699720527872" 53) 53
  == (F "6004799503160661/20282409603651670423947251286016" 53, .lt)
#guard A (F "1180591620717411303424" 53) 53 == (F "1/1180591620717411303424" 53, .lt)
#guard A (F "-1180591620717411303424" 53) 53 == (F "-1/1180591620717411303424" 53, .gt)
#guard A (F "2" 53) 53 .Floor == (F "4716158501352293/9007199254740992" 53, .lt)
#guard A (F "-3/2" 53) 53 .Floor == (F "-6572802401331423/9007199254740992" 53, .lt)
#guard A (F "1125899906842624" 53) 53 .Floor == (F "1/1125899906842624" 53, .lt)
#guard A (F "-1180591620717411303424" 53) 53 .Floor
  == (F "-4503599627370497/5316911983139663491615228241121378304" 53, .lt)
#guard A (F "2" 53) 53 .Ceiling == (F "2358079250676147/4503599627370496" 53, .gt)
#guard A (F "-3/2" 53) 53 .Ceiling == (F "-3286401200665711/4503599627370496" 53, .gt)
#guard A (F "1125899906842624" 53) 53 .Ceiling
  == (F "4503599627370497/5070602400912917605986812821504" 53, .gt)
#guard A (F "-1180591620717411303424" 53) 53 .Ceiling == (F "-1/1180591620717411303424" 53, .gt)
#guard A (F "2" 53) 20 == (F "549033/1048576" 20, .lt)
#guard A (F "2" 53) 1 == (F "1/2" 1, .lt)
#guard A (F "3/2" 53) 113
  == (F "7577925234026520191382024829077409/10384593717069655257060992658440192" 113, .gt)
#guard A (F "-3/2" 53) 2 == (F "-3/4" 2, .lt)
#guard A (F "1024" 53) 200 == asinPrecRound (F "1/1024" 53) 200 .Nearest
#guard A (F "1024" 53) 120
  == (F "664614103530053290214990741842365567/680564733841876926926749214863536422912" 120, .lt)
#guard A (F "2" 53) 53 == asinPrecRound (F "1/2" 53) 53 .Nearest
#guard A (F "-4" 53) 53 .Floor == asinPrecRound (F "-1/4" 53) 53 .Floor
#guard acsc (F "2" 53) == (A (F "2" 53) 53).1

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor && odd (F "3/2" 53) 53 .Ceiling
#guard odd (F "1000001/1000000" 53) 20 .Floor && odd (F "1024" 53) 113 .Ceiling

-- next to `±1`
#guard A (F "4503599627370497/4503599627370496" 53) 53
  == (F "7074237657122175/4503599627370496" 53, .gt)
#guard A (F "-4503599627370497/4503599627370496" 53) 53 .Floor
  == (F "-7074237657122175/4503599627370496" 53, .lt)

-- 200-bit strings
#guard (toString (A (F "2" 200) 200).1).startsWith
  "0.52359877559829887307710723054658381403286156656251763682"
#guard (toString (A (F "-3/2" 200) 200).1).startsWith
  "-0.7297276562269663634547966598133206953965059140477136907"

-- huge powers of two: exponentially close to the float `1/x`
private def succ1 : AzFloat := F "4503599627370497/4503599627370496" 53
private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)
private def tiny (k : Int) : AzFloat := h (F "1" 53) (-k)
private def pow2ok (k : Int) : Bool :=
  A (pw k) 53 == (tiny k, .lt) && A (pw k) 53 .Floor == (tiny k, .lt)
    && A (pw k) 53 .Ceiling == (h succ1 (-k), .gt)
    && A (-(pw k)) 53 == (-(tiny k), .gt) && A (-(pw k)) 53 .Ceiling == (-(tiny k), .gt)
    && A (-(pw k)) 53 .Floor == (-(h succ1 (-k)), .lt)
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
#guard A (h (F "3" 53) 300) 53 == (h (F "6004799503160661/18014398509481984" 53) (-300), .lt)
