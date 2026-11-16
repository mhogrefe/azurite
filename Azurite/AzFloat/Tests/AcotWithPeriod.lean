/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot (x) u / (2π)`

The special values (`NaN`; `0` at `±∞`; `u = 0`; `u/4` at `0`; `±u/8` at `±1` — exact or
correctly rounded; `p = 0`), the correctly rounded 53-bit values in degrees on both sides of
`1`, other periods (`1`, `7`, `400`, `2^64 − 1`), oddness, the directed modes, 1-, 20- and
113-bit results, a 200-bit string, the neighbours `±(1 + 2^(−52))` of `±1`, tiny arguments
`±2^(−60)`, `±2^(−2^30)` (the value is next to the quarter turn `±u/4`, at no extra cost), and
huge arguments `±2^1000`, `±2^(2^30)`, `±3·2^(2^30)` (the value is `u/(2πx)` up to a relative
`2^(−2e)`, at no extra cost).  References: an independent 1400-bit fixed-point evaluation
rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotWithPeriodPrecRound x u p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard W nan 360 53 == (nan, .eq)
#guard W nan 0 53 == (nan, .eq)
#guard W (infinity true) 360 53 == (zero, .eq)
#guard W (infinity false) 360 53 == (zero, .eq)
#guard W (infinity false) 0 0 == (zero, .eq)
#guard W zero 360 53 == (F "90" 53, .eq)
#guard W zero 0 53 == (zero, .eq)
#guard W zero 7 53 == (F "7/4" 53, .eq)
#guard W zero 7 1 == (F "2" 1, .gt)
#guard W zero 7 1 .Floor == (F "1" 1, .lt)
#guard W (F "3" 53) 0 53 == (zero, .eq)
#guard W (F "-1/3" 53) 0 53 == (zero, .eq)
#guard W (F "-1" 53) 0 53 == (zero, .eq)
#guard W (F "3" 53) 360 0 == (nan, .eq)
#guard W (F "1" 53) 360 53 == (F "45" 53, .eq)
#guard W (F "-1" 200) 360 53 == (F "-45" 53, .eq)
#guard W (F "1" 53) 7 53 == (F "7/8" 53, .eq)
#guard W (F "1" 53) 7 1 == (F "1" 1, .gt)
#guard W (F "-1" 53) 7 1 == (F "-1" 1, .lt)
#guard W (F "-1" 53) 7 1 .Ceiling == (F "-1/2" 1, .gt)

-- correctly rounded values
#guard W (F "3" 53) 360 53 == (F "1297244197648527/70368744177664" 53, .lt)
#guard W (F "-3" 53) 360 53 == (F "-1297244197648527/70368744177664" 53, .gt)
#guard W (F "3/2" 53) 360 53 == (F "2370727743063897/70368744177664" 53, .lt)
#guard W (F "-7/5" 53) 360 53 == (F "-5001483514423393/140737488355328" 53, .gt)
#guard W (F "1/4" 53) 360 53 == (F "2672737075089917/35184372088832" 53, .lt)
#guard W (F "100" 53) 360 53 == (F "5160573010786969/9007199254740992" 53, .gt)
#guard W (F "-1000" 53) 360 53 == (F "-8257189288084933/144115188075855872" 53, .gt)
#guard W (F "1/1000" 53) 360 53 == (F "6329155145282687/70368744177664" 53, .lt)
#guard W (F "-3/1024" 53) 360 53 == (F "-6321375001822051/70368744177664" 53, .gt)
#guard W (F "22/7" 53) 360 53 == (F "4968068303745017/281474976710656" 53, .gt)
#guard W (F "1125899906842624" 53) 360 53
  == (F "1007958012753983/19807040628566084398385987584" 53, .gt)
#guard W (F "2" 53) 360 53 == (F "1869349290346353/70368744177664" 53, .gt)
#guard W (F "-1/2" 53) 360 53 == (F "-4463837685643407/70368744177664" 53, .gt)
#guard W (F "3/2" 53) 1 53 == (F "6743403358048419/72057594037927936" 53, .gt)
#guard W (F "-4" 53) 1 53 == (F "-5618988520163133/144115188075855872" 53, .gt)
#guard W (F "3/2" 53) 7 53 == (F "2950238969146183/4503599627370496" 53, .lt)
#guard W (F "-4" 53) 7 53 == (F "-4916614955142741/18014398509481984" 53, .gt)
#guard W (F "3/2" 53) 400 53 == (F "5268283873475327/140737488355328" 53, .gt)
#guard W (F "-4" 53) 400 53 == (F "-8779669562754895/562949953421312" 53, .gt)
#guard W (F "3/2" 53) 18446744073709551615 53 == (F "1726311259660395264" 53, .gt)
#guard W (F "-4" 53) 18446744073709551615 53 == (F "-719230530580881024" 53, .gt)
#guard W (F "3/2" 53) 360 53 .Floor == (F "2370727743063897/70368744177664" 53, .lt)
#guard W (F "-4" 53) 360 53 .Floor == (F "-3950851303239703/281474976710656" 53, .lt)
#guard W (F "3/2" 53) 360 53 .Ceiling == (F "4741455486127795/140737488355328" 53, .gt)
#guard W (F "-4" 53) 360 53 .Ceiling == (F "-7901702606479405/562949953421312" 53, .gt)
#guard W (F "3/2" 53) 360 20 == (F "275989/8192" 20, .lt)
#guard W (F "-4" 53) 360 1 == (F "-16" 1, .lt)
#guard W (F "3/2" 53) 360 113
  == (F "5466525993092845621329999940000617/162259276829213363391578010288128" 113, .lt)
#guard acotWithPeriod (F "3/2" 53) 360 == (W (F "3/2" 53) 360 53).1
#guard (toString (acotWithPeriodPrecRound (F "3/2" 200) 360 200 .Nearest).1).startsWith
  "33.69006752597978691352549456166013942025636351590594485"

-- oddness: `f(−x, u, m) = −f(x, u, −m)`
private def odd (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode) : Bool :=
  let r := W x u p (-m)
  W (-x) u p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 360 53 .Nearest && odd (F "3/2" 53) 7 53 .Floor
#guard odd (F "1/1000" 53) 400 20 .Ceiling && odd (F "1" 53) 7 2 .Floor

-- next to `±1`
#guard W (F "4503599627370497/4503599627370496" 53) 360 53
  == (F "6333186975989759/140737488355328" 53, .lt)
#guard W (F "-4503599627370497/4503599627370496" 53) 360 53
  == (F "-6333186975989759/140737488355328" 53, .gt)

private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)

-- tiny arguments: just inside the quarter turn
private def b90 : AzFloat := F "6333186975989759/70368744177664" 53
private def tinyOk (k : Int) : Bool :=
  W (pw (-k)) 360 53 == (F "90" 53, .gt) && W (pw (-k)) 360 53 .Floor == (b90, .lt)
    && W (pw (-k)) 360 53 .Ceiling == (F "90" 53, .gt)
    && W (-(pw (-k))) 360 53 == (F "-90" 53, .lt)
    && W (-(pw (-k))) 360 53 .Floor == (F "-90" 53, .lt)
    && W (-(pw (-k))) 360 53 .Ceiling == (-b90, .gt)
    && W (h (F "3" 53) (-k)) 7 53 == (F "7/4" 53, .gt)
    && W (h (F "3" 53) (-k)) 7 53 .Floor == (F "7881299347898367/4503599627370496" 53, .lt)
#guard tinyOk 60
#guard tinyOk 200
#guard tinyOk 1073741824

-- huge arguments: `360/(2π) / x`
private def cN : AzFloat := F "1007958012753983/17592186044416" 53
private def cF : AzFloat := F "8063664102031863/140737488355328" 53
private def hugeOk (k : Int) : Bool :=
  W (pw k) 360 53 == (h cN (-k), .gt) && W (pw k) 360 53 .Floor == (h cF (-k), .lt)
    && W (pw k) 360 53 .Ceiling == (h cN (-k), .gt)
    && W (-(pw k)) 360 53 == (-(h cN (-k)), .lt)
    && W (-(pw k)) 360 53 .Ceiling == (-(h cF (-k)), .gt)
#guard hugeOk 1000
#guard hugeOk 1073741824
#guard hugeOk 60
private def big3 : AzFloat := h (F "3" 53) 1073741824
#guard W big3 360 53 == (h (F "2687888034010621/140737488355328" 53) (-1073741824), .lt)
#guard W big3 360 53 .Ceiling
  == (h (F "5375776068021243/281474976710656" 53) (-1073741824), .gt)
#guard W (-big3) 360 53 .Ceiling
  == (-(h (F "2687888034010621/140737488355328" 53) (-1073741824)), .gt)
