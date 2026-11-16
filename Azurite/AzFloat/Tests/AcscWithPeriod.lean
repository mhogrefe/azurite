/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccsc (x) u / (2π)`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and for `u = 0`; `0` at `±∞`;
`u = 0`; `±u/4` at `±1`; `±u/12` at `±2` — exact for `u = 360`, the correctly rounded rationals
for `u = 7`, `1` in several modes; `p = 0`), the correctly rounded 53-bit values in degrees,
other periods (`1`, `7`, `400`, `2^64 − 1`), oddness, the directed modes, 1-, 20- and 113-bit
results, a 200-bit string, the neighbours `±(1 + 2^(−52))` of `±1`, and huge arguments
`±2^1000`, `±2^(2^30)`, `±3·2^(2^30)`: the value is `u/(2πx)` up to a relative `2^(−2e)`, at no
extra cost.  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscWithPeriodPrecRound x u p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard W nan 360 53 == (nan, .eq)
#guard W zero 360 53 == (nan, .eq)
#guard W zero 0 53 == (nan, .eq)
#guard W (F "1/2" 53) 360 53 == (nan, .eq)
#guard W (F "-3/4" 53) 0 53 == (nan, .eq)
#guard W (infinity true) 360 53 == (zero, .eq)
#guard W (infinity false) 360 53 == (zero, .eq)
#guard W (infinity false) 0 0 == (zero, .eq)
#guard W (F "3" 53) 0 53 == (zero, .eq)
#guard W (F "-1" 53) 0 53 == (zero, .eq)
#guard W (F "3" 53) 360 0 == (nan, .eq)
#guard W (F "1" 53) 360 53 == (F "90" 53, .eq)
#guard W (F "-1" 200) 360 53 == (F "-90" 53, .eq)
#guard W (F "1" 53) 7 1 == (F "2" 1, .gt)
#guard W (F "-1" 53) 7 1 == (F "-2" 1, .lt)
-- a twelfth of a turn
#guard W (F "2" 53) 360 53 == (F "30" 53, .eq)
#guard W (F "-2" 200) 360 53 == (F "-30" 53, .eq)
#guard W (F "2" 53) 3 53 == (F "1/4" 53, .eq)
#guard W (F "2" 53) 7 53 == (F "5254199565265579/9007199254740992" 53, .gt)
#guard W (F "2" 53) 7 53 .Floor == (F "2627099782632789/4503599627370496" 53, .lt)
#guard W (F "-2" 53) 7 53 == (F "-5254199565265579/9007199254740992" 53, .lt)
#guard W (F "2" 53) 1 53 == (F "6004799503160661/72057594037927936" 53, .lt)
#guard W (F "-2" 53) 1 53 .Floor == (F "-3002399751580331/36028797018963968" 53, .lt)

-- correctly rounded values
#guard W (F "3" 53) 360 53 == (F "42817666989229/2199023255552" 53, .gt)
#guard W (F "-3" 53) 360 53 == (F "-42817666989229/2199023255552" 53, .lt)
#guard W (F "3/2" 53) 360 53 == (F "5884278705777237/140737488355328" 53, .lt)
#guard W (F "-7/5" 53) 360 53 == (F "-6415474975483775/140737488355328" 53, .lt)
#guard W (F "5/4" 53) 360 53 == (F "1869349290346353/35184372088832" 53, .gt)
#guard W (F "100" 53) 360 53 == (F "2580415520794135/4503599627370496" 53, .lt)
#guard W (F "-1000" 53) 360 53 == (F "-8257193416679921/144115188075855872" 53, .gt)
#guard W (F "1000001/1000000" 53) 360 53 == (F "98866954793719/1099511627776" 53, .gt)
#guard W (F "-1000001/1000000" 53) 360 53 == (F "-98866954793719/1099511627776" 53, .lt)
#guard W (F "22/7" 53) 360 53 == (F "5222206519407635/281474976710656" 53, .lt)
#guard W (F "1125899906842624" 53) 360 53
  == (F "1007958012753983/19807040628566084398385987584" 53, .gt)
#guard W (F "3/2" 53) 1 53 == (F "2092187984276351/18014398509481984" 53, .lt)
#guard W (F "-4" 53) 1 53 == (F "-5795637198738295/144115188075855872" 53, .gt)
#guard W (F "3/2" 53) 7 53 == (F "7322657944967229/9007199254740992" 53, .gt)
#guard W (F "-4" 53) 7 53 == (F "-633897818612001/2251799813685248" 53, .gt)
#guard W (F "3/2" 53) 400 53 == (F "6538087450863597/140737488355328" 53, .gt)
#guard W (F "-4" 53) 400 53 == (F "-4527841561514293/281474976710656" 53, .gt)
#guard W (F "3/2" 53) 18446744073709551615 53 == (F "2142400495898983424" 53, .lt)
#guard W (F "-4" 53) 18446744073709551615 53 == (F "-741841561438501760" 53, .gt)
#guard W (F "3/2" 53) 360 53 .Floor == (F "5884278705777237/140737488355328" 53, .lt)
#guard W (F "-4" 53) 360 53 .Floor == (F "-254691087835179/17592186044416" 53, .lt)
#guard W (F "3/2" 53) 360 53 .Ceiling == (F "2942139352888619/70368744177664" 53, .gt)
#guard W (F "-4" 53) 360 53 .Ceiling == (F "-8150114810725727/562949953421312" 53, .gt)
#guard W (F "3/2" 53) 360 20 == (F "171255/4096" 20, .lt)
#guard W (F "-4" 53) 360 1 == (F "-16" 1, .lt)
#guard W (F "3/2" 53) 360 113
  == (F "6784111458990722617650671609596317/162259276829213363391578010288128" 113, .lt)
#guard acscWithPeriod (F "3/2" 53) 360 == (W (F "3/2" 53) 360 53).1
#guard (toString (acscWithPeriodPrecRound (F "3/2" 200) 360 200 .Nearest).1).startsWith
  "41.81031489577859806585791673057825953101411953590134775"

-- oddness: `f(−x, u, m) = −f(x, u, −m)`
private def odd (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode) : Bool :=
  let r := W x u p (-m)
  W (-x) u p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 360 53 .Nearest && odd (F "3/2" 53) 7 53 .Floor
#guard odd (F "1000001/1000000" 53) 400 20 .Ceiling && odd (F "2" 53) 7 53 .Floor

-- next to `±1`
#guard W (F "4503599627370497/4503599627370496" 53) 360 53
  == (F "6333186891025253/70368744177664" 53, .gt)
#guard W (F "-4503599627370497/4503599627370496" 53) 360 53
  == (F "-6333186891025253/70368744177664" 53, .lt)
#guard W (F "-4503599627370497/4503599627370496" 53) 360 53 .Ceiling
  == (F "-1583296722756313/17592186044416" 53, .gt)

-- huge arguments: `360/(2π) / x`
private def cN : AzFloat := F "1007958012753983/17592186044416" 53
private def cF : AzFloat := F "8063664102031863/140737488355328" 53
private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)
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
