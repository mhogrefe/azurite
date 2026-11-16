/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Csch
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `csch x`

The special values (`NaN`, `±∞ ↦ 0`, `csch 0 = +∞`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results,
200-bit strings, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)`, `±3·2^(−2^30)` (the value
is just inside `1/x`, at no cost), and large arguments (`±2^20`, where `csch x` rounds like
`±2 exp (−|x|)`).  References: an independent 6000-bit fixed-point evaluation of
`2/(e^x − e^(−x))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cschPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (zero, .eq)
#guard A (infinity false) 53 == (zero, .eq)
#guard A (infinity false) 0 == (zero, .eq)
#guard A zero 53 == (infinity true, .eq)
#guard A zero 0 == (infinity true, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "7664389130522817/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 == (F "-7664389130522817/9007199254740992" 53, .lt)
#guard A (F "2" 53) 53 == (F "2483470065529171/9007199254740992" 53, .lt)
#guard A (F "1/2" 53) 53 == (F "8642564191023085/4503599627370496" 53, .gt)
#guard A (F "-1/3" 53) 53 == (F "-1657975583154331/562949953421312" 53, .lt)
#guard A (F "3/2" 53) 53 == (F "8460326081848095/18014398509481984" 53, .gt)
#guard A (F "-7/5" 53) 53 == (F "-2364961443310145/4503599627370496" 53, .gt)
#guard A (F "22/7" 53) 53 == (F "3115759792419219/36028797018963968" 53, .lt)
#guard A (F "10" 53) 53 == (F "6699847096152993/73786976294838206464" 53, .gt)
#guard A (F "-100" 53) 53
  == (F "-7472414516752221/100433627766186892221372630771322662657637687111424552206336" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "8796091556192667/8796093022208" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53 == (F "-1000000000000" 53, .gt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1125899906842624" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "1267650600228229401496703205376" 53, .gt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-535646014752996728779660432739556678793109967729782270459904" 53, .gt)
#guard A (F "30" 53) 53 == (F "7413872733224821/39614081257132168796771975168" 53, .gt)
#guard A (F "-37" 53) 53 == (F "-6922830684512341/40564819207303340847894502572032" 53, .lt)
#guard A (F "700" 53) 53
  == (h (F "4872120970063999" 53) (-1061), .lt)
#guard A (F "1" 53) 53 .Floor == (F "119756080164419/140737488355328" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-7664389130522817/9007199254740992" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "4230163040924047/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "-4729922886620291/9007199254740992" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "8796091556192667/8796093022208" 53, .lt)
#guard A (F "-100" 53) 53 .Floor
  == (F "-7472414516752221/100433627766186892221372630771322662657637687111424552206336" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "1267650600228229260759214850048" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "7664389130522817/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-119756080164419/140737488355328" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "8460326081848095/18014398509481984" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "-2364961443310145/4503599627370496" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "2199022889048167/2199023255552" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling
  == (F "-1868103629188055/25108406941546723055343157692830665664409421777856138051584" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "1267650600228229401496703205376" 53, .gt)
#guard A (F "1" 53) 20 == (F "223063/262144" 20, .lt)
#guard A (F "1" 53) 1 == (F "1" 1, .gt)
#guard A (F "-3/2" 53) 2 == (F "-1/2" 2, .lt)
#guard A (F "3/2" 53) 113
  == (F "4877045937874428027712981285910855/10384593717069655257060992658440192" 113, .gt)
#guard A (F "1/3" 200) 200
  == (h (F "295792728202479634110885021201911456459443453125228466475629" 200) (-196), .lt)
#guard A (F "1/3" 200) 10 .Floor == (F "753/256" 10, .lt)
#guard A (F "10" 53) 120
  == (F "494361458862881467777166001960547627/5444517870735015415413993718908291383296" 120, .lt)
#guard csch (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (cschPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "0.850918128239321545133842763287175284181724660910339616"
#guard (toString (cschPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "-0.46964244059522458472956443188701361531532331044785050"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor
#guard odd (F "100" 53) 20 .Ceiling && odd (F "1/1000" 53) 113 .Floor
#guard odd (h (F "1" 53) (-1000)) 53 .Ceiling && odd (F "1048576" 53) 53 .Floor

-- tiny arguments: just inside `1/x`
private def tinyOk (k : Int) : Bool :=
  let x := h (F "1" 53) (-k)
  let y := h (F "1" 53) k
  A x 53 == (y, .gt) && A x 53 .Ceiling == (y, .gt) && A x 53 .Floor == (h dn k, .lt)
    && A (-x) 53 == (-y, .lt) && A (-x) 53 .Floor == (-y, .lt)
    && A (-x) 53 .Ceiling == (-(h dn k), .gt)
#guard tinyOk 100
#guard tinyOk 1000
#guard tinyOk 1073741824
private def t3 : AzFloat := h (F "3" 53) (-1073741824)
#guard A t3 53 == (h (F "6004799503160661/18014398509481984" 53) 1073741824, .lt)
#guard A t3 53 .Ceiling == (h (F "3002399751580331/9007199254740992" 53) 1073741824, .gt)
#guard A (-t3) 53 .Floor == (-(h (F "3002399751580331/9007199254740992" 53) 1073741824), .lt)

-- large arguments: `csch x` rounds like `2 exp (−x)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound (-x) p m
  A x p m == (h r.1 1, r.2)
#guard big (F "1048576" 53) 53 .Nearest && big (F "1048576" 53) 53 .Floor
#guard big (F "123456789/8" 53) 20 .Ceiling && big (F "1000" 53) 113 .Nearest
