/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Tanh
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tanh x`

The special values (`NaN`, `±∞ ↦ ±1`, `0`, `p = 0`), the correctly rounded 53-bit values from
`2^(−200)` to `700` in three modes, the transition to `±1` (`18` to `40`), 1-, 2-, 20-, 113-,
120- and 200-bit results, 200-bit strings, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)`
(the value is just inside `x`, at no cost), and large arguments `±100`, `±2^20`, `±2^(2^30)`
(the value is just inside `±1`, at no cost).  References: an independent 6000-bit fixed-point
evaluation of `(e^(2x) − 1)/(e^(2x) + 1)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := tanhPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (F "1" 53, .eq)
#guard A (infinity false) 53 == (F "-1" 53, .eq)
#guard A (infinity false) 1 .Floor == (F "-1" 1, .eq)
#guard A (infinity true) 0 == (nan, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "1714957578484965/2251799813685248" 53, .lt)
#guard A (F "-1" 53) 53 == (F "-1714957578484965/2251799813685248" 53, .gt)
#guard A (F "2" 53) 53 == (F "2170797125202165/2251799813685248" 53, .gt)
#guard A (F "1/2" 53) 53 == (F "8324762628950771/18014398509481984" 53, .lt)
#guard A (F "-1/3" 53) 53 == (F "-2895929289884673/9007199254740992" 53, .lt)
#guard A (F "3/2" 53) 53 == (F "8152850675660151/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "-996817338233891/1125899906842624" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "8973705755907005/9007199254740992" 53, .lt)
#guard A (F "10" 53) 53 == (F "9007199217610549/9007199254740992" 53, .lt)
#guard A (F "-100" 53) 53 == (F "-1" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "2305842240599665/2305843009213693952" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53
  == (F "-4951760157141521/4951760157141521099596496896" 53, .lt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53, .lt)
#guard A (F "30" 53) 53 == (F "1" 53, .gt)
#guard A (F "-37" 53) 53 == (F "-1" 53, .lt)
#guard A (F "700" 53) 53 == (F "1" 53, .gt)
#guard A (F "1" 53) 53 .Floor == (F "1714957578484965/2251799813685248" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-6859830313939861/9007199254740992" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "8152850675660151/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "-996817338233891/1125899906842624" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "2305842240599665/2305843009213693952" 53, .lt)
#guard A (F "-100" 53) 53 .Floor == (F "-1" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "9007199254740991/11417981541647679048466287755595961091061972992" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "6859830313939861/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-1714957578484965/2251799813685248" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "1019106334457519/1125899906842624" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "-7974538705871127/9007199254740992" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "4611684481199331/4611686018427387904" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling == (F "-9007199254740991/9007199254740992" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard A (F "1" 53) 20 == (F "798589/1048576" 20, .lt)
#guard A (F "1" 53) 1 == (F "1" 1, .gt)
#guard A (F "-3/2" 53) 2 == (F "-1" 2, .lt)
#guard A (F "3/2" 53) 113
  == (F "9399596867817050698161137246586739/10384593717069655257060992658440192" 113, .lt)
#guard A (F "1/3" 200) 200
  == (h (F "1033302099306877109020385759981387236169641414901540924688809" 200) (-201), .gt)
#guard A (F "1/3" 200) 10 .Floor == (F "329/1024" 10, .lt)
#guard A (F "10" 53) 120
  == (F "332306997576357421770055751771202145/332306998946228968225951765070086144" 120, .lt)
#guard tanh (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (tanhPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "0.761594155955764888119458282604793590412768597257936551"
#guard (toString (tanhPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "-0.90514825364486643824230369645649559722764113515878179"

-- the transition to `±1`
#guard A (F "18" 53) 53 == (F "2251799813685247/2251799813685248" 53, .gt)
#guard A (F "18" 53) 53 .Floor == (F "9007199254740987/9007199254740992" 53, .lt)
#guard A (F "18" 53) 53 .Ceiling == (F "2251799813685247/2251799813685248" 53, .gt)
#guard A (F "-19" 53) 53 == (F "-9007199254740991/9007199254740992" 53, .gt)
#guard A (F "-19" 53) 53 .Floor == (F "-1" 53, .lt)
#guard A (F "-19" 53) 53 .Ceiling == (F "-9007199254740991/9007199254740992" 53, .gt)
#guard A (F "20" 53) 53 == (F "1" 53, .gt)
#guard A (F "20" 53) 53 .Floor == (F "9007199254740991/9007199254740992" 53, .lt)
#guard A (F "20" 53) 53 .Ceiling == (F "1" 53, .gt)
#guard A (F "40" 53) 53 == (F "1" 53, .gt)
#guard A (F "40" 53) 53 .Floor == (F "9007199254740991/9007199254740992" 53, .lt)
#guard A (F "40" 53) 53 .Ceiling == (F "1" 53, .gt)
#guard A (F "75/4" 53) 53 == (F "9007199254740991/9007199254740992" 53, .lt)
#guard A (F "75/4" 53) 53 .Floor == (F "9007199254740991/9007199254740992" 53, .lt)
#guard A (F "75/4" 53) 53 .Ceiling == (F "1" 53, .gt)

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

-- large arguments: just inside `±1`
private def bigOk (x : AzFloat) : Bool :=
  A x 53 == (F "1" 53, .gt) && A x 53 .Ceiling == (F "1" 53, .gt) && A x 53 .Floor == (dn, .lt)
    && A (-x) 53 == (F "-1" 53, .lt) && A (-x) 53 .Floor == (F "-1" 53, .lt)
    && A (-x) 53 .Ceiling == (-dn, .gt) && A x 1 .Floor == (F "1/2" 1, .lt)
    && A x 200 .Nearest == (F "1" 200, .gt)
#guard bigOk (F "1000" 53)
#guard bigOk (F "1048576" 53)
#guard bigOk (h (F "1" 53) 1073741824)
#guard bigOk (h (F "3" 53) 1073741824)
#guard A (F "100" 53) 53 == (F "1" 53, .gt)
#guard A (F "100" 53) 53 .Floor == (dn, .lt)
