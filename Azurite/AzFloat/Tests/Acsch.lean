/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsch
import Azurite.AzFloat.Ln
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acsch x`

The special values (`NaN`, `±∞ ↦ 0`, `acsch 0 = +∞`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `2^101` in three modes — across the switch to the huge-argument
enclosure — 1-, 2-, 20-, 113-, 120- and 200-bit results, 200-bit strings, oddness, huge
arguments `±2^1000`, `±2^(2^30)`, `±3·2^(2^30)` (the value is just inside `1/x`, at no cost),
and tiny arguments `2^(−2^30)` (where `acsch x` rounds like `ln (2/x)`).  References: an
independent 6000-bit fixed-point evaluation of `ln (1/x + √(1/x² + 1))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acschPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (zero, .eq)
#guard A (infinity false) 53 == (zero, .eq)
#guard A (infinity false) 0 == (zero, .eq)
#guard A zero 53 == (infinity true, .eq)
#guard A zero 0 == (infinity true, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "7938707516150823/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 == (F "-7938707516150823/9007199254740992" 53, .lt)
#guard A (F "2" 53) 53 == (F "4334370792049413/9007199254740992" 53, .gt)
#guard A (F "1/2" 53) 53 == (F "6501556188074119/4503599627370496" 53, .lt)
#guard A (F "-1/3" 53) 53 == (F "-4094777398095367/2251799813685248" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "5630806634202923/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "-5983758126563647/9007199254740992" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "5639296546097153/18014398509481984" 53, .lt)
#guard A (F "10" 53) 53 == (F "3596901764234783/36028797018963968" 53, .lt)
#guard A (F "-100" 53) 53 == (F "-5764511450565383/576460752303423488" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "8557855652593173/1125899906842624" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53 == (F "-498284038225175/17592186044416" 53, .lt)
#guard A (F "1/1125899906842624" 53) 53 == (F "4975141455881771/140737488355328" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "4926365559255479/70368744177664" 53, .gt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-4863323627396471/35184372088832" 53, .lt)
#guard A (F "30" 53) 53 == (F "1200737611777035/36028797018963968" 53, .lt)
#guard A (F "-37" 53) 53 == (F "-3894531047907991/144115188075855872" 53, .gt)
#guard A (F "700" 53) 53 == (F "6588120642611631/4611686018427387904" 53, .lt)
#guard A (F "1" 53) 53 .Floor == (F "3969353758075411/4503599627370496" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-7938707516150823/9007199254740992" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "5630806634202923/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "-5983758126563647/9007199254740992" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "8557855652593173/1125899906842624" 53, .lt)
#guard A (F "-100" 53) 53 .Floor == (F "-5764511450565383/576460752303423488" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "2463182779627739/35184372088832" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "7938707516150823/9007199254740992" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-3969353758075411/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "1407701658550731/2251799813685248" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "-2991879063281823/4503599627370496" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "4278927826296587/562949953421312" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling == (F "-2882255725282691/288230376151711744" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "4926365559255479/70368744177664" 53, .gt)
#guard A (F "1" 53) 20 == (F "924187/1048576" 20, .lt)
#guard A (F "1" 53) 1 == (F "1" 1, .gt)
#guard A (F "-3/2" 53) 2 == (F "-3/4" 2, .lt)
#guard A (F "3/2" 53) 113
  == (F "6491878056855450093881103690126781/10384593717069655257060992658440192" 113, .lt)
#guard A (F "1/3" 200) 200
  == (h (F "730532699197015788235251700419320553508952827236660048023317" 200) (-198), .gt)
#guard A (F "1/3" 200) 10 .Floor == (F "931/512" 10, .lt)
#guard A (F "10" 53) 120
  == (F "530809010424907318700422845009159097/5316911983139663491615228241121378304" 120, .gt)
#guard A (F "1000000" 110) 53 == (F "2361183241434429/2361183241434822606848" 53, .lt)
#guard A (F "1000000" 110) 53 .Floor == (F "2361183241434429/2361183241434822606848" 53, .lt)
#guard A (F "1000000" 110) 53 .Ceiling == (F "4722366482868859/4722366482869645213696" 53, .gt)
#guard A (F "-123456789012345678901234567890" 110) 53
  == (F "-1445088301870579/178405961588244985132285746181186892047843328" 53, .gt)
#guard A (F "-123456789012345678901234567890" 110) 53 .Floor
  == (F "-5780353207482317/713623846352979940529142984724747568191373312" 53, .lt)
#guard A (F "-123456789012345678901234567890" 110) 53 .Ceiling
  == (F "-1445088301870579/178405961588244985132285746181186892047843328" 53, .gt)
#guard A (F "1267650600228229401496703205376" 110) 53
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard A (F "1267650600228229401496703205376" 110) 53 .Floor
  == (F "9007199254740991/11417981541647679048466287755595961091061972992" 53, .lt)
#guard A (F "1267650600228229401496703205376" 110) 53 .Ceiling
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard A (F "3802951800684688204490109616128" 110) 53
  == (F "6004799503160661/22835963083295358096932575511191922182123945984" 53, .lt)
#guard A (F "3802951800684688204490109616128" 110) 53 .Floor
  == (F "6004799503160661/22835963083295358096932575511191922182123945984" 53, .lt)
#guard A (F "3802951800684688204490109616128" 110) 53 .Ceiling
  == (F "3002399751580331/11417981541647679048466287755595961091061972992" 53, .gt)
#guard A (F "1125899906842624" 110) 53 == (F "1/1125899906842624" 53, .gt)
#guard A (F "1125899906842624" 110) 53 .Floor
  == (F "9007199254740991/10141204801825835211973625643008" 53, .lt)
#guard A (F "1125899906842624" 110) 53 .Ceiling == (F "1/1125899906842624" 53, .gt)
#guard A (F "-35184372088832" 110) 53 == (F "-1/35184372088832" 53, .lt)
#guard A (F "-35184372088832" 110) 53 .Floor == (F "-1/35184372088832" 53, .lt)
#guard A (F "-35184372088832" 110) 53 .Ceiling
  == (F "-9007199254740991/316912650057057350374175801344" 53, .gt)
#guard acsch (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (acschPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "0.881373587019543025232609324979792309028160328261635410"
#guard (toString (acschPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "-0.62514511725041668763425167322610240703418438895317101"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor
#guard odd (F "100" 53) 20 .Ceiling && odd (F "1/1000" 53) 113 .Floor
#guard odd (h (F "1" 53) (-1000)) 53 .Ceiling && odd (h (F "1" 53) 1000) 53 .Ceiling

-- huge arguments: just inside `1/x`
private def hugeOk (k : Int) : Bool :=
  let x := h (F "1" 53) k
  let y := h (F "1" 53) (-k)
  A x 53 == (y, .gt) && A x 53 .Ceiling == (y, .gt) && A x 53 .Floor == (h dn (-k), .lt)
    && A (-x) 53 == (-y, .lt) && A (-x) 53 .Floor == (-y, .lt)
    && A (-x) 53 .Ceiling == (-(h dn (-k)), .gt)
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

-- tiny arguments: `acsch x` rounds like `ln (2/x)`
#guard A (h (F "1" 53) (-1073741824)) 53 == lnPrecRound (h (F "1" 53) 1073741825) 53 .Nearest
#guard A (h (F "1" 53) (-100000)) 113 .Floor == lnPrecRound (h (F "1" 53) 100001) 113 .Floor
