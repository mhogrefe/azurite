/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sech
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sech x`

The special values (`NaN`, `±∞ ↦ 0`, `sech 0 = 1`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results,
200-bit strings, evenness, tiny arguments `±2^(−1000)`, `±2^(−2^30)` (the value is just below
`1`, at no cost), the neighbourhood of the last place (`2^(−26)`, `2^(−27)`), and large
arguments (`±2^20`, where `sech x` rounds like `2 exp (−|x|)`).  References: an independent
6000-bit fixed-point evaluation of `2/(e^x + e^(−x))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sechPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (zero, .eq)
#guard A (infinity false) 53 == (zero, .eq)
#guard A (infinity false) 0 == (zero, .eq)
#guard A zero 53 == (F "1" 53, .eq)
#guard A zero 1 .Floor == (F "1" 1, .eq)
#guard A zero 0 == (nan, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "5837153970777063/9007199254740992" 53, .lt)
#guard A (F "-1" 53) 53 == (F "5837153970777063/9007199254740992" 53, .lt)
#guard A (F "2" 53) 53 == (F "2394133637462817/9007199254740992" 53, .lt)
#guard A (F "1/2" 53) 53 == (F "499234649424093/562949953421312" 53, .gt)
#guard A (F "-1/3" 53) 53 == (F "2132241074002227/2251799813685248" 53, .lt)
#guard A (F "3/2" 53) 53 == (F "7657849378250919/18014398509481984" 53, .gt)
#guard A (F "-7/5" 53) 53 == (F "4187645023538877/9007199254740992" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "6208347521242877/72057594037927936" 53, .gt)
#guard A (F "10" 53) 53 == (F "6699847068534165/73786976294838206464" 53, .gt)
#guard A (F "-100" 53) 53
  == (F "7472414516752221/100433627766186892221372630771322662657637687111424552206336" 53, .gt)
#guard A (F "1/1000" 53) 53 == (F "9007194751143241/9007199254740992" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53 == (F "1" 53, .gt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 == (F "1" 53, .gt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "1" 53, .gt)
#guard A (F "30" 53) 53 == (F "7413872733224821/39614081257132168796771975168" 53, .gt)
#guard A (F "-37" 53) 53 == (F "6922830684512341/40564819207303340847894502572032" 53, .gt)
#guard A (F "700" 53) 53
  == (h (F "4872120970063999" 53) (-1061), .lt)
#guard A (F "1" 53) 53 .Floor == (F "5837153970777063/9007199254740992" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "5837153970777063/9007199254740992" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "3828924689125459/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "4187645023538877/9007199254740992" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "9007194751143241/9007199254740992" 53, .lt)
#guard A (F "-100" 53) 53 .Floor
  == (F "1868103629188055/25108406941546723055343157692830665664409421777856138051584" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "9007199254740991/9007199254740992" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "729644246347133/1125899906842624" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "729644246347133/1125899906842624" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "7657849378250919/18014398509481984" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "8375290047077755/18014398509481984" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "4503597375571621/4503599627370496" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling
  == (F "7472414516752221/100433627766186892221372630771322662657637687111424552206336" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling == (F "1" 53, .gt)
#guard A (F "1" 53) 20 == (F "339767/524288" 20, .lt)
#guard A (F "1" 53) 1 == (F "1/2" 1, .lt)
#guard A (F "-3/2" 53) 2 == (F "3/8" 2, .lt)
#guard A (F "3/2" 53) 113
  == (F "8828899227225656611519637096835299/20769187434139310514121985316880384" 113, .lt)
#guard A (F "1/3" 200) 200
  == (h (F "1521618076581278249287038293277146699851690216099029011451977" 200) (-200), .gt)
#guard A (F "1/3" 200) 10 .Floor == (F "969/1024" 10, .lt)
#guard A (F "10" 53) 120
  == (F "988722913649943297038269511076447267/10889035741470030830827987437816582766592" 120, .lt)
#guard sech (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (sechPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "0.648054273663885399574977353226150323108489312071942023"
#guard (toString (sechPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "0.425096034942280460924680900107124339005353669915344249"

-- evenness
private def even (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool := A (-x) p m == A x p m
#guard even (F "3/2" 53) 53 .Nearest && even (F "3/2" 53) 53 .Floor
#guard even (F "100" 53) 20 .Ceiling && even (h (F "1" 53) (-1000)) 53 .Floor

-- tiny arguments: just below `1`
private def tinyOk (x : AzFloat) : Bool :=
  A x 53 == (F "1" 53, .gt) && A x 53 .Ceiling == (F "1" 53, .gt) && A x 53 .Floor == (dn, .lt)
    && A (-x) 53 .Floor == (dn, .lt) && A x 1 .Floor == (F "1/2" 1, .lt)
#guard tinyOk (h (F "1" 53) (-100))
#guard tinyOk (h (F "1" 53) (-1000))
#guard tinyOk (h (F "3" 53) (-1073741824))
-- `sech (2^(−26)) = 1 − 2^(−53) + …`: just above the float below `1`
#guard A (h (F "1" 53) (-26)) 53 == (dn, .lt)
#guard A (h (F "1" 53) (-26)) 53 .Ceiling == (F "1" 53, .gt)
#guard A (h (F "1" 53) (-27)) 53 == (F "1" 53, .gt)
#guard A (h (F "1" 53) (-27)) 53 .Floor == (dn, .lt)

-- large arguments: `sech x` rounds like `2 exp (−|x|)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound (-x) p m
  A x p m == (h r.1 1, r.2) && A (-x) p m == (h r.1 1, r.2)
#guard big (F "1048576" 53) 53 .Nearest && big (F "1048576" 53) 53 .Floor
#guard big (F "123456789/8" 53) 20 .Ceiling && big (F "1000" 53) 113 .Nearest
