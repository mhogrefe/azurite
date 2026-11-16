/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sinh
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinh x`

The special values (`NaN`, `±∞`, `0`, `p = 0`), the correctly rounded 53-bit values from
`2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results, a 200-bit
string, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)`, `±3·2^(−2^30)` (the value is just
outside `x`, at no cost), an argument more precise than the result, and large arguments
(`±2^20`, where `sinh x` rounds like `±exp |x| / 2`).  References: an independent 6000-bit
fixed-point evaluation of `(e^x − e^(−x))/2` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinhPrecRound x p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (infinity true, .eq)
#guard A (infinity false) 53 == (infinity false, .eq)
#guard A (infinity false) 0 == (infinity false, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "2646317828889793/2251799813685248" 53, .lt)
#guard A (F "-1" 53) 53 == (F "-2646317828889793/2251799813685248" 53, .gt)
#guard A (F "2" 53) 53 == (F "8166963590652319/2251799813685248" 53, .lt)
#guard A (F "1/2" 53) 53 == (F "4693609247292311/9007199254740992" 53, .gt)
#guard A (F "-1/3" 53) 53 == (F "-6116618908543873/18014398509481984" 53, .lt)
#guard A (F "3/2" 53) 53 == (F "149834721258323/70368744177664" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "-2144052883084551/1125899906842624" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "6509619147470761/562949953421312" 53, .gt)
#guard A (F "10" 53) 53 == (F "3027294401285321/274877906944" 53, .gt)
#guard A (F "-100" 53) 53 == (F "-13440585709080678047126700217981451777343488" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "4611686787041763/4611686018427387904" 53, .gt)
#guard A (F "-1/1000000000000" 53) 53
  == (F "-4951760157141521/4951760157141521099596496896" 53, .gt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1/1125899906842624" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "1/1267650600228229401496703205376" 53, .lt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53, .gt)
#guard A (F "30" 53) 53 == (F "5471474985740525/1024" 53, .gt)
#guard A (F "-37" 53) 53 == (F "-5859571186401306" 53, .lt)
#guard A (F "700" 53) 53
  == (h (F "4162952793716295" 53) (957), .lt)
#guard A (F "1" 53) 53 .Floor == (F "2646317828889793/2251799813685248" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-5292635657779587/4503599627370496" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "149834721258323/70368744177664" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "-2144052883084551/1125899906842624" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "2305843393520881/2305843009213693952" 53, .lt)
#guard A (F "-100" 53) 53 .Floor == (F "-13440585709080678047126700217981451777343488" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "1/1267650600228229401496703205376" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "5292635657779587/4503599627370496" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-2646317828889793/2251799813685248" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "4794711080266337/2251799813685248" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "-8576211532338203/4503599627370496" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "4611686787041763/4611686018427387904" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling == (F "-13440585709080675571246621647220901979095040" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "4503599627370497/5708990770823839524233143877797980545530986496" 53, .gt)
#guard A (F "1" 53) 20 == (F "38509/32768" 20, .gt)
#guard A (F "1" 53) 1 == (F "1" 1, .lt)
#guard A (F "-3/2" 53) 2 == (F "-2" 2, .gt)
#guard A (F "3/2" 53) 113
  == (F "5527925512815785231171841913352779/2596148429267413814265248164610048" 113, .lt)
#guard A (F "1/3" 200) 200
  == (h (F "545620639023805613979149325531051054693636118293968280010031" 200) (-200), .lt)
#guard A (F "1/3" 200) 10 .Floor == (F "695/2048" 10, .lt)
#guard A (F "10" 53) 120
  == (F "55843725056284099936909113149749201/5070602400912917605986812821504" 120, .lt)
#guard sinh (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (sinhPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "1.175201193643801456882381850595600815155717981334095870"
#guard (toString (sinhPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "-2.12927945509481749683438749467763164883178911950429386"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor && odd (F "100" 53) 20 .Ceiling
#guard odd (F "1/1000" 53) 113 .Floor && odd (h (F "1" 53) (-1000)) 53 .Ceiling

-- tiny arguments: just outside `x`
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def tinyOk (k : Int) : Bool :=
  let x := h (F "1" 53) (-k)
  A x 53 == (x, .lt) && A x 53 .Floor == (x, .lt) && A x 53 .Ceiling == (h up (-k), .gt)
    && A (-x) 53 == (-x, .gt) && A (-x) 53 .Ceiling == (-x, .gt)
    && A (-x) 53 .Floor == (-(h up (-k)), .lt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824
private def t3 : AzFloat := h (F "3" 53) (-1073741824)
#guard A t3 53 == (t3, .lt)
#guard A t3 2 .Ceiling == (h (F "4" 2) (-1073741824), .gt)
#guard A t3 1 == (h (F "4" 1) (-1073741824), .gt)
#guard A (-t3) 1 .Ceiling == (-(h (F "2" 1) (-1073741824)), .gt)
-- an argument more precise than the result
private def fine : AzFloat := h (F "1267650600228229401496703205377" 101) (-300)
#guard A fine 53 == (h (F "1" 53) (-200), .lt)
#guard A fine 53 .Ceiling == (h up (-200), .gt)
#guard A fine 101 == (fine, .lt)

-- large arguments: `sinh x` rounds like `exp |x| / 2`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound x p m
  A x p m == (h r.1 (-1), r.2)
#guard big (F "1048576" 53) 53 .Nearest && big (F "1048576" 53) 53 .Floor
#guard big (F "123456789/8" 53) 20 .Ceiling && big (F "1000" 53) 113 .Nearest
#guard odd (F "1048576" 53) 53 .Floor
