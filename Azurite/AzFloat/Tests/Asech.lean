/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asech
import Azurite.AzFloat.Ln
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asech x`

The special values (`NaN`; `±∞ ↦ NaN`; `NaN` for `x < 0` and `x > 1`; `asech 0 = +∞`;
`asech 1 = 0`; `p = 0`), the correctly rounded 53-bit values from `2^(−200)` to `1 − 2^(−53)`
in three modes (next to `1` the value is `≈ √(2 (1 − x))`), 1-, 2-, 20-, 113-, 120- and
200-bit results, 200-bit strings, and tiny arguments
`2^(−2^30)`, `3·2^(−2^30)` (where `asech x` rounds like `ln (2/x)`).  References: an
independent 6000-bit fixed-point evaluation of `ln (1/x + √(1/x² − 1))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asechPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (nan, .eq)
#guard A (infinity false) 53 == (nan, .eq)
#guard A zero 53 == (infinity true, .eq)
#guard A zero 0 == (infinity true, .eq)
#guard A (F "1" 53) 53 == (zero, .eq)
#guard A (F "1" 200) 1 .Floor == (zero, .eq)
#guard A (F "1" 53) 0 == (zero, .eq)
#guard A (F "2" 53) 53 == (nan, .eq)
#guard A (F "4503599627370497/4503599627370496" 53) 53 == (nan, .eq)
#guard A (h (F "1" 53) 1000) 53 == (nan, .eq)
#guard A (F "-1/2" 53) 53 == (nan, .eq)
#guard A (F "-1" 53) 53 == (nan, .eq)
#guard A (F "-3" 53) 53 == (nan, .eq)
#guard A (h (F "-1" 53) (-1000)) 53 == (nan, .eq)
#guard A (F "1/2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1/2" 53) 53 == (F "5931051093853237/4503599627370496" 53, .gt)
#guard A (F "1/3" 53) 53 == (F "7938707516150823/4503599627370496" 53, .lt)
#guard A (F "2/7" 53) 53 == (F "4334370792049413/2251799813685248" 53, .gt)
#guard A (F "3/4" 53) 53 == (F "223875474674459/281474976710656" 53, .lt)
#guard A (F "99/100" 53) 53 == (F "5116609459402099/36028797018963968" 53, .gt)
#guard A (F "999999/1000000" 53) 53 == (F "3260955815111981/2305843009213693952" 53, .gt)
#guard A (F "9007199254740991/9007199254740992" 53) 53 == (F "1/67108864" 53, .lt)
#guard A (F "4503599627370495/4503599627370496" 53) 53
  == (F "6369051672525773/302231454903657293676544" 53, .lt)
#guard A (F "1/1000" 53) 53 == (F "2139463772410805/281474976710656" 53, .gt)
#guard A (F "1/1000000000000" 53) 53 == (F "498284038225175/17592186044416" 53, .gt)
#guard A (F "1/1125899906842624" 53) 53 == (F "4975141455881771/140737488355328" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "4926365559255479/70368744177664" 53, .gt)
#guard A (F "3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "4863323627396471/35184372088832" 53, .gt)
#guard A (F "1/2" 53) 53 .Floor == (F "1482762773463309/1125899906842624" 53, .lt)
#guard A (F "99/100" 53) 53 .Floor == (F "2558304729701049/18014398509481984" 53, .lt)
#guard A (F "9007199254740991/9007199254740992" 53) 53 .Floor == (F "1/67108864" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "8557855089643219/1125899906842624" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "2463182779627739/35184372088832" 53, .lt)
#guard A (F "1/2" 53) 53 .Ceiling == (F "5931051093853237/4503599627370496" 53, .gt)
#guard A (F "99/100" 53) 53 .Ceiling == (F "5116609459402099/36028797018963968" 53, .gt)
#guard A (F "9007199254740991/9007199254740992" 53) 53 .Ceiling
  == (F "4503599627370497/302231454903657293676544" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "2139463772410805/281474976710656" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "4926365559255479/70368744177664" 53, .gt)
#guard A (F "1/2" 53) 20 == (F "690465/524288" 20, .lt)
#guard A (F "1/2" 53) 1 == (F "1" 1, .lt)
#guard A (F "3/4" 53) 2 == (F "3/4" 2, .lt)
#guard A (F "3/4" 53) 113
  == (F "8259547171399978926639845712777699/10384593717069655257060992658440192" 113, .lt)
#guard A (F "1/3" 200) 200
  == (h (F "1416312748186715446898730825533860510221026663879987549855105" 200) (-199), .lt)
#guard A (F "1/3" 200) 10 .Floor == (F "451/256" 10, .lt)
#guard A (F "7/8" 53) 120
  == (F "351152370089074282585698552969043841/664613997892457936451903530140172288" 120, .gt)
#guard asech (F "1/2" 53) == (A (F "1/2" 53) 53).1
#guard (toString (asechPrecRound (F "1/2" 200) 200 .Nearest).1).startsWith
  "1.316957896924816708625046347307968444026981971467516479"
#guard (toString (asechPrecRound (F "3/4" 200) 200 .Nearest).1).startsWith
  "0.795365461223905630527890933147806300976582563714367134"

-- tiny arguments: `asech x` rounds like `ln (2/x)`; for `x = 2^(−k)` that is `(k + 1) ln 2`
private def tiny (x y : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  A x p m == lnPrecRound y p m
#guard tiny (h (F "1" 53) (-1073741824)) (h (F "1" 53) 1073741825) 53 .Nearest
#guard tiny (h (F "1" 53) (-1073741824)) (h (F "1" 53) 1073741825) 53 .Floor
#guard tiny (h (F "1" 53) (-100000)) (h (F "1" 53) 100001) 113 .Ceiling
