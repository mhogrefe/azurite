/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcoshRat
import Azurite.AzFloat.Acosh
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acosh q` of a rational

The special values (`NaN` below `1`, `acosh 1 = 0`, `p = 0`), the correctly rounded 53-bit
values at exact rationals from `1 + 10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113-
and 200-bit results, agreement with the float `acosh` at representable arguments, 200-bit
strings, rationals extremely close to `1` (`1 + 2^(−5000)`, where the value is `≈ 2^(−2499.5)`),
and a huge rational (where `acosh q` rounds like `ln (2q)`).  References: an independent
6000-bit fixed-point evaluation of `ln (q + √(q² − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acoshRatPrecRound (Q q) p m

-- special values
#guard T "1" 53 == (zero, .eq)
#guard T "3/3" 0 == (zero, .eq)
#guard T "0" 53 == (nan, .eq)
#guard T "1/2" 53 == (nan, .eq)
#guard T "999999/1000000" 53 == (nan, .eq)
#guard T "-1" 53 == (nan, .eq)
#guard T "-3" 53 == (nan, .eq)
#guard T "4/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "2" 53 == (F "5931051093853237/4503599627370496" 53, .gt)
#guard T "4/3" 53 == (F "223875474674459/281474976710656" 53, .lt)
#guard T "22/7" 53 == (F "8160300771249005/4503599627370496" 53, .gt)
#guard T "355/113" 53 == (F "4079194724512939/2251799813685248" 53, .gt)
#guard T "7/5" 53 == (F "7809374398295283/9007199254740992" 53, .lt)
#guard T "10" 53 == (F "1685034661806453/562949953421312" 53, .lt)
#guard T "100/3" 53 == (F "4728194142931667/1125899906842624" 53, .gt)
#guard T "1000001/1000000" 53 == (F "815238546146763/576460752303423488" 53, .lt)
#guard T "1000000007/1000000006" 53 == (F "6599707773627853/147573952589676412928" 53, .gt)
#guard T "700/3" 53 == (F "6919342441512837/1125899906842624" 53, .lt)
#guard T "3000000000000000000000000000001/3000000000000000000000000000000" 53
  == (F "1035032380897329/1267650600228229401496703205376" 53, .gt)
#guard T "4/3" 53 .Floor == (F "223875474674459/281474976710656" 53, .lt)
#guard T "22/7" 53 .Floor == (F "2040075192812251/1125899906842624" 53, .lt)
#guard T "1000001/1000000" 53 .Floor == (F "815238546146763/576460752303423488" 53, .lt)
#guard T "100/3" 53 .Floor == (F "2364097071465833/562949953421312" 53, .lt)
#guard T "4/3" 53 .Ceiling == (F "7164015189582689/9007199254740992" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "8160300771249005/4503599627370496" 53, .gt)
#guard T "1000001/1000000" 53 .Ceiling == (F "6521908369174105/4611686018427387904" 53, .gt)
#guard T "100/3" 53 .Ceiling == (F "4728194142931667/1125899906842624" 53, .gt)
#guard T "4/3" 20 == (F "834001/1048576" 20, .lt)
#guard T "4/3" 1 == (F "1" 1, .gt)
#guard T "22/7" 2 == (F "2" 2, .gt)
#guard T "4/3" 113
  == (F "8259547171399978926639845712777699/10384593717069655257060992658440192" 113, .lt)
#guard T "7/5" 200
  == (h (F "696619474465246027754818035546008576481904682180959016208361" 200) (-199), .gt)

-- agreement with the float `acosh` at representable arguments
#guard T "3/2" 53 == acoshPrecRound (F "3/2" 53) 53 .Nearest
#guard T "1025/1024" 53 .Floor == acoshPrecRound (F "1025/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == acoshPrecRound (F "100" 53) 20 .Ceiling
#guard acoshRat (Q "4/3") 53 == (T "4/3" 53).1
#guard (toString (acoshRat (Q "4/3") 200)).startsWith
  "0.795365461223905630527890933147806300976582563714367134"
#guard (toString (acoshRat (Q "22/7") 200)).startsWith
  "1.811950760821413556235972813109322036695962129898042791"

-- next to `1`: `acosh (1 + 2^(−5000)) = √2 · 2^(−2500) (1 − …)`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard acoshRatPrecRound (1 + pw 5000) 53 .Nearest
  == (h (F "6369051672525773/4503599627370496" 53) (-2500), .gt)
#guard acoshRatPrecRound (1 + pw 5000) 53 .Floor
  == (h (F "1592262918131443/1125899906842624" 53) (-2500), .lt)
-- `acosh (1 + 2^(−5001)) = 2^(−2500) (1 − 2^(−5001)/12 + …)`: just below a float
#guard acoshRatPrecRound (1 + pw 5001) 53 .Nearest == (h (F "1" 53) (-2500), .gt)
#guard acoshRatPrecRound (1 + pw 5001) 53 .Floor
  == (h (F "9007199254740991/9007199254740992" 53) (-2500), .lt)

-- a huge rational: `acosh q` rounds like `ln (2q)`
private def bigq : AzRat := Q "2/3" * (pw 5000)⁻¹
#guard acoshRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard acoshRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Floor == lnRatPrecRound bigq 53 .Floor
