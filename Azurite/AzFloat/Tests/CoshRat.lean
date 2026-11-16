/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CoshRat
import Azurite.AzFloat.Cosh
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cosh q` of a rational

The special values (`cosh 0 = 1`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results,
agreement with the float `cosh` at representable arguments, evenness, 200-bit strings, tiny
rationals `±2^(−5000)`, `±1/(3·2^5000)` (the value is just above `1`, at no cost), and a large
rational (where `cosh q` rounds like `exp |q| / 2`).  References: an independent 6000-bit
fixed-point evaluation of `(e^q + e^(−q))/2` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  coshRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (F "1" 53, .eq)
#guard T "0" 1 .Ceiling == (F "1" 1, .eq)
#guard T "0" 0 == (nan, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "434338585747285/281474976710656" 53, .lt)
#guard T "-1" 53 == (F "434338585747285/281474976710656" 53, .lt)
#guard T "1/3" 53 == (F "4756124870435379/4503599627370496" 53, .gt)
#guard T "-2/7" 53 == (F "4688673906816253/4503599627370496" 53, .lt)
#guard T "22/7" 53 == (F "816739459826149/70368744177664" 53, .gt)
#guard T "355/113" 53 == (F "6525691290847735/562949953421312" 53, .gt)
#guard T "-7/5" 53 == (F "37839005965845/17592186044416" 53, .gt)
#guard T "10" 53 == (F "6054588827529517/549755813888" 53, .lt)
#guard T "-100/3" 53 == (F "2396473975313455/16" 53, .gt)
#guard T "1/1000" 53 == (F "4503601879170497/4503599627370496" 53, .lt)
#guard T "-1/1000000007" 53 == (F "1" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "1" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53 == (F "1" 53, .lt)
#guard T "700/3" 53
  == (h (F "3482012665771007" 53) (284), .lt)
#guard T "1/3" 53 .Floor == (F "2378062435217689/2251799813685248" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "4688673906816253/4503599627370496" 53, .lt)
#guard T "22/7" 53 .Floor == (F "6533915678609191/562949953421312" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "4792947950626909/32" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "1" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "4756124870435379/4503599627370496" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "2344336953408127/2251799813685248" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "816739459826149/70368744177664" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "2396473975313455/16" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "4503599627370497/4503599627370496" 53, .gt)
#guard T "1/3" 20 == (F "276843/262144" 20, .gt)
#guard T "1/3" 1 == (F "1" 1, .lt)
#guard T "-22/7" 2 == (F "12" 2, .gt)
#guard T "1/3" 113
  == (F "5483438641720401983200035971670981/5192296858534827628530496329220096" 113, .lt)
#guard T "-7/5" 200
  == (h (F "864090143344629180963974303572801625437339576417648543148831" 200) (-198), .lt)

-- agreement with the float `cosh` at representable arguments, evenness
#guard T "3/2" 53 == coshPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == coshPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == coshPrecRound (F "100" 53) 20 .Ceiling
#guard coshRat (Q "1/3") 53 == (T "1/3" 53).1
#guard T "-22/7" 53 .Floor == T "22/7" 53 .Floor
#guard T "-1/1000000007" 20 .Ceiling == T "1/1000000007" 20 .Ceiling
#guard (toString (coshRat (Q "1/3") 200)).startsWith
  "1.056071867829939389526864708263983252525509287510"
#guard (toString (coshRat (Q "-22/7") 200)).startsWith
  "11.60656580376196641440105294515190289031076068876"

-- tiny rationals: just above `1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def tinyOk (q : AzRat) : Bool :=
  coshRatPrecRound q 53 .Nearest == (F "1" 53, .lt)
    && coshRatPrecRound q 53 .Floor == (F "1" 53, .lt)
    && coshRatPrecRound q 53 .Ceiling == (up, .gt)
    && coshRatPrecRound (-q) 53 .Ceiling == (up, .gt)
#guard tinyOk (pw 5000)
#guard tinyOk (Q "1/3" * pw 5000)
#guard tinyOk (pw 100)

-- a large rational: `cosh q` rounds like `exp |q| / 2`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (Q q) p m
  T q p m == (h r.1 (-1), r.2) && coshRatPrecRound (-(Q q)) p m == (h r.1 (-1), r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
