/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acos
import Azurite.AzFloat.AcosRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccos q` of a rational

The special values (`arccos 1 = 0`; `arccos 0 = π/2` and `arccos (−1) = π` in several modes;
`|q| > 1` gives `NaN`; `p = 0`), the correctly rounded 53-bit values at exact rationals,
agreement with the float `acos` at representable arguments, the directed modes, 20- and 113-bit
results, a 200-bit string, and the rationals `±(1 − 2^(−200))` next to `±1` (the first gives a
result of size `2^(−99.5)` with full relative accuracy).  References: an independent 1400-bit
fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosRatPrecRound (Q q) p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard T "1" 53 == (zero, .eq)
#guard T "1" 0 == (zero, .eq)
#guard T "0" 53 == (h piN (-1), .lt)
#guard T "0" 53 .Ceiling == (h piC (-1), .gt)
#guard T "-1" 53 == (piN, .lt)
#guard T "-1" 53 .Ceiling == (piC, .gt)
#guard T "3/2" 53 == (nan, .eq)
#guard T "-22/7" 53 == (nan, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1/3" 53 == (F "1385937093311029/1125899906842624" 53, .gt)
#guard T "-1/3" 53 == (F "8604727130812765/4503599627370496" 53, .gt)
#guard T "1/10" 53 == (F "413945236963161/281474976710656" 53, .lt)
#guard T "-7/10" 53 == (F "2641579407207161/1125899906842624" 53, .gt)
#guard T "3/4" 53 == (F "6509811378280789/9007199254740992" 53, .gt)
#guard T "-22/23" 53 == (F "1601947125135619/562949953421312" 53, .lt)
#guard T "999999/1000000" 53 == (F "6521909456158923/4611686018427387904" 53, .gt)
#guard T "1/1000000007" 53 == (F "7074237747524841/4503599627370496" 53, .gt)
#guard T "355/452" 53 == (F "1502979792083137/2251799813685248" 53, .lt)
#guard T "1/3" 53 .Floor == (F "5543748373244115/4503599627370496" 53, .lt)
#guard T "-3/4" 53 .Floor == (F "5446784907458243/2251799813685248" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "1385937093311029/1125899906842624" 53, .gt)
#guard T "-3/4" 53 .Ceiling == (F "1361696226864561/562949953421312" 53, .gt)
#guard T "1/3" 20 == (F "645377/524288" 20, .lt)
#guard T "3/4" 113
  == (F "3752650764477129491985459529029319/5192296858534827628530496329220096" 113, .lt)

-- agreement with the float `acos` at representable arguments
#guard T "1/2" 53 == acosPrecRound (F "1/2" 53) 53 .Nearest
#guard T "-3/4" 53 .Floor == acosPrecRound (F "-3/4" 53) 53 .Floor
#guard T "1/1024" 53 == acosPrecRound (F "1/1024" 53) 53 .Nearest
#guard acosRat (Q "1/3") 53 == (T "1/3" 53).1
#guard (toString (acosRat (Q "1/3") 200)).startsWith
  "1.23095941734077468213492917824798737571034000935509483"

-- rationals next to `±1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 - pw 200
#guard acosRatPrecRound near1 53 .Nearest
  == (F "6369051672525773/5708990770823839524233143877797980545530986496" 53, .gt)
#guard acosRatPrecRound (-near1) 53 .Nearest == (piN, .lt)
#guard acosRatPrecRound (-near1) 53 .Ceiling == (piC, .gt)
-- a tiny rational: next to `π/2`
#guard acosRatPrecRound (pw 5000) 53 .Nearest == (h piN (-1), .lt)
#guard acosRatPrecRound (-(pw 5000)) 53 .Ceiling == (h piC (-1), .gt)
