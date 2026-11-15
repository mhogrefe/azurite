/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Rat
import Azurite.AzFloat.AtanRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x)` of rationals

The special values (`y = 0` against the sign of `x`; `x = 0`; `p = 0`), the correctly rounded
53-bit values in all eight octants and on the diagonals, at rationals that are not floats
(`(1/3, 7/5)`, `(22/7, −1/1000)`, …), agreement with the float `atan2` at representable
arguments and with `atanRat` for `x = 1`, invariance under a common positive factor, the
directed modes, 1-, 20- and 113-bit results, a 200-bit string, and tiny and huge ratios
(`1/(3·2^1000)`, the exactly representable `2^(−200)` and `2^(−5000)` with both signs, in every
octant).  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def B (y x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2RatPrecRound (Q y) (Q x) p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard B "0" "0" 53 == (zero, .eq)
#guard B "0" "3/7" 53 == (zero, .eq)
#guard B "0" "3/7" 0 == (zero, .eq)
#guard B "0" "-3/7" 53 == (piN, .lt)
#guard B "0" "-3/7" 53 .Ceiling == (piC, .gt)
#guard B "2/3" "0" 53 == (h piN (-1), .lt)
#guard B "-2/3" "0" 53 == (-(h piN (-1)), .gt)
#guard B "-2/3" "0" 53 .Floor == (-(h piC (-1)), .lt)
#guard B "1/3" "7/5" 0 == (nan, .eq)

-- correctly rounded values
#guard B "1" "1" 53 == (F "884279719003555/1125899906842624" 53, .lt)
#guard B "1" "-1" 53 == (F "2652839157010665/1125899906842624" 53, .lt)
#guard B "-1" "-1" 53 == (F "-2652839157010665/1125899906842624" 53, .gt)
#guard B "-1" "1" 53 == (F "-884279719003555/1125899906842624" 53, .gt)
#guard B "1" "3" 53 == (F "5796142707547873/18014398509481984" 53, .lt)
#guard B "3" "1" 53 == (F "175787564848171/140737488355328" 53, .gt)
#guard B "1" "-3" 53 == (F "1587429978396239/562949953421312" 53, .lt)
#guard B "3" "-1" 53 == (F "8523273428915409/4503599627370496" 53, .gt)
#guard B "-1" "3" 53 == (F "-5796142707547873/18014398509481984" 53, .gt)
#guard B "-3" "1" 53 == (F "-175787564848171/140737488355328" 53, .lt)
#guard B "-1" "-3" 53 == (F "-1587429978396239/562949953421312" 53, .gt)
#guard B "-3" "-1" 53 == (F "-8523273428915409/4503599627370496" 53, .lt)
#guard B "1/3" "7/5" 53 == (F "8421485618092631/36028797018963968" 53, .lt)
#guard B "-7/5" "1/3" 53 == (F "-6021552049766861/4503599627370496" 53, .gt)
#guard B "22/7" "-1/1000" 53 == (F "3537835357748941/2251799813685248" 53, .lt)
#guard B "1/1000" "-22/7" 53 == (F "7073521270293719/2251799813685248" 53, .lt)
#guard B "355/113" "1000000007/3" 53 == (F "5696929154323177/604462909807314587353088" 53, .lt)
#guard B "1000000007/3" "355/113" 53 == (F "3537118854791505/2251799813685248" 53, .lt)
#guard B "-1/1000000000000000000000000000000" "-1" 53
  == (F "-884279719003555/281474976710656" 53, .gt)
#guard B "1" "3" 53 .Floor == (F "5796142707547873/18014398509481984" 53, .lt)
#guard B "-3" "-1" 53 .Floor == (F "-8523273428915409/4503599627370496" 53, .lt)
#guard B "3" "-1" 53 .Floor == (F "532704589307213/281474976710656" 53, .lt)
#guard B "1" "3" 53 .Ceiling == (F "2898071353773937/9007199254740992" 53, .gt)
#guard B "-3" "-1" 53 .Ceiling == (F "-532704589307213/281474976710656" 53, .gt)
#guard B "3" "-1" 53 .Ceiling == (F "8523273428915409/4503599627370496" 53, .gt)
#guard B "1" "3" 20 == (F "84345/262144" 20, .gt)
#guard B "1" "-3" 1 == (F "2" 1, .lt)
#guard B "-3" "1" 113
  == (F "-6485416440189663768299072965959417/5192296858534827628530496329220096" 113, .gt)

-- agreement with the float `atan2`, with `atanRat`, and homogeneity
#guard B "1/2" "-3" 53 == atan2PrecRound (F "1/2" 53) (F "-3" 53) 53 .Nearest
#guard B "-5" "1/1024" 53 .Floor == atan2PrecRound (F "-5" 53) (F "1/1024" 53) 53 .Floor
#guard B "1/3" "1" 53 == atanRatPrecRound (Q "1/3") 53 .Nearest
#guard B "-22/7" "1" 53 .Ceiling == atanRatPrecRound (Q "-22/7") 53 .Ceiling
#guard B "2/21" "-2/5" 53 == B "5" "-21" 53
#guard atan2Rat (Q "1") (Q "3") 53 == (B "1" "3" 53).1
#guard (toString (atan2Rat (Q "1") (Q "-2") 200)).startsWith
  "2.67794504458898712224838715181828848216863234508898555"

-- tiny and huge ratios
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some 53
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def one' : AzRat := Q "1"
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard atan2RatPrecRound tinyQ one' 53 .Nearest == atanRatPrecRound tinyQ 53 .Nearest
#guard atan2RatPrecRound (-tinyQ) one' 53 .Floor == atanRatPrecRound (-tinyQ) 53 .Floor
#guard same (atan2RatPrecRound (pw 200) one' 53 .Nearest) (powerOf2 (AzInt.ofInt (-200))) .gt
#guard (atan2RatPrecRound (pw 200) one' 53 .Floor).2 == .lt
#guard same (atan2RatPrecRound (-(pw 200)) one' 53 .Nearest)
  (-(powerOf2 (AzInt.ofInt (-200)))) .lt
#guard same (atan2RatPrecRound (pw 5000) one' 53 .Nearest) (powerOf2 (AzInt.ofInt (-5000))) .gt
#guard same (atan2RatPrecRound one' (pw 5000)⁻¹ 53 .Nearest) (powerOf2 (AzInt.ofInt (-5000)))
  .gt
#guard atan2RatPrecRound one' (pw 5000) 53 .Nearest == (h piN (-1), .lt)
#guard atan2RatPrecRound (pw 5000) (-one') 53 .Nearest == (piN, .lt)
#guard atan2RatPrecRound (-(pw 5000)) (-one') 53 .Floor == (-piC, .lt)
#guard atan2RatPrecRound (-one') (-(pw 5000)) 53 .Nearest == (-(h piN (-1)), .gt)
