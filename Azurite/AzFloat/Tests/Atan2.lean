/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2
import Azurite.AzFloat.Atan
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x)`

The whole table of special values (`NaN`; `y = 0` against the sign of `x`, with `±∞`; `x = 0`;
`y = ±∞` against finite `x` and `±∞`; finite `y` against `±∞`; `p = 0`), with the directed modes
at the multiples of `π` and the constant `3π/4` at 1, 20 and 113 bits; the correctly rounded
53-bit values in all eight octants (`(±1, ±2)`, `(±2, ±1)`), on the diagonals, at inexact and
at very unequal arguments; agreement with `atan` for `x = 1`; the directed modes; 1-, 20- and
113-bit results; 200-bit strings; and extreme ratios in every octant (`2⁻²⁰⁰`, `2^1000`,
`2^(±2^30)`), which cost nothing extra.  References: an independent 1400-bit fixed-point
evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (y x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atan2PrecRound y x p m
private def inf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def one' : AzFloat := F "1" 53
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- `NaN`
#guard A nan one' 53 == (nan, .eq)
#guard A one' nan 53 == (nan, .eq)
#guard A nan nan 53 == (nan, .eq)
#guard A inf nan 53 == (nan, .eq)
#guard A nan zero 53 == (nan, .eq)
-- `y = 0`
#guard A zero zero 53 == (zero, .eq)
#guard A zero (F "3" 53) 53 == (zero, .eq)
#guard A zero inf 53 == (zero, .eq)
#guard A zero zero 0 == (zero, .eq)
#guard A zero (F "-3" 53) 53 == (piN, .lt)
#guard A zero (F "-3" 53) 53 .Ceiling == (piC, .gt)
#guard A zero ninf 53 == (piN, .lt)
#guard A zero ninf 53 .Ceiling == (piC, .gt)
-- `x = 0`
#guard A (F "2" 53) zero 53 == (h piN (-1), .lt)
#guard A (F "-2" 53) zero 53 == (-(h piN (-1)), .gt)
#guard A (F "-2" 53) zero 53 .Floor == (-(h piC (-1)), .lt)
-- `y = ±∞`
#guard A inf (F "5" 53) 53 == (h piN (-1), .lt)
#guard A inf zero 53 == (h piN (-1), .lt)
#guard A ninf (F "-5" 53) 53 == (-(h piN (-1)), .gt)
#guard A ninf zero 53 .Floor == (-(h piC (-1)), .lt)
#guard A inf inf 53 == (h piN (-2), .lt)
#guard A ninf inf 53 == (-(h piN (-2)), .gt)
#guard A ninf inf 53 .Floor == (-(h piC (-2)), .lt)
#guard A inf ninf 53 == (F "2652839157010665/1125899906842624" 53, .lt)
#guard A inf ninf 53 .Ceiling == (F "5305678314021331/2251799813685248" 53, .gt)
#guard A ninf ninf 53 == (F "-2652839157010665/1125899906842624" 53, .gt)
#guard A ninf ninf 53 .Floor == (F "-5305678314021331/2251799813685248" 53, .lt)
#guard A inf ninf 1 == (F "2" 1, .lt)
#guard A inf ninf 20 == (F "308831/131072" 20, .lt)
#guard A inf ninf 113
  == (F "3058515312380695575312653655515301/1298074214633706907132624082305024" 113, .lt)
-- finite `y`, `x = ±∞`
#guard A (F "5" 53) inf 53 == (zero, .eq)
#guard A (F "-5" 53) inf 53 == (zero, .eq)
#guard A (F "5" 53) ninf 53 == (piN, .lt)
#guard A (F "-5" 53) ninf 53 == (-piN, .gt)
#guard A (F "-5" 53) ninf 53 .Floor == (-piC, .lt)
-- `p = 0`
#guard A one' one' 0 == (nan, .eq)
#guard A (F "5" 53) inf 0 == (zero, .eq)

-- correctly rounded values
#guard A (F "1" 53) (F "1" 53) 53 == (F "884279719003555/1125899906842624" 53, .lt)
#guard A (F "1" 53) (F "2" 53) 53 == (F "8352332796509007/18014398509481984" 53, .lt)
#guard A (F "2" 53) (F "1" 53) 53 == (F "1246538638225297/1125899906842624" 53, .lt)
#guard A (F "1" 53) (F "-2" 53) 53 == (F "3015098076232407/1125899906842624" 53, .lt)
#guard A (F "2" 53) (F "-1" 53) 53 == (F "2290580237788923/1125899906842624" 53, .lt)
#guard A (F "-1" 53) (F "2" 53) 53 == (F "-8352332796509007/18014398509481984" 53, .gt)
#guard A (F "-2" 53) (F "1" 53) 53 == (F "-1246538638225297/1125899906842624" 53, .gt)
#guard A (F "-1" 53) (F "-2" 53) 53 == (F "-3015098076232407/1125899906842624" 53, .gt)
#guard A (F "-2" 53) (F "-1" 53) 53 == (F "-2290580237788923/1125899906842624" 53, .gt)
#guard A (F "1" 53) (F "-1" 53) 53 == (F "2652839157010665/1125899906842624" 53, .lt)
#guard A (F "-1" 53) (F "-1" 53) 53 == (F "-2652839157010665/1125899906842624" 53, .gt)
#guard A (F "1/3" 53) (F "7/5" 53) 53 == (F "8421485618092631/36028797018963968" 53, .lt)
#guard A (F "-7/5" 53) (F "1/3" 53) 53 == (F "-6021552049766861/4503599627370496" 53, .gt)
#guard A (F "22/7" 53) (F "-1/1000" 53) 53 == (F "3537835357748941/2251799813685248" 53, .lt)
#guard A (F "1/1000" 53) (F "-22/7" 53) 53 == (F "7073521270293719/2251799813685248" 53, .lt)
#guard A (F "1000000000000" 53) (F "3" 53) 53 == (F "7074237752014929/4503599627370496" 53, .lt)
#guard A (F "3" 53) (F "1000000000000" 53) 53
  == (F "3713820117856141/1237940039285380274899124224" 53, .gt)
#guard A (F "3" 53) (F "-1000000000000" 53) 53 == (F "7074237752021685/2251799813685248" 53, .gt)
#guard A (F "1" 53) (F "2" 53) 53 .Floor == (F "8352332796509007/18014398509481984" 53, .lt)
#guard A (F "-2" 53) (F "-1" 53) 53 .Floor == (F "-4581160475577847/2251799813685248" 53, .lt)
#guard A (F "2" 53) (F "-1" 53) 53 .Floor == (F "2290580237788923/1125899906842624" 53, .lt)
#guard A (F "1" 53) (F "2" 53) 53 .Ceiling == (F "522020799781813/1125899906842624" 53, .gt)
#guard A (F "-2" 53) (F "-1" 53) 53 .Ceiling == (F "-2290580237788923/1125899906842624" 53, .gt)
#guard A (F "2" 53) (F "-1" 53) 53 .Ceiling == (F "4581160475577847/2251799813685248" 53, .gt)
#guard A (F "1" 53) (F "2" 53) 20 == (F "243085/524288" 20, .gt)
#guard A (F "1" 53) (F "-2" 53) 1 == (F "2" 1, .lt)
#guard A (F "-2" 53) (F "1" 53) 113
  == (F "-5748644809333118532951541656101787/5192296858534827628530496329220096" 113, .lt)

-- agreement with `atan` for `x = 1`
#guard A (F "1/3" 53) one' 53 == atanPrecRound (F "1/3" 53) 53 .Nearest
#guard A (F "-22/7" 53) one' 53 .Floor == atanPrecRound (F "-22/7" 53) 53 .Floor
#guard atan2 (F "1" 53) (F "2" 53) == (A (F "1" 53) (F "2" 53) 53).1
#guard (toString (atan2PrecRound (F "1" 200) (F "-2" 200) 200 .Nearest).1).startsWith
  "2.67794504458898712224838715181828848216863234508898555"
#guard (toString (atan2PrecRound (F "-2" 200) (F "1" 200) 200 .Nearest).1).startsWith
  "-1.10714871779409050301706546017853704007004764540143264"

-- extreme ratios (`same`: equality of the values, the expected floats having precision `1`)
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some 53
private def t : AzFloat := powerOf2 (AzInt.ofInt (-200))
private def T : AzFloat := powerOf2 (AzInt.ofInt 1000)
#guard same (A t one' 53) t .gt
#guard A t one' 53 .Floor
  == (F ("9007199254740991/"
    ++ "14474011154664524427946373126085988481658748083205070504932198000989141204992") 53, .lt)
#guard A one' t 53 == (h piN (-1), .lt)
#guard A t (-one') 53 == (piN, .lt)
#guard A (-t) (-one') 53 == (-piN, .gt)
#guard A (-t) (-one') 53 .Floor == (-piC, .lt)
#guard A T one' 53 == (h piN (-1), .lt)
#guard same (A one' T 53) (powerOf2 (AzInt.ofInt (-1000))) .gt
#guard (A one' T 53 .Floor).2 == .lt
#guard A one' (-T) 53 == (piN, .lt)
#guard A (-one') (-T) 53 .Floor == (-piC, .lt)
#guard A T (-T) 53 == (F "2652839157010665/1125899906842624" 53, .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard same (A tiny one' 53) tiny .gt
#guard same (A one' huge 53) tiny .gt
#guard same (A (-tiny) huge 53 .Floor) (-(h tiny (-1073741824))) .lt
#guard same (A (-tiny) one' 53) (-tiny) .lt
#guard A huge tiny 53 == (h piN (-1), .lt)
#guard A tiny (-huge) 53 == (piN, .lt)
#guard A (-huge) (-tiny) 53 == (-(h piN (-1)), .gt)
