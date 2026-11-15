/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Pi
import Azurite.AzFloat.AtanPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x) / π`

`atan2Pi`: the special values (`NaN`; `±1/4`, `±3/4`, `±1/2` for `y = ±∞`; `0`, `±1` for
`x = ±∞`; the axes; the diagonals; `p = 0`), the correctly rounded 53-bit values in all eight
octants, the directed modes, 20- and 113-bit results, agreement with `atanPi` for `x = 1`, and
extreme ratios `2^(±2^30)`.  `atan2PiRat`: the special values, exact rationals, the directed
modes, agreement with the float function, and extreme ratios.  References: an independent
1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (y x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2PiPrecRound y x p m
private def PR (y x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2PiRatPrecRound (Q y) (Q x) p m
private def inf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def one' : AzFloat := F "1" 53

-- special values
#guard P nan one' 53 == (nan, .eq)
#guard P one' nan 53 == (nan, .eq)
#guard P inf inf 53 == (F "1/4" 53, .eq)
#guard P ninf inf 53 == (F "-1/4" 53, .eq)
#guard P inf ninf 53 == (F "3/4" 53, .eq)
#guard P ninf ninf 53 == (F "-3/4" 53, .eq)
#guard P inf ninf 1 == (F "1" 1, .gt)
#guard P inf one' 53 == (F "1/2" 53, .eq)
#guard P ninf zero 53 == (F "-1/2" 53, .eq)
#guard P one' inf 53 == (zero, .eq)
#guard P one' ninf 53 == (F "1" 53, .eq)
#guard P (-one') ninf 53 == (F "-1" 53, .eq)
#guard P zero ninf 53 == (F "1" 53, .eq)
#guard P zero zero 53 == (zero, .eq)
#guard P zero (F "3" 53) 53 == (zero, .eq)
#guard P zero (F "-3" 53) 53 == (F "1" 53, .eq)
#guard P (F "2" 53) zero 53 == (F "1/2" 53, .eq)
#guard P (F "-2" 53) zero 53 == (F "-1/2" 53, .eq)
#guard P (F "3" 53) (F "3" 53) 53 == (F "1/4" 53, .eq)
#guard P (F "-3" 53) (F "-3" 53) 53 == (F "-3/4" 53, .eq)
#guard P (F "3" 53) (F "-3" 53) 1 .Floor == (F "1/2" 1, .lt)
#guard P one' (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard P (F "1" 53) (F "2" 53) 53 == (F "664657525456481/4503599627370496" 53, .lt)
#guard P (F "2" 53) (F "1" 53) 53 == (F "1587142288228767/4503599627370496" 53, .gt)
#guard P (F "1" 53) (F "-2" 53) 53 == (F "3838942101914015/4503599627370496" 53, .gt)
#guard P (F "2" 53) (F "-1" 53) 53 == (F "2916457339141729/4503599627370496" 53, .lt)
#guard P (F "-1" 53) (F "2" 53) 53 == (F "-664657525456481/4503599627370496" 53, .gt)
#guard P (F "-2" 53) (F "1" 53) 53 == (F "-1587142288228767/4503599627370496" 53, .lt)
#guard P (F "-1" 53) (F "-2" 53) 53 == (F "-3838942101914015/4503599627370496" 53, .lt)
#guard P (F "-2" 53) (F "-1" 53) 53 == (F "-2916457339141729/4503599627370496" 53, .gt)
#guard P (F "1/3" 53) (F "7/5" 53) 53 == (F "5361284257186991/72057594037927936" 53, .lt)
#guard P (F "1" 53) (F "-2" 53) 53 .Floor == (F "7677884203828029/9007199254740992" 53, .lt)
#guard P (F "1" 53) (F "-2" 53) 53 .Ceiling == (F "3838942101914015/4503599627370496" 53, .gt)
#guard P (F "1" 53) (F "2" 53) 20 == (F "619011/4194304" 20, .gt)
#guard P (F "-2" 53) (F "1" 53) 113
  == (F "-7319401899879455944750911548089715/20769187434139310514121985316880384" 113, .gt)
#guard P (F "1/3" 53) one' 53 == atanPiPrecRound (F "1/3" 53) 53 .Nearest
#guard atan2Pi (F "1" 53) (F "2" 53) == (P (F "1" 53) (F "2" 53) 53).1
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard P huge tiny 53 == (F "1/2" 53, .gt)
#guard P huge (-tiny) 53 == (F "1/2" 53, .lt)
#guard P tiny (-huge) 53 == (F "1" 53, .gt)
#guard P (-tiny) (-huge) 53 .Ceiling == (F "-9007199254740991/9007199254740992" 53, .gt)
#guard (P tiny huge 53).2 == .gt
#guard (P tiny huge 53 .Floor).2 == .lt

-- rationals
#guard PR "0" "0" 53 == (zero, .eq)
#guard PR "0" "-2/3" 53 == (F "1" 53, .eq)
#guard PR "2/3" "0" 53 == (F "1/2" 53, .eq)
#guard PR "-2/3" "2/3" 53 == (F "-1/4" 53, .eq)
#guard PR "2/3" "-2/3" 53 == (F "3/4" 53, .eq)
#guard PR "1/3" "7/5" 0 == (nan, .eq)
#guard PR "1" "3" 53 == (F "7379878102178287/72057594037927936" 53, .lt)
#guard PR "-3" "1" 53 == (F "-1790557432299105/4503599627370496" 53, .gt)
#guard PR "1/3" "7/5" 53 == (F "5361284257186991/72057594037927936" 53, .gt)
#guard PR "22/7" "-1/1000" 53 == (F "4504511880248223/9007199254740992" 53, .lt)
#guard PR "1" "-3" 53 .Floor == (F "4042357245984353/4503599627370496" 53, .lt)
#guard PR "1" "-3" 53 .Ceiling == (F "8084714491968707/9007199254740992" 53, .gt)
#guard PR "1" "3" 20 == (F "859131/8388608" 20, .gt)
#guard PR "1/2" "-3" 53 == P (F "1/2" 53) (F "-3" 53) 53
#guard atan2PiRat (Q "1") (Q "3") 53 == (PR "1" "3" 53).1
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard atan2PiRatPrecRound (Q "1") (pw 5000) 53 .Nearest == (F "1/2" 53, .gt)
#guard atan2PiRatPrecRound (pw 5000) (Q "-1") 53 .Nearest == (F "1" 53, .gt)
#guard atanPiRatPrecRound (pw 5000)⁻¹ 53 .Nearest == (F "1/2" 53, .gt)
