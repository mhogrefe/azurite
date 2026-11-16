/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot (x) / π`

`acotPi` and `acotPiRat`: the special values (`NaN`; `1/2` at `0`; `0` at `±∞`; `±1/4` at
`±1`; `p = 0`), the correctly rounded 53-bit values, the directed modes, a 20-bit result, a
200-bit string, tiny and huge arguments, exact rationals, agreement with the float function.
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acotPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotPiRatPrecRound (Q q) p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard P nan 53 == (nan, .eq)
#guard P zero 53 == (F "1/2" 53, .eq)
#guard P (infinity true) 53 == (zero, .eq)
#guard P (infinity false) 53 == (zero, .eq)
#guard P (F "1" 53) 53 == (F "1/4" 53, .eq)
#guard P (F "-1" 53) 53 == (F "-1/4" 53, .eq)
#guard P (F "3" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard P (F "3" 53) 53 == (F "7379878102178287/72057594037927936" 53, .lt)
#guard P (F "-3" 53) 53 == (F "-7379878102178287/72057594037927936" 53, .gt)
#guard P (F "3/2" 53) 53 == (F "6743403358048419/36028797018963968" 53, .gt)
#guard P (F "-7/5" 53) 53 == (F "-889152624786381/4503599627370496" 53, .gt)
#guard P (F "100" 53) 53 == (F "7339481615341467/2305843009213693952" 53, .gt)
#guard P (F "1/4" 53) 53 == (F "7602452124700209/18014398509481984" 53, .gt)
#guard P (F "2" 53) 53 == (F "664657525456481/4503599627370496" 53, .lt)
#guard P (F "3/2" 53) 53 .Floor == (F "3371701679024209/18014398509481984" 53, .lt)
#guard P (F "3/2" 53) 53 .Ceiling == (F "6743403358048419/36028797018963968" 53, .gt)
#guard P (F "3/2" 53) 20 == (F "785035/4194304" 20, .lt)
#guard acotPi (F "3/2" 53) == (P (F "3/2" 53) 53).1
#guard (toString (acotPiPrecRound (F "3/2" 200) 200 .Nearest).1).startsWith
  "0.18716704181099881618625274756477855233475757508836636030"
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard P huge 53 == (h (F "5734161139222659/18014398509481984" 53) (-1073741824), .gt)
#guard P huge 53 .Floor == (h (F "2867080569611329/9007199254740992" 53) (-1073741824), .lt)
#guard P (-huge) 53 == (-(h (F "5734161139222659/18014398509481984" 53) (-1073741824)), .lt)
#guard P tiny 53 == (F "1/2" 53, .gt)
#guard P tiny 53 .Floor == (F "9007199254740991/18014398509481984" 53, .lt)
#guard P (-tiny) 53 == (F "-1/2" 53, .lt)
#guard P (-tiny) 53 .Ceiling == (F "-9007199254740991/18014398509481984" 53, .gt)

-- rationals
#guard PR "0" 53 == (F "1/2" 53, .eq)
#guard PR "1" 53 == (F "1/4" 53, .eq)
#guard PR "-1" 53 == (F "-1/4" 53, .eq)
#guard PR "3" 0 == (nan, .eq)
#guard PR "3" 53 == (F "7379878102178287/72057594037927936" 53, .lt)
#guard PR "-7/5" 53 == (F "-889152624786381/4503599627370496" 53, .gt)
#guard PR "22/7" 53 == (F "883212142888003/9007199254740992" 53, .gt)
#guard PR "1/3" 53 == (F "1790557432299105/4503599627370496" 53, .lt)
#guard PR "3" 53 .Floor == (F "7379878102178287/72057594037927936" 53, .lt)
#guard PR "3" 53 .Ceiling == (F "461242381386143/4503599627370496" 53, .gt)
#guard PR "3/2" 53 == P (F "3/2" 53) 53
#guard acotPiRat (Q "3") 53 == (PR "3" 53).1
