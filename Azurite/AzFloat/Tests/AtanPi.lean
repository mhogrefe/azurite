/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arctan (x) / π`

`atanPi`: the special values (`NaN`, `±1/2` at `±∞`, `0`, `±1/4` at `±1`, `p = 0`), the
correctly rounded 53-bit values at `1/2`, `3`, `−1000`, `1/1024`, `10¹²`, the directed modes,
1-, 20- and 113-bit results, a 200-bit string, the tiny `2⁻²⁰⁰` and the huge `2^1000`.
`atanPiRat`: the special values, the exact rationals `1/3`, `−22/7`, `1/10`, `355/113`, `10³⁰`,
the directed modes, 20- and 113-bit results, agreement with the float function.  References: an
independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atanPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanPiRatPrecRound (Q q) p m

-- special values
#guard P nan 53 == (nan, .eq)
#guard P (infinity true) 53 == (F "1/2" 53, .eq)
#guard P (infinity false) 53 == (F "-1/2" 53, .eq)
#guard P (infinity false) 1 .Floor == (F "-1/2" 1, .eq)
#guard P zero 53 == (zero, .eq)
#guard P zero 0 == (zero, .eq)
#guard P (F "1" 53) 53 == (F "1/4" 53, .eq)
#guard P (F "-1" 53) 1 == (F "-1/4" 1, .eq)
#guard P (F "3" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard P (F "1/2" 53) 53 == (F "664657525456481/4503599627370496" 53, .lt)
#guard P (F "3" 53) 53 == (F "1790557432299105/4503599627370496" 53, .lt)
#guard P (F "-1000" 53) 53 == (F "-9001465095513155/18014398509481984" 53, .gt)
#guard P (F "1/1024" 53) 53 == (F "5734159316382967/18446744073709551616" 53, .gt)
#guard P (F "1000000000000" 53) 53 == (F "4503599627367629/9007199254740992" 53, .gt)
#guard P (F "1/2" 53) 53 .Floor == (F "664657525456481/4503599627370496" 53, .lt)
#guard P (F "-3" 53) 53 .Floor == (F "-7162229729196421/18014398509481984" 53, .lt)
#guard P (F "1/2" 53) 53 .Ceiling == (F "5317260203651849/36028797018963968" 53, .gt)
#guard P (F "-3" 53) 53 .Ceiling == (F "-1790557432299105/4503599627370496" 53, .gt)
#guard P (F "3" 53) 20 == (F "833793/2097152" 20, .lt)
#guard P (F "3" 53) 1 == (F "1/2" 1, .gt)
#guard P (F "1/2" 53) 113
  == (F "6130383634380398624620162220700953/41538374868278621028243970633760768" 113, .lt)
#guard atanPi (F "1/2" 53) == (P (F "1/2" 53) 53).1
#guard (toString (atanPiPrecRound (F "1/2" 200) 200 .Nearest).1).startsWith
  "0.14758361765043327417540107622474052595113452388691789"
#guard P (powerOf2 (AzInt.ofInt (-200))) 53 == (F ("5734161139222659/"
  ++ "28948022309329048855892746252171976963317496166410141009864396001978282409984") 53, .gt)
#guard P (powerOf2 (AzInt.ofInt 1000)) 53 == (F "1/2" 53, .gt)
#guard P (powerOf2 (AzInt.ofInt 1000)) 53 .Floor
  == (F "9007199254740991/18014398509481984" 53, .lt)

-- rationals
#guard PR "0" 53 == (zero, .eq)
#guard PR "1" 53 == (F "1/4" 53, .eq)
#guard PR "-1" 53 == (F "-1/4" 53, .eq)
#guard PR "1/3" 0 == (nan, .eq)
#guard PR "1/3" 53 == (F "7379878102178287/72057594037927936" 53, .lt)
#guard PR "-22/7" 53 == (F "-3620387484482493/9007199254740992" 53, .gt)
#guard PR "1/10" 53 == (F "4572128911308071/144115188075855872" 53, .lt)
#guard PR "355/113" 53 == (F "7240108283566383/18014398509481984" 53, .lt)
#guard PR "1000000000000000000000000000000" 53 == (F "1/2" 53, .gt)
#guard PR "1/3" 53 .Floor == (F "7379878102178287/72057594037927936" 53, .lt)
#guard PR "1/3" 53 .Ceiling == (F "461242381386143/4503599627370496" 53, .gt)
#guard PR "1/3" 20 == (F "859131/8388608" 20, .gt)
#guard PR "-1/3" 113
  == (F "-8508420165378513264881660875478477/83076749736557242056487941267521536" 113, .gt)
#guard PR "1/2" 53 == P (F "1/2" 53) 53
#guard PR "-3" 53 .Ceiling == P (F "-3" 53) 53 .Ceiling
#guard atanPiRat (Q "1/3") 53 == (PR "1/3" 53).1
#guard (toString (atanPiRat (Q "1/3") 200)).startsWith
  "0.10241638234956672582459892377525947404886547611308210"
