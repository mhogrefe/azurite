/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccsc (x) / π`

`acscPi`: the special values (`NaN`, `|x| < 1`, `0` at `±∞`, `±1/2` at `±1`, the correctly
rounded `±1/6` at `±2`, `p = 0`), the correctly rounded 53-bit values, the directed modes, a
20-bit result, a 200-bit string, huge arguments (`1/(πx)`).  `acscPiRat`: the special values,
exact rationals, the directed modes, agreement with the float function.  References: an
independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acscPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscPiRatPrecRound (Q q) p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard P nan 53 == (nan, .eq)
#guard P zero 53 == (nan, .eq)
#guard P (F "1/2" 53) 53 == (nan, .eq)
#guard P (infinity true) 53 == (zero, .eq)
#guard P (infinity false) 53 == (zero, .eq)
#guard P (F "1" 53) 53 == (F "1/2" 53, .eq)
#guard P (F "-1" 53) 53 == (F "-1/2" 53, .eq)
#guard P (F "3" 53) 0 == (nan, .eq)
#guard P (F "2" 53) 53 == (F "6004799503160661/36028797018963968" 53, .lt)
#guard P (F "2" 53) 53 .Ceiling == (F "3002399751580331/18014398509481984" 53, .gt)
#guard P (F "-2" 53) 53 == (F "-6004799503160661/36028797018963968" 53, .gt)
#guard P (F "-2" 53) 53 .Floor == (F "-3002399751580331/18014398509481984" 53, .lt)

-- correctly rounded values
#guard P (F "3" 53) 53 == (F "7794718399461421/72057594037927936" 53, .lt)
#guard P (F "-3" 53) 53 == (F "-7794718399461421/72057594037927936" 53, .gt)
#guard P (F "3/2" 53) 53 == (F "2092187984276351/9007199254740992" 53, .lt)
#guard P (F "-7/5" 53) 53 == (F "-4562115538121795/18014398509481984" 53, .gt)
#guard P (F "100" 53) 53 == (F "917481074060137/288230376151711744" 53, .gt)
#guard P (F "3/2" 53) 53 .Floor == (F "2092187984276351/9007199254740992" 53, .lt)
#guard P (F "3/2" 53) 53 .Ceiling == (F "8368751937105405/36028797018963968" 53, .gt)
#guard P (F "3/2" 53) 20 == (F "974251/4194304" 20, .gt)
#guard acscPi (F "3/2" 53) == (P (F "3/2" 53) 53).1
#guard (toString (acscPiPrecRound (F "3/2" 200) 200 .Nearest).1).startsWith
  "0.2322795271987699892547662040587681085056339974216741541"
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard P huge 53 == (h (F "5734161139222659/18014398509481984" 53) (-1073741824), .gt)
#guard P huge 53 .Floor == (h (F "2867080569611329/9007199254740992" 53) (-1073741824), .lt)
#guard P (-huge) 53 == (-(h (F "5734161139222659/18014398509481984" 53) (-1073741824)), .lt)

-- rationals
#guard PR "1" 53 == (F "1/2" 53, .eq)
#guard PR "-1" 53 == (F "-1/2" 53, .eq)
#guard PR "1/2" 53 == (nan, .eq)
#guard PR "0" 53 == (nan, .eq)
#guard PR "3" 0 == (nan, .eq)
#guard PR "2" 53 == (F "6004799503160661/36028797018963968" 53, .lt)
#guard PR "-4/2" 53 .Floor == (F "-3002399751580331/18014398509481984" 53, .lt)
#guard PR "3" 53 == (F "7794718399461421/72057594037927936" 53, .lt)
#guard PR "-7/5" 53 == (F "-4562115538121795/18014398509481984" 53, .lt)
#guard PR "22/7" 53 == (F "7427138160935303/72057594037927936" 53, .gt)
#guard PR "3" 53 .Floor == (F "7794718399461421/72057594037927936" 53, .lt)
#guard PR "3" 53 .Ceiling == (F "3897359199730711/36028797018963968" 53, .gt)
#guard PR "3/2" 53 == P (F "3/2" 53) 53
#guard acscPiRat (Q "3") 53 == (PR "3" 53).1
