/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin (x) / π`

`asinPi`: the special values (`NaN`, `|x| > 1`, `0`, `±1/2` at `±1`, the correctly rounded
`±1/6` at `±1/2` in all modes, `p = 0`), the correctly rounded 53-bit values, the directed
modes, a 20-bit result, a 200-bit string, tiny arguments.  `asinPiRat`: the special values,
exact rationals, the directed modes, agreement with the float function.  References: an
independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asinPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinPiRatPrecRound (Q q) p m

-- special values
#guard P nan 53 == (nan, .eq)
#guard P (infinity true) 53 == (nan, .eq)
#guard P (F "2" 53) 53 == (nan, .eq)
#guard P zero 53 == (zero, .eq)
#guard P zero 0 == (zero, .eq)
#guard P (F "3/4" 53) 0 == (nan, .eq)
#guard P (F "1" 53) 53 == (F "1/2" 53, .eq)
#guard P (F "-1" 53) 1 == (F "-1/2" 1, .eq)
#guard P (F "1/2" 53) 53 == (F "6004799503160661/36028797018963968" 53, .lt)
#guard P (F "1/2" 53) 53 .Ceiling == (F "3002399751580331/18014398509481984" 53, .gt)
#guard P (F "-1/2" 53) 53 == (F "-6004799503160661/36028797018963968" 53, .gt)
#guard P (F "-1/2" 53) 53 .Floor == (F "-3002399751580331/18014398509481984" 53, .lt)

-- correctly rounded values
#guard P (F "1/3" 53) 53 == (F "7794718399461421/72057594037927936" 53, .gt)
#guard P (F "-7/10" 53) 53 == (F "-4446254192515913/18014398509481984" 53, .gt)
#guard P (F "3/4" 53) 53 == (F "4862924616943985/18014398509481984" 53, .lt)
#guard P (F "9/10" 53) 53 == (F "1605234709447843/4503599627370496" 53, .lt)
#guard P (F "1/1024" 53) 53 == (F "5734162050643417/18446744073709551616" 53, .lt)
#guard P (F "3/4" 53) 53 .Floor == (F "4862924616943985/18014398509481984" 53, .lt)
#guard P (F "3/4" 53) 53 .Ceiling == (F "2431462308471993/9007199254740992" 53, .gt)
#guard P (F "3/4" 53) 20 == (F "566119/2097152" 20, .gt)
#guard asinPi (F "3/4" 53) == (P (F "3/4" 53) 53).1
#guard (toString (asinPiPrecRound (F "3/4" 200) 200 .Nearest).1).startsWith
  "0.2699465438373841147862194322948571069900886047292858979"
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard (P tiny 53).2 == .gt
#guard (P (-tiny) 53).2 == .lt

-- rationals
#guard PR "0" 53 == (zero, .eq)
#guard PR "1" 53 == (F "1/2" 53, .eq)
#guard PR "-1" 53 == (F "-1/2" 53, .eq)
#guard PR "3/2" 53 == (nan, .eq)
#guard PR "1/3" 0 == (nan, .eq)
#guard PR "1/2" 53 == (F "6004799503160661/36028797018963968" 53, .lt)
#guard PR "-2/4" 53 .Floor == (F "-3002399751580331/18014398509481984" 53, .lt)
#guard PR "1/3" 53 == (F "7794718399461421/72057594037927936" 53, .lt)
#guard PR "-22/23" 53 == (F "-3655050085819417/9007199254740992" 53, .gt)
#guard PR "355/452" 53 == (F "2589946321152413/9007199254740992" 53, .lt)
#guard PR "1/3" 53 .Floor == (F "7794718399461421/72057594037927936" 53, .lt)
#guard PR "1/3" 53 .Ceiling == (F "3897359199730711/36028797018963968" 53, .gt)
#guard PR "3/4" 53 == P (F "3/4" 53) 53
#guard asinPiRat (Q "1/3") 53 == (PR "1/3" 53).1
