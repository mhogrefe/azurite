/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccos (x) / π`

`acosPi`: the special values (`NaN`, `|x| > 1`, `1/2` at `0`, `0` at `1`, `1` at `−1`, the
correctly rounded `1/3` at `1/2` and `2/3` at `−1/2`, `p = 0`), the correctly rounded 53-bit
values, the directed modes, a 20-bit result, a 200-bit string, tiny arguments (next to `1/2`).
`acosPiRat`: the special values, exact rationals, the directed modes, agreement with the float
function.  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acosPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosPiRatPrecRound (Q q) p m

-- special values
#guard P nan 53 == (nan, .eq)
#guard P (infinity true) 53 == (nan, .eq)
#guard P (F "2" 53) 53 == (nan, .eq)
#guard P zero 53 == (F "1/2" 53, .eq)
#guard P (F "1" 53) 53 == (zero, .eq)
#guard P (F "-1" 53) 53 == (F "1" 53, .eq)
#guard P (F "3/4" 53) 0 == (nan, .eq)
#guard P (F "1/2" 53) 53 == (F "6004799503160661/18014398509481984" 53, .lt)
#guard P (F "1/2" 53) 53 .Ceiling == (F "3002399751580331/9007199254740992" 53, .gt)
#guard P (F "-1/2" 53) 53 == (F "6004799503160661/9007199254740992" 53, .lt)
#guard P (F "-1/2" 53) 53 .Ceiling == (F "3002399751580331/4503599627370496" 53, .gt)
#guard P (F "1/2" 53) 1 == (F "1/4" 1, .lt)
#guard P (F "-1/2" 53) 3 == (F "5/8" 3, .lt)

-- correctly rounded values
#guard P (F "1/3" 53) 53 == (F "7058519654875637/18014398509481984" 53, .gt)
#guard P (F "-7/10" 53) 53 == (F "6726726723628453/9007199254740992" 53, .gt)
#guard P (F "3/4" 53) 53 == (F "8288549275594013/36028797018963968" 53, .lt)
#guard P (F "9/10" 53) 53 == (F "5172520833899239/36028797018963968" 53, .lt)
#guard P (F "-1/1024" 53) 53 == (F "4506399511184287/9007199254740992" 53, .gt)
#guard P (F "3/4" 53) 53 .Floor == (F "8288549275594013/36028797018963968" 53, .lt)
#guard P (F "3/4" 53) 53 .Ceiling == (F "4144274637797007/18014398509481984" 53, .gt)
#guard P (F "3/4" 53) 20 == (F "482457/2097152" 20, .lt)
#guard acosPi (F "3/4" 53) == (P (F "3/4" 53) 53).1
#guard (toString (acosPiPrecRound (F "3/4" 200) 200 .Nearest).1).startsWith
  "0.2300534561626158852137805677051428930099113952707141020"
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard P tiny 53 == (F "1/2" 53, .gt)
#guard P (-tiny) 53 == (F "1/2" 53, .lt)
#guard (P tiny 53 .Floor).2 == .lt

-- rationals
#guard PR "0" 53 == (F "1/2" 53, .eq)
#guard PR "1" 53 == (zero, .eq)
#guard PR "-1" 53 == (F "1" 53, .eq)
#guard PR "3/2" 53 == (nan, .eq)
#guard PR "1/3" 0 == (nan, .eq)
#guard PR "1/2" 53 == (F "6004799503160661/18014398509481984" 53, .lt)
#guard PR "-2/4" 53 .Ceiling == (F "3002399751580331/4503599627370496" 53, .gt)
#guard PR "1/3" 53 == (F "7058519654875637/18014398509481984" 53, .gt)
#guard PR "-22/23" 53 == (F "8158649713189913/9007199254740992" 53, .lt)
#guard PR "355/452" 53 == (F "1913653306218083/9007199254740992" 53, .gt)
#guard PR "1/3" 53 .Floor == (F "1764629913718909/4503599627370496" 53, .lt)
#guard PR "1/3" 53 .Ceiling == (F "7058519654875637/18014398509481984" 53, .gt)
#guard PR "3/4" 53 == P (F "3/4" 53) 53
#guard acosPiRat (Q "1/3") 53 == (PR "1/3" 53).1
