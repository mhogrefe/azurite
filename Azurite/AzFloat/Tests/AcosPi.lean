/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosPi
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acosPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosPiRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P nan 53) == ("NaN", .eq)
#guard D (P (infinity true) 53) == ("NaN", .eq)
#guard D (P (X "2" 53) 53) == ("NaN", .eq)
#guard D (P zero 53) == ("0.5", .eq)
#guard D (P (X "1" 53) 53) == ("0.0", .eq)
#guard D (P (X "-1" 53) 53) == ("1.0", .eq)
#guard D (P (X "0.75" 53) 0) == ("NaN", .eq)
#guard D (P (X "0.5" 53) 53) == ("0.3333333333333333", .lt)
#guard D (P (X "0.5" 53) 53 .Ceiling) == ("0.33333333333333337", .gt)
#guard D (P (X "-0.5" 53) 53) == ("0.6666666666666666", .lt)
#guard D (P (X "-0.5" 53) 53 .Ceiling) == ("0.6666666666666667", .gt)
#guard D (P (X "0.5" 53) 1) == ("0.2", .lt)
#guard D (P (X "-0.5" 53) 3) == ("0.6", .lt)

-- correctly rounded values
#guard D (P (X "0.3333333333333333" 53) 53) == ("0.3918265520306073", .gt)
#guard D (P (X "-0.7" 53) 53) == ("0.746816688893365", .gt)
#guard D (P (X "0.75" 53) 53) == ("0.23005345616261588", .lt)
#guard D (P (X "0.9" 53) 53) == ("0.14356629312870625", .lt)
#guard D (P (X "-0.0009765625" 53) 53) == ("0.5003108495476346", .gt)
#guard D (P (X "0.75" 53) 53 .Floor) == ("0.23005345616261588", .lt)
#guard D (P (X "0.75" 53) 53 .Ceiling) == ("0.2300534561626159", .gt)
#guard D (P (X "0.75" 53) 20) == ("0.2300534", .lt)
#guard acosPi (X "0.75" 53) == (P (X "0.75" 53) 53).1
#guard toString (acosPiPrecRound (X "0.75" 200) 200 .Nearest).1 == "0.23005345616261588521378056770\
  51428930099113952707141020558749"
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard D (P tiny 53) == ("0.5", .gt)
#guard D (P (-tiny) 53) == ("0.5", .lt)
#guard (P tiny 53 .Floor).2 == .lt

-- rationals
#guard D (PR "0" 53) == ("0.5", .eq)
#guard D (PR "1" 53) == ("0.0", .eq)
#guard D (PR "-1" 53) == ("1.0", .eq)
#guard D (PR "3/2" 53) == ("NaN", .eq)
#guard D (PR "1/3" 0) == ("NaN", .eq)
#guard D (PR "1/2" 53) == ("0.3333333333333333", .lt)
#guard D (PR "-2/4" 53 .Ceiling) == ("0.6666666666666667", .gt)
#guard D (PR "1/3" 53) == ("0.3918265520306073", .gt)
#guard D (PR "-22/23" 53) == ("0.9057920761434871", .lt)
#guard D (PR "355/452" 53) == ("0.2124581961713371", .gt)
#guard D (PR "1/3" 53 .Floor) == ("0.39182655203060723", .lt)
#guard D (PR "1/3" 53 .Ceiling) == ("0.3918265520306073", .gt)
#guard PR "3/4" 53 == P (X "0.75" 53) 53
#guard acosPiRat (Q "1/3") 53 == (PR "1/3" 53).1
