/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinPi
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asinPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinPiRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P nan 53) == ("NaN", .eq)
#guard D (P (infinity true) 53) == ("NaN", .eq)
#guard D (P (X "2" 53) 53) == ("NaN", .eq)
#guard D (P zero 53) == ("0.0", .eq)
#guard D (P zero 0) == ("0.0", .eq)
#guard D (P (X "0.75" 53) 0) == ("NaN", .eq)
#guard D (P (X "1" 53) 53) == ("0.5", .eq)
#guard D (P (X "-1" 53) 1) == ("-0.5", .eq)
#guard D (P (X "0.5" 53) 53) == ("0.16666666666666666", .lt)
#guard D (P (X "0.5" 53) 53 .Ceiling) == ("0.16666666666666669", .gt)
#guard D (P (X "-0.5" 53) 53) == ("-0.16666666666666666", .gt)
#guard D (P (X "-0.5" 53) 53 .Floor) == ("-0.16666666666666669", .lt)

-- correctly rounded values
#guard D (P (X "0.3333333333333333" 53) 53) == ("0.10817344796939272", .gt)
#guard D (P (X "-0.7" 53) 53) == ("-0.246816688893365", .gt)
#guard D (P (X "0.75" 53) 53) == ("0.2699465438373841", .lt)
#guard D (P (X "0.9" 53) 53) == ("0.3564337068712937", .lt)
#guard D (P (X "0.0009765625" 53) 53) == ("0.0003108495476345764", .lt)
#guard D (P (X "0.75" 53) 53 .Floor) == ("0.2699465438373841", .lt)
#guard D (P (X "0.75" 53) 53 .Ceiling) == ("0.26994654383738415", .gt)
#guard D (P (X "0.75" 53) 20) == ("0.2699466", .gt)
#guard asinPi (X "0.75" 53) == (P (X "0.75" 53) 53).1
#guard toString (asinPiPrecRound (X "0.75" 200) 200 .Nearest).1 == "0.26994654383738411478621943229\
  4857106990088604729285897944125"
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard (P tiny 53).2 == .gt
#guard (P (-tiny) 53).2 == .lt

-- rationals
#guard D (PR "0" 53) == ("0.0", .eq)
#guard D (PR "1" 53) == ("0.5", .eq)
#guard D (PR "-1" 53) == ("-0.5", .eq)
#guard D (PR "3/2" 53) == ("NaN", .eq)
#guard D (PR "1/3" 0) == ("NaN", .eq)
#guard D (PR "1/2" 53) == ("0.16666666666666666", .lt)
#guard D (PR "-2/4" 53 .Floor) == ("-0.16666666666666669", .lt)
#guard D (PR "1/3" 53) == ("0.10817344796939272", .lt)
#guard D (PR "-22/23" 53) == ("-0.4057920761434871", .gt)
#guard D (PR "355/452" 53) == ("0.2875418038286629", .lt)
#guard D (PR "1/3" 53 .Floor) == ("0.10817344796939272", .lt)
#guard D (PR "1/3" 53 .Ceiling) == ("0.10817344796939274", .gt)
#guard PR "3/4" 53 == P (X "0.75" 53) 53
#guard asinPiRat (Q "1/3") 53 == (PR "1/3" 53).1
