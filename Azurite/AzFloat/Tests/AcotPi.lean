/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `arccot (x) / π`

`acotPi` and `acotPiRat`: the special values (`NaN`; `1/2` at `0`; `0` at `±∞`; `±1/4` at
`±1`; `p = 0`), the correctly rounded 53-bit values, the directed modes, a 20-bit result, a
200-bit string, tiny and huge arguments, exact rationals, agreement with the float function.
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acotPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotPiRatPrecRound (Q q) p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P nan 53) == ("NaN", .eq)
#guard D (P zero 53) == ("0.5", .eq)
#guard D (P (infinity true) 53) == ("0.0", .eq)
#guard D (P (infinity false) 53) == ("0.0", .eq)
#guard D (P (X "1" 53) 53) == ("0.25", .eq)
#guard D (P (X "-1" 53) 53) == ("-0.25", .eq)
#guard D (P (X "3" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (P (X "3" 53) 53) == ("0.10241638234956672", .lt)
#guard D (P (X "-3" 53) 53) == ("-0.10241638234956672", .gt)
#guard D (P (X "1.5" 53) 53) == ("0.18716704181099883", .gt)
#guard D (P (X "-1.4" 53) 53) == ("-0.19743154328874657", .gt)
#guard D (P (X "100" 53) 53) == ("0.003182992764908255", .gt)
#guard D (P (X "0.25" 53) 53) == ("0.4220208696226307", .gt)
#guard D (P (X "2" 53) 53) == ("0.14758361765043326", .lt)
#guard D (P (X "1.5" 53) 53 .Floor) == ("0.1871670418109988", .lt)
#guard D (P (X "1.5" 53) 53 .Ceiling) == ("0.18716704181099883", .gt)
#guard D (P (X "1.5" 53) 20) == ("0.187167", .lt)
#guard acotPi (X "1.5" 53) == (P (X "1.5" 53) 53).1
#guard toString (acotPiPrecRound (X "1.5" 200) 200 .Nearest).1
  == "0.1871670418109988161862527475647785523347575750883663603090479"
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard P huge 53 == (h (X "0.3183098861837907" 53) (-1073741824), .gt)
#guard P huge 53 .Floor == (h (X "0.31830988618379064" 53) (-1073741824), .lt)
#guard P (-huge) 53 == (-(h (X "0.3183098861837907" 53) (-1073741824)), .lt)
#guard D (P tiny 53) == ("0.5", .gt)
#guard D (P tiny 53 .Floor) == ("0.49999999999999994", .lt)
#guard D (P (-tiny) 53) == ("-0.5", .lt)
#guard D (P (-tiny) 53 .Ceiling) == ("-0.49999999999999994", .gt)

-- rationals
#guard D (PR "0" 53) == ("0.5", .eq)
#guard D (PR "1" 53) == ("0.25", .eq)
#guard D (PR "-1" 53) == ("-0.25", .eq)
#guard D (PR "3" 0) == ("NaN", .eq)
#guard D (PR "3" 53) == ("0.10241638234956672", .lt)
#guard D (PR "-7/5" 53) == ("-0.19743154328874657", .gt)
#guard D (PR "22/7" 53) == ("0.09805624566627846", .gt)
#guard D (PR "1/3" 53) == ("0.39758361765043326", .lt)
#guard D (PR "3" 53 .Floor) == ("0.10241638234956672", .lt)
#guard D (PR "3" 53 .Ceiling) == ("0.10241638234956674", .gt)
#guard PR "3/2" 53 == P (X "1.5" 53) 53
#guard acotPiRat (Q "3") 53 == (PR "3" 53).1
