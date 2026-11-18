/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanPi
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atanPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanPiRatPrecRound (Q q) p m

-- special values
#guard D (P nan 53) == ("NaN", .eq)
#guard D (P (infinity true) 53) == ("0.5", .eq)
#guard D (P (infinity false) 53) == ("-0.5", .eq)
#guard D (P (infinity false) 1 .Floor) == ("-0.5", .eq)
#guard D (P zero 53) == ("0.0", .eq)
#guard D (P zero 0) == ("0.0", .eq)
#guard D (P (X "1" 53) 53) == ("0.25", .eq)
#guard D (P (X "-1" 53) 1) == ("-0.2", .eq)
#guard D (P (X "3" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (P (X "0.5" 53) 53) == ("0.14758361765043326", .lt)
#guard D (P (X "3" 53) 53) == ("0.39758361765043326", .lt)
#guard D (P (X "-1000" 53) 53) == ("-0.4996816902199194", .gt)
#guard D (P (X "0.0009765625" 53) 53) == ("0.0003108493994100204", .gt)
#guard D (P (X "1000000000000" 53) 53) == ("0.4999999999996817", .gt)
#guard D (P (X "0.5" 53) 53 .Floor) == ("0.14758361765043326", .lt)
#guard D (P (X "-3" 53) 53 .Floor) == ("-0.3975836176504333", .lt)
#guard D (P (X "0.5" 53) 53 .Ceiling) == ("0.1475836176504333", .gt)
#guard D (P (X "-3" 53) 53 .Ceiling) == ("-0.39758361765043326", .gt)
#guard D (P (X "3" 53) 20) == ("0.3975835", .lt)
#guard D (P (X "3" 53) 1) == ("0.5", .gt)
#guard D (P (X "0.5" 53) 113) == ("0.14758361765043327417540107622474052", .lt)
#guard atanPi (X "0.5" 53) == (P (X "0.5" 53) 53).1
#guard toString ((atanPiPrecRound (X "0.5" 200) 200 .Nearest).1)
  == "0.1475836176504332741754010762247405259511345238869178945999224"
#guard D (P (powerOf2 (AzInt.ofInt (-200))) 53) == ("1.9808472848159706e-61", .gt)
#guard D (P (powerOf2 (AzInt.ofInt 1000)) 53) == ("0.5", .gt)
#guard D (P (powerOf2 (AzInt.ofInt 1000)) 53 .Floor) == ("0.49999999999999994", .lt)

-- rationals
#guard D (PR "0" 53) == ("0.0", .eq)
#guard D (PR "1" 53) == ("0.25", .eq)
#guard D (PR "-1" 53) == ("-0.25", .eq)
#guard D (PR "1/3" 0) == ("NaN", .eq)
#guard D (PR "1/3" 53) == ("0.10241638234956672", .lt)
#guard D (PR "-22/7" 53) == ("-0.40194375433372154", .gt)
#guard D (PR "1/10" 53) == ("0.03172551743055357", .lt)
#guard D (PR "355/113" 53) == ("0.401906745859736", .lt)
#guard D (PR "1000000000000000000000000000000" 53) == ("0.5", .gt)
#guard D (PR "1/3" 53 .Floor) == ("0.10241638234956672", .lt)
#guard D (PR "1/3" 53 .Ceiling) == ("0.10241638234956674", .gt)
#guard D (PR "1/3" 20) == ("0.1024164", .gt)
#guard D (PR "-1/3" 113) == ("-0.10241638234956672582459892377525947", .gt)
#guard PR "1/2" 53 == P (X "0.5" 53) 53
#guard PR "-3" 53 .Ceiling == P (X "-3" 53) 53 .Ceiling
#guard atanPiRat (Q "1/3") 53 == (PR "1/3" 53).1
#guard toString (atanPiRat (Q "1/3") 200)
  == "0.1024163823495667258245989237752594740488654761130821054000777"

-- a huge argument: within `2^(−2^30)` of `1/2`, at no extra cost
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard D (P huge 53) == ("0.5", .gt)
#guard D (P huge 53 .Floor) == ("0.49999999999999994", .lt)
#guard D (P (-huge) 53 .Ceiling) == ("-0.49999999999999994", .gt)
