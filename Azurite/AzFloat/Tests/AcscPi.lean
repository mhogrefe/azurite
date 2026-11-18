/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscPi
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acscPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscPiRatPrecRound (Q q) p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard D (P nan 53) == ("NaN", .eq)
#guard D (P zero 53) == ("NaN", .eq)
#guard D (P (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (P (infinity true) 53) == ("0.0", .eq)
#guard D (P (infinity false) 53) == ("0.0", .eq)
#guard D (P (X "1" 53) 53) == ("0.5", .eq)
#guard D (P (X "-1" 53) 53) == ("-0.5", .eq)
#guard D (P (X "3" 53) 0) == ("NaN", .eq)
#guard D (P (X "2" 53) 53) == ("0.16666666666666666", .lt)
#guard D (P (X "2" 53) 53 .Ceiling) == ("0.16666666666666669", .gt)
#guard D (P (X "-2" 53) 53) == ("-0.16666666666666666", .gt)
#guard D (P (X "-2" 53) 53 .Floor) == ("-0.16666666666666669", .lt)

-- correctly rounded values
#guard D (P (X "3" 53) 53) == ("0.10817344796939272", .lt)
#guard D (P (X "-3" 53) 53) == ("-0.10817344796939272", .gt)
#guard D (P (X "1.5" 53) 53) == ("0.23227952719876999", .lt)
#guard D (P (X "-1.4" 53) 53) == ("-0.25324828557115014", .gt)
#guard D (P (X "100" 53) 53) == ("0.0031831519158730705", .gt)
#guard D (P (X "1.5" 53) 53 .Floor) == ("0.23227952719876999", .lt)
#guard D (P (X "1.5" 53) 53 .Ceiling) == ("0.23227952719877", .gt)
#guard D (P (X "1.5" 53) 20) == ("0.2322795", .gt)
#guard acscPi (X "1.5" 53) == (P (X "1.5" 53) 53).1
#guard toString ((acscPiPrecRound (X "1.5" 200) 200 .Nearest).1)
  == "0.2322795271987699892547662040587681085056339974216741541854044"
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard P huge 53 == (h (X "0.3183098861837907" 53) (-1073741824), .gt)
#guard P huge 53 .Floor == (h (X "0.31830988618379064" 53) (-1073741824), .lt)
#guard P (-huge) 53 == (-(h (X "0.3183098861837907" 53) (-1073741824)), .lt)

-- rationals
#guard D (PR "1" 53) == ("0.5", .eq)
#guard D (PR "-1" 53) == ("-0.5", .eq)
#guard D (PR "1/2" 53) == ("NaN", .eq)
#guard D (PR "0" 53) == ("NaN", .eq)
#guard D (PR "3" 0) == ("NaN", .eq)
#guard D (PR "2" 53) == ("0.16666666666666666", .lt)
#guard D (PR "-4/2" 53 .Floor) == ("-0.16666666666666669", .lt)
#guard D (PR "3" 53) == ("0.10817344796939272", .lt)
#guard D (PR "-7/5" 53) == ("-0.25324828557115014", .lt)
#guard D (PR "22/7" 53) == ("0.10307224741678143", .gt)
#guard D (PR "3" 53 .Floor) == ("0.10817344796939272", .lt)
#guard D (PR "3" 53 .Ceiling) == ("0.10817344796939274", .gt)
#guard PR "3/2" 53 == P (X "1.5" 53) 53
#guard acscPiRat (Q "3") 53 == (PR "3" 53).1
