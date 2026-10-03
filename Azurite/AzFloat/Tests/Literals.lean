/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzFloat.Literals
import Azurite.AzFloat.Sci
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for literals, `Repr`, and `toSci` with options
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def D (s : String) : AzFloat := ofAzRat ((AzRat.fromSci s).get!) 53

/-! ## Literals -/

#guard (5 : AzFloat) == F "5" 3
#guard (1000000 : AzFloat) == F "1000000" 20
#guard (0 : AzFloat) == zero
#guard (1 : AzFloat) == one
#guard (2.5 : AzFloat) == F "5/2" 53
#guard (1e-3 : AzFloat) == F "1/1000" 53
#guard (0.1 : AzFloat) == F "1/10" 53
#guard (123.456e2 : AzFloat) == D "12345.6"
#guard toString (0.1 : AzFloat) == "0.1"
#guard toString ((2.5 : AzFloat) + 1) == "3.5"
#guard ((0.1 : AzFloat) + 0.2 : AzFloat) == D "0.30000000000000004"

/-! ## `Repr` is the hexadecimal debug format -/

#guard (repr (1.5 : AzFloat)).pretty == toHexString (F "3/2" 53)
#guard (repr (F "1/2" 5)).pretty == "0x0.80#5"
#guard (repr nan).pretty == "NaN"

/-! ## `toSci` with options -/

#guard toSci (F "1/3" 53) == some "0.3333333333333333"
#guard toSci (F "1/3" 53) { size := .precision 5 } == some "0.33333"
#guard toSci (F "1/3" 53) { size := .precision 5, mode := .Ceiling } == some "0.33334"
#guard toSci one { size := .precision 3, format := { includeTrailingZeros := true } } == some "1.00"
#guard toSci (F "1/8" 3) { base := 2 } == some "0.001"
#guard toSci (F "255" 8) { base := 16 } == some "ff"
#guard toSci (F "1000000" 20) { size := .precision 2 } == some "1e6"
#guard toSci nan == some "NaN"
#guard toSci (infinity false) == some "-Infinity"
#guard toSci zero == some "0"
#guard toSci one { base := 1 } == none
