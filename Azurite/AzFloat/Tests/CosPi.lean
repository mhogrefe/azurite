/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.CosPi
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `cos (π x)`

Floats: the special values, the exact values at integers and half-integers (including `10²⁰`
and `10²⁰ + 1` at 80 bits), the correctly rounded `cos (π/4)`, `cos (π/1024)`,
`cos (π (10²⁰ + 1/8))` (80-bit argument: exact reduction, no loss from the size),
`cos (π ⌊1/10⌋₅₃)`, `cos (π ⌊1/3⌋₅₃)` (just above `1/2`: rounds to `1/2` with `.lt`), the directed
modes, a tiny argument.  Rationals: the special values, the exact values (`1/3 ↦ 1/2`,
`2/3 ↦ −1/2`, `−4/3 ↦ −1/2`, `7/2 ↦ 0`, `−5 ↦ −1`), `cos (π/6)`, `cos (π/10)`, `cos (π/180)`,
`cos (−7π/5)`, agreement with the float variant, a 200-bit value.  References: a 240-digit
evaluation with exact reduction, rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def C (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cosPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) := cosPiRatPrecRound (Q q) p m
private def belowOne : AzFloat := X "0.9999999999999999" 53

-- floats: special and exact values
#guard D (C nan 53) == ("NaN", .eq)
#guard D (C (infinity true) 53) == ("NaN", .eq)
#guard D (C (infinity false) 53) == ("NaN", .eq)
#guard D (C zero 53) == ("1.0", .eq)
#guard D (C zero 0) == ("NaN", .eq)
#guard D (C (X "1" 53) 0) == ("NaN", .eq)
#guard D (C (X "1" 53) 53) == ("-1.0", .eq)
#guard D (C (X "2" 53) 53) == ("1.0", .eq)
#guard D (C (X "-3" 53) 53) == ("-1.0", .eq)
#guard D (C (X "0.5" 53) 53) == ("0.0", .eq)
#guard D (C (X "-2.5" 53) 53) == ("0.0", .eq)
#guard D (C (X "100000000000000000000" 80) 53) == ("1.0", .eq)
#guard D (C (X "100000000000000000001" 80) 53) == ("-1.0", .eq)
#guard D (C (X "100000000000000000000.5" 80) 53) == ("0.0", .eq)

-- floats: correctly rounded values
#guard D (C (X "0.25" 53) 53) == ("0.7071067811865476", .gt)
#guard D (C (X "0.25" 53) 53 .Floor) == ("0.7071067811865475", .lt)
#guard D (C (X "0.0009765625" 53) 53) == ("0.9999952938095762", .gt)
#guard D (C (X "100000000000000000000.125" 80) 53) == ("0.9238795325112867", .lt)
#guard D (C (X "0.1" 53) 53) == ("0.9510565162951535", .lt)
#guard D (C (X "0.3333333333333333" 53) 53) == ("0.5", .lt)
#guard D (C (X "0.3333333333333333" 53) 53 .Ceiling) == ("0.5000000000000001", .gt)
#guard toString (cosPi (X "0.25" 53)) == "0.7071067811865476"
#guard D (C ((X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) 53 .Floor) == ("0.9999999999999999", .lt)

-- rationals: special and exact values
#guard D (R "0" 53) == ("1.0", .eq)
#guard D (R "0" 0) == ("NaN", .eq)
#guard D (R "1/3" 0) == ("NaN", .eq)
#guard D (R "1/3" 53) == ("0.5", .eq)
#guard D (R "2/3" 53) == ("-0.5", .eq)
#guard D (R "-4/3" 53) == ("-0.5", .eq)
#guard D (R "5/3" 53) == ("0.5", .eq)
#guard D (R "7/2" 53) == ("0.0", .eq)
#guard D (R "-5" 53) == ("-1.0", .eq)
#guard D (R "100000000000000000000" 53) == ("1.0", .eq)

-- rationals: correctly rounded values
#guard D (R "1/6" 53) == ("0.8660254037844386", .lt)
#guard D (R "1/6" 53 .Ceiling) == ("0.8660254037844387", .gt)
#guard D (R "1/10" 53) == ("0.9510565162951535", .lt)
#guard D (R "1/180" 53) == ("0.9998476951563913", .gt)
#guard D (R "-7/5" 53) == ("-0.30901699437494745", .lt)
#guard D (R "-7/5" 53 .Ceiling) == ("-0.3090169943749474", .gt)
#guard R "1/4" 53 == C (X "0.25" 53) 53
#guard toString (cosPiRat (Q "1/6") 53) == "0.8660254037844386"
#guard toString (cosPiRat (Q "1/10") 200)
  == "0.9510565162951535721164393333793821434056986341257502224473056"
