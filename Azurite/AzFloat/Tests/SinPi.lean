/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `sin (π x)`

Floats: the special values, the exact values at integers and half-integers (including `10²⁰`
and `10²⁰ + 1/2` at 80 bits), the correctly rounded `sin (π/4)`, `sin (π/1024)`,
`sin (π (10²⁰ + 1/8))` and `sin (π (10²⁰ + 1/4))` (80-bit arguments: exact reduction, no loss
from the size), `sin (π ⌊1/10⌋₅₃)`, `sin (±π ⌊1/6⌋₅₃)` (just below `1/2`: rounds to `±1/2`
inexactly), the float next above `1` (`sin ≈ −7·10⁻¹⁶`), the directed modes, the tiny path at
`±2^(−2^30)`.  Rationals: the special values, the exact values (`1/6 ↦ 1/2`, `5/6 ↦ 1/2`,
`7/6 ↦ −1/2`, `−1/6 ↦ −1/2`, `7/2 ↦ −1`, `−5 ↦ 0`), `sin (π/3)`, `sin (π/10)`, `sin (π/180)`,
`sin (−7π/5)`, `sin (22π/7)`, agreement with the float variant, a 200-bit value.  References: a
300-digit evaluation with exact reduction, rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) := sinPiRatPrecRound (Q q) p m
private def half : AzFloat := X "0.5" 53
private def nhalf : AzFloat := X "-0.5" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- floats: special and exact values
#guard D (S nan 53) == ("NaN", .eq)
#guard D (S (infinity true) 53) == ("NaN", .eq)
#guard D (S (infinity false) 53) == ("NaN", .eq)
#guard D (S zero 53) == ("0.0", .eq)
#guard D (S zero 0) == ("0.0", .eq)
#guard D (S (X "1" 53) 0) == ("NaN", .eq)
#guard D (S (X "1" 53) 53) == ("0.0", .eq)
#guard D (S (X "2" 53) 53) == ("0.0", .eq)
#guard D (S (X "-3" 53) 53) == ("0.0", .eq)
#guard D (S (X "0.5" 53) 53) == ("1.0", .eq)
#guard D (S (X "-0.5" 53) 53) == ("-1.0", .eq)
#guard D (S (X "1.5" 53) 53) == ("-1.0", .eq)
#guard D (S (X "-2.5" 53) 53) == ("-1.0", .eq)
#guard D (S (X "100000000000000000000" 80) 53) == ("0.0", .eq)
#guard D (S (X "100000000000000000000.5" 80) 53) == ("1.0", .eq)
#guard D (S (X "100000000000000000001.5" 80) 53) == ("-1.0", .eq)

-- floats: correctly rounded values
#guard D (S (X "0.25" 53) 53) == ("0.7071067811865476", .gt)
#guard D (S (X "0.25" 53) 53 .Floor) == ("0.7071067811865475", .lt)
#guard D (S (X "0.0009765625" 53) 53) == ("0.003067956762965976", .lt)
#guard D (S (X "100000000000000000000.125" 80) 53) == ("0.3826834323650898", .gt)
#guard D (S (X "100000000000000000000.25" 80) 53) == ("0.7071067811865476", .gt)
#guard D (S (X "0.1" 53) 53) == ("0.30901699437494745", .gt)
#guard D (S (X "0.16666666666666666" 53) 53) == ("0.5", .gt)
#guard D (S (X "0.16666666666666666" 53) 53 .Floor) == ("0.49999999999999994", .lt)
#guard D (S (X "-0.16666666666666666" 53) 53) == ("-0.5", .lt)
#guard D (S (X "-0.16666666666666666" 53) 53 .Ceiling) == ("-0.49999999999999994", .gt)
#guard D (S (X "1.0000000000000002" 53) 53) == ("-6.975736996017264e-16", .gt)
#guard toString (sinPi (X "0.25" 53)) == "0.7071067811865476"

-- floats: the tiny path (`sin (π x)` rounds like a value just below `π x`)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def piLo : AzFloat := (X "3.141592653589793" 53) <<< tinyE
private def piHi : AzFloat := (X "3.1415926535897936" 53) <<< tinyE
#guard S tinyX 53 == (piLo, .lt)
#guard S tinyX 53 .Ceiling == (piHi, .gt)
#guard S (-tinyX) 53 == (-piLo, .gt)
#guard S (-tinyX) 53 .Floor == (-piHi, .lt)

-- rationals: special and exact values
#guard D (R "0" 53) == ("0.0", .eq)
#guard D (R "0" 0) == ("0.0", .eq)
#guard D (R "1/3" 0) == ("NaN", .eq)
#guard D (R "1/6" 53) == ("0.5", .eq)
#guard D (R "5/6" 53) == ("0.5", .eq)
#guard D (R "7/6" 53) == ("-0.5", .eq)
#guard D (R "11/6" 53) == ("-0.5", .eq)
#guard D (R "-1/6" 53) == ("-0.5", .eq)
#guard D (R "13/6" 53) == ("0.5", .eq)
#guard D (R "7/2" 53) == ("-1.0", .eq)
#guard D (R "-7/2" 53) == ("1.0", .eq)
#guard D (R "-5" 53) == ("0.0", .eq)
#guard D (R "100000000000000000000" 53) == ("0.0", .eq)

-- rationals: correctly rounded values
#guard D (R "1/3" 53) == ("0.8660254037844386", .lt)
#guard D (R "1/3" 53 .Ceiling) == ("0.8660254037844387", .gt)
#guard D (R "1/10" 53) == ("0.30901699437494745", .gt)
#guard D (R "1/180" 53) == ("0.01745240643728351", .lt)
#guard D (R "-7/5" 53) == ("0.9510565162951535", .lt)
#guard D (R "-7/5" 53 .Ceiling) == ("0.9510565162951536", .gt)
#guard D (R "22/7" 53) == ("-0.4338837391175581", .gt)
#guard R "1/4" 53 == S (X "0.25" 53) 53
#guard toString (sinPiRat (Q "1/3") 53) == "0.8660254037844386"
#guard toString (sinPiRat (Q "1/10") 200)
  == "0.3090169943749474241022934171828190588601545899028814310677242"
