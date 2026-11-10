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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def S (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) := sinPiRatPrecRound (Q q) p m
private def half : AzFloat := F "1/2" 53
private def nhalf : AzFloat := F "-1/2" 53

-- floats: special and exact values
#guard S nan 53 == (nan, .eq)
#guard S (infinity true) 53 == (nan, .eq)
#guard S (infinity false) 53 == (nan, .eq)
#guard S zero 53 == (zero, .eq)
#guard S zero 0 == (zero, .eq)
#guard S (F "1" 53) 0 == (nan, .eq)
#guard S (F "1" 53) 53 == (zero, .eq)
#guard S (F "2" 53) 53 == (zero, .eq)
#guard S (F "-3" 53) 53 == (zero, .eq)
#guard S (F "1/2" 53) 53 == (F "1" 53, .eq)
#guard S (F "-1/2" 53) 53 == (F "-1" 53, .eq)
#guard S (F "3/2" 53) 53 == (F "-1" 53, .eq)
#guard S (F "-5/2" 53) 53 == (F "-1" 53, .eq)
#guard S (F "100000000000000000000" 80) 53 == (zero, .eq)
#guard S (F "200000000000000000001/2" 80) 53 == (F "1" 53, .eq)
#guard S (F "200000000000000000003/2" 80) 53 == (F "-1" 53, .eq)

-- floats: correctly rounded values
#guard S (F "1/4" 53) 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard S (F "1/4" 53) 53 .Floor == (F "1592262918131443/2251799813685248" 53, .lt)
#guard S (F "1/1024" 53) 53 == (F "3537113327227485/1152921504606846976" 53, .lt)
#guard S (F "800000000000000000001/8" 80) 53 == (F "6893811853601123/18014398509481984" 53, .gt)
#guard S (F "400000000000000000001/4" 80) 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard S (F "1/10" 53) 53 == (F "347922205179541/1125899906842624" 53, .gt)
#guard S (F "1/6" 53) 53 == (half, .gt)
#guard S (F "1/6" 53) 53 .Floor == (F "9007199254740991/18014398509481984" 53, .lt)
#guard S (F "-1/6" 53) 53 == (nhalf, .lt)
#guard S (F "-1/6" 53) 53 .Ceiling == (F "-9007199254740991/18014398509481984" 53, .gt)
#guard S (F "4503599627370497/4503599627370496" 53) 53
  == (F "-884279719003555/1267650600228229401496703205376" 53, .gt)
#guard sinPi (F "1/4" 53) == F "6369051672525773/9007199254740992" 53

-- floats: the tiny path (`sin (π x)` rounds like a value just below `π x`)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
private def piLo : AzFloat := (F "884279719003555/281474976710656" 53) <<< tinyE
private def piHi : AzFloat := (F "7074237752028441/2251799813685248" 53) <<< tinyE
#guard S tinyX 53 == (piLo, .lt)
#guard S tinyX 53 .Ceiling == (piHi, .gt)
#guard S (-tinyX) 53 == (-piLo, .gt)
#guard S (-tinyX) 53 .Floor == (-piHi, .lt)

-- rationals: special and exact values
#guard R "0" 53 == (zero, .eq)
#guard R "0" 0 == (zero, .eq)
#guard R "1/3" 0 == (nan, .eq)
#guard R "1/6" 53 == (half, .eq)
#guard R "5/6" 53 == (half, .eq)
#guard R "7/6" 53 == (nhalf, .eq)
#guard R "11/6" 53 == (nhalf, .eq)
#guard R "-1/6" 53 == (nhalf, .eq)
#guard R "13/6" 53 == (half, .eq)
#guard R "7/2" 53 == (F "-1" 53, .eq)
#guard R "-7/2" 53 == (F "1" 53, .eq)
#guard R "-5" 53 == (zero, .eq)
#guard R "100000000000000000000" 53 == (zero, .eq)

-- rationals: correctly rounded values
#guard R "1/3" 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard R "1/3" 53 .Ceiling == (F "7800463371553963/9007199254740992" 53, .gt)
#guard R "1/10" 53 == (F "347922205179541/1125899906842624" 53, .gt)
#guard R "1/180" 53 == (F "2515156836085391/144115188075855872" 53, .lt)
#guard R "-7/5" 53 == (F "8566355544790271/9007199254740992" 53, .lt)
#guard R "-7/5" 53 .Ceiling == (F "33462326346837/35184372088832" 53, .gt)
#guard R "22/7" 53 == (F "-7816154583247809/18014398509481984" 53, .gt)
#guard R "1/4" 53 == S (F "1/4" 53) 53
#guard sinPiRat (Q "1/3") 53 == F "3900231685776981/4503599627370496" 53
#guard (toString (sinPiRat (Q "1/10") 200)).startsWith
  "0.30901699437494742410229341718281905886015458990288143106772"
