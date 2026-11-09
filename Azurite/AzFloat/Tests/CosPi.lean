/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.CosPi
import Azurite.AzFloat.ToString
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def C (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cosPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) := cosPiRatPrecRound (Q q) p m
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53

-- floats: special and exact values
#guard C nan 53 == (nan, .eq)
#guard C (infinity true) 53 == (nan, .eq)
#guard C (infinity false) 53 == (nan, .eq)
#guard C zero 53 == (F "1" 53, .eq)
#guard C zero 0 == (nan, .eq)
#guard C (F "1" 53) 0 == (nan, .eq)
#guard C (F "1" 53) 53 == (F "-1" 53, .eq)
#guard C (F "2" 53) 53 == (F "1" 53, .eq)
#guard C (F "-3" 53) 53 == (F "-1" 53, .eq)
#guard C (F "1/2" 53) 53 == (zero, .eq)
#guard C (F "-5/2" 53) 53 == (zero, .eq)
#guard C (F "100000000000000000000" 80) 53 == (F "1" 53, .eq)
#guard C (F "100000000000000000001" 80) 53 == (F "-1" 53, .eq)
#guard C (F "200000000000000000001/2" 80) 53 == (zero, .eq)

-- floats: correctly rounded values
#guard C (F "1/4" 53) 53 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard C (F "1/4" 53) 53 .Floor == (F "1592262918131443/2251799813685248" 53, .lt)
#guard C (F "1/1024" 53) 53 == (F "4503578432573057/4503599627370496" 53, .gt)
#guard C (F "800000000000000000001/8" 80) 53 == (F "4160783518353059/4503599627370496" 53, .lt)
#guard C (F "1/10" 53) 53 == (F "8566355544790271/9007199254740992" 53, .lt)
#guard C (F "1/3" 53) 53 == (F "1/2" 53, .lt)
#guard C (F "1/3" 53) 53 .Ceiling == (F "4503599627370497/9007199254740992" 53, .gt)
#guard cosPi (F "1/4" 53) == F "6369051672525773/9007199254740992" 53
#guard C ((F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) 53 .Floor == (belowOne, .lt)

-- rationals: special and exact values
#guard R "0" 53 == (F "1" 53, .eq)
#guard R "0" 0 == (nan, .eq)
#guard R "1/3" 0 == (nan, .eq)
#guard R "1/3" 53 == (F "1/2" 53, .eq)
#guard R "2/3" 53 == (F "-1/2" 53, .eq)
#guard R "-4/3" 53 == (F "-1/2" 53, .eq)
#guard R "5/3" 53 == (F "1/2" 53, .eq)
#guard R "7/2" 53 == (zero, .eq)
#guard R "-5" 53 == (F "-1" 53, .eq)
#guard R "100000000000000000000" 53 == (F "1" 53, .eq)

-- rationals: correctly rounded values
#guard R "1/6" 53 == (F "3900231685776981/4503599627370496" 53, .lt)
#guard R "1/6" 53 .Ceiling == (F "7800463371553963/9007199254740992" 53, .gt)
#guard R "1/10" 53 == (F "8566355544790271/9007199254740992" 53, .lt)
#guard R "1/180" 53 == (F "4502913707333573/4503599627370496" 53, .gt)
#guard R "-7/5" 53 == (F "-347922205179541/1125899906842624" 53, .lt)
#guard R "-7/5" 53 .Ceiling == (F "-5566755282872655/18014398509481984" 53, .gt)
#guard R "1/4" 53 == C (F "1/4" 53) 53
#guard cosPiRat (Q "1/6") 53 == F "3900231685776981/4503599627370496" 53
#guard (toString (cosPiRat (Q "1/10") 200)).startsWith
  "0.95105651629515357211643933337938214340569863412575022244730"
