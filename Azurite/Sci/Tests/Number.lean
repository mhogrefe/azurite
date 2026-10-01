/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Sci.Number

/-!
# Tests for `SciNumber` rendering

Hand-built `SciNumber`s whose expected strings come from the author's Malachite `to_sci`
tests and doc examples.
-/

open Azurite Azurite.SciNumber

private def N (neg : Bool) (base : UInt64) (ds : List Nat) (scale : Int) : SciNumber :=
  { negative := neg, base := base, digits := (ds.map Nat.toUInt64).toArray, scale := scale }

private def F : SciFormat := {}

-- 22/7 to 16 significant digits: 3142857142857143 · 10^-15
#guard (N false 10 [3,1,4,2,8,5,7,1,4,2,8,5,7,1,4,3] 15).toString F == "3.142857142857143"
#guard (N false 10 [3,1,4,2,8,5,7,1,4,2,8,5,7,1,4,3] 15).value
  == (3142857142857143 : ℚ) / 10 ^ 15
-- 22/7 to 3 digits, and rounded with Ceiling
#guard (N false 10 [3,1,4] 2).toString F == "3.14"
#guard (N false 10 [3,1,5] 2).toString F == "3.15"
#guard (N true 10 [3,1,5] 2).toString F == "-3.15"
-- 936851431250/1397 to 6 digits: 670617 · 10^3 (scale −3 forces exponent form)
#guard (N false 10 [6,7,0,6,1,7] (-3)).toString F == "6.70617e8"
#guard (N false 10 [6,7,0,6,1,7] (-3)).toString { F with eLowercase := false } == "6.70617E8"
#guard (N false 10 [6,7,0,6,1,7] (-3)).toString
  { F with eLowercase := false, forceExponentPlusSign := true } == "6.70617E+8"
#guard (N false 10 [6,7,0,6,1,7] (-3)).exponent == 8
-- 123/45678909876: 2692708743135418 · 10^-24, exponent −9
#guard (N false 10 [2,6,9,2,7,0,8,7,4,3,1,3,5,4,1,8] 24).toString F == "2.692708743135418e-9"
#guard (N false 10 [2,6,9,2,7,0,8,7,4,3,1,3,5,4,1,8] 24).toString { F with negExpThreshold := -10 }
  == "0.000000002692708743135418"
-- 1/2, 1/4, 1/3 at 16 digits
#guard (N false 10 [5] 1).toString F == "0.5"
#guard (N false 10 [2,5] 2).toString F == "0.25"
#guard (N false 10 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 16).toString F == "0.3333333333333333"
-- integers: 123 (scale 0), 1000 at precision 2 → digits "10", scale −2
#guard (N false 10 [1,2,3] 0).toString F == "123"
#guard (N false 10 [1,0] (-2)).toString F == "1e3"
#guard (N false 10 [1,0] (-2)).toString { F with includeTrailingZeros := true } == "1.0e3"
-- plain form with trailing zeros: 1.50 at scale 2
#guard (N false 10 [1,5,0] 2).toString F == "1.5"
#guard (N false 10 [1,5,0] 2).toString { F with includeTrailingZeros := true } == "1.50"
-- trailing zeros before the point are never trimmed: 100.0 at scale 1
#guard (N false 10 [1,0,0,0] 1).toString F == "100"
#guard (N false 10 [1,0,0,0] 1).toString { F with includeTrailingZeros := true } == "100.0"
-- zero
#guard (N false 10 [] 0).toString F == "0"
#guard (N false 10 [] 3).toString F == "0"
#guard (N false 10 [] 3).toString { F with includeTrailingZeros := true } == "0.000"
#guard (N false 10 [] 0).value == 0
-- base 20 and case: 22/7 = 3.2h2h2h2h2h2h2h3 (digits 3,2,17,2,17,…,3), scale 15
#guard (N false 20 [3,2,17,2,17,2,17,2,17,2,17,2,17,2,17,3] 15).toString F == "3.2h2h2h2h2h2h2h3"
#guard (N false 20 [3,2,17,2,17,2,17,2,17,2,17,2,17,2,17,3] 15).toString { F with lowercase := false }
  == "3.2H2H2H2H2H2H2H3"
-- base 2: 22/7 with Floor at 19 digits, with and without trailing zeros
#guard (N false 2 [1,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0] 17).toString F == "11.001001001001001"
#guard (N false 2 [1,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0] 17).toString
  { F with includeTrailingZeros := true } == "11.00100100100100100"
-- large exponents: 2^1000000 ≈ 9.900656229295898e301029 (digits ·10^(301029−15))
#guard (N false 10 [9,9,0,0,6,5,6,2,2,9,2,9,5,8,9,8] (15 - 301029)).toString F
  == "9.900656229295898e301029"
#guard (N true 10 [1,0,1,0,0,3,4,0,5,9,1,9,8,0,3] (14 + 301030)).toString F
  == "-1.01003405919803e-301030"
-- base ≥ 15 forces the plus sign on positive exponents
#guard (N false 16 [1,0] (-2)).toString F == "1e+3"
