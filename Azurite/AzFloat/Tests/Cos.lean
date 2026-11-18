/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `cos`

The special values (`NaN`, `±∞`, `cos 0 = 1`, `p = 0`), the correctly rounded 53-bit values of
`cos (1/2)`, `cos (±1)`, `cos 3`, `cos (1/1024)`, `cos 100`, `cos (−1000)`, `cos 10¹²`,
`cos 2⁶⁰`, `cos` of the 53-bit floats nearest `−7/5`, `22/7` and `π`, and `cos 2⁻¹⁰⁰` (both
round to `±1`), the directed modes, a 20-bit result, and 200-bit values of `cos 1` and `cos 100`.
References: a 240-digit evaluation (Machin `π`, exact reduction, Taylor series) at the exact
float arguments, rounded to 53 bits with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def C (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cosPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (C nan 53) == ("NaN", .eq)
#guard D (C (infinity true) 53) == ("NaN", .eq)
#guard D (C (infinity false) 53) == ("NaN", .eq)
#guard D (C zero 53) == ("1.0", .eq)
#guard D (C zero 0) == ("NaN", .eq)
#guard D (C (X "1" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (C (X "0.5" 53) 53) == ("0.8775825618903728", .gt)
#guard D (C (X "1" 53) 53) == ("0.5403023058681398", .gt)
#guard D (C (X "-1" 53) 53) == ("0.5403023058681398", .gt)
#guard D (C (X "3" 53) 53) == ("-0.9899924966004454", .gt)
#guard D (C (X "0.0009765625" 53) 53) == ("0.9999995231628797", .lt)
#guard D (C (X "100" 53) 53) == ("0.8623188722876839", .lt)
#guard D (C (X "-1000" 53) 53) == ("0.5623790762907029", .lt)
#guard D (C (X "1000000000000" 53) 53) == ("0.7914463018528902", .lt)
#guard D (C (X "1152921504606846976" 53) 53) == ("-0.5567960822766417", .gt)
#guard D (C (X "-1.4" 53) 53) == ("0.16996714290024104", .gt)
#guard D (C (X "3.142857142857143" 53) 53) == ("-0.999999200533553", .lt)
#guard D (C (X "3.141592653589793" 53) 53) == ("-1.0", .lt)
#guard D (C (X "7.888609052210118e-31" 53) 53) == ("1.0", .gt)

-- directed modes and other precisions
#guard D (C (X "1" 53) 53 .Floor) == ("0.5403023058681397", .lt)
#guard D (C (X "1" 53) 53 .Ceiling) == ("0.5403023058681398", .gt)
#guard D (C (X "3" 53) 53 .Floor) == ("-0.9899924966004455", .lt)
#guard D (C (X "3" 53) 53 .Ceiling) == ("-0.9899924966004454", .gt)
#guard D (C (X "3" 53) 20) == ("-0.989992", .gt)
#guard toString (cos (X "1" 53)) == "0.5403023058681398"
#guard toString (cos (X "1" 200))
  == "0.540302305868139717400936607442976603732310420617922227670097"
#guard toString (cos (X "100" 200))
  == "0.862318872287683934101938513950842535510084008535510829280162"

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (cosPrecRound tinyX 53 .Nearest) == ("1.0", .gt)
#guard D (cosPrecRound tinyX 53 .Ceiling) == ("1.0", .gt)
#guard D (cosPrecRound tinyX 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (cosPrecRound (-tinyX) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (cosPrecRound ((X "0.3333333333333333333333333333333333333333333333333333333333334\
  " 200) <<< tinyE) 10 .Nearest) == ("1.0", .gt)
#guard toString (cos tinyX) == "1.0"
-- the tiny path and the loop agree where both apply
#guard D (cosPrecRound ((X "1" 53) <<< AzInt.ofInt (-130)) 53 .Floor) == ("0.9999999999999999", .lt)

-- a huge argument (`2^1000`; reference with a 700-digit `π`): only `π` and the exact remainder
-- are computed at the reduction precision, the series runs at `w + 12` bits
#guard D (C ((X "1" 53) <<< AzInt.ofInt 1000) 53) == ("0.9872460775989135", .lt)
