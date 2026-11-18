/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Sin
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `sin`

The special values (`NaN`, `±∞`, `sin 0 = 0` at every precision, `p = 0`), the correctly rounded
53-bit values of `sin (1/2)`, `sin (±1)`, `sin 3`, `sin (1/1024)`, `sin 100`, `sin (−1000)`,
`sin 10¹²`, `sin 2⁶⁰`, `sin` of the 53-bit floats nearest `−7/5` and `22/7`, the directed
modes, a 20-bit result, 200-bit values.  Extreme arguments: the 53-bit float nearest `π`
(`sin ≈ 1.2·10⁻¹⁶`: the loop resolves the small result), `2⁻⁴⁰` (the ordinary path next to the
argument), and `±2^(−2^30)`, `(3/2)·2^(−2^30)` at 100 bits (the tiny path, independent of the
exponent), and `2^1000` (a 700-digit `π` for the reference).  References: a 260-digit evaluation
(Machin `π`, exact reduction, Taylor series) at
the exact float arguments, rounded to 53 bits with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinPrecRound x p m

-- special values
#guard D (S nan 53) == ("NaN", .eq)
#guard D (S (infinity true) 53) == ("NaN", .eq)
#guard D (S (infinity false) 53) == ("NaN", .eq)
#guard D (S zero 53) == ("0.0", .eq)
#guard D (S zero 0) == ("0.0", .eq)
#guard D (S (X "1" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (S (X "0.5" 53) 53) == ("0.479425538604203", .gt)
#guard D (S (X "1" 53) 53) == ("0.8414709848078965", .lt)
#guard D (S (X "-1" 53) 53) == ("-0.8414709848078965", .gt)
#guard D (S (X "3" 53) 53) == ("0.1411200080598672", .lt)
#guard D (S (X "0.0009765625" 53) 53) == ("0.0009765623447795783", .gt)
#guard D (S (X "100" 53) 53) == ("-0.5063656411097588", .gt)
#guard D (S (X "-1000" 53) 53) == ("-0.8268795405320025", .gt)
#guard D (S (X "1000000000000" 53) 53) == ("-0.6112387023768895", .gt)
#guard D (S (X "1152921504606846976" 53) 53) == ("-0.8306492176372546", .gt)
#guard D (S (X "-1.4" 53) 53) == ("-0.9854497299884601", .gt)
#guard D (S (X "3.142857142857143" 53) 53) == ("-0.00126448893037729", .lt)

-- directed modes and other precisions
#guard D (S (X "1" 53) 53 .Floor) == ("0.8414709848078965", .lt)
#guard D (S (X "1" 53) 53 .Ceiling) == ("0.8414709848078966", .gt)
#guard D (S (X "-1" 53) 53 .Floor) == ("-0.8414709848078966", .lt)
#guard D (S (X "-1" 53) 53 .Ceiling) == ("-0.8414709848078965", .gt)
#guard D (S (X "3" 53) 20) == ("0.14112", .lt)
#guard toString (sin (X "1" 53)) == "0.8414709848078965"
#guard toString (sin (X "1" 200))
  == "0.841470984807896506652502321630298999622563060798371065672752"
#guard toString (sin (X "100" 200))
  == "-0.5063656411097587936565576104597854320650327212906573234433926"

-- near a multiple of `π`: the 53-bit float nearest `π`
private def pi53 : AzFloat := X "3.141592653589793" 53
#guard D (S pi53 53) == ("1.2246467991473532e-16", .gt)
#guard D (S pi53 53 .Floor) == ("1.224646799147353e-16", .lt)
#guard D (S (-pi53) 53 .Ceiling) == ("-1.224646799147353e-16", .gt)

-- small arguments on the ordinary path
#guard D (S (X "9.094947017729282e-13" 53) 53) == ("9.094947017729282e-13", .gt)
#guard D (S (X "9.094947017729282e-13" 53) 53 .Floor) == ("9.094947017729281e-13", .lt)

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
#guard S tinyX 53 == (tinyX, .gt)
#guard S tinyX 53 .Ceiling == (tinyX, .gt)
#guard (S tinyX 53 .Floor).2 == .lt
#guard (S tinyX 53 .Floor).1 != tinyX
#guard S (-tinyX) 53 == (-tinyX, .lt)
#guard S (-tinyX) 53 .Floor == (-tinyX, .lt)
#guard (S (-tinyX) 53 .Ceiling).2 == .gt
#guard S ((X "1.5" 100) <<< tinyE) 53 == ((X "1.5" 53) <<< tinyE, .gt)
#guard (S tinyX 200).1 == (X "1" 200) <<< tinyE
#guard sin tinyX == tinyX
-- the tiny path and the loop agree where both apply (`2^(−200)` at 53 and at 150 bits)
#guard S ((X "1" 53) <<< AzInt.ofInt (-200)) 53 .Floor
  == ((S ((X "1" 53) <<< AzInt.ofInt (-200)) 150 .Floor).1 |> fun y => (setPrecRound y 53 .Floor))

-- a huge argument (`2^1000`; reference with a 700-digit `π`): the reduction needs `π` to about
-- 1000 more bits, the series does not
#guard D (S ((X "1" 53) <<< AzInt.ofInt 1000) 53) == ("-0.15920170308624243", .gt)
