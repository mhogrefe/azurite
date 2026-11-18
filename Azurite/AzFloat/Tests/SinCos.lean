/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCos
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `sinCos`

The special values, the correctly rounded 53-bit pairs `(sin x, cos x)` at `1/2`, `±1`, `3`,
`1/1024`, `100`, `−1000`, `10¹²`, `2⁶⁰`, the 53-bit floats nearest `−7/5`, `22/7` and `π`
(reference values of `Tests/Sin.lean` and `Tests/Cos.lean`), the directed modes, a 20-bit result,
200-bit and 2000-bit values, the agreement with `sinPrecRound` and `cosPrecRound` on a sweep of
arguments covering all the octants and both signs, small arguments on the ordinary path, tiny
arguments (delegated), and `2^1000`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A pair of floats as decimal outputs. -/
private def D2f (r : AzFloat × AzFloat) : String × String := (toString r.1, toString r.2)
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A pair of results as decimal outputs and comparison tags. -/
private def D2 (r : (AzFloat × Ordering) × (AzFloat × Ordering)) :
    (String × Ordering) × (String × Ordering) :=
  ((toString r.1.1, r.1.2), (toString r.2.1, r.2.2))
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def SC (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinCosPrecRound x p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosPrecRound x p m == (sinPrecRound x p m, cosPrecRound x p m)

-- special values
#guard D2 (SC nan 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC (infinity true) 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC (infinity false) 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC zero 53) == (("0.0", .eq), ("1.0", .eq))
#guard D2 (SC zero 0) == (("0.0", .eq), ("NaN", .eq))
#guard D2 (SC (X "1" 53) 0) == (("NaN", .eq), ("NaN", .eq))

-- correctly rounded values
#guard D2 (SC (X "0.5" 53) 53) == (("0.479425538604203", .gt), ("0.8775825618903728", .gt))
#guard D2 (SC (X "1" 53) 53) == (("0.8414709848078965", .lt), ("0.5403023058681398", .gt))
#guard D2 (SC (X "-1" 53) 53) == (("-0.8414709848078965", .gt), ("0.5403023058681398", .gt))
#guard D2 (SC (X "3" 53) 53) == (("0.1411200080598672", .lt), ("-0.9899924966004454", .gt))
#guard D2 (SC (X "0.0009765625" 53) 53)
  == (("0.0009765623447795783", .gt), ("0.9999995231628797", .lt))
#guard D2 (SC (X "100" 53) 53) == (("-0.5063656411097588", .gt), ("0.8623188722876839", .lt))
#guard D2 (SC (X "-1000" 53) 53) == (("-0.8268795405320025", .gt), ("0.5623790762907029", .lt))
#guard D2 (SC (X "1000000000000" 53) 53)
  == (("-0.6112387023768895", .gt), ("0.7914463018528902", .lt))
#guard D2 (SC (X "1152921504606846976" 53) 53)
  == (("-0.8306492176372546", .gt), ("-0.5567960822766417", .gt))
#guard D2 (SC (X "-1.4" 53) 53) == (("-0.9854497299884601", .gt), ("0.16996714290024104", .gt))
#guard D2 (SC (X "3.142857142857143" 53) 53) == (("-0.00126448893037729", .lt), ("-0.99999920053355\
  3", .lt))

-- directed modes and other precisions
#guard D2 (SC (X "1" 53) 53 .Floor) == (("0.8414709848078965", .lt), ("0.5403023058681397", .lt))
#guard D2 (SC (X "1" 53) 53 .Ceiling) == (("0.8414709848078966", .gt), ("0.5403023058681398", .gt))
#guard D2 (SC (X "3" 53) 20) == (("0.14112", .lt), ("-0.989992", .gt))
#guard D2f (sinCos (X "1" 53)) == ("0.8414709848078965", "0.5403023058681398")
#guard toString ((sinCos (X "1" 200)).1)
  == "0.841470984807896506652502321630298999622563060798371065672752"
#guard toString ((sinCos (X "1" 200)).2)
  == "0.540302305868139717400936607442976603732310420617922227670097"
#guard toString ((sinCos (X "100" 200)).1)
  == "-0.5063656411097587936565576104597854320650327212906573234433926"

-- near a multiple of `π`: the 53-bit float nearest `π`
private def pi53 : AzFloat := X "3.141592653589793" 53
#guard D2 (SC pi53 53) == (("1.2246467991473532e-16", .gt), ("-1.0", .lt))
#guard agrees (-pi53) 53 .Ceiling

-- agreement with the separate functions: all the octants, both signs, several modes
#guard (List.range 26).all fun i => agrees (F s!"{i + 1}/4" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"-{i + 1}/4" 53) 53 .Floor
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 13).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 40 .Down
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (X "1" 53) 1
#guard agrees (X "12345678814.81481618629628669593" 100) 300
#guard agrees (X "0.3333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    3333333333333333333333333333333333333333333333333335" 2000) 2000

-- small arguments on the ordinary path, tiny arguments (delegated) and a huge argument
#guard agrees (X "9.094947017729282e-13" 53) 53
#guard agrees (X "9.094947017729282e-13" 53) 53 .Floor
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard SC tinyX 53 == ((tinyX, .gt), (X "1" 53, .gt))
#guard agrees (-tinyX) 53 .Floor
#guard agrees ((X "1" 53) <<< AzInt.ofInt (-200)) 53
#guard D (SC ((X "1" 53) <<< AzInt.ofInt 1000) 53).1 == ("-0.15920170308624243", .gt)
