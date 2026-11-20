/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammer
import Azurite.AzFloat.Gamma
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for the generalized Pochhammer symbol `Γ(x + y)/Γ(x)`

`NaN` and infinite arguments; an integer `y ≥ 0` (Pochhammer's symbol, also at the poles of
`Γ(x)`: `(−5)₃ = −60`, `(−2)₃ = 0`); an integer `y < 0` (`1/((x − 1) ⋯ (x + y))`: the limits
at the poles of `Γ(x)`, the poles `x = 1, …, −y`); a `y` that is not an integer (all four
sign patterns of `x` and `x + y`, `Γ(1/2)/Γ(1) … = 1/√π`, the zeros at the poles of `Γ(x)`,
`NaN` at the poles of `Γ(x + y)`); agreement with `Γ(1 + y)` and `Γ(2 + y)`, with Pochhammer's
symbol and with the functional equation; other precisions.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x y : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  genPochhammerPrecRound (X x 53) (X y 53) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `NaN` and infinite arguments
#guard D (genPochhammerPrecRound nan (X "1" 53) 53 .Nearest) == ("NaN", .eq)
#guard D (genPochhammerPrecRound (X "1" 53) nan 53 .Nearest) == ("NaN", .eq)
#guard D (genPochhammerPrecRound (infinity true) (X "1" 53) 53 .Nearest) == ("NaN", .eq)
#guard D (genPochhammerPrecRound (X "1" 53) (infinity true) 53 .Nearest) == ("NaN", .eq)
#guard D (genPochhammerPrecRound (infinity false) (infinity true) 53 .Nearest) == ("NaN", .eq)
#guard D (P "0.5" "0.5" 0) == ("NaN", .eq)
#guard D (P "-2" "0.5" 0) == ("0.0", .eq)

-- an integer `y ≥ 0`: Pochhammer's symbol
#guard D (P "2.5" "3" 53) == ("39.375", .eq)
#guard D (P "0.1" "4" 53) == ("0.7161000000000001", .gt)
#guard D (P "-5" "3" 53) == ("-6.0e1", .eq)
#guard D (P "-2" "3" 53) == ("0.0", .eq)
#guard D (P "2.5" "0" 53) == ("1.0", .eq)
#guard D (P "-3" "0" 53) == ("1.0", .eq)
#guard D (P "0" "0" 53) == ("1.0", .eq)
#guard D (P "0.5" "200" 53) == ("3.1443238660087782e373", .lt)

-- an integer `y < 0`: the reciprocal of a product, its limits and its poles
#guard D (P "2.5" "-2" 53) == ("1.3333333333333333", .lt)
#guard D (P "4" "-3" 53) == ("0.16666666666666666", .lt)
#guard D (P "4" "-3" 53 .Ceiling) == ("0.16666666666666669", .gt)
#guard D (P "3" "-2" 53) == ("0.5", .eq)
#guard D (P "-2" "-3" 53) == ("-0.016666666666666666", .gt)
#guard D (P "-2" "-3" 53 .Floor) == ("-0.01666666666666667", .lt)
#guard D (P "0" "-1" 53) == ("-1.0", .eq)
#guard D (P "0.5" "-1" 53) == ("-2.0", .eq)
#guard D (P "0.5" "-1000" 53) == ("1.3931086891239053e-2566", .lt)
#guard D (P "100.5" "-300" 53 .Up) == ("6.047653152611967e-531", .gt)
#guard D (P "3" "-3" 53) == ("NaN", .eq)
#guard D (P "1" "-1" 53) == ("NaN", .eq)
#guard D (P "2" "-5" 53) == ("NaN", .eq)
#guard D (P "5" "-5" 53) == ("NaN", .eq)

-- a `y` that is not an integer
#guard D (P "1" "0.5" 53) == ("0.886226925452758", .gt)
#guard D (P "0.5" "0.5" 53) == ("0.5641895835477563", .lt)
#guard D (P "0.5" "0.5" 53 .Floor) == ("0.5641895835477563", .lt)
#guard D (P "0.5" "-0.25" 53) == ("2.045531344226337", .lt)
#guard D (P "-2.5" "0.25" 53) == ("1.8436462374301157", .gt)
#guard D (P "-2.5" "5.25" 53) == ("-1.7014118109096281", .gt)
#guard D (P "2.5" "-5.25" 53 .Ceiling) == ("-0.7556363984443613", .gt)
#guard D (P "0.25" "0.5" 53) == ("0.33798912003364234", .lt)
#guard D (P "1e10" "0.5" 53) == ("99999.99999875", .gt)
#guard D (P "0.3" "1e-20" 53) == ("1.0", .gt)
#guard D (P "1e-20" "0.5" 53) == ("1.772453850905516e-20", .gt)
#guard D (P "100.5" "-1000.25" 53) == ("3.866640183863595e-2426", .gt)

-- zeros at the poles of `Γ(x)`, `NaN` at the poles of `Γ(x + y)`
#guard D (P "-2" "0.5" 53) == ("0.0", .eq)
#guard D (P "0" "0.5" 53) == ("0.0", .eq)
#guard D (P "-2.5" "0.5" 53) == ("NaN", .eq)
#guard D (P "0.5" "-0.5" 53) == ("NaN", .eq)
#guard D (P "0.25" "-3.25" 53) == ("NaN", .eq)

-- other precisions
#guard D (P "1" "0.5" 200)
  == ("0.886226925452758013649083741670572591398774728061193564106904", .lt)
#guard D (P "1" "0.5" 1) == ("1.0", .gt)
#guard D (P "0.5" "0.5" 20 .Up) == ("0.56419", .gt)

-- `Γ(1 + y)/Γ(1) = Γ(1 + y)` and `Γ(2 + y)/Γ(2) = Γ(2 + y)`
#guard P "1" "0.5" 53 == gammaPrecRound (X "1.5" 53) 53 .Nearest
#guard P "1" "-0.5" 53 .Floor == gammaPrecRound (X "0.5" 53) 53 .Floor
#guard P "1" "-3.5" 53 .Up == gammaPrecRound (X "-2.5" 53) 53 .Up
#guard P "2" "-0.75" 100 == gammaPrecRound (X "1.25" 53) 100 .Nearest
#guard P "2" "40.5" 53 .Ceiling == gammaPrecRound (X "42.5" 53) 53 .Ceiling
#guard P "1" "200.5" 200 == gammaPrecRound (X "201.5" 53) 200 .Nearest

-- an integer `y` against Pochhammer's symbol
#guard P "0.5" "200" 53 .Floor == pochhammerPrecRound (X "0.5" 53) 200 53 .Floor
#guard P "-100.5" "1000" 53 == pochhammerPrecRound (X "-100.5" 53) 1000 53 .Nearest

-- `genPochhammer`
#guard toString (genPochhammer (X "2.5" 53) (X "3" 53)) == "39.375"
#guard toString (genPochhammer (X "0.5" 53) (X "0.5" 53)) == "0.5641895835477563"

-- the fuel as an argument
#guard D (genPochhammerPrecRoundFuel 3 (X "0.3" 53) (X "2.5" 53) 53 .Nearest)
  == ("0.5604051902745265", .gt)
#guard D (genPochhammerPrecRoundFuel 3 (X "300.3" 53) (X "-200" 53) 53 .Nearest)
  == ("6.574779833933506e-457", .gt)
#guard genPochhammerPrecRoundFuel (gammaFuel 53) (X "0.3" 53) (X "2.5" 53) 53 .Nearest
  == P "0.3" "2.5" 53
