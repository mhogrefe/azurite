/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammerRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzRat.Instances

/-!
# Tests for the generalized Pochhammer symbol of two rationals

An integer `y ≥ 0` (Pochhammer's symbol), an integer `y < 0` (`(1/3)₋₂ = 9/10`, the limits at
the poles of `Γ(x)`, the poles `x = 1, …, −y`), a `y` that is not an integer (all sign
patterns, `Γ(2/3)/Γ(1/3)`, the zeros at the poles of `Γ(x)`, `NaN` at the poles of
`Γ(x + y)`), `p = 0`; agreement with `Γ(1 + y)` and `Γ(2 + y)`, with Pochhammer's symbol,
with exact rational products, and with the float function on dyadic arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x y : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  genPochhammerRatPrecRound (Q x) (Q y) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `p = 0`
#guard D (P "1/3" "1/3" 0) == ("NaN", .eq)
#guard D (P "1/3" "2" 0) == ("NaN", .eq)
#guard D (P "1/3" "-2" 0) == ("NaN", .eq)
#guard D (P "-2" "1/2" 0) == ("0.0", .eq)

-- an integer `y ≥ 0`: Pochhammer's symbol
#guard D (P "1/3" "3" 53) == ("1.037037037037037", .lt)
#guard D (P "-5" "3" 53) == ("-6.0e1", .eq)
#guard D (P "-2" "3" 53) == ("0.0", .eq)
#guard D (P "1/3" "0" 53) == ("1.0", .eq)
#guard D (P "0" "0" 53) == ("1.0", .eq)

-- an integer `y < 0`: the reciprocal of a product, its limits and its poles
#guard D (P "1/3" "-2" 53) == ("0.9", .gt)
#guard D (P "4" "-3" 53) == ("0.16666666666666666", .lt)
#guard D (P "4" "-3" 53 .Ceiling) == ("0.16666666666666669", .gt)
#guard D (P "-2" "-3" 53) == ("-0.016666666666666666", .gt)
#guard D (P "0" "-1" 53) == ("-1.0", .eq)
#guard D (P "1/3" "-1000" 53) == ("3.365584677580421e-2567", .lt)
#guard D (P "301/3" "-300" 53 .Up) == ("6.220056094444147e-531", .gt)
#guard D (P "3" "-3" 53) == ("NaN", .eq)
#guard D (P "1" "-1" 53) == ("NaN", .eq)
#guard D (P "2" "-5" 53) == ("NaN", .eq)

-- a `y` that is not an integer
#guard D (P "1" "1/2" 53) == ("0.886226925452758", .gt)
#guard D (P "1/2" "1/2" 53) == ("0.5641895835477563", .lt)
#guard D (P "1/3" "1/3" 53) == ("0.5054680881560892", .lt)
#guard D (P "1/3" "1/3" 53 .Floor) == ("0.5054680881560892", .lt)
#guard D (P "1/3" "-1/4" 53) == ("4.292531551989674", .gt)
#guard D (P "-7/3" "1/4" 53) == ("4.298090437430903", .lt)
#guard D (P "-7/3" "21/4" 53) == ("-1.4202774812634873", .lt)
#guard D (P "7/3" "-21/4" 53 .Ceiling) == ("-1.8847388677736703", .gt)
#guard D (P "10000000000" "1/2" 53) == ("99999.99999875", .gt)
#guard D (P "1/3" "1/100000000000000000000" 53) == ("1.0", .gt)
#guard D (P "301/3" "-4001/4" 53) == ("7.323104917685887e-2426", .gt)

-- zeros at the poles of `Γ(x)`, `NaN` at the poles of `Γ(x + y)`
#guard D (P "-2" "1/2" 53) == ("0.0", .eq)
#guard D (P "0" "1/3" 53) == ("0.0", .eq)
#guard D (P "-5/2" "1/2" 53) == ("NaN", .eq)
#guard D (P "1/3" "-1/3" 53) == ("NaN", .eq)
#guard D (P "1/4" "-13/4" 53) == ("NaN", .eq)

-- other precisions
#guard D (P "1/3" "1/3" 200)
  == ("0.505468088156089278032068745403594403597883874275750484633694", .gt)
#guard D (P "1/3" "1/3" 1) == ("0.5", .lt)
#guard D (P "1/3" "1/3" 20 .Up) == ("0.505468", .gt)

-- `Γ(1 + y)/Γ(1) = Γ(1 + y)` and `Γ(2 + y)/Γ(2) = Γ(2 + y)`
#guard P "1" "1/3" 53 == gammaRatPrecRound (Q "4/3") 53 .Nearest
#guard P "1" "-2/3" 53 .Floor == gammaRatPrecRound (Q "1/3") 53 .Floor
#guard P "1" "-10/3" 53 .Up == gammaRatPrecRound (Q "-7/3") 53 .Up
#guard P "2" "-3/4" 100 == gammaRatPrecRound (Q "5/4") 100 .Nearest
#guard P "2" "121/3" 53 .Ceiling == gammaRatPrecRound (Q "127/3") 53 .Ceiling

-- an integer `y` against Pochhammer's symbol and exact rational products
private def recip (x : String) (n p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  ofAzRatRound
    (Q "1" / (List.range n).foldl (fun acc j => acc * (Q x - Q (toString (j + 1)))) (Q "1")) p m
#guard P "1/3" "200" 53 .Floor == pochhammerRatPrecRound (Q "1/3") 200 53 .Floor
#guard P "-301/3" "1000" 53 == pochhammerRatPrecRound (Q "-301/3") 1000 53 .Nearest
#guard P "1/3" "-200" 53 == recip "1/3" 200 53 .Nearest
#guard P "301/3" "-201" 53 .Floor == recip "301/3" 201 53 .Floor
#guard P "1/3" "-1000" 53 .Up == recip "1/3" 1000 53 .Up
#guard P "1001/3" "-1001" 53 .Ceiling == recip "1001/3" 1001 53 .Ceiling
#guard P "-7/3" "-1000" 53 .Down == recip "-7/3" 1000 53 .Down

-- agreement with the float function on dyadic arguments
#guard P "1/2" "1/2" 53 == genPochhammerPrecRound (X "0.5" 53) (X "0.5" 53) 53 .Nearest
#guard P "-5/2" "21/4" 53 .Floor
  == genPochhammerPrecRound (X "-2.5" 53) (X "5.25" 53) 53 .Floor
#guard P "5/2" "-2" 53 == genPochhammerPrecRound (X "2.5" 53) (X "-2" 53) 53 .Nearest

-- `genPochhammerRat`
#guard toString (genPochhammerRat (Q "1/3") (Q "-2") 53) == "0.9"
#guard toString (genPochhammerRat (Q "1/3") (Q "1/3") 53) == "0.5054680881560892"

-- the fuel as an argument
#guard D (genPochhammerRatPrecRoundFuel 3 (Q "1/3") (Q "5/2") 53 .Nearest)
  == ("0.6437384500594929", .lt)
#guard D (genPochhammerRatPrecRoundFuel 3 (Q "901/3") (Q "-200") 53 .Nearest)
  == ("6.338106190823902e-457", .lt)
#guard genPochhammerRatPrecRoundFuel (gammaFuel 53) (Q "1/3") (Q "5/2") 53 .Nearest
  == P "1/3" "5/2" 53

-- no fuel for an integer `y` when the denominator of `x` is not a power of two (and `n ≥ 4`
-- for `y < 0`: `1/((−2/3)(1/3)(4/3)) = −27/8` is dyadic)
#guard !recipPochRatSpecial (Q "7/3") 3 && recipPochRatSpecial (Q "7/3") 4
#guard !recipPochRatSpecial (Q "7/4") 200
#guard D (genPochhammerRatPrecRoundFuel 0 (Q "7/3") (Q "-3") 53 .Nearest) == ("-3.375", .eq)
#guard D (genPochhammerRatPrecRoundFuel 0 (Q "901/3") (Q "-200") 53 .Nearest)
  == ("6.338106190823902e-457", .lt)
#guard D (genPochhammerRatPrecRoundFuel 0 (Q "1/3") (Q "200") 53 .Nearest)
  == ("8.603289796878314e372", .lt)
