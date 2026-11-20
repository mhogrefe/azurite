/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Polygamma
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for the polygamma functions

The special values (`NaN`, the infinities, `0`, the negative integers for odd and even `n`,
`p = 0`), the classical values (`ψ′(1) = π²/6`, `ψ′(1/2) = π²/2`, `ψ″(1) = −2 ζ(3)`,
`ψ‴(1) = π⁴/15`, `ψ′(−1/2) = π²/2 + 4`, `ψ″(−1/2) = 16 − 14 ζ(3)`,
`ψ⁽¹⁰⁰⁾(1) = −100! ζ(101)`), negative arguments, large `n`, tiny and huge arguments, the
tiny-argument path at powers of two (where the leading term is a float), 200-bit
values against the known digits, `n = 0` (the digamma function) and `trigamma`.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (n : Nat) (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  polygammaPrecRound n (X x 53) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (polygammaPrecRound 1 nan 53 .Nearest) == ("NaN", .eq)
#guard D (polygammaPrecRound 1 (infinity true) 53 .Nearest) == ("0.0", .eq)
#guard D (polygammaPrecRound 2 (infinity true) 53 .Nearest) == ("0.0", .eq)
#guard D (polygammaPrecRound 1 (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard D (P 1 "0" 53) == ("Infinity", .eq)
#guard D (P 2 "0" 53) == ("-Infinity", .eq)
#guard D (P 3 "0" 0) == ("Infinity", .eq)
#guard D (P 1 "-1" 53) == ("Infinity", .eq)
#guard D (P 3 "-7" 53) == ("Infinity", .eq)
#guard D (P 2 "-1" 53) == ("NaN", .eq)
#guard D (P 4 "-7" 53) == ("NaN", .eq)
#guard D (P 1 "1" 0) == ("NaN", .eq)

-- positive arguments: `π²/6`, `π²/2`, `−2 ζ(3)`, `π⁴/15`, …
#guard D (P 1 "1" 53) == ("1.6449340668482264", .lt)
#guard D (P 1 "1" 53 .Floor) == ("1.6449340668482264", .lt)
#guard D (P 1 "1" 53 .Ceiling) == ("1.6449340668482266", .gt)
#guard D (P 1 "0.5" 53) == ("4.934802200544679", .lt)
#guard D (P 2 "1" 53) == ("-2.4041138063191885", .gt)
#guard D (P 2 "1" 53 .Floor) == ("-2.404113806319189", .lt)
#guard D (P 3 "1" 53) == ("6.493939402266829", .lt)
#guard D (P 1 "100" 53) == ("0.010050166663333571", .lt)
#guard D (P 5 "0.25" 53) == ("491552.5137676813", .gt)
#guard D (P 4 "7.5" 53) == ("-0.002457482989368555", .gt)

-- negative arguments: `ψ′(−1/2) = π²/2 + 4`, `ψ″(−1/2) = 16 − 14 ζ(3)`, …
#guard D (P 1 "-0.5" 53) == ("8.934802200544679", .lt)
#guard D (P 2 "-0.5" 53) == ("-0.82879664423432", .gt)
#guard D (P 1 "-100.5" 53) == ("9.859703491870086", .lt)
#guard D (P 2 "-2.25" 53) == ("123.89694977406016", .lt)
#guard D (P 2 "-2.25" 53 .Up) == ("123.89694977406018", .gt)
#guard D (P 3 "-0.001" 53) == ("6000000000006.519", .gt)
#guard D (P 2 "-1.5" 53) == ("-0.2362040516417274", .gt)
#guard D (P 4 "-1.5" 53) == ("-0.3137559995067314", .lt)

-- large `n`: `ψ⁽¹⁰⁰⁾(1) = −100! ζ(101)`
#guard D (P 20 "3.5" 53) == ("-9182070.204945628", .lt)
#guard D (P 50 "10" 53) == ("-30652457252905.85", .gt)
#guard D (P 100 "1" 53) == ("-9.332621544394415e157", .gt)

-- tiny and huge arguments; integers
#guard D (P 1 "1e10" 53) == ("1.00000000005e-10", .gt)
#guard D (P 1 "1e-10" 53) == ("1.0e20", .gt)
#guard D (P 2 "1e-10" 53) == ("-1.9999999999999998e30", .gt)
#guard D (P 1 "0.0009765625" 53) == ("1048577.6425893921", .lt)
#guard D (P 1 "1e30" 53) == ("9.999999999999999e-31", .lt)
#guard D (P 3 "-1e6" 53) == ("Infinity", .eq)

-- the tiny-argument path at `±2^k`, where the leading term `(−1)ⁿ⁺¹ n!/xⁿ⁺¹` is a float:
-- `ψ′(2⁻¹⁰⁰) = 2²⁰⁰ + π²/6 + …`, `ψ″(±2⁻¹⁰⁰) = ∓2³⁰¹ − 2 ζ(3) + …`
private def T (n : Nat) (k : Int) (neg : Bool) (p : Nat) (m : RoundingMode := .Nearest) :=
  let x := one <<< AzInt.ofInt k
  polygammaPrecRound n (if neg then -x else x) p m
#guard D (T 1 (-100) false 53) == ("1.6069380442589903e60", .lt)
#guard D (T 1 (-100) false 53 .Floor) == ("1.6069380442589903e60", .lt)
#guard D (T 1 (-100) false 53 .Ceiling) == ("1.6069380442589906e60", .gt)
#guard D (T 1 (-100) true 53) == ("1.6069380442589903e60", .lt)
#guard D (T 2 (-100) false 53) == ("-4.074071952668972e90", .gt)
#guard D (T 2 (-100) false 53 .Ceiling) == ("-4.074071952668972e90", .gt)
#guard D (T 2 (-100) false 53 .Floor) == ("-4.074071952668973e90", .lt)
#guard D (T 2 (-100) true 53) == ("4.074071952668972e90", .gt)
#guard D (T 2 (-100) true 53 .Floor) == ("4.0740719526689717e90", .lt)
#guard D (T 3 (-1000) true 53 .Down) == ("7.909224560585659e1204", .lt)
#guard D (T 1 (-40) false 53) == ("1.2089258196146292e24", .lt)
#guard D (T 1 (-40) false 53 .Up) == ("1.2089258196146294e24", .gt)
private def same (a b : AzFloat) : Bool := le a b && le b a
#guard same (T 1 (-100) false 53).1 (one <<< AzInt.ofInt 200)
#guard same (T 2 (-100) true 53).1 (one <<< AzInt.ofInt 301)
#guard same (T 2 (-100) false 53).1 (-(one <<< AzInt.ofInt 301))
#guard (polygammaTiny? 1 (one <<< AzInt.ofInt (-100)) true (AzInt.ofInt (-99)) 53 .Nearest).isSome
#guard (polygammaTiny? 1 (one <<< AzInt.ofInt (-40)) true (AzInt.ofInt (-39)) 53 .Nearest).isNone
-- at a cost independent of the exponent: `ψ′(2^(−10⁶))`, `ψ⁽⁵⁾(−2^(−10⁶))`
#guard same (T 1 (-1000000) false 53).1 (one <<< AzInt.ofInt 2000000)
#guard (T 1 (-1000000) false 53).2 == .lt
#guard (expOf (T 5 (-1000000) true 53).1).toInt == 6000007

-- other precisions: 60 digits of `π²/6` and of `−2 ζ(3)`
#guard D (P 1 "1" 200) == ("1.644934066848226436472415166646025189218949901206798437735558", .lt)
#guard D (P 2 "1" 200) == ("-2.404113806319188570799476323022899981529972584680997763584544", .lt)
#guard D (P 1 "1" 1) == ("2.0", .gt)
#guard D (P 1 "1" 20 .Up) == ("1.644936", .gt)

-- `n = 0`: the digamma function
#guard D (P 0 "1" 53) == ("-0.5772156649015329", .lt)
#guard D (P 0 "-0.5" 53) == ("0.03648997397857652", .lt)
#guard polygammaPrecRound 0 (X "3.25" 53) 80 .Floor == digammaPrecRound (X "3.25" 53) 80 .Floor

-- `trigamma`, `polygamma`
#guard trigammaPrecRound (X "0.5" 53) 53 .Up == polygammaPrecRound 1 (X "0.5" 53) 53 .Up
#guard toString (trigamma (X "1" 53)) == "1.6449340668482264"
#guard toString (polygamma 2 (X "1" 53)) == "-2.4041138063191885"

-- the fuel as an argument; for an odd `n` no fuel is needed at the positive integers and the
-- half-integers, where the value is irrational (`ψ′(1) = π²/6`, `ψ′(1/2) = π²/2`)
#guard D (polygammaPrecRoundFuel 0 1 (X "1" 53) 53 .Nearest) == ("1.6449340668482264", .lt)
#guard D (polygammaPrecRoundFuel 0 1 (X "0.5" 53) 53 .Nearest) == ("4.934802200544679", .lt)
#guard D (polygammaPrecRoundFuel 0 3 (X "-2.5" 53) 53 .Nearest) == ("194.74787621918762", .lt)
#guard D (polygammaPrecRoundFuel 0 1 (X "7" 53) 53 .Nearest) == ("0.15354517795933756", .gt)
#guard D (polygammaPrecRoundFuel 3 2 (X "1" 53) 53 .Nearest) == ("-2.4041138063191885", .gt)
#guard D (polygammaPrecRoundFuel 3 1 (X "0.3" 53) 53 .Nearest) == ("12.245364546107732", .gt)
#guard polygammaPrecRoundFuel (lnGammaFuel 53) 2 (X "0.3" 53) 53 .Nearest == P 2 "0.3" 53
