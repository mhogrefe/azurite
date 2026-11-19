/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.FallingFactorial
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzRat.Instances

/-!
# Tests for the falling factorial

Float and rational arguments.  The special values (`NaN`, `n = 0`, the infinities, the exact
zeros where a factor vanishes — `x` an integer with `0 ≤ x < n` —, `p = 0`), small values
(`5·4·3 = 60`, `(1/2)(−1/2)(−3/2) = 3/8`, the falling factorial of `n` of length `n` is
`n!`), even and odd `n` in the directed modes, the loop against the product in exact
rational arithmetic, the reflection `x (x − 1) ⋯ (x − n + 1) = (x − n + 1)ₙ`, and agreement
of the two functions on dyadic arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : String) (n p : Nat) (m : RoundingMode := .Nearest) :=
  fallingFactorialPrecRound (X x 53) n p m
private def R (q : String) (n p : Nat) (m : RoundingMode := .Nearest) :=
  fallingFactorialRatPrecRound (Q q) n p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (fallingFactorialPrecRound nan 3 53 .Nearest) == ("NaN", .eq)
#guard D (fallingFactorialPrecRound nan 0 53 .Nearest) == ("NaN", .eq)
#guard D (P "2.5" 0 53) == ("1.0", .eq)
#guard D (P "0" 0 53) == ("1.0", .eq)
#guard D (P "2.5" 0 0) == ("NaN", .eq)
#guard D (fallingFactorialPrecRound (infinity true) 0 53 .Nearest) == ("1.0", .eq)
#guard D (fallingFactorialPrecRound (infinity true) 3 53 .Nearest) == ("Infinity", .eq)
#guard D (fallingFactorialPrecRound (infinity true) 4 53 .Nearest) == ("Infinity", .eq)
#guard D (fallingFactorialPrecRound (infinity false) 3 53 .Nearest) == ("-Infinity", .eq)
#guard D (fallingFactorialPrecRound (infinity false) 4 53 .Nearest) == ("Infinity", .eq)
#guard D (P "0" 1 53) == ("0.0", .eq)
#guard D (P "0" 5 0) == ("0.0", .eq)
#guard D (P "2" 3 53) == ("0.0", .eq)
#guard D (P "5" 6 53) == ("0.0", .eq)
#guard D (P "5" 1000001 53) == ("0.0", .eq)
#guard D (P "5" 5 0) == ("NaN", .eq)
#guard D (R "1/3" 0 53) == ("1.0", .eq)
#guard D (R "1/3" 0 0) == ("NaN", .eq)
#guard D (R "0" 1 53) == ("0.0", .eq)
#guard D (R "5" 6 53) == ("0.0", .eq)
#guard D (R "5" 7 0) == ("0.0", .eq)
#guard D (R "1/3" 5 0) == ("NaN", .eq)

-- float arguments
#guard D (P "5" 3 53) == ("6.0e1", .eq)
#guard D (P "5" 5 53) == ("1.2e2", .eq)
#guard D (P "0.5" 3 53) == ("0.375", .eq)
#guard D (P "-0.5" 2 53) == ("0.75", .eq)
#guard D (P "-0.5" 3 53) == ("-1.875", .eq)
#guard D (P "2.5" 4 53) == ("-0.9375", .eq)
#guard D (P "0.1" 4 53) == ("-0.4959", .gt)
#guard D (P "0.1" 4 53 .Floor) == ("-0.49590000000000006", .lt)
#guard D (P "0.1" 5 53 .Floor) == ("1.93401", .lt)
#guard D (P "0.1" 5 53 .Ceiling) == ("1.9340100000000002", .gt)
#guard D (P "30" 30 53) == ("2.6525285981219107e32", .gt)
#guard D (P "30" 30 53 .Floor) == ("2.6525285981219103e32", .lt)
#guard D (P "100.5" 200 53) == ("-2.793281378035082e313", .gt)
#guard D (P "100.5" 201 53) == ("2.7793149711449067e315", .gt)
#guard D (P "100.5" 201 53 .Up) == ("2.7793149711449067e315", .gt)
#guard D (P "-0.5" 1001 53) == ("-7.18177991287379e2568", .gt)
#guard D (P "1e30" 3 53) == ("1.0000000000000001e90", .gt)
#guard D (P "-1e30" 3 53) == ("-1.0000000000000001e90", .lt)
#guard D (P "500.5" 1000 200 .Floor)
  == ("-9.49180123673100634166934080777157381304961500914509462242095e2264", .lt)

-- rational arguments
#guard D (R "5" 3 53) == ("6.0e1", .eq)
#guard D (R "1/3" 3 53) == ("0.37037037037037035", .lt)
#guard D (R "1/3" 3 53 .Floor) == ("0.37037037037037035", .lt)
#guard D (R "1/3" 4 53 .Floor) == ("-0.9876543209876544", .lt)
#guard D (R "-7/3" 3 53) == ("-33.7037037037037", .gt)
#guard D (R "22/7" 10 53) == ("548.7501639479925", .gt)
#guard D (R "301/3" 200 53) == ("-2.411672218035846e313", .lt)
#guard D (R "301/3" 201 53 .Down) == ("2.403633310642393e315", .lt)
#guard D (R "1/3" 1001 53) == ("9.904173130862144e2565", .gt)
#guard D (R "1/3" 300 200)
  == ("-3.75421339994390296380713114971058081533869976738699109958246e610", .gt)

-- against the product in exact rational arithmetic (the loop from `n = 1000`)
private def exact (q : String) (n p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  ofAzRatRound ((List.range n).foldl (fun acc j => acc * (Q q - Q (toString j))) (Q "1")) p m
#guard R "1/3" 200 53 == exact "1/3" 200 53 .Nearest
#guard R "1/3" 201 53 .Floor == exact "1/3" 201 53 .Floor
#guard R "301/3" 201 53 .Ceiling == exact "301/3" 201 53 .Ceiling
#guard R "1/3" 1000 53 .Up == exact "1/3" 1000 53 .Up
#guard R "1/3" 1001 53 .Floor == exact "1/3" 1001 53 .Floor
#guard R "1001/3" 1001 53 .Ceiling == exact "1001/3" 1001 53 .Ceiling
#guard R "4001/3" 1001 53 .Down == exact "4001/3" 1001 53 .Down
#guard P "500.5" 1001 53 .Floor == exact "1001/2" 1001 53 .Floor
#guard P "-0.5" 1001 53 .Up == exact "-1/2" 1001 53 .Up

-- the reflection: the falling factorial at `x` is Pochhammer's symbol at `x − n + 1`
#guard P "100.5" 200 53 == pochhammerPrecRound (X "-98.5" 53) 200 53 .Nearest
#guard P "100.5" 201 53 .Floor == pochhammerPrecRound (X "-99.5" 53) 201 53 .Floor
#guard R "301/3" 201 53 .Up == pochhammerRatPrecRound (Q "-299/3") 201 53 .Up

-- agreement of the two functions on dyadic arguments
#guard P "0.5" 3 53 == R "1/2" 3 53
#guard P "100.5" 201 53 .Floor == R "201/2" 201 53 .Floor

-- the wrappers
#guard toString (fallingFactorial (X "5" 53) 3) == "6.0e1"
#guard toString (fallingFactorialRat (Q "1/2") 3 53) == "0.375"
