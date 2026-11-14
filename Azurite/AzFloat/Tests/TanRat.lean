/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosRat
import Azurite.AzFloat.Tan
import Azurite.AzFloat.TanRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tanRat`

The special values (`q = 0`, `p = 0`), the agreement with the float `tan` at representable
arguments, `tan (1/3)` to 59 digits (reference: the Taylor series of `sin` and `cos` in exact
rational arithmetic), `tan (22/7)` and `tan (355/113)` (small results), `tan (11/7)`
(next to the pole `π/2`: `≈ −1.6·10³`), oddness, the directed modes, and a sweep over all the
octants, both signs, several modes and precisions against the correctly rounded quotient of
`sin q` and `cos q` computed with 300 extra bits; a 50-digit denominator; tiny rationals (the
tiny path) and a small one on the ordinary path.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) := tanRatPrecRound (Q q) p m
/-- The reference: the quotient of `sin q` and `cos q` at `p + 300` bits, rounded to `p`. -/
private def ref (q : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  let sc := sinCosRatPrecRound (Q q) (p + 300) .Nearest
  divPrecRound sc.1.1 sc.2.1 p m
private def agrees (q : String) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  T q p m == ref q p m

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- agreement with the float `tan` at representable arguments
#guard T "1/2" 53 == tanPrecRound (F "1/2" 53) 53 .Nearest
#guard T "-3" 53 == tanPrecRound (F "-3" 53) 53 .Nearest
#guard T "1000000000000" 53 == tanPrecRound (F "1000000000000" 53) 53 .Nearest
#guard T "1/1024" 53 == tanPrecRound (F "1/1024" 53) 53 .Nearest
#guard T "1" 200 == tanPrecRound (F "1" 53) 200 .Nearest

-- values
#guard (toString (tanRat (Q "1/3") 200)).startsWith
  "0.34625354951057549103854356560974077459570391618980021797644"
#guard agrees "1/3" 200
#guard agrees "22/7" 53
#guard agrees "355/113" 53
#guard agrees "11/7" 53
#guard (T "11/7" 53).1.isNegative
#guard (T "-1/3" 53 .Floor).1 == -(T "1/3" 53 .Ceiling).1
#guard (T "1/3" 53 .Floor).2 == .lt
#guard (T "1/3" 53 .Ceiling).2 == .gt
#guard agrees "1/3" 20

-- a sweep against the quotient of `sin` and `cos`
#guard (List.range 26).all fun i => agrees s!"{i + 1}/4" 53
#guard (List.range 26).all fun i => agrees s!"-{i + 1}/4" 53 .Floor
#guard (List.range 13).all fun i => agrees s!"{2 * i + 1}/7" 53 .Ceiling
#guard (List.range 13).all fun i => agrees s!"-{2 * i + 1}/3" 40 .Down
#guard (List.range 13).all fun i => agrees s!"{2 * i + 1}/5" 100 .Up
#guard agrees "1/3" 1
#guard agrees "12345678901234567890/1000000007" 300
#guard agrees "1/3" 2000
#guard agrees ("314159265358979323846264338327950288419716939937510/"
  ++ "100000000000000000000000000000000000000000000000001") 64
#guard agrees "1000000000000000000000000000000" 53

-- tiny rationals (the tiny path) and a small one on the ordinary path
#guard T "1/1267650600228229401496703205376" 20 == (F "1/1267650600228229401496703205376" 20, .lt)
#guard T "-1/1267650600228229401496703205376" 20
  == (F "-1/1267650600228229401496703205376" 20, .gt)
#guard (T "1/3802951800684688204490109616128" 20 .Ceiling).2 == .gt
#guard agrees "1/1099511627776" 53
