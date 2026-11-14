/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosPi
import Azurite.AzFloat.TanPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tanPi` and `tanPiRat`

IEEE 754 `tanPi` (without signed zeros): `0` at the integers; at the half-integers `n + 1/2` the
poles, `+∞` for even `n` and `−∞` for odd `n` (so `tanPi (1/2) = +∞`, `tanPi (3/2) = −∞`,
`tanPi (−1/2) = −∞`, `tanPi (−3/2) = +∞`), also for huge arguments; `±1` at the odd quarters;
correctly rounded values against the quotient of `sinPi` and `cosPi` computed with 300 extra
bits.  The rational variant: the same exact values and poles, and the agreement with the float
variant.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := tanPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) := tanPiRatPrecRound (Q q) p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  let sc := sinCosPiPrecRound x (p + 300) .Nearest
  T x p m == divPrecRound sc.1.1 sc.2.1 p m
private def agreesRat (q : String) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  let sc := sinCosPiRatPrecRound (Q q) (p + 300) .Nearest
  R q p m == divPrecRound sc.1.1 sc.2.1 p m

-- floats: special values
#guard T nan 53 == (nan, .eq)
#guard T (infinity true) 53 == (nan, .eq)
#guard T (infinity false) 53 == (nan, .eq)
#guard T zero 53 == (zero, .eq)
#guard T zero 0 == (zero, .eq)
#guard T (F "1" 53) 0 == (nan, .eq)

-- floats: zeros, poles (IEEE 754 signs) and `±1`
#guard T (F "1" 53) 53 == (zero, .eq)
#guard T (F "-3" 53) 53 == (zero, .eq)
#guard T (F "100000000000000000000" 80) 53 == (zero, .eq)
#guard T (F "1/2" 53) 53 == (infinity true, .eq)
#guard T (F "3/2" 53) 53 == (infinity false, .eq)
#guard T (F "5/2" 53) 53 == (infinity true, .eq)
#guard T (F "-1/2" 53) 53 == (infinity false, .eq)
#guard T (F "-3/2" 53) 53 == (infinity true, .eq)
#guard T (F "200000000000000000001/2" 80) 53 == (infinity true, .eq)
#guard T (F "200000000000000000003/2" 80) 53 == (infinity false, .eq)
#guard T (F "1/4" 53) 53 == (F "1" 53, .eq)
#guard T (F "3/4" 53) 53 == (F "-1" 53, .eq)
#guard T (F "-1/4" 53) 53 == (F "-1" 53, .eq)
#guard T (F "5/4" 53) 53 == (F "1" 53, .eq)
#guard tanPi (F "1/2" 53) == infinity true

-- floats: correctly rounded values
#guard (List.range 64).all fun i => (i + 1) % 4 == 0 || agrees (F s!"{i + 1}/16" 53) 53
#guard (List.range 64).all fun i => (i + 1) % 4 == 0 || agrees (F s!"-{i + 1}/16" 53) 53 .Floor
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (F "1/1024" 53) 53
#guard agrees (F "800000000000000000001/8" 80) 53
#guard agrees (F "1/3" 2000) 2000
#guard agrees ((F "3" 53) <<< AzInt.ofInt (-200)) 53

-- rationals
#guard R "0" 53 == (zero, .eq)
#guard R "0" 0 == (zero, .eq)
#guard R "1/7" 0 == (nan, .eq)
#guard R "7" 53 == (zero, .eq)
#guard R "1/2" 53 == (infinity true, .eq)
#guard R "-7/2" 53 == (infinity true, .eq)
#guard R "7/2" 53 == (infinity false, .eq)
#guard R "1/4" 53 == (F "1" 53, .eq)
#guard R "-5/4" 53 == (F "-1" 53, .eq)
#guard (List.range 28).all fun i => agreesRat s!"{i + 1}/7" 53
#guard (List.range 30).all fun i => agreesRat s!"-{2 * i + 1}/12" 53 .Floor
#guard agreesRat "12345678901234567890123456789/1000000007" 300
#guard R "1/8" 53 == T (F "1/8" 53) 53
#guard tanPiRat (Q "1/3") 53 == (R "1/3" 53).1
