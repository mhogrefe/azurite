/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinCosPi` and `sinCosPiRat`

Floats: the special values, the exact values at the integers and half-integers (also for huge
arguments), `1/4` (`sin = cos = √2/2`), `1/1024`, a huge argument with a fractional part, and
the agreement with `sinPiPrecRound` and `cosPiPrecRound` over the sixteenths of two periods,
both signs, several modes and precisions.  Rationals: the special values, the exact values at
the halves, thirds and sixths, and the agreement with `sinPiRatPrecRound` and
`cosPiRatPrecRound` over the sevenths and twelfths, and with the float function at a
representable argument.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def SC (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinCosPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinCosPiRatPrecRound (Q q) p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosPiPrecRound x p m == (sinPiPrecRound x p m, cosPiPrecRound x p m)
private def agreesRat (q : String) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosPiRatPrecRound (Q q) p m == (sinPiRatPrecRound (Q q) p m, cosPiRatPrecRound (Q q) p m)

-- floats: special and exact values
#guard SC nan 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity true) 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity false) 53 == ((nan, .eq), (nan, .eq))
#guard SC zero 53 == ((zero, .eq), (F "1" 53, .eq))
#guard SC zero 0 == ((zero, .eq), (nan, .eq))
#guard SC (F "1" 53) 0 == ((nan, .eq), (nan, .eq))
#guard SC (F "1" 53) 53 == ((zero, .eq), (F "-1" 53, .eq))
#guard SC (F "2" 53) 53 == ((zero, .eq), (F "1" 53, .eq))
#guard SC (F "-3" 53) 53 == ((zero, .eq), (F "-1" 53, .eq))
#guard SC (F "1/2" 53) 53 == ((F "1" 53, .eq), (zero, .eq))
#guard SC (F "-1/2" 53) 53 == ((F "-1" 53, .eq), (zero, .eq))
#guard SC (F "3/2" 53) 53 == ((F "-1" 53, .eq), (zero, .eq))
#guard SC (F "100000000000000000000" 80) 53 == ((zero, .eq), (F "1" 53, .eq))
#guard SC (F "200000000000000000003/2" 80) 53 == ((F "-1" 53, .eq), (zero, .eq))

-- floats: correctly rounded values
#guard (SC (F "1/4" 53) 53).1 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard (SC (F "1/4" 53) 53).1 == (SC (F "1/4" 53) 53).2
#guard (SC (F "1/1024" 53) 53).1 == (F "3537113327227485/1152921504606846976" 53, .lt)
#guard (SC (F "800000000000000000001/8" 80) 53).1
  == (F "6893811853601123/18014398509481984" 53, .gt)
#guard sinCosPi (F "1/4" 53) == (sinPi (F "1/4" 53), cosPi (F "1/4" 53))

-- floats: agreement with the separate functions
#guard (List.range 65).all fun i => agrees (F s!"{i}/16" 53) 53
#guard (List.range 64).all fun i => agrees (F s!"-{i + 1}/16" 53) 53 .Floor
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 40).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 40 .Down
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (F "1/3" 2000) 2000
#guard agrees ((F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) 53
#guard agrees ((F "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 53

-- rationals: special and exact values
#guard R "0" 53 == ((zero, .eq), (F "1" 53, .eq))
#guard R "0" 0 == ((zero, .eq), (nan, .eq))
#guard R "1/7" 0 == ((nan, .eq), (nan, .eq))
#guard R "1/2" 53 == ((F "1" 53, .eq), (zero, .eq))
#guard R "-7/2" 53 == ((F "1" 53, .eq), (zero, .eq))
#guard (R "1/6" 53).1 == (F "1/2" 53, .eq)
#guard (R "-5/6" 53).1 == (F "-1/2" 53, .eq)
#guard (R "1/3" 53).2 == (F "1/2" 53, .eq)
#guard (R "2/3" 53).2 == (F "-1/2" 53, .eq)

-- rationals: agreement with the separate functions and with the float function
#guard (List.range 29).all fun i => agreesRat s!"{i}/7" 53
#guard (List.range 49).all fun i => agreesRat s!"-{i + 1}/12" 53 .Floor
#guard (List.range 30).all fun i => agreesRat s!"{2 * i + 1}/11" 100 .Ceiling
#guard agreesRat "12345678901234567890123456789/1000000007" 300
#guard agreesRat "1/1267650600228229401496703205376" 20
#guard R "1/4" 53 == SC (F "1/4" 53) 53
#guard sinCosPiRat (Q "1/7") 53 == (sinPiRat (Q "1/7") 53, cosPiRat (Q "1/7") 53)
