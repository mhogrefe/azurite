/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def SC (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinCosPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinCosPiRatPrecRound (Q q) p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosPiPrecRound x p m == (sinPiPrecRound x p m, cosPiPrecRound x p m)
private def agreesRat (q : String) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosPiRatPrecRound (Q q) p m == (sinPiRatPrecRound (Q q) p m, cosPiRatPrecRound (Q q) p m)
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- floats: special and exact values
#guard SC nan 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity true) 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity false) 53 == ((nan, .eq), (nan, .eq))
#guard SC zero 53 == ((zero, .eq), (X "1" 53, .eq))
#guard SC zero 0 == ((zero, .eq), (nan, .eq))
#guard SC (X "1" 53) 0 == ((nan, .eq), (nan, .eq))
#guard SC (X "1" 53) 53 == ((zero, .eq), (X "-1" 53, .eq))
#guard SC (X "2" 53) 53 == ((zero, .eq), (X "1" 53, .eq))
#guard SC (X "-3" 53) 53 == ((zero, .eq), (X "-1" 53, .eq))
#guard SC (X "0.5" 53) 53 == ((X "1" 53, .eq), (zero, .eq))
#guard SC (X "-0.5" 53) 53 == ((X "-1" 53, .eq), (zero, .eq))
#guard SC (X "1.5" 53) 53 == ((X "-1" 53, .eq), (zero, .eq))
#guard SC (X "100000000000000000000" 80) 53 == ((zero, .eq), (X "1" 53, .eq))
#guard SC (X "100000000000000000001.5" 80) 53 == ((X "-1" 53, .eq), (zero, .eq))

-- floats: correctly rounded values
#guard D ((SC (X "0.25" 53) 53).1) == ("0.7071067811865476", .gt)
#guard (SC (X "0.25" 53) 53).1 == (SC (X "0.25" 53) 53).2
#guard D ((SC (X "0.0009765625" 53) 53).1) == ("0.003067956762965976", .lt)
#guard D ((SC (X "100000000000000000000.125" 80) 53).1) == ("0.3826834323650898", .gt)
#guard sinCosPi (X "0.25" 53) == (sinPi (X "0.25" 53), cosPi (X "0.25" 53))

-- floats: agreement with the separate functions
#guard (List.range 65).all fun i => agrees (F s!"{i}/16" 53) 53
#guard (List.range 64).all fun i => agrees (F s!"-{i + 1}/16" 53) 53 .Floor
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 40).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 40 .Down
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (X "0.3333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333335" 2000) 2000
#guard agrees ((X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) 53
#guard agrees ((X "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 53

-- rationals: special and exact values
#guard R "0" 53 == ((zero, .eq), (X "1" 53, .eq))
#guard R "0" 0 == ((zero, .eq), (nan, .eq))
#guard R "1/7" 0 == ((nan, .eq), (nan, .eq))
#guard R "1/2" 53 == ((X "1" 53, .eq), (zero, .eq))
#guard R "-7/2" 53 == ((X "1" 53, .eq), (zero, .eq))
#guard D ((R "1/6" 53).1) == ("0.5", .eq)
#guard D ((R "-5/6" 53).1) == ("-0.5", .eq)
#guard D ((R "1/3" 53).2) == ("0.5", .eq)
#guard D ((R "2/3" 53).2) == ("-0.5", .eq)

-- rationals: agreement with the separate functions and with the float function
#guard (List.range 29).all fun i => agreesRat s!"{i}/7" 53
#guard (List.range 49).all fun i => agreesRat s!"-{i + 1}/12" 53 .Floor
#guard (List.range 30).all fun i => agreesRat s!"{2 * i + 1}/11" 100 .Ceiling
#guard agreesRat "12345678901234567890123456789/1000000007" 300
#guard agreesRat "1/1267650600228229401496703205376" 20
#guard R "1/4" 53 == SC (X "0.25" 53) 53
#guard sinCosPiRat (Q "1/7") 53 == (sinPiRat (Q "1/7") 53, cosPiRat (Q "1/7") 53)
