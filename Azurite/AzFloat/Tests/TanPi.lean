/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := tanPiPrecRound x p m
private def R (q : String) (p : Nat) (m : RoundingMode := .Nearest) := tanPiRatPrecRound (Q q) p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  let sc := sinCosPiPrecRound x (p + 300) .Nearest
  T x p m == divPrecRound sc.1.1 sc.2.1 p m
private def agreesRat (q : String) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  let sc := sinCosPiRatPrecRound (Q q) (p + 300) .Nearest
  R q p m == divPrecRound sc.1.1 sc.2.1 p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- floats: special values
#guard D (T nan 53) == ("NaN", .eq)
#guard D (T (infinity true) 53) == ("NaN", .eq)
#guard D (T (infinity false) 53) == ("NaN", .eq)
#guard D (T zero 53) == ("0.0", .eq)
#guard D (T zero 0) == ("0.0", .eq)
#guard D (T (X "1" 53) 0) == ("NaN", .eq)

-- floats: zeros, poles (IEEE 754 signs) and `±1`
#guard D (T (X "1" 53) 53) == ("0.0", .eq)
#guard D (T (X "-3" 53) 53) == ("0.0", .eq)
#guard D (T (X "100000000000000000000" 80) 53) == ("0.0", .eq)
#guard D (T (X "0.5" 53) 53) == ("Infinity", .eq)
#guard D (T (X "1.5" 53) 53) == ("-Infinity", .eq)
#guard D (T (X "2.5" 53) 53) == ("Infinity", .eq)
#guard D (T (X "-0.5" 53) 53) == ("-Infinity", .eq)
#guard D (T (X "-1.5" 53) 53) == ("Infinity", .eq)
#guard D (T (X "100000000000000000000.5" 80) 53) == ("Infinity", .eq)
#guard D (T (X "100000000000000000001.5" 80) 53) == ("-Infinity", .eq)
#guard D (T (X "0.25" 53) 53) == ("1.0", .eq)
#guard D (T (X "0.75" 53) 53) == ("-1.0", .eq)
#guard D (T (X "-0.25" 53) 53) == ("-1.0", .eq)
#guard D (T (X "1.25" 53) 53) == ("1.0", .eq)
#guard toString (tanPi (X "0.5" 53)) == "Infinity"

-- floats: correctly rounded values
#guard (List.range 64).all fun i => (i + 1) % 4 == 0 || agrees (F s!"{i + 1}/16" 53) 53
#guard (List.range 64).all fun i => (i + 1) % 4 == 0 || agrees (F s!"-{i + 1}/16" 53) 53 .Floor
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 40).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (X "0.0009765625" 53) 53
#guard agrees (X "100000000000000000000.125" 80) 53
#guard agrees (X "0.3333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333335" 2000) 2000
#guard agrees ((X "3" 53) <<< AzInt.ofInt (-200)) 53

-- rationals
#guard D (R "0" 53) == ("0.0", .eq)
#guard D (R "0" 0) == ("0.0", .eq)
#guard D (R "1/7" 0) == ("NaN", .eq)
#guard D (R "7" 53) == ("0.0", .eq)
#guard D (R "1/2" 53) == ("Infinity", .eq)
#guard D (R "-7/2" 53) == ("Infinity", .eq)
#guard D (R "7/2" 53) == ("-Infinity", .eq)
#guard D (R "1/4" 53) == ("1.0", .eq)
#guard D (R "-5/4" 53) == ("-1.0", .eq)
#guard (List.range 28).all fun i => agreesRat s!"{i + 1}/7" 53
#guard (List.range 30).all fun i => agreesRat s!"-{2 * i + 1}/12" 53 .Floor
#guard agreesRat "12345678901234567890123456789/1000000007" 300
#guard R "1/8" 53 == T (X "0.125" 53) 53
#guard tanPiRat (Q "1/3") 53 == (R "1/3" 53).1
