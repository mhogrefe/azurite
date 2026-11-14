/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosRatWithPeriod
import Azurite.AzFloat.TanRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tanRatWithPeriod`

The special values (`u = 0`, `q = 0`, `p = 0`), the exact values (`0`, `±1`), the poles with the
IEEE 754 signs, the agreement with the float function at a representable argument, and a sweep
over every third of a degree of a turn that is not exceptional, both signs, against the
correctly rounded quotient of `sin` and `cos` computed with 300 extra bits; other periods,
modes and precisions; huge and tiny rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  tanRatWithPeriodPrecRound (Q q) u p m
private def ref (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  let sc := sinCosRatWithPeriodPrecRound (Q q) u (p + 300) .Nearest
  divPrecRound sc.1.1 sc.2.1 p m
private def agrees (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  T q u p m == ref q u p m

-- special values
#guard T "1/3" 0 53 == (nan, .eq)
#guard T "0" 360 53 == (zero, .eq)
#guard T "0" 360 0 == (zero, .eq)
#guard T "1/3" 360 0 == (nan, .eq)

-- exact values and poles
#guard T "180" 360 53 == (zero, .eq)
#guard T "1/2" 1 53 == (zero, .eq)
#guard T "45" 360 53 == (F "1" 53, .eq)
#guard T "3/8" 1 53 == (F "-1" 53, .eq)
#guard T "-1/8" 1 53 == (F "-1" 53, .eq)
#guard T "-7/8" 1 53 == (F "1" 53, .eq)
#guard T "90" 360 53 == (infinity true, .eq)
#guard T "1/4" 1 53 == (infinity true, .eq)
#guard T "3/4" 1 53 == (infinity false, .eq)
#guard T "-1/4" 1 53 == (infinity false, .eq)
#guard T "-3/4" 1 53 == (infinity true, .eq)
#guard T "5/4" 1 53 == (infinity true, .eq)
#guard T "45/2" 90 53 == (infinity true, .eq)

-- agreement with the float function at a representable argument
#guard T "1/3" 360 200 == tanWithPeriodPrecRound (F "1" 200) 1080 200 .Nearest

-- a sweep against the quotient of `sin` and `cos` (thirds of a degree, not multiples of `45°`)
#guard (List.range 1081).all fun i => i % 135 == 0 || agrees s!"{i}/3" 360 53
#guard (List.range 400).all fun i => agrees s!"-{i + 1}/7" 360 53 .Floor
#guard (List.range 60).all fun i => agrees s!"{i + 1}/11" 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees s!"-{2 * i + 1}/13" 1 40 .Down
#guard (List.range 60).all fun i => agrees s!"{2 * i + 1}/5" 400 100 .Up
#guard agrees "1/7" 360 1
#guard agrees "1/7" 18446744073709551615 53
#guard agrees "12345678901234567890123456789/1000000007" 360 300
#guard agrees "1/7" 360 2000

-- tiny rationals (the tiny path) and a small one on the ordinary path
#guard T "-1/1267650600228229401496703205376" 360 20
  == (-(T "1/1267650600228229401496703205376" 360 20).1,
    (T "1/1267650600228229401496703205376" 360 20).2.swap)
#guard agrees "1/1099511627776" 360 53
