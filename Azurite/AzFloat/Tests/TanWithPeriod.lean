/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosWithPeriod
import Azurite.AzFloat.TanWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tanWithPeriod`

The special values (`u = 0`, `NaN`, `±∞`, zero, `p = 0`), the exact values in degrees (`0` at
the multiples of `180°`, `±1` at the odd multiples of `45°`), the **poles** with the IEEE 754
signs (`+∞` at `90°`, `−∞` at `270°`, mirrored for negative arguments), and every whole degree of
two turns that is not exceptional, both signs, against the correctly rounded quotient of
`sin` and `cos` computed with 300 extra bits; `tan 1°` to 59 digits (reference: Machin's `π` and
the Taylor series in exact rational arithmetic); other periods, modes and precisions; a tiny
argument (the tiny path) and a huge one.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  tanWithPeriodPrecRound x u p m
/-- The reference: the quotient of the sine and the cosine at `p + 300` bits, rounded to `p`. -/
private def ref (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  let sc := sinCosWithPeriodPrecRound x u (p + 300) .Nearest
  divPrecRound sc.1.1 sc.2.1 p m
private def agrees (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  T x u p m == ref x u p m

-- special values
#guard T (F "1" 53) 0 53 == (nan, .eq)
#guard T nan 360 53 == (nan, .eq)
#guard T (infinity true) 360 53 == (nan, .eq)
#guard T zero 360 53 == (zero, .eq)
#guard T zero 360 0 == (zero, .eq)
#guard T (F "1" 53) 360 0 == (nan, .eq)

-- exact values
#guard T (F "180" 53) 360 53 == (zero, .eq)
#guard T (F "360" 53) 360 53 == (zero, .eq)
#guard T (F "-540" 53) 360 53 == (zero, .eq)
#guard T (F "45" 53) 360 53 == (F "1" 53, .eq)
#guard T (F "135" 53) 360 53 == (F "-1" 53, .eq)
#guard T (F "225" 53) 360 53 == (F "1" 53, .eq)
#guard T (F "315" 53) 360 53 == (F "-1" 53, .eq)
#guard T (F "-45" 53) 360 53 == (F "-1" 53, .eq)
#guard T (F "-135" 53) 360 53 == (F "1" 53, .eq)
#guard T (F "45" 53) 360 1 .Floor == (F "1" 1, .eq)

-- the poles, with the signs of IEEE 754 `tanPi`
#guard T (F "90" 53) 360 53 == (infinity true, .eq)
#guard T (F "270" 53) 360 53 == (infinity false, .eq)
#guard T (F "450" 53) 360 53 == (infinity true, .eq)
#guard T (F "-90" 53) 360 53 == (infinity false, .eq)
#guard T (F "-270" 53) 360 53 == (infinity true, .eq)
#guard T (F "1/4" 53) 1 53 .Floor == (infinity true, .eq)
#guard T (F "3/4" 53) 1 53 .Ceiling == (infinity false, .eq)

-- a sweep against the quotient of `sin` and `cos` (the degrees that are not multiples of `45`)
#guard (List.range 721).all fun i => i % 45 == 0 || agrees (F s!"{i}" 53) 360 53
#guard (List.range 400).all fun i =>
  (i + 1) % 45 == 0 || agrees (F s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agrees (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 3 40 .Down
#guard (List.range 60).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agrees (F "1" 53) 360 1
#guard agrees (F "1" 53) 18446744073709551615 53
#guard agrees (F "12345678901234567890/1000000007" 100) 360 300
#guard agrees (F "1/3" 2000) 360 2000
#guard (toString (tanWithPeriod (F "1" 200) 360)).startsWith
  "0.01745506492821758576512889521972782431410158883987527690471"

-- next to a pole: one ulp below and above `90°` at 53 bits
#guard agrees (F "6333186975989759/70368744177664" 53) 360 53
#guard agrees (F "6333186975989761/70368744177664" 53) 360 53
#guard (T (F "6333186975989761/70368744177664" 53) 360 53).1.isNegative

-- a tiny argument (the tiny path) and a huge one
private def tinyX : AzFloat := (F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard (T tinyX 360 53).2 == .lt || (T tinyX 360 53).2 == .gt
#guard T (-tinyX) 360 53 == (-(T tinyX 360 53 ).1, (T tinyX 360 53).2.swap)
#guard agrees ((F "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Floor
#guard agrees ((F "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53
