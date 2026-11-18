/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 2000 bits. -/
private def third2000 : AzFloat :=
  X "0.333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333335" 2000
private def T (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  tanWithPeriodPrecRound x u p m
/-- The reference: the quotient of the sine and the cosine at `p + 300` bits, rounded to `p`. -/
private def ref (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  let sc := sinCosWithPeriodPrecRound x u (p + 300) .Nearest
  divPrecRound sc.1.1 sc.2.1 p m
private def agrees (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  T x u p m == ref x u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T (X "1" 53) 0 53) == ("NaN", .eq)
#guard D (T nan 360 53) == ("NaN", .eq)
#guard D (T (infinity true) 360 53) == ("NaN", .eq)
#guard D (T zero 360 53) == ("0.0", .eq)
#guard D (T zero 360 0) == ("0.0", .eq)
#guard D (T (X "1" 53) 360 0) == ("NaN", .eq)

-- exact values
#guard D (T (X "180" 53) 360 53) == ("0.0", .eq)
#guard D (T (X "360" 53) 360 53) == ("0.0", .eq)
#guard D (T (X "-540" 53) 360 53) == ("0.0", .eq)
#guard D (T (X "45" 53) 360 53) == ("1.0", .eq)
#guard D (T (X "135" 53) 360 53) == ("-1.0", .eq)
#guard D (T (X "225" 53) 360 53) == ("1.0", .eq)
#guard D (T (X "315" 53) 360 53) == ("-1.0", .eq)
#guard D (T (X "-45" 53) 360 53) == ("-1.0", .eq)
#guard D (T (X "-135" 53) 360 53) == ("1.0", .eq)
#guard D (T (X "45" 53) 360 1 .Floor) == ("1.0", .eq)

-- the poles, with the signs of IEEE 754 `tanPi`
#guard D (T (X "90" 53) 360 53) == ("Infinity", .eq)
#guard D (T (X "270" 53) 360 53) == ("-Infinity", .eq)
#guard D (T (X "450" 53) 360 53) == ("Infinity", .eq)
#guard D (T (X "-90" 53) 360 53) == ("-Infinity", .eq)
#guard D (T (X "-270" 53) 360 53) == ("Infinity", .eq)
#guard D (T (X "0.25" 53) 1 53 .Floor) == ("Infinity", .eq)
#guard D (T (X "0.75" 53) 1 53 .Ceiling) == ("-Infinity", .eq)

-- a sweep against the quotient of `sin` and `cos` (the degrees that are not multiples of `45`)
#guard (List.range 721).all fun i => i % 45 == 0 || agrees (X s!"{i}" 53) 360 53
#guard (List.range 400).all fun i =>
  (i + 1) % 45 == 0 || agrees (X s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agrees (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 3 40 .Down
#guard (List.range 60).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agrees (X "1" 53) 360 1
#guard agrees (X "1" 53) 18446744073709551615 53
#guard agrees (X "12345678814.81481618629628669593" 100) 360 300
#guard agrees third2000 360 2000
#guard toString (tanWithPeriod (X "1" 200) 360) == "0.017455064928217585765128895219727824314101588\
  83987527690471143"

-- next to a pole: one ulp below and above `90°` at 53 bits
#guard agrees (X "89.99999999999999" 53) 360 53
#guard agrees (X "90.00000000000001" 53) 360 53
#guard (T (X "90.00000000000001" 53) 360 53).1.isNegative

-- a tiny argument (the tiny path) and a huge one
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard (T tinyX 360 53).2 == .lt || (T tinyX 360 53).2 == .gt
#guard T (-tinyX) 360 53 == (-(T tinyX 360 53 ).1, (T tinyX 360 53).2.swap)
#guard agrees ((X "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Floor
#guard agrees ((X "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53
