/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Rsqrt
import Azurite.AzFloat.Shift
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.SqrtRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the square root and reciprocal square root of a rational

Expected values computed by hand or from independent decimal expansions, shown as the decimal
output of the result, and agreement with the float square root and reciprocal square root on
rationals that are exactly representable.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrtRatPrecRound (Q s) p m

private def RS (s : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  rsqrtRatPrecRound (Q s) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Exact results -/

#guard D (R "1" 1) == ("1.0", .eq)
#guard D (R "4" 3) == ("2.0", .eq)
#guard D (R "9/4" 2) == ("1.5", .eq)
#guard D (R "1/4" 1) == ("0.5", .eq)
#guard D (R "1/9" 1) == ("0.2", .lt)  -- 1/3 → 1/4
#guard D (R "25/16" 3) == ("1.2", .eq)
#guard D (R "1/1024" 1) == ("0.03", .eq)
#guard D (R "1267650600228229401496703205376" 1) == ("1.0e15", .eq)  -- 2^100

/-! ## Inexact results -/

#guard D (R "2" 2) == ("1.5", .gt)  -- √2 → 1.5
#guard D (R "2" 2 .Floor) == ("1.0", .lt)
#guard D (R "2" 2 .Ceiling) == ("1.5", .gt)
#guard D (R "2" 53) == ("1.4142135623730951", .gt)
#guard D (R "1/2" 53) == ("0.7071067811865476", .gt)  -- √2 / 2
#guard D (R "1/3" 3) == ("0.6", .gt)  -- 0.577… → 0.625
#guard D (R "1/3" 3 .Floor) == ("0.5", .lt)
#guard D (R "1/3" 3 .Up) == ("0.6", .gt)
#guard D (R "2535301200456458802993406410752" 1) == ("1.0e15", .lt)  -- √2 · 2^50
#guard D (R "2535301200456458802993406410752" 1 .Ceiling) == ("2.0e15", .gt)
#guard D (R "9/4" 1) == ("2.0", .gt)  -- tie 1.5 → 2
#guard D (R "25/4" 2) == ("2.0", .lt)  -- tie 2.5 → 2
#guard toString (R "1/10" 53).1 == "0.31622776601683794"
#guard toString (R "10" 53).1 == "3.1622776601683795"
#guard toString (R "3/7" 53).1 == "0.6546536707079772"

/-! ## Special values -/

#guard D (R "0" 3) == ("0.0", .eq)
#guard D (R "-1" 3) == ("NaN", .eq)
#guard D (R "-1/4" 3) == ("NaN", .eq)

/-! ## Agreement with the float square root -/

private def agrees (s : String) (p : Nat) (m : RoundingMode) : Bool :=
  sqrtRatPrecRound (Q s) p m == sqrtPrecRound (F s 64) p m

#guard [("2", 1), ("2", 7), ("3", 20), ("5/4", 10), ("7/32", 33), ("3/4096", 5), ("123456789", 40),
    ("987654321/65536", 61)].all fun (s, p) =>
  [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m => agrees s p m

/-! ## Reciprocal square root -/

#guard D (RS "1" 1) == ("1.0", .eq)
#guard D (RS "4" 1) == ("0.5", .eq)
#guard D (RS "4" 5) == ("0.5", .eq)
#guard D (RS "1/4" 2) == ("2.0", .eq)
#guard D (RS "16" 3) == ("0.25", .eq)
#guard D (RS "9/4" 2) == ("0.8", .gt)  -- 0.667 → 0.75
#guard D (RS "2" 53) == ("0.7071067811865476", .gt)  -- 1/√2
#guard D (RS "1/2" 53) == ("1.4142135623730951", .gt)  -- √2
#guard D (RS "2" 1) == ("0.5", .lt)  -- 0.707 → 1/2
#guard D (RS "2" 1 .Up) == ("1.0", .gt)
#guard D (RS "5" 4) == ("0.44", .lt)  -- 0.447 → 0.4375
#guard D (RS "8" 3) == ("0.4", .gt)  -- 0.354 → 0.375
#guard D (RS "3" 2) == ("0.5", .lt)  -- 0.577 → 0.5
#guard D (RS "3" 2 .Ceiling) == ("0.8", .gt)
#guard D (RS "1267650600228229401496703205376" 1) == ("9.0e-16", .eq)  -- 2^100
#guard D (RS "2535301200456458802993406410752" 1) == ("4.0e-16", .lt)  -- 2^101
#guard toString (RS "1/10" 53).1 == "3.1622776601683795"
#guard toString (RS "10" 53).1 == "0.31622776601683794"
#guard toString (RS "3/7" 53).1 == "1.5275252316519468"
#guard D (RS "0" 3) == ("Infinity", .eq)
#guard D (RS "-1" 3) == ("NaN", .eq)
#guard D (RS "-1/4" 3) == ("NaN", .eq)

private def agreesRsqrt (s : String) (p : Nat) (m : RoundingMode) : Bool :=
  rsqrtRatPrecRound (Q s) p m == rsqrtPrecRound (F s 64) p m

#guard [("2", 1), ("2", 7), ("3", 20), ("5/4", 10), ("7/32", 33), ("3/4096", 5), ("123456789", 40),
    ("987654321/65536", 61), ("1/1024", 3)].all fun (s, p) =>
  [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m => agreesRsqrt s p m
