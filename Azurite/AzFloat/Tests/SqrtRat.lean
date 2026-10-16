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

Expected values computed by hand or from independent decimal expansions, and agreement with the
float square root and reciprocal square root on rationals that are exactly representable.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrtRatPrecRound (Q s) p m

private def RS (s : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  rsqrtRatPrecRound (Q s) p m

/-! ## Exact results -/

#guard (R "1" 1) == (one, .eq)
#guard (R "4" 3) == (F "2" 3, .eq)
#guard (R "9/4" 2) == (F "3/2" 2, .eq)
#guard (R "1/4" 1) == (oneHalf, .eq)
#guard (R "1/9" 1) == (F "1/4" 1, .lt)                                        -- 1/3 → 1/4
#guard (R "25/16" 3) == (F "5/4" 3, .eq)
#guard (R "1/1024" 1) == (one >>> 5, .eq)
#guard (R "1267650600228229401496703205376" 1) == (one <<< 50, .eq)        -- 2^100

/-! ## Inexact results -/

#guard (R "2" 2) == (F "3/2" 2, .gt)                                        -- √2 → 1.5
#guard (R "2" 2 .Floor) == (F "1" 2, .lt)
#guard (R "2" 2 .Ceiling) == (F "3/2" 2, .gt)
#guard (R "2" 53) == (F "6369051672525773/4503599627370496" 53, .gt)
#guard (R "1/2" 53) == (F "6369051672525773/9007199254740992" 53, .gt)      -- √2 / 2
#guard (R "1/3" 3) == (F "5/8" 3, .gt)                                      -- 0.577… → 0.625
#guard (R "1/3" 3 .Floor) == (F "1/2" 3, .lt)
#guard (R "1/3" 3 .Up) == (F "5/8" 3, .gt)
#guard (R "2535301200456458802993406410752" 1) == (one <<< 50, .lt)        -- √2 · 2^50
#guard (R "2535301200456458802993406410752" 1 .Ceiling) == (one <<< 51, .gt)
#guard (R "9/4" 1) == (two, .gt)                                            -- tie 1.5 → 2
#guard (R "25/4" 2) == (F "2" 2, .lt)                                       -- tie 2.5 → 2
#guard toString (R "1/10" 53).1 == "0.31622776601683794"
#guard toString (R "10" 53).1 == "3.1622776601683795"
#guard toString (R "3/7" 53).1 == "0.6546536707079772"

/-! ## Special values -/

#guard (R "0" 3) == (zero, .eq)
#guard (R "-1" 3) == (nan, .eq)
#guard (R "-1/4" 3) == (nan, .eq)

/-! ## Agreement with the float square root -/

private def agrees (s : String) (p : Nat) (m : RoundingMode) : Bool :=
  sqrtRatPrecRound (Q s) p m == sqrtPrecRound (F s 64) p m

#guard [("2", 1), ("2", 7), ("3", 20), ("5/4", 10), ("7/32", 33), ("3/4096", 5), ("123456789", 40),
    ("987654321/65536", 61)].all fun (s, p) =>
  [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m => agrees s p m

/-! ## Reciprocal square root -/

#guard (RS "1" 1) == (one, .eq)
#guard (RS "4" 1) == (oneHalf, .eq)
#guard (RS "4" 5) == (F "1/2" 5, .eq)
#guard (RS "1/4" 2) == (F "2" 2, .eq)
#guard (RS "16" 3) == (F "1/4" 3, .eq)
#guard (RS "9/4" 2) == (F "3/4" 2, .gt)                                          -- 0.667 → 0.75
#guard (RS "2" 53) == (F "6369051672525773/9007199254740992" 53, .gt)            -- 1/√2
#guard (RS "1/2" 53) == (F "6369051672525773/4503599627370496" 53, .gt)          -- √2
#guard (RS "2" 1) == (oneHalf, .lt)                                              -- 0.707 → 1/2
#guard (RS "2" 1 .Up) == (one, .gt)
#guard (RS "5" 4) == (F "7/16" 4, .lt)                                           -- 0.447 → 0.4375
#guard (RS "8" 3) == (F "3/8" 3, .gt)                                            -- 0.354 → 0.375
#guard (RS "3" 2) == (F "1/2" 2, .lt)                                            -- 0.577 → 0.5
#guard (RS "3" 2 .Ceiling) == (F "3/4" 2, .gt)
#guard (RS "1267650600228229401496703205376" 1) == (one >>> 50, .eq)             -- 2^100
#guard (RS "2535301200456458802993406410752" 1) == (one >>> 51, .lt)             -- 2^101
#guard toString (RS "1/10" 53).1 == "3.1622776601683795"
#guard toString (RS "10" 53).1 == "0.31622776601683794"
#guard toString (RS "3/7" 53).1 == "1.5275252316519468"
#guard (RS "0" 3) == (infinity true, .eq)
#guard (RS "-1" 3) == (nan, .eq)
#guard (RS "-1/4" 3) == (nan, .eq)

private def agreesRsqrt (s : String) (p : Nat) (m : RoundingMode) : Bool :=
  rsqrtRatPrecRound (Q s) p m == rsqrtPrecRound (F s 64) p m

#guard [("2", 1), ("2", 7), ("3", 20), ("5/4", 10), ("7/32", 33), ("3/4096", 5), ("123456789", 40),
    ("987654321/65536", 61), ("1/1024", 3)].all fun (s, p) =>
  [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m => agreesRsqrt s p m
