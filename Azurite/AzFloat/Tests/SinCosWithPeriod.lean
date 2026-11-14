/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinCosWithPeriod`

The special values (`u = 0`, `NaN`, `±∞`, zero, `p = 0`), the exact values in degrees (`0°`,
`30°`, `45°`-multiples, `60°`, `90°`, `180°`, `270°`: the delegated denominators), the pair at
`45°` (`sin = cos = √2/2`) and `1°` at 53 bits and at 200 bits, and the agreement with
`sinWithPeriodPrecRound` and `cosWithPeriodPrecRound` over every whole degree of two turns, both
signs, several periods, modes and precisions, non-integer arguments, a tiny argument (delegated)
and a huge one (`3·2^(2^20)`).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def SC (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinCosWithPeriodPrecRound x u p m
private def agrees (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosWithPeriodPrecRound x u p m
    == (sinWithPeriodPrecRound x u p m, cosWithPeriodPrecRound x u p m)

-- special values
#guard SC (F "1" 53) 0 53 == ((nan, .eq), (nan, .eq))
#guard SC nan 360 53 == ((nan, .eq), (nan, .eq))
#guard SC (infinity true) 360 53 == ((nan, .eq), (nan, .eq))
#guard SC zero 360 53 == ((zero, .eq), (F "1" 53, .eq))
#guard SC zero 360 0 == ((zero, .eq), (nan, .eq))
#guard SC (F "1" 53) 360 0 == ((nan, .eq), (nan, .eq))

-- exact values in degrees
#guard SC (F "30" 53) 360 53
  == ((F "1/2" 53, .eq), cosWithPeriodPrecRound (F "30" 53) 360 53 .Nearest)
#guard SC (F "60" 53) 360 53
  == (sinWithPeriodPrecRound (F "60" 53) 360 53 .Nearest, (F "1/2" 53, .eq))
#guard SC (F "90" 53) 360 53 == ((F "1" 53, .eq), (zero, .eq))
#guard SC (F "180" 53) 360 53 == ((zero, .eq), (F "-1" 53, .eq))
#guard SC (F "270" 53) 360 53 == ((F "-1" 53, .eq), (zero, .eq))
#guard SC (F "-90" 53) 360 53 == ((F "-1" 53, .eq), (zero, .eq))
#guard SC (F "720" 53) 360 53 == ((zero, .eq), (F "1" 53, .eq))

-- `45°`: `sin = cos = √2/2`; `1°`
#guard (SC (F "45" 53) 360 53).1 == (SC (F "45" 53) 360 53).2
#guard (SC (F "45" 53) 360 53).1 == (F "6369051672525773/9007199254740992" 53, .gt)
#guard (SC (F "135" 53) 360 53 .Floor).2.1 == -(SC (F "45" 53) 360 53 .Ceiling).1.1
#guard (toString (sinCosWithPeriod (F "1" 200) 360).1).startsWith
  "0.01745240643728351281941897851631619247225272030713964268361"
#guard (toString (sinCosWithPeriod (F "1" 200) 360).2).startsWith
  "0.99984769515639123915701155881391485169274031058318593965832"

-- agreement with the separate functions
#guard (List.range 721).all fun i => agrees (F s!"{i}" 53) 360 53
#guard (List.range 400).all fun i => agrees (F s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agrees (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 1 40 .Down
#guard (List.range 60).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agrees (F "1" 53) 360 1
#guard agrees (F "1" 53) 18446744073709551615 53
#guard agrees (F "12345678901234567890/1000000007" 100) 360 300
#guard agrees (F "1/3" 2000) 360 2000

-- a tiny argument (delegated) and a huge one
#guard agrees ((F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) 360 53
#guard agrees ((F "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Floor
#guard agrees ((F "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53
