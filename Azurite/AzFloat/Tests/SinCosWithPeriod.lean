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
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def big1 : AzFloat := X "0.3333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333333333333333333335" 2000
private def SC (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinCosWithPeriodPrecRound x u p m
private def agrees (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosWithPeriodPrecRound x u p m
    == (sinWithPeriodPrecRound x u p m, cosWithPeriodPrecRound x u p m)
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A pair of results as decimal output and comparison tags. -/
private def D2 (r : (AzFloat × Ordering) × (AzFloat × Ordering)) :
    (String × Ordering) × (String × Ordering) := ((toString r.1.1, r.1.2), (toString r.2.1, r.2.2))

-- special values
#guard D2 (SC (X "1" 53) 0 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC nan 360 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC (infinity true) 360 53) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (SC zero 360 53) == (("0.0", .eq), ("1.0", .eq))
#guard D2 (SC zero 360 0) == (("0.0", .eq), ("NaN", .eq))
#guard D2 (SC (X "1" 53) 360 0) == (("NaN", .eq), ("NaN", .eq))

-- exact values in degrees
#guard SC (X "30" 53) 360 53
  == ((X "0.5" 53, .eq), cosWithPeriodPrecRound (X "30" 53) 360 53 .Nearest)
#guard SC (X "60" 53) 360 53
  == (sinWithPeriodPrecRound (X "60" 53) 360 53 .Nearest, (X "0.5" 53, .eq))
#guard D2 (SC (X "90" 53) 360 53) == (("1.0", .eq), ("0.0", .eq))
#guard D2 (SC (X "180" 53) 360 53) == (("0.0", .eq), ("-1.0", .eq))
#guard D2 (SC (X "270" 53) 360 53) == (("-1.0", .eq), ("0.0", .eq))
#guard D2 (SC (X "-90" 53) 360 53) == (("-1.0", .eq), ("0.0", .eq))
#guard D2 (SC (X "720" 53) 360 53) == (("0.0", .eq), ("1.0", .eq))

-- `45°`: `sin = cos = √2/2`; `1°`
#guard (SC (X "45" 53) 360 53).1 == (SC (X "45" 53) 360 53).2
#guard D ((SC (X "45" 53) 360 53).1) == ("0.7071067811865476", .gt)
#guard (SC (X "135" 53) 360 53 .Floor).2.1 == -(SC (X "45" 53) 360 53 .Ceiling).1.1
#guard toString (sinCosWithPeriod (X "1" 200) 360).1
  == "0.01745240643728351281941897851631619247225272030713964268361243"
#guard toString (sinCosWithPeriod (X "1" 200) 360).2
  == "0.999847695156391239157011558813914851692740310583185939658321"

-- agreement with the separate functions
#guard (List.range 721).all fun i => agrees (F s!"{i}" 53) 360 53
#guard (List.range 400).all fun i => agrees (F s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agrees (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 1 40 .Down
#guard (List.range 60).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agrees (X "1" 53) 360 1
#guard agrees (X "1" 53) 18446744073709551615 53
#guard agrees (X "12345678814.81481618629628669593" 100) 360 300
#guard agrees big1 360 2000

-- a tiny argument (delegated) and a huge one
#guard agrees ((X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))) 360 53
#guard agrees ((X "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Floor
#guard agrees ((X "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53
