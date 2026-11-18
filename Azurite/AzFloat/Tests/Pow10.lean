/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pow10
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the base-`10` powers

`pow10`, `pow10Rat`, `pow10M1` and `pow10M1Rat` against the general `powBase*` functions at
base `10`, the exact powers of ten, `10^(1/2) = √10`, the correctly rounded `10^(1/3)` and
`10^(1/3) − 1` (references from a 200-digit evaluation), and the special values.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)

private def refThird : AzRat :=
  R ("2154434690031883721759293566519350495259344942192108582489235506346411106648340800185441" ++
    "5035432432761012612204917809204465575051000832749571206753778093319327305836534892638281" ++
    "254969314038783827968633") 199
private def refThirdM1 : AzRat :=
  R ("1154434690031883721759293566519350495259344942192108582489235506346411106648340800185441" ++
    "5035432432761012612204917809204465575051000832749571206753778093319327305836534892638281" ++
    "254969314038783827968633") 199
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- agreement with the general functions
#guard pow10PrecRound (X "0.75" 53) 150 .Nearest == powBasePrecRound 10 (X "0.75" 53) 150 .Nearest
#guard pow10PrecRound (X "-1.75" 53) 150 .Floor == powBasePrecRound 10 (X "-1.75" 53) 150 .Floor
#guard pow10 (X "0.75" 53) == powBase 10 (X "0.75" 53)
#guard pow10RatPrecRound (Q "1/3") 150 .Ceiling == powBaseRatPrecRound 10 (Q "1/3") 150 .Ceiling
#guard pow10Rat (Q "22/7") 100 == powBaseRat 10 (Q "22/7") 100
#guard pow10M1PrecRound (X "0.0009765625" 53) 150 .Nearest
  == powBaseM1PrecRound 10 (X "0.0009765625" 53) 150 .Nearest
#guard pow10M1 (X "-0.75" 53) == powBaseM1 10 (X "-0.75" 53)
#guard pow10M1RatPrecRound (Q "-1/1000000") 150 .Up
  == powBaseM1RatPrecRound 10 (Q "-1/1000000") 150 .Up
#guard pow10M1Rat (Q "1/3") 100 == powBaseM1Rat 10 (Q "1/3") 100

-- exact powers of ten
#guard D (pow10PrecRound (X "3" 53) 53 .Nearest) == ("1.0e3", .eq)
#guard D (pow10PrecRound (X "-2" 53) 53 .Nearest) == ("0.01", .gt)
#guard D (pow10RatPrecRound (Q "5") 53 .Nearest) == ("1.0e5", .eq)
#guard D (pow10RatPrecRound (Q "0") 53 .Nearest) == ("1.0", .eq)
#guard D (pow10M1PrecRound (X "3" 53) 53 .Nearest) == ("999.0", .eq)
#guard D (pow10M1RatPrecRound (Q "-1") 53 .Nearest) == ("-0.9", .lt)
#guard D (pow10M1RatPrecRound (Q "0") 53 .Nearest) == ("0.0", .eq)
#guard toString (pow10 (X "20" 53)) == "1.0e20"

-- `10^(1/2) = √10` and `10^(1/3)`
#guard pow10PrecRound (X "0.5" 53) 150 .Nearest == sqrtPrecRound (X "10" 53) 150 .Nearest
#guard toString (pow10RatPrecRound (Q "1/3") 150 .Nearest).1 == "2.15443469003188372175929356651935\
  0495259344943"
#guard D (pow10RatPrecRound (Q "1/3") 150 .Floor) ==
  ("2.15443469003188372175929356651935049525934494", .lt)
#guard toString (pow10M1RatPrecRound (Q "1/3") 150 .Nearest).1 == "1.154434690031883721759293566519\
  350495259344942"
#guard toString (pow10Rat (Q "1/3") 53) == "2.154434690031884"
#guard toString (pow10Rat (Q "1/3") 53) == "2.154434690031884"

-- special values
#guard D (pow10PrecRound nan 53 .Nearest) == ("NaN", .eq)
#guard D (pow10PrecRound (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (pow10PrecRound (infinity false) 53 .Nearest) == ("0.0", .eq)
#guard D (pow10PrecRound zero 53 .Nearest) == ("1.0", .eq)
#guard D (pow10PrecRound (X "0.5" 53) 0 .Nearest) == ("NaN", .eq)
#guard D (pow10M1PrecRound (infinity false) 53 .Nearest) == ("-1.0", .eq)
#guard D (pow10M1PrecRound zero 53 .Nearest) == ("0.0", .eq)
#guard toString (pow10M1 nan) == "NaN"
