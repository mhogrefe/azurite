/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pow10
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Conversion
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
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

-- agreement with the general functions
#guard pow10PrecRound (F "3/4" 53) 150 .Nearest == powBasePrecRound 10 (F "3/4" 53) 150 .Nearest
#guard pow10PrecRound (F "-7/4" 53) 150 .Floor == powBasePrecRound 10 (F "-7/4" 53) 150 .Floor
#guard pow10 (F "3/4" 53) == powBase 10 (F "3/4" 53)
#guard pow10RatPrecRound (Q "1/3") 150 .Ceiling == powBaseRatPrecRound 10 (Q "1/3") 150 .Ceiling
#guard pow10Rat (Q "22/7") 100 == powBaseRat 10 (Q "22/7") 100
#guard pow10M1PrecRound (F "1/1024" 53) 150 .Nearest
  == powBaseM1PrecRound 10 (F "1/1024" 53) 150 .Nearest
#guard pow10M1 (F "-3/4" 53) == powBaseM1 10 (F "-3/4" 53)
#guard pow10M1RatPrecRound (Q "-1/1000000") 150 .Up
  == powBaseM1RatPrecRound 10 (Q "-1/1000000") 150 .Up
#guard pow10M1Rat (Q "1/3") 100 == powBaseM1Rat 10 (Q "1/3") 100

-- exact powers of ten
#guard pow10PrecRound (F "3" 53) 53 == (F "1000" 53, .eq)
#guard pow10PrecRound (F "-2" 53) 53 == ofAzRatRound (Q "1/100") 53 .Nearest
#guard pow10RatPrecRound (Q "5") 53 == (F "100000" 53, .eq)
#guard pow10RatPrecRound (Q "0") 53 == (F "1" 53, .eq)
#guard pow10M1PrecRound (F "3" 53) 53 == (F "999" 53, .eq)
#guard pow10M1RatPrecRound (Q "-1") 53 == ofAzRatRound (Q "-9/10") 53 .Nearest
#guard pow10M1RatPrecRound (Q "0") 53 == (zero, .eq)
#guard pow10 (F "20" 53) == F "100000000000000000000" 53

-- `10^(1/2) = √10` and `10^(1/3)`
#guard pow10PrecRound (F "1/2" 53) 150 .Nearest == sqrtPrecRound (F "10" 53) 150 .Nearest
#guard (pow10RatPrecRound (Q "1/3") 150 .Nearest).1 == ofAzRat refThird 150
#guard pow10RatPrecRound (Q "1/3") 150 .Floor == ofAzRatRound refThird 150 .Floor
#guard (pow10M1RatPrecRound (Q "1/3") 150 .Nearest).1 == ofAzRat refThirdM1 150
#guard pow10Rat (Q "1/3") 53 == ofAzRat refThird 53
#guard toString (pow10Rat (Q "1/3") 53) == "2.154434690031884"

-- special values
#guard pow10PrecRound nan 53 == (nan, .eq)
#guard pow10PrecRound (infinity true) 53 == (infinity true, .eq)
#guard pow10PrecRound (infinity false) 53 == (zero, .eq)
#guard pow10PrecRound zero 53 == (F "1" 53, .eq)
#guard pow10PrecRound (F "1/2" 53) 0 == (nan, .eq)
#guard pow10M1PrecRound (infinity false) 53 == (F "-1" 53, .eq)
#guard pow10M1PrecRound zero 53 == (zero, .eq)
#guard pow10M1 nan == nan
