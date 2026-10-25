/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log10
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the base-10 logarithms

Agreement with the base-`10` natural-base functions, exact powers of ten, and
`log₁₀ 2 = 0.301029995663981195213738894724493026768189881462108541310427…`,
`log₁₀ (1 + 2^(−30)) = 4.044682548390866259699468258342346736699294276436398216273…·10^(−10)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def ref102 : AzRat :=
  Q ("301029995663981195213738894724493026768189881462108541310427/1"
    ++ "".pushn '0' 60)
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)

-- `log10`
#guard log10PrecRound nan 10 .Nearest == (nan, .eq)
#guard log10PrecRound zero 10 .Nearest == (infinity false, .eq)
#guard log10PrecRound (F "-1" 53) 10 .Nearest == (nan, .eq)
#guard log10PrecRound (F "1000" 53) 53 .Nearest == (F "3" 53, .eq)
#guard log10PrecRound (F "1" 53) 53 .Nearest == (zero, .eq)
#guard (log10PrecRound (F "2" 53) 150 .Nearest).1 == ofAzRat ref102 150
#guard log10PrecRound (F "2" 53) 150 .Floor == logBasePrecRound (F "2" 53) 10 150 .Floor
#guard log10 (F "1000" 10) == F "3" 10
#guard log10 (F "2" 53) == logBase (F "2" 53) 10

-- `log10Rat`
#guard log10RatPrecRound (Q "0") 10 .Nearest == (infinity false, .eq)
#guard log10RatPrecRound (Q "-1/10") 10 .Nearest == (nan, .eq)
#guard log10RatPrecRound (Q "1/1000") 53 .Nearest == (F "-3" 53, .eq)
#guard log10RatPrecRound (Q "100") 53 .Nearest == (F "2" 53, .eq)
#guard (log10RatPrecRound (Q "1/2") 150 .Nearest).1 == ofAzRat (-ref102) 150
#guard log10RatPrecRound (Q "7/4") 100 .Ceiling == logBaseRatPrecRound (Q "7/4") 10 100 .Ceiling
#guard log10Rat (Q "1/1000") 10 == F "-3" 10
#guard log10Rat (Q "3") 60 == logBaseRat (Q "3") 10 60

-- `log10P1`
#guard log10P1PrecRound zero 10 .Nearest == (zero, .eq)
#guard log10P1PrecRound (F "-1" 53) 10 .Nearest == (infinity false, .eq)
#guard log10P1PrecRound (F "-2" 53) 10 .Nearest == (nan, .eq)
#guard log10P1PrecRound (F "999" 53) 53 .Nearest == (F "3" 53, .eq)
#guard log10P1PrecRound (F "1" 53) 150 .Nearest == log10PrecRound (F "2" 53) 150 .Nearest
#guard (log10P1PrecRound (F "1/1073741824" 53) 100 .Nearest).1 == ofAzRat refTiny 100
#guard log10P1PrecRound (F "-1/2" 53) 60 .Up == logBaseP1PrecRound (F "-1/2" 53) 10 60 .Up
#guard log10P1 (F "999" 10) == F "3" 10
#guard log10P1 (F "1/1073741824" 53) == logBaseP1 (F "1/1073741824" 53) 10
