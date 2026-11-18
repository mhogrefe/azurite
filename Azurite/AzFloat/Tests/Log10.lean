/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log10
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def ref102 : AzRat :=
  Q ("301029995663981195213738894724493026768189881462108541310427/1"
    ++ "".pushn '0' 60)
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `log10`
#guard D (log10PrecRound nan 10 .Nearest) == ("NaN", .eq)
#guard D (log10PrecRound zero 10 .Nearest) == ("-Infinity", .eq)
#guard D (log10PrecRound (X "-1" 53) 10 .Nearest) == ("NaN", .eq)
#guard D (log10PrecRound (X "1000" 53) 53 .Nearest) == ("3.0", .eq)
#guard D (log10PrecRound (X "1" 53) 53 .Nearest) == ("0.0", .eq)
#guard toString ((log10PrecRound (X "2" 53) 150 .Nearest).1) == "0.30102999566398119521373889472449\
  30267681898814"
#guard log10PrecRound (X "2" 53) 150 .Floor == logBasePrecRound (X "2" 53) 10 150 .Floor
#guard toString (log10 (X "1000" 10)) == "3.0"
#guard log10 (X "2" 53) == logBase (X "2" 53) 10

-- `log10Rat`
#guard D (log10RatPrecRound (Q "0") 10 .Nearest) == ("-Infinity", .eq)
#guard D (log10RatPrecRound (Q "-1/10") 10 .Nearest) == ("NaN", .eq)
#guard D (log10RatPrecRound (Q "1/1000") 53 .Nearest) == ("-3.0", .eq)
#guard D (log10RatPrecRound (Q "100") 53 .Nearest) == ("2.0", .eq)
#guard toString ((log10RatPrecRound (Q "1/2") 150 .Nearest).1) == "-0.30102999566398119521373889472\
  44930267681898814"
#guard log10RatPrecRound (Q "7/4") 100 .Ceiling == logBaseRatPrecRound (Q "7/4") 10 100 .Ceiling
#guard toString (log10Rat (Q "1/1000") 10) == "-3.0"
#guard log10Rat (Q "3") 60 == logBaseRat (Q "3") 10 60

-- `log10P1`
#guard D (log10P1PrecRound zero 10 .Nearest) == ("0.0", .eq)
#guard D (log10P1PrecRound (X "-1" 53) 10 .Nearest) == ("-Infinity", .eq)
#guard D (log10P1PrecRound (X "-2" 53) 10 .Nearest) == ("NaN", .eq)
#guard D (log10P1PrecRound (X "999" 53) 53 .Nearest) == ("3.0", .eq)
#guard log10P1PrecRound (X "1" 53) 150 .Nearest == log10PrecRound (X "2" 53) 150 .Nearest
#guard toString ((log10P1PrecRound (X "0.000000000931322574615478515625" 53) 100 .Nearest).1)
  == "4.044682548390866259699468258343e-10"
#guard log10P1PrecRound (X "-0.5" 53) 60 .Up == logBaseP1PrecRound (X "-0.5" 53) 10 60 .Up
#guard toString (log10P1 (X "999" 10)) == "3.0"
#guard log10P1 (X "0.000000000931322574615478515625" 53) == logBaseP1 (X
    "0.000000000931322574615478515625" 53) 10
