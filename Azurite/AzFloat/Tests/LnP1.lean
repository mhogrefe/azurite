/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln
import Azurite.AzFloat.LnP1
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln (1 + x)`

`ln (1 + 2^(−30)) = 9.31322574181797646900062748524378479907790510761607…·10^(−10)`,
`ln (1 − 2^(−30)) = −9.313225750491594…·10^(−10)`; `ln (1 + 2^(−100))` lies just below `2^(−100)`,
so the 53-bit rounding to nearest is `2^(−100)` itself, from above.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `7.8886090522…` at 300 bits. -/
private def negFourThirds300 : AzFloat :=
  X "7.888609052210118054117285652827862296732064351090230047702789306640625e-31" 300
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard toString (lnP1 nan) == "NaN"
#guard toString (lnP1 (infinity true)) == "Infinity"
#guard toString (lnP1 (infinity false)) == "NaN"
#guard toString (lnP1 zero) == "0.0"
#guard toString (lnP1 (X "-1" 53)) == "-Infinity"
#guard toString (lnP1 (X "-2" 53)) == "NaN"
#guard toString (lnP1 (X "-1.5" 53)) == "NaN"
#guard D (lnP1PrecRound (X "-1" 53) 53 .Nearest) == ("-Infinity", .eq)

-- agreement with the float logarithm on exactly representable sums
#guard lnP1 (X "3" 53) == ln (X "4" 53)
#guard lnP1 (X "-0.5" 53) == ln (X "0.5" 53)
#guard lnP1 (X "1" 53) == ln (X "2" 53)
#guard lnP1 (X "7" 200) == ln (X "8" 200)
#guard lnP1PrecRound (X "3" 53) 53 .Floor == lnPrecRound (X "4" 53) 53 .Floor

-- small arguments
#guard toString (lnP1 (X "0.000000000931322574615478515625" 53)) == "9.313225741817976e-10"
#guard toString (lnP1 (X "-0.000000000931322574615478515625" 53)) == "-9.313225750491594e-10"
#guard D (lnP1PrecRound (X "7.888609052210118e-31" 53) 53 .Nearest) ==
  ("7.888609052210118e-31", .gt)
#guard (lnP1PrecRound (X "0.000000000931322574615478515625" 53) 53 .Floor).2 == .lt
#guard (lnP1PrecRound (X "0.000000000931322574615478515625" 53) 53 .Ceiling).2 == .gt

-- high precision
#guard toString (lnP1 (X "0.000000000931322574615478515625" 200))
  == "9.31322574181797646900062748524378479907790510761607319818776e-10"
#guard toString (lnP1 (X "-0.000000000931322574615478515625" 200))
  == "-9.31322575049159384888466296106498912866875882669738160663179e-10"
#guard toString (lnP1 negFourThirds300)
  == "7.888609052210118054117285652824750789093133780236"
    ++ "658015675900880884818306491157115024101102e-31"

-- precomputed constants: the same results
#guard lnP1With (LnConsts.forPrecision 53) (X "0.5" 53) == lnP1 (X "0.5" 53)
#guard lnP1With (LnConsts.forPrecision 53) (X "9" 53) == lnP1 (X "9" 53)
#guard lnP1With (LnConsts.forPrecision 53) (X "-0.5" 53) == lnP1 (X "-0.5" 53)
#guard lnP1With (LnConsts.forPrecision 53) (X "0.000001" 53) == lnP1 (X "0.000001" 53)
#guard lnP1PrecRoundWith (LnConsts.forPrecision 53) (X "0.5" 53) 53 .Ceiling
  == lnP1PrecRound (X "0.5" 53) 53 .Ceiling

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def third200 : AzFloat := (X "0.3333333333333333" 53) <<< AzInt.ofInt (-200)
#guard lnP1PrecRound tinyX 53 .Nearest == (tinyX, .gt)
#guard lnP1PrecRound tinyX 53 .Ceiling == (tinyX, .gt)
#guard (lnP1PrecRound tinyX 53 .Floor).2 == .lt
#guard (lnP1PrecRound tinyX 53 .Floor).1 != tinyX
#guard lnP1PrecRound (-tinyX) 53 .Ceiling == (-tinyX, .gt)
#guard (lnP1PrecRound (-tinyX) 53 .Nearest).2 == .gt
#guard lnP1PrecRound ((X "1.5" 100) <<< tinyE) 53 .Nearest
  == ((X "1.5" 53) <<< tinyE, .gt)
#guard (lnP1PrecRound tinyX 200 .Nearest).1 == (X "1" 200) <<< tinyE
#guard lnP1 tinyX == tinyX
-- `ln (1 ± ⌊1/3⌋₅₃ 2^(−200))` (references from the series with exact rationals)
#guard D (lnP1PrecRound third200 53 .Nearest) == ("2.0743384259537138e-61", .gt)
#guard D (lnP1PrecRound third200 53 .Ceiling) == ("2.0743384259537138e-61", .gt)
#guard D (lnP1PrecRound third200 53 .Floor) == ("2.0743384259537134e-61", .lt)
#guard D (lnP1PrecRound (-third200) 53 .Nearest) == ("-2.0743384259537138e-61", .gt)
#guard D (lnP1PrecRound (-third200) 53 .Floor) == ("-2.074338425953714e-61", .lt)
#guard lnP1PrecRoundWith (LnConsts.forPrecision 53) tinyX 53 .Floor
  == lnP1PrecRound tinyX 53 .Floor
