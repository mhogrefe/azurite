/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln
import Azurite.AzFloat.Ln1p
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

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard ln1p nan == nan
#guard ln1p (infinity true) == infinity true
#guard ln1p (infinity false) == nan
#guard ln1p zero == zero
#guard ln1p (F "-1" 53) == infinity false
#guard ln1p (F "-2" 53) == nan
#guard ln1p (F "-3/2" 53) == nan
#guard ln1pPrecRound (F "-1" 53) 53 .Nearest == (infinity false, .eq)

-- agreement with the float logarithm on exactly representable sums
#guard ln1p (F "3" 53) == ln (F "4" 53)
#guard ln1p (F "-1/2" 53) == ln (F "1/2" 53)
#guard ln1p (F "1" 53) == ln (F "2" 53)
#guard ln1p (F "7" 200) == ln (F "8" 200)
#guard ln1pPrecRound (F "3" 53) 53 .Floor == lnPrecRound (F "4" 53) 53 .Floor

-- small arguments
#guard toString (ln1p (F "1/1073741824" 53)) == "9.313225741817976e-10"
#guard toString (ln1p (F "-1/1073741824" 53)) == "-9.313225750491594e-10"
#guard ln1pPrecRound (F "1/1267650600228229401496703205376" 53) 53 .Nearest
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard (ln1pPrecRound (F "1/1073741824" 53) 53 .Floor).2 == .lt
#guard (ln1pPrecRound (F "1/1073741824" 53) 53 .Ceiling).2 == .gt

-- high precision
#guard toString (ln1p (F "1/1073741824" 200))
  == "9.31322574181797646900062748524378479907790510761607319818776e-10"
#guard toString (ln1p (F "-1/1073741824" 200))
  == "-9.31322575049159384888466296106498912866875882669738160663179e-10"
#guard toString (ln1p (F "1/1267650600228229401496703205376" 300))
  == "7.888609052210118054117285652824750789093133780236658015675900880884818306491157115024101102e-31"
