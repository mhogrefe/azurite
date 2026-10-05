/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the square root

Expected values computed by hand or from independent decimal expansions.  `H` is the exact
hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def H (x : AzFloat) : String := toHexString x

private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrtPrecRound x p m

/-! ## Square root -/

#guard (R one 1) == (one, .eq)
#guard (R (F "4" 3) 2) == (F "2" 2, .eq)
#guard (R (F "9/4" 4) 2) == (F "3/2" 2, .eq)
#guard (R (F "2" 2) 2) == (F "3/2" 2, .gt)                                          -- √2 → 1.5
#guard (R (F "2" 2) 2 .Floor) == (F "1" 2, .lt)
#guard (R (F "2" 2) 53) == (F "6369051672525773/4503599627370496" 53, .gt)
#guard (R (F "1/4" 2) 1) == (oneHalf, .eq)
#guard (R (one <<< 100) 1) == (one <<< 50, .eq)
#guard (R (one <<< 101) 1) == (one <<< 50, .lt)                                     -- √2·2^50
#guard (R (one <<< 101) 1 .Ceiling) == (one <<< 51, .gt)
#guard (R (F "9/4" 4) 1) == (two, .gt)                                              -- tie 1.5 → 2
#guard (R (F "25/4" 5) 2) == (F "2" 2, .lt)                                         -- tie 2.5 → 2
#guard (R nan 3) == (nan, .eq)
#guard (R (infinity true) 3) == (infinity true, .eq)
#guard (R (infinity false) 3) == (nan, .eq)
#guard (R zero 3) == (zero, .eq)
#guard (R negOne 3) == (nan, .eq)
#guard toString (sqrt (F "2" 53)) == "1.4142135623730951"
#guard toString (sqrt (F "1/10" 53)) == "0.31622776601683794"
