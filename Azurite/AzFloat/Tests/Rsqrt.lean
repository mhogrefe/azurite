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
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the reciprocal square root

Expected values computed from independent decimal expansions.  `H` is the exact hexadecimal
rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def H (x : AzFloat) : String := toHexString x

private def RS (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  rsqrtPrecRound x p m

private def DS (s : String) : AzFloat := ofAzRat ((AzRat.fromSci s).get!) 53

/-! ## Reciprocal square root -/

#guard (RS one 1) == (one, .eq)
#guard (RS (F "4" 3) 1) == (oneHalf, .eq)                         -- odd e, power of 2
#guard (RS (F "4" 3) 5) == (F "1/2" 5, .eq)
#guard (RS (F "1/4" 2) 2) == (F "2" 2, .eq)
#guard (RS (F "16" 5) 3) == (F "1/4" 3, .eq)
#guard (RS (F "2" 2) 53) == (DS "0.7071067811865476", .gt)                        -- 1/√2
#guard (RS (F "1/2" 1) 53) == (DS "1.4142135623730951", .gt)                      -- √2
#guard (RS (F "2" 2) 1) == (oneHalf, .lt)                                         -- 0.707 → 1/2
#guard (RS (F "2" 2) 1 .Up) == (one, .gt)
#guard (RS (F "5" 3) 4) == (F "7/16" 4, .lt)                                      -- 0.447 → 0.4375
#guard (RS (F "8" 4) 3) == (F "3/8" 3, .gt)                                       -- 0.354 → 0.375
#guard (RS (F "3" 2) 2) == (F "1/2" 2, .lt)                                       -- 0.577 → 0.5
#guard (RS (F "3" 2) 2 .Ceiling) == (F "3/4" 2, .gt)
#guard (RS (one <<< 100) 1) == (one >>> 50, .eq)
#guard (RS (one <<< 101) 1) == (one >>> 51, .lt)                 -- 0.707·2^-50 → 2^-51
#guard (RS (one >>> 1000) 1) == (one <<< 500, .eq)
#guard (RS nan 3) == (nan, .eq)
#guard (RS (infinity true) 3) == (zero, .eq)
#guard (RS (infinity false) 3) == (nan, .eq)
#guard (RS zero 3) == (infinity true, .eq)
#guard (RS negOne 3) == (nan, .eq)
#guard toString (rsqrt (F "2" 53)) == "0.7071067811865476"
#guard toString (rsqrt (F "100" 53)) == "0.1"
