/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Div
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for division and the rounding of unreduced fractions

Expected values computed by hand (the exact quotient, then rounding).  `H` is the exact
hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def H (x : AzFloat) : String := toHexString x

private def D (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  divPrecRound x y p m

/-! ## Division -/

#guard (D one one 1) == (one, .eq)
#guard (D (F "6" 3) (F "3" 2) 2) == (F "2" 2, .eq)
#guard (D one (F "3" 2) 2) == (F "3/8" 2, .gt)                                      -- 1/3 → 0.375
#guard (D one (F "3" 2) 2 .Floor) == (F "1/4" 2, .lt)
#guard (D one (F "3" 2) 53) == (F "1/3" 53, .lt)
#guard (D (F "1/3" 53) (F "1/3" 53) 53) == (F "1" 53, .eq)
#guard (D two (F "3" 2) 1) == (oneHalf, .lt)                                        -- 2/3 → 1/2
#guard (D (F "7" 3) (F "5" 3) 3) == (F "3/2" 3, .gt)                                -- 1.4 → 1.5
#guard (D (F "5" 3) (F "7" 3) 3) == (F "3/4" 3, .gt)                                -- 0.714 → 0.75
#guard (D (F "1" 100) (F "3" 2) 10) == (F "1/3" 10, .gt)                            -- 683/2048
#guard (D negOne (F "3" 2) 2) == (F "-3/8" 2, .lt)
#guard (D negOne negOne 1) == (one, .eq)
#guard (D (one <<< 1000) (one <<< 999) 1) == (two, .eq)
#guard (D one (one <<< 1000) 1) == (one >>> 1000, .eq)
#guard (D nan one 5) == (nan, .eq)
#guard (D one nan 5) == (nan, .eq)
#guard (D (infinity true) (infinity false) 5) == (nan, .eq)
#guard (D (infinity false) one 5) == (infinity false, .eq)
#guard (D (infinity false) negOne 5) == (infinity true, .eq)
#guard (D (infinity true) zero 5) == (infinity true, .eq)
#guard (D one zero 5) == (infinity true, .eq)
#guard (D negOne zero 5) == (infinity false, .eq)
#guard (D zero zero 5) == (nan, .eq)
#guard (D zero one 5) == (zero, .eq)
#guard (D zero (infinity true) 5) == (zero, .eq)
#guard (D one (infinity false) 5) == (zero, .eq)
#guard toString (one / F "3" 2) == "0.4"
#guard toString (F "1" 53 / F "3" 53) == "0.3333333333333333"
#guard toString (F "22" 53 / F "7" 53) == "3.142857142857143"


/-! ## Rounding an unreduced fraction -/

#guard (ofFractionRound true (AzNat.ofNat 2) (AzNat.ofNat 6) 53 .Nearest).1 == F "1/3" 53
#guard (ofFractionRound false (AzNat.ofNat 10) (AzNat.ofNat 30) 2 .Nearest).1 == F "-1/3" 2
#guard (ofFractionRound true (AzNat.ofNat 12) (AzNat.ofNat 4) 5 .Nearest) == (F "3" 5, .eq)
#guard (ofFractionRound true (AzNat.ofNat 0) (AzNat.ofNat 4) 5 .Nearest) == (zero, .eq)
#guard (ofFractionRound true (AzNat.ofNat 1) (AzNat.ofNat 10) 53 .Nearest).1 == F "1/10" 53
#guard (ofFractionRound true (AzNat.ofNat 7) (AzNat.ofNat 5) 3 .Floor) == (F "5/4" 3, .lt)
