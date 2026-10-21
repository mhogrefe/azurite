/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundToInteger
import Azurite.AzFloat.Add
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for rounding to an integer
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  roundToIntegerPrecRound x p m

/-! ## Special values -/

#guard R nan 10 == (nan, .eq, false)
#guard R (infinity true) 10 == (infinity true, .eq, false)
#guard R (infinity false) 10 .Floor == (infinity false, .eq, false)
#guard R zero 10 == (zero, .eq, true)
#guard isInteger nan == false
#guard isInteger (infinity true) == false
#guard isInteger zero == true
#guard isInteger (F "7" 3) == true
#guard isInteger (F "6" 3) == true
#guard isInteger (F "7/2" 3) == false
#guard isInteger (F "1/4" 10) == false
#guard isInteger (F "1024" 3) == true
#guard isInteger (F "-5" 53) == true

/-! ## Integers that fit are unchanged -/

#guard R (F "7" 3) 3 == (F "7" 3, .eq, true)
#guard R (F "7" 3) 10 == (F "7" 10, .eq, true)
#guard R (F "-5" 53) 53 .Floor == (F "-5" 53, .eq, true)
#guard R (F "1024" 3) 1 == (F "1024" 1, .eq, true)

/-! ## Integers rounded to fit the precision: `(.lt, true)` / `(.gt, true)` -/

#guard R (F "10" 4) 2 == (F "8" 2, .lt, true)            -- tie between 8 and 12: even coordinate
#guard R (F "10" 4) 2 .Ceiling == (F "12" 2, .gt, true)
#guard R (F "11" 4) 2 == (F "12" 2, .gt, true)
#guard R (F "123456789" 53) 10 == (F "123469824" 10, .gt, true)
#guard R (F "123456789" 53) 10 .Down == (F "123338752" 10, .lt, true)
#guard R (F "-123456789" 53) 10 .Down == (F "-123338752" 10, .gt, true)

/-! ## Non-integers: one rounding at the target precision -/

-- `10.5` to nearest at 2 bits is `12`, not `10` rounded again
#guard R (F "21/2" 5) 2 == (F "12" 2, .gt, false)
#guard R (F "21/2" 5) 2 .Floor == (F "8" 2, .lt, false)
#guard R (F "21/2" 5) 2 .Down == (F "8" 2, .lt, false)
#guard R (F "21/2" 5) 2 .Up == (F "12" 2, .gt, false)
#guard R (F "-21/2" 5) 2 == (F "-12" 2, .lt, false)
#guard R (F "-21/2" 5) 2 .Down == (F "-8" 2, .gt, false)
#guard R (F "21/2" 5) 5 == (F "10" 5, .lt, false)         -- ties to even: 10
#guard R (F "23/2" 5) 5 == (F "12" 5, .gt, false)
-- small values: the integer rounding
#guard R (F "5/2" 10) 10 == (F "2" 10, .lt, false)
#guard R (F "7/2" 10) 10 == (F "4" 10, .gt, false)
#guard R (F "-5/2" 10) 10 == (F "-2" 10, .gt, false)
#guard R (F "3/2" 10) 10 == (F "2" 10, .gt, false)
#guard R (F "1/2" 10) 10 == (zero, .lt, false)
#guard R (F "-1/2" 10) 10 == (zero, .gt, false)
#guard R (F "2/5" 10) 10 == (zero, .lt, false)
#guard R (F "3/5" 10) 10 .Floor == (zero, .lt, false)
#guard R (F "3/5" 10) 10 .Ceiling == (F "1" 10, .gt, false)
#guard R (F "-29/4" 10) 10 .Down == (F "-7" 10, .gt, false)
#guard R (F "-29/4" 10) 10 .Up == (F "-8" 10, .lt, false)
#guard R (F "-29/4" 10) 10 .Floor == (F "-8" 10, .lt, false)
#guard R (F "-29/4" 10) 10 .Ceiling == (F "-7" 10, .gt, false)
#guard R (F "-29/4" 10) 10 == (F "-7" 10, .gt, false)
-- rounding at the boundary `2^(p−1)`: `7.5` at 3 bits (`2^(p−1) = 4`) rounds to the 3-bit
-- integer `8`
#guard R (F "15/2" 10) 3 == (F "8" 3, .gt, false)
#guard R (F "15/2" 10) 3 .Floor == (F "7" 3, .lt, false)
-- a huge integer plus a fraction
private def big : AzFloat := F "1" 200 <<< 100 + F "3/4" 200   -- 2^100 + 3/4, exact
#guard R big 200 .Floor == (F "1" 200 <<< 100, .lt, false)
#guard R big 200 .Ceiling == (F "1" 200 <<< 100 + F "1" 200, .gt, false)
#guard R big 200 == (F "1" 200 <<< 100 + F "1" 200, .gt, false)
#guard R big 5 == (F "1" 5 <<< 100, .lt, false)

/-! ## Wrappers -/

#guard roundToIntegerPrec (F "21/2" 5) 2 == F "12" 2
#guard roundToIntegerRound (F "21/2" 5) .Floor == F "10" 5
#guard roundToInteger (F "21/2" 5) == F "10" 5
#guard roundToInteger (F "7/2" 5) == F "4" 5
#guard roundToInteger (F "-1/3" 5) == zero
#guard roundToInteger nan == nan
#guard roundToInteger (infinity false) == infinity false
