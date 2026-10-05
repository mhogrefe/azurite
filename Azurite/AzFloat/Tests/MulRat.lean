/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.HexString
import Azurite.AzFloat.MulRat
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for the multiplication of a float by a rational

Expected values computed by hand (the exact product, then rounding to the destination
precision).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def M (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  mulRatPrecRound x (Q s) p m

/-! ## Special values -/

#guard M nan "1/3" 5 == (nan, .eq)
#guard M (infinity true) "-2/3" 5 == (infinity false, .eq)
#guard M (infinity false) "-2/3" 5 == (infinity true, .eq)
#guard M (infinity true) "0" 5 == (nan, .eq)
#guard M zero "1/3" 5 == (zero, .eq)
#guard M one "0" 5 == (zero, .eq)

/-! ## Exact products -/

#guard M (F "3" 2) "1/3" 5 == (F "1" 5, .eq)
#guard M (F "-3" 2) "1/3" 1 == (F "-1" 1, .eq)
#guard M (F "6" 3) "5/3" 5 == (F "10" 5, .eq)
#guard M (F "3" 2) "1/6" 5 == (F "1/2" 5, .eq)
#guard M (F "15" 4) "7/5" 6 == (F "21" 6, .eq)
#guard M one "1/4" 3 == (F "1/4" 3, .eq)                                     -- dyadic `q`
#guard M (F "3" 2) "1/3" 1 == (one, .eq)
#guard M (F "9" 4) "1/3" 1 == (F "4" 1, .gt)                               -- exact 3, re-rounded
#guard M (F "9" 4) "1/3" 1 .Floor == (two, .lt)

/-! ## Rounded products -/

#guard M one "1/3" 53 == (F "1/3" 53, .lt)
#guard M (F "2" 2) "1/3" 53 == (F "2/3" 53, .lt)
#guard M (F "-1" 1) "1/3" 53 == (F "-1/3" 53, .gt)
#guard M (F "-1" 1) "-1/3" 53 == (F "1/3" 53, .lt)
#guard M (F "3" 2) "2/5" 4 == (F "5/4" 4, .gt)                              -- 6/5 = 1.0011..
#guard M (F "3" 2) "2/5" 4 .Floor == (F "9/8" 4, .lt)
#guard M (F "3" 2) "2/5" 4 .Down == (F "9/8" 4, .lt)
#guard M (F "-3" 2) "2/5" 4 .Down == (F "-9/8" 4, .gt)
#guard M (F "-3" 2) "2/5" 4 .Up == (F "-5/4" 4, .lt)
#guard M one "1/3" 1 == (F "1/4" 1, .lt)                                     -- 1/3 to one bit
#guard M one "1/3" 1 .Ceiling == (oneHalf, .gt)

/-! ## Far exponents -/

#guard M (powerOf2 (AzInt.ofInt 1000000000)) "1/3" 5 ==
  (F "1/3" 5 <<< (AzInt.ofInt 1000000000), .lt)
#guard M (powerOf2 (AzInt.ofInt (-1000000000))) "-1/3" 5 ==
  (F "-1/3" 5 >>> (AzInt.ofInt 1000000000), .gt)

/-! ## The `*` instances: nearest, at the float's precision -/

#guard one * Q "1/3" == F "1/4" 1
#guard Q "1/3" * F "3" 2 == F "1" 2
#guard F "1" 5 * Q "1/3" == F "1/3" 5
#guard Q "-2/7" * F "7" 3 == F "-2" 3
#guard zero * Q "1/3" == zero
#guard infinity true * Q "-1" == infinity false
