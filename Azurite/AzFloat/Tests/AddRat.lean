/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddRat
import Azurite.AzFloat.HexString
import Azurite.AzRat.Parse

/-!
# Tests for the addition of a float and a rational

Expected values computed by hand (the exact sum, then rounding to the destination precision).
The exact fallback `addRatExact` is also compared with the Ziv result, since both compute the
same specification by different routes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def H (x : AzFloat) : String := toHexString x

private def A (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  addRatPrecRound x (Q s) p m

private def E (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  addRatExact x (Q s) p m

/-! ## Special values -/

#guard A nan "1/3" 5 == (nan, .eq)
#guard A (infinity true) "1/3" 5 == (infinity true, .eq)
#guard A (infinity false) "-7" 5 == (infinity false, .eq)
#guard A zero "1/3" 10 == ofAzRatRound (Q "1/3") 10 .Nearest
#guard A zero "0" 10 == (zero, .eq)
#guard A one "0" 5 == (setPrec one 5, .eq)
#guard A one "-1" 5 == (zero, .eq)

/-! ## Exact (dyadic) cases -/

#guard A one "1/2" 2 == (F "3/2" 2, .eq)
#guard A one "1/4" 3 == (F "5/4" 3, .eq)
#guard A (F "10" 4) "5" 4 == (F "15" 4, .eq)
#guard A one "-1023/1024" 5 == (F "1/1024" 5, .eq)                         -- cancellation
#guard A (F "3" 2) "-3/2" 2 == (F "3/2" 2, .eq)
#guard A (F "3" 2) "-3/2" 1 == (two, .gt)                                   -- tie to even
#guard H (A one "1/2" 2).1 == "0x1.8#2"

/-! ## Rounded cases -/

#guard A one "1/3" 53 == (F "4/3" 53, .lt)
#guard A one "1/3" 53 .Ceiling == ((ofAzRatRound (Q "4/3") 53 .Ceiling).1, .gt)
#guard A one "1/3" 53 .Floor == (F "4/3" 53, .lt)
#guard A one "-2/3" 1 == (F "1/4" 1, .lt)                                   -- 1/3 to one bit
#guard A one "-2/3" 1 .Ceiling == (oneHalf, .gt)
#guard A (F "-1" 1) "2/3" 1 == (F "-1/4" 1, .gt)
#guard A one "1/3" 1 == (F "1" 1, .lt)                                      -- 4/3 to one bit
#guard A one "1/3" 1 .Up == (two, .gt)

/-! ## Near a midpoint: the first working precision is not enough -/

-- `1/2 + 1/(3·2^80)`: the sum `3/2 + 2^-80/3` is just above the one-bit midpoint
#guard A one "1813388729421943762059265/3626777458843887524118528" 1 == (two, .gt)
#guard A one "1813388729421943762059265/3626777458843887524118528" 1 .Floor == (one, .lt)
#guard A one "1813388729421943762059265/3626777458843887524118528" 1 .Down == (one, .lt)
-- `1/2 − 1/(3·2^80)`: just below the midpoint
#guard A one "1813388729421943762059263/3626777458843887524118528" 1 == (one, .lt)
#guard A one "1813388729421943762059263/3626777458843887524118528" 1 .Ceiling == (two, .gt)
-- exactly the midpoint (dyadic, exact): ties to even
#guard A one "1/2" 1 == (two, .gt)
#guard A (F "3" 2) "1/2" 3 == (F "7/2" 3, .eq)
#guard A (F "3" 2) "1/2" 2 == (F "4" 2, .gt)
#guard A (F "3" 2) "1/2" 1 == (F "4" 1, .gt)

/-! ## Far apart exponents -/

#guard A (powerOf2 (AzInt.ofInt 1000)) "1/3" 5 == (setPrec (powerOf2 (AzInt.ofInt 1000)) 5, .lt)
#guard A (powerOf2 (AzInt.ofInt 1000)) "-1/3" 5 ==
  (setPrec (powerOf2 (AzInt.ofInt 1000)) 5, .gt)
#guard A (powerOf2 (AzInt.ofInt (-1000))) "1/3" 5 == (F "1/3" 5, .lt)
#guard A (powerOf2 (AzInt.ofInt (-1000))) "-1/3" 5 == (F "-1/3" 5, .gt)

/-! ## Agreement with the exact fallback -/

#guard A one "1/3" 53 == E one "1/3" 53
#guard A one "1/3" 53 .Ceiling == E one "1/3" 53 .Ceiling
#guard A (F "22/7" 20) "-355/113" 30 == E (F "22/7" 20) "-355/113" 30
#guard A (F "22/7" 20) "-355/113" 30 .Floor == E (F "22/7" 20) "-355/113" 30 .Floor
#guard A (F "-1/7" 100) "1/11" 7 .Down == E (F "-1/7" 100) "1/11" 7 .Down
#guard A one "1813388729421943762059265/3626777458843887524118528" 1 ==
  E one "1813388729421943762059265/3626777458843887524118528" 1

/-! ## Subtraction -/

#guard subRatPrecRound one (Q "1/2") 2 .Nearest == (F "1/2" 2, .eq)
#guard subRatPrecRound one (Q "-1/3") 53 .Nearest == (F "4/3" 53, .lt)
#guard ratSubPrecRound (Q "1/2") one 2 .Nearest == (F "-1/2" 2, .eq)
#guard ratSubPrecRound (Q "1/3") one 53 .Nearest == (F "-2/3" 53, .gt)
#guard ratSubPrecRound (Q "1/3") zero 5 .Nearest == (F "1/3" 5, .lt)
#guard subRatPrecRound (infinity true) (Q "5") 5 .Nearest == (infinity true, .eq)
#guard ratSubPrecRound (Q "5") (infinity true) 5 .Nearest == (infinity false, .eq)

/-! ## The `+` and `−` instances: nearest, at the float's precision (`1` for a special float) -/

#guard one + Q "1/3" == one                                        -- 4/3 to one bit
#guard F "1" 5 + Q "1/3" == F "4/3" 5
#guard Q "1/3" + F "1" 5 == F "4/3" 5
#guard zero + Q "1/3" == F "1/4" 1
#guard Q "1/3" + zero == F "1/4" 1
#guard F "1" 5 - Q "1/3" == F "2/3" 5
#guard Q "1/3" - F "1" 5 == F "-2/3" 5
#guard F "7/4" 20 - Q "7/4" == zero
#guard infinity true + Q "-1" == infinity true
#guard Q "5" - infinity true == infinity false
#guard nan + Q "1" == nan
