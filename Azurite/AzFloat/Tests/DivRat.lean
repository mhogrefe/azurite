/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DivRat
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Precision
import Azurite.AzRat.Parse

/-!
# Tests for the divisions between a float and a rational

Expected values computed by hand (the exact quotient, then rounding to the destination
precision).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def D (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  divRatPrecRound x (Q s) p m

private def R (s : String) (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  ratDivPrecRound (Q s) x p m

/-! ## `x / q`: special values -/

#guard D nan "1" 5 == (nan, .eq)
#guard D (infinity true) "-2" 5 == (infinity false, .eq)
#guard D (infinity false) "-2" 5 == (infinity true, .eq)
#guard D (infinity true) "0" 5 == (infinity true, .eq)
#guard D zero "0" 5 == (nan, .eq)
#guard D zero "7" 5 == (zero, .eq)
#guard D one "0" 5 == (infinity true, .eq)
#guard D (F "-1" 1) "0" 5 == (infinity false, .eq)

/-! ## `x / q`: values -/

#guard D (F "3" 2) "3" 5 == (F "1" 5, .eq)
#guard D one "3" 53 == (F "1/3" 53, .lt)
#guard D one "-3" 53 == (F "-1/3" 53, .gt)
#guard D one "3" 1 == (F "1/4" 1, .lt)
#guard D (F "3" 2) "2/5" 4 == (F "15/2" 4, .eq)                              -- 7.5 = 111.1
#guard D (F "3" 2) "2/5" 3 == (F "8" 3, .gt)                                 -- tie to even
#guard D (F "3" 2) "2/5" 3 .Floor == (F "7" 3, .lt)
#guard D (F "-3" 2) "2/5" 3 .Down == (F "-7" 3, .gt)
#guard D (powerOf2 (AzInt.ofInt 1000000000)) "3" 5 ==
  (F "1/3" 5 <<< (AzInt.ofInt 1000000000), .lt)

/-! ## `q / x`: special values -/

#guard R "1" nan 5 == (nan, .eq)
#guard R "5" (infinity false) 3 == (zero, .eq)
#guard R "0" (infinity true) 3 == (zero, .eq)
#guard R "0" zero 5 == (nan, .eq)
#guard R "5" zero 3 == (infinity true, .eq)
#guard R "-5" zero 3 == (infinity false, .eq)
#guard R "0" one 5 == (zero, .eq)

/-! ## `q / x`: values -/

#guard R "1" one 5 == (F "1" 5, .eq)
#guard R "1" (F "3" 2) 53 == (F "1/3" 53, .lt)
#guard R "2" (F "3" 2) 53 == (F "2/3" 53, .lt)
#guard R "1" (F "-3" 2) 53 == (F "-1/3" 53, .gt)
#guard R "-1" (F "-3" 2) 53 == (F "1/3" 53, .lt)
#guard R "3/2" (F "3" 2) 4 == (F "1/2" 4, .eq)
#guard R "2/5" (F "3" 2) 4 == (F "9/64" 4, .gt)                               -- 0.0010001000..
#guard R "2/5" (F "3" 2) 4 .Ceiling == (F "9/64" 4, .gt)
#guard R "2/5" (F "3" 2) 4 .Floor == (F "1/8" 4, .lt)
#guard R "1" (powerOf2 (AzInt.ofInt 1000000000)) 5 ==
  (setPrec (powerOf2 (AzInt.ofInt (-1000000000))) 5, .eq)

/-! ## The `/` instances: nearest, at the float's precision -/

#guard one / Q "3" == F "1/4" 1
#guard F "1" 5 / Q "3" == F "1/3" 5
#guard Q "1" / F "3" 2 == F "1/3" 2
#guard Q "3/2" / F "3" 2 == F "1/2" 2
#guard zero / Q "3" == zero
#guard Q "3" / zero == infinity true
