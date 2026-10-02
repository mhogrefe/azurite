/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Compare
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Precision
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString

/-!
# Tests for `setPrecRound`, `ulp?` and `partialCompare`

Expected values computed by hand.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def R (x : AzFloat) : String := (x.toAzRat?.map toString).getD "<none>"
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def E (z : Int) : Option AzInt := some (AzInt.ofInt z)

/-! ## Precision changes -/

#guard R (setPrec (F "1/3" 53) 10) == "683/2048"
#guard (setPrecRound (F "1/3" 53) 10 .Nearest).2 == .gt
#guard (setPrec (F "1/3" 53) 10).precision? == some 10
#guard R (setPrecRound (F "1/3" 53) 10 .Floor).1 == "341/1024"
#guard (setPrecRound (F "1/3" 53) 10 .Floor).2 == .lt
#guard R (setPrecRound (F "-1/3" 53) 10 .Floor).1 == "-683/2048"
#guard (setPrecRound (F "-1/3" 53) 10 .Floor).2 == .lt
#guard R (setPrecRound (F "-1/3" 53) 10 .Ceiling).1 == "-341/1024"
#guard (setPrecRound (F "-1/3" 53) 10 .Ceiling).2 == .gt
#guard R (setPrec (F "1000000" 20) 7) == "999424"
#guard R (setPrecRound (F "1000000" 20) 7 .Up).1 == "1007616"
#guard R (setPrec (F "22/7" 10) 1) == "4"                        -- carry to a power of two
#guard (setPrec (F "22/7" 10) 1).exponent? == E 3
#guard (setPrec (F "22/7" 10) 1).precision? == some 1
#guard R (setPrec (F "1/3" 10) 53) == "683/2048"                 -- raising is exact
#guard (setPrecRound (F "1/3" 10) 53 .Nearest).2 == .eq
#guard (setPrec (F "1/3" 10) 53).precision? == some 53
#guard (setPrec (F "1/3" 10) 53).significand?.map AzNat.size == some 64
#guard R (setPrec (F "1/3" 10) 100) == "683/2048"
#guard (setPrec (F "1/3" 10) 100).significand?.map AzNat.size == some 128
#guard R (setPrec (F "1/3" 100) 64) == "12297829382473034411/36893488147419103232"
#guard (setPrec (F "1/3" 100) 64).significand?.map AzNat.size == some 64
#guard setPrec (F "1/3" 10) 10 == F "1/3" 10
#guard (setPrec nan 10).isNaN
#guard setPrec posInfinity 10 == posInfinity
#guard setPrec zero 10 == zero
#guard (setPrec one 0).isNaN
#guard (setPrecRound one 1 .Nearest) == (one, .eq)

/-! ## Units in the last place -/

#guard (ulp? one).map R == some "1"
#guard (ulp? (F "1/3" 10)).map R == some "1/2048"
#guard (ulp? (F "1000000" 7)).map R == some "8192"
#guard (ulp? (F "1" 53)).map R == some (toString ((Q "1") >>> 52))
#guard ulp? zero == none
#guard ulp? nan == none

/-! ## Comparison -/

#guard partialCompare one two == some .lt
#guard partialCompare two one == some .gt
#guard partialCompare one (F "1" 53) == some .eq               -- different precisions
#guard partialCompare (F "1/3" 10) (F "1/3" 53) == some .gt     -- 683/2048 > the 53-bit value
#guard partialCompare (F "1/3" 53) (F "1/3" 10) == some .lt
#guard partialCompare (F "1/3" 10) (F "1/3" 10) == some .eq
#guard partialCompare (F "-1/3" 10) (F "-1/3" 53) == some .lt
#guard partialCompare (F "-2" 1) (F "-1" 1) == some .lt
#guard partialCompare (F "-1" 1) (F "2" 1) == some .lt
#guard partialCompare (F "3" 2) (F "2" 1) == some .gt   -- same exponent, longer significand
#guard partialCompare (F "2" 1) (F "3" 2) == some .lt
#guard partialCompare (F "1/2" 1) (F "1" 1) == some .lt
#guard partialCompare zero one == some .lt
#guard partialCompare zero (F "-1" 1) == some .gt
#guard partialCompare zero zero == some .eq
#guard partialCompare negInfinity posInfinity == some .lt
#guard partialCompare posInfinity posInfinity == some .eq
#guard partialCompare posInfinity (F "1000000" 7) == some .gt
#guard partialCompare (F "-1000000" 7) negInfinity == some .gt
#guard partialCompare nan nan == none
#guard partialCompare nan one == none
#guard partialCompare one nan == none
#guard !eqIEEE nan nan
#guard eqIEEE one (F "1" 53)
#guard !(one == F "1" 53)                        -- structural equality sees the precision
#guard lt one two && !lt two one && !lt one one
#guard le one two && le one one && !le two one && !le nan nan
#guard gt two one && ge two two && !ge nan one
