/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Recip
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the reciprocal
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard recip nan == nan
#guard recip zero == infinity true
#guard recip (infinity true) == zero
#guard recip (infinity false) == zero

-- exact reciprocals
#guard recipPrecRound (F "1" 53) 53 .Nearest == (F "1" 53, .eq)
#guard recipPrecRound (F "4" 53) 53 .Nearest == (F "1/4" 53, .eq)
#guard recipPrecRound (F "-8" 53) 53 .Floor == (F "-1/8" 53, .eq)
#guard recipPrecRound (F "1/1024" 53) 53 .Ceiling == (F "1024" 53, .eq)

-- rounded reciprocals agree with the rounding of the exact rational
#guard recip (F "3" 53) == F "1/3" 53
#guard recip (F "7" 200) == F "1/7" 200
#guard recip (F "-3/2" 53) == F "-2/3" 53
#guard toString (recip (F "3" 53)) == "0.3333333333333333"
#guard toString (recip (F "3/2" 53)) == "0.6666666666666666"
#guard (recipPrecRound (F "3" 53) 53 .Floor).2 == .lt
#guard (recipPrecRound (F "3" 53) 53 .Ceiling).2 == .gt
#guard recipPrecRound (F "3" 53) 53 .Floor == divPrecRound one (F "3" 53) 53 .Floor
