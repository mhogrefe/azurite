/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.OfString
import Azurite.AzFloat.Recip
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the reciprocal
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard toString (recip nan) == "NaN"
#guard toString (recip zero) == "Infinity"
#guard toString (recip (infinity true)) == "0.0"
#guard toString (recip (infinity false)) == "0.0"

-- exact reciprocals
#guard D (recipPrecRound (X "1" 53) 53 .Nearest) == ("1.0", .eq)
#guard D (recipPrecRound (X "4" 53) 53 .Nearest) == ("0.25", .eq)
#guard D (recipPrecRound (X "-8" 53) 53 .Floor) == ("-0.125", .eq)
#guard D (recipPrecRound (X "0.0009765625" 53) 53 .Ceiling) == ("1024.0", .eq)

-- rounded reciprocals agree with the rounding of the exact rational
#guard toString (recip (X "3" 53)) == "0.3333333333333333"
#guard toString (recip (X "7" 200)) == "0.142857142857142857142857142857142857142857142857142857142\
  8571"
#guard toString (recip (X "-1.5" 53)) == "-0.6666666666666666"
#guard toString (recip (X "3" 53)) == "0.3333333333333333"
#guard toString (recip (X "1.5" 53)) == "0.6666666666666666"
#guard (recipPrecRound (X "3" 53) 53 .Floor).2 == .lt
#guard (recipPrecRound (X "3" 53) 53 .Ceiling).2 == .gt
#guard recipPrecRound (X "3" 53) 53 .Floor == divPrecRound one (X "3" 53) 53 .Floor
