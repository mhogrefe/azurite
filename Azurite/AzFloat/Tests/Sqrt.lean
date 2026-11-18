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
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for the square root

Expected values computed by hand or from independent decimal expansions, shown as decimal
output.  `H` is the exact hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def H (x : AzFloat) : String := toHexString x

private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrtPrecRound x p m

/-! ## Square root -/

#guard D (R one 1) == ("1.0", .eq)
#guard D (R (X "4" 3) 2) == ("2.0", .eq)
#guard D (R (X "2.25" 4) 2) == ("1.5", .eq)
#guard D (R (X "2" 2) 2) == ("1.5", .gt)  -- √2 → 1.5
#guard D (R (X "2" 2) 2 .Floor) == ("1.0", .lt)
#guard D (R (X "2" 2) 53) == ("1.4142135623730951", .gt)
#guard D (R (X "0.25" 2) 1) == ("0.5", .eq)
#guard D (R (one <<< 100) 1) == ("1.0e15", .eq)
#guard D (R (one <<< 101) 1) == ("1.0e15", .lt)  -- √2·2^50
#guard D (R (one <<< 101) 1 .Ceiling) == ("2.0e15", .gt)
#guard D (R (X "2.25" 4) 1) == ("2.0", .gt)  -- tie 1.5 → 2
#guard D (R (X "6.25" 5) 2) == ("2.0", .lt)  -- tie 2.5 → 2
#guard D (R nan 3) == ("NaN", .eq)
#guard D (R (infinity true) 3) == ("Infinity", .eq)
#guard D (R (infinity false) 3) == ("NaN", .eq)
#guard D (R zero 3) == ("0.0", .eq)
#guard D (R negOne 3) == ("NaN", .eq)
#guard toString (sqrt (X "2" 53)) == "1.4142135623730951"
#guard toString (sqrt (X "0.1" 53)) == "0.31622776601683794"
