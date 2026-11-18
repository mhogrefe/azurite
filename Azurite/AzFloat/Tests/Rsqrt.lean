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
import Azurite.AzFloat.OfString

/-!
# Tests for the reciprocal square root

Expected values computed from independent decimal expansions.  `H` is the exact hexadecimal
rendering.
-/

open Azurite Azurite.AzFloat


/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def H (x : AzFloat) : String := toHexString x

private def RS (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  rsqrtPrecRound x p m

private def DS (s : String) : AzFloat := ofAzRat ((AzRat.fromSci s).get!) 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Reciprocal square root -/

#guard D (RS one 1) == ("1.0", .eq)
#guard D (RS (X "4" 3) 1) == ("0.5", .eq) -- odd e, power of 2
#guard D (RS (X "4" 3) 5) == ("0.5", .eq)
#guard D (RS (X "0.25" 2) 2) == ("2.0", .eq)
#guard D (RS (X "16" 5) 3) == ("0.25", .eq)
#guard D (RS (X "2" 2) 53) == ("0.7071067811865476", .gt) -- 1/√2
#guard D (RS (X "0.5" 1) 53) == ("1.4142135623730951", .gt) -- √2
#guard D (RS (X "2" 2) 1) == ("0.5", .lt) -- 0.707 → 1/2
#guard D (RS (X "2" 2) 1 .Up) == ("1.0", .gt)
#guard D (RS (X "5" 3) 4) == ("0.44", .lt) -- 0.447 → 0.4375
#guard D (RS (X "8" 4) 3) == ("0.4", .gt) -- 0.354 → 0.375
#guard D (RS (X "3" 2) 2) == ("0.5", .lt) -- 0.577 → 0.5
#guard D (RS (X "3" 2) 2 .Ceiling) == ("0.8", .gt)
#guard D (RS (one <<< 100) 1) == ("9.0e-16", .eq)
#guard D (RS (one <<< 101) 1) == ("4.0e-16", .lt) -- 0.707·2^-50 → 2^-51
#guard D (RS (one >>> 1000) 1) == ("3.0e150", .eq)
#guard D (RS nan 3) == ("NaN", .eq)
#guard D (RS (infinity true) 3) == ("0.0", .eq)
#guard D (RS (infinity false) 3) == ("NaN", .eq)
#guard D (RS zero 3) == ("Infinity", .eq)
#guard D (RS negOne 3) == ("NaN", .eq)
#guard toString (rsqrt (X "2" 53)) == "0.7071067811865476"
#guard toString (rsqrt (X "100" 53)) == "0.1"
