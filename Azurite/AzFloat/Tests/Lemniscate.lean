/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Lemniscate
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the lemniscate constant

`ϖ = 2.62205755429211981046483958989111941368275495143162316281682170380079058707041425023…`;
`ϖ · 2^51 = 5904348712226992.4357…`, `ϖ · 2^98 = 830963208132842219828410015072.3447…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (lemniscateConstantPrecRound 1 .Nearest) == ("2.0", .lt)
#guard D (lemniscateConstantPrecRound 1 .Ceiling) == ("4.0", .gt)
#guard D (lemniscateConstantPrecRound 2 .Nearest) == ("3.0", .gt)
#guard D (lemniscateConstantPrecRound 2 .Floor) == ("2.0", .lt)
#guard D (lemniscateConstantPrecRound 3 .Nearest) == ("2.5", .lt)
#guard D (lemniscateConstantPrecRound 3 .Ceiling) == ("3.0", .gt)
#guard D (lemniscateConstantPrecRound 53 .Nearest) == ("2.6220575542921196", .lt)
#guard D (lemniscateConstantPrecRound 53 .Up) == ("2.62205755429212", .gt)
#guard D (lemniscateConstantPrecRound 100 .Nearest) == ("2.62205755429211981046483958989", .lt)
#guard D (lemniscateConstantPrecRound 100 .Ceiling) == ("2.622057554292119810464839589893", .gt)
#guard toString (lemniscateConstant 53) == "2.6220575542921196"
