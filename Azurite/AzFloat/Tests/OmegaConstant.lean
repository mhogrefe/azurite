/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.OmegaConstant
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.ToString

/-!
# Tests for the omega constant

`Ω = W₀(1) = 0.56714329040978387299996866221035554975381578718651250813513107922304579308668…`
-/

open Azurite Azurite.AzFloat

/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (omegaConstantPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (omegaConstantPrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (omegaConstantPrecRound 2 .Nearest) == ("0.5", .lt)
#guard D (omegaConstantPrecRound 3 .Nearest) == ("0.6", .gt)
#guard D (omegaConstantPrecRound 53 .Nearest) == ("0.5671432904097838", .lt)
#guard D (omegaConstantPrecRound 53 .Floor) == ("0.5671432904097838", .lt)
#guard D (omegaConstantPrecRound 53 .Ceiling) == ("0.567143290409784", .gt)
#guard D (omegaConstantPrecRound 53 .Down) == ("0.5671432904097838", .lt)
#guard D (omegaConstantPrecRound 53 .Up) == ("0.567143290409784", .gt)
#guard D (omegaConstantPrecRound 100 .Nearest) == ("0.56714329040978387299996866221", .lt)
#guard D (omegaConstantPrecRound 200 .Nearest)
  == ("0.567143290409783872999968662210355549753815787186512508135131", .gt)
#guard toString (omegaConstant 53) == "0.5671432904097838"
#guard toString (omegaConstant 300)
  == "0.567143290409783872999968662210355549753815787186512508135131079223045793086684566693219447"

-- the general Lambert `W₀` at `1` agrees, every precision and mode
#guard [1, 2, 7, 53, 64, 65, 200, 1000].all fun p =>
  [RoundingMode.Floor, .Ceiling, .Nearest].all fun m =>
    D (omegaConstantPrecRound p m) == D (lambertW0PrecRound one p m)
