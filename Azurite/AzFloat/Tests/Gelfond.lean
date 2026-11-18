/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gelfond
import Azurite.AzFloat.Exp
import Azurite.AzFloat.Pi
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Gelfond's constant

`e^π = 23.140692632779269005729086367948547380266106242600211993445046409524342350690452783…`.
The correctly rounded values at 1, 2, 3, 53 and 100 bits in the nearest, floor and ceiling
modes (exact rationals from a 120-digit evaluation), precision `0`, agreement with
`exp (pi 300)` at a lower precision, and the decimal string at 53 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (gelfondPrecRound 1 .Nearest) == ("2.0e1", .lt)
#guard D (gelfondPrecRound 1 .Floor) == ("2.0e1", .lt)
#guard D (gelfondPrecRound 1 .Ceiling) == ("3.0e1", .gt)
#guard D (gelfondPrecRound 2 .Nearest) == ("24.0", .gt)
#guard D (gelfondPrecRound 2 .Floor) == ("2.0e1", .lt)
#guard D (gelfondPrecRound 2 .Ceiling) == ("24.0", .gt)
#guard D (gelfondPrecRound 3 .Nearest) == ("24.0", .gt)
#guard D (gelfondPrecRound 3 .Floor) == ("2.0e1", .lt)
#guard D (gelfondPrecRound 3 .Ceiling) == ("24.0", .gt)
#guard D (gelfondPrecRound 53 .Nearest) == ("23.14069263277927", .gt)
#guard D (gelfondPrecRound 53 .Floor) == ("23.140692632779267", .lt)
#guard D (gelfondPrecRound 53 .Ceiling) == ("23.14069263277927", .gt)
#guard D (gelfondPrecRound 100 .Nearest) == ("23.14069263277926900572908636794", .lt)
#guard D (gelfondPrecRound 100 .Floor) == ("23.14069263277926900572908636794", .lt)
#guard D (gelfondPrecRound 100 .Ceiling) == ("23.14069263277926900572908636796", .gt)

#guard D (gelfondPrecRound 0 .Nearest) == ("NaN", .eq)
#guard (gelfondPrecRound 200 .Floor).2 == .lt
#guard (gelfondPrecRound 200 .Ceiling).2 == .gt
#guard gelfond 100 == (expPrecRound (pi 300) 100 .Nearest).1
#guard toString (gelfond 53) == "23.14069263277927"
