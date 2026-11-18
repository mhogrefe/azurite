/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ramanujan
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Ramanujan's constant

`e^(π √163) = 262537412640768743.99999999999925007259719818568887935385633733699086270753741…`,
within `7.5 · 10^(−13)` of the integer `640320³ + 744 = 262537412640768744`.  The correctly
rounded values at 1, 2, 3, 53, 60, 100 and 150 bits in the nearest, floor and ceiling modes
(exact rationals from a 140-digit evaluation; at 60 bits the nearest value is the integer
itself, from above), and precision `0`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard D (ramanujanPrecRound 1 .Nearest) == ("3.0e17", .gt)
#guard D (ramanujanPrecRound 1 .Floor) == ("1.4e17", .lt)
#guard D (ramanujanPrecRound 1 .Ceiling) == ("3.0e17", .gt)
#guard D (ramanujanPrecRound 2 .Nearest) == ("3.0e17", .gt)
#guard D (ramanujanPrecRound 2 .Floor) == ("2.0e17", .lt)
#guard D (ramanujanPrecRound 2 .Ceiling) == ("3.0e17", .gt)
#guard D (ramanujanPrecRound 3 .Nearest) == ("2.5e17", .lt)
#guard D (ramanujanPrecRound 3 .Floor) == ("2.5e17", .lt)
#guard D (ramanujanPrecRound 3 .Ceiling) == ("3.0e17", .gt)
#guard D (ramanujanPrecRound 53 .Nearest) == ("2.6253741264076874e17", .lt)
#guard D (ramanujanPrecRound 53 .Floor) == ("2.6253741264076874e17", .lt)
#guard D (ramanujanPrecRound 53 .Ceiling) == ("2.6253741264076877e17", .gt)
#guard D (ramanujanPrecRound 60 .Nearest) == ("262537412640768744.0", .gt)
#guard D (ramanujanPrecRound 60 .Floor) == ("262537412640768743.8", .lt)
#guard D (ramanujanPrecRound 60 .Ceiling) == ("262537412640768744.0", .gt)
#guard D (ramanujanPrecRound 100 .Nearest) == ("262537412640768743.9999999999993", .gt)
#guard D (ramanujanPrecRound 100 .Floor) == ("262537412640768743.999999999999", .lt)
#guard D (ramanujanPrecRound 100 .Ceiling) == ("262537412640768743.9999999999993", .gt)
#guard D (ramanujanPrecRound 150 .Nearest)
  == ("262537412640768743.9999999999992500725971981857", .lt)
#guard D (ramanujanPrecRound 150 .Floor) == ("262537412640768743.9999999999992500725971981857", .lt)
#guard D (ramanujanPrecRound 150 .Ceiling)
  == ("262537412640768743.9999999999992500725971981859", .gt)

#guard D (ramanujanPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (ramanujanPrecRound 60 .Nearest) == ("262537412640768744.0", .gt)
#guard toString (ramanujan 60) == "262537412640768744.0"
#guard (ramanujanPrecRound 150 .Floor).2 == .lt
#guard (ramanujanPrecRound 150 .Ceiling).2 == .gt
