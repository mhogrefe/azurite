/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pi
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `π`

`π = 3.14159265358979323846264338327950288419716939937510582097494459…`;
`π · 2^51 = 7074237752028440.4506…`, `π · 2^98 = 995610453248924340922087778488.8396…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard D (piPrecRound 1 .Nearest) == ("4.0", .gt)
#guard D (piPrecRound 1 .Floor) == ("2.0", .lt)
#guard D (piPrecRound 2 .Nearest) == ("3.0", .lt)
#guard D (piPrecRound 2 .Ceiling) == ("4.0", .gt)
#guard D (piPrecRound 3 .Nearest) == ("3.0", .lt)
#guard D (piPrecRound 3 .Up) == ("3.5", .gt)
#guard D (piPrecRound 53 .Nearest) == ("3.141592653589793", .lt)
#guard D (piPrecRound 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (piPrecRound 100 .Nearest) == ("3.14159265358979323846264338328", .lt)
#guard D (piPrecRound 100 .Up) == ("3.141592653589793238462643383282", .gt)
#guard toString (pi 53) == "3.141592653589793"
#guard toString (pi 200)
  == "3.141592653589793238462643383279502884197169399375105820974944"
