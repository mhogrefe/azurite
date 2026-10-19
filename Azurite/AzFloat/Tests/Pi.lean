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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard piPrecRound 1 .Nearest == (F "4" 1, .gt)
#guard piPrecRound 1 .Floor == (F "2" 1, .lt)
#guard piPrecRound 2 .Nearest == (F "3" 2, .lt)
#guard piPrecRound 2 .Ceiling == (F "4" 2, .gt)
#guard piPrecRound 3 .Nearest == (F "3" 3, .lt)
#guard piPrecRound 3 .Up == (F "7/2" 3, .gt)
#guard piPrecRound 53 .Nearest == (F "7074237752028440/2251799813685248" 53, .lt)
#guard piPrecRound 53 .Ceiling == (F "7074237752028441/2251799813685248" 53, .gt)
#guard piPrecRound 100 .Nearest
  == (F "995610453248924340922087778488/316912650057057350374175801344" 100, .lt)
#guard piPrecRound 100 .Up
  == (F "995610453248924340922087778489/316912650057057350374175801344" 100, .gt)
#guard toString (pi 53) == "3.141592653589793"
#guard toString (pi 200)
  == "3.141592653589793238462643383279502884197169399375105820974944"
