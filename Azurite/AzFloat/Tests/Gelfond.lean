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

#guard gelfondPrecRound 1 .Nearest == (F "16" 1, .lt)
#guard gelfondPrecRound 1 .Floor == (F "16" 1, .lt)
#guard gelfondPrecRound 1 .Ceiling == (F "32" 1, .gt)
#guard gelfondPrecRound 2 .Nearest == (F "24" 2, .gt)
#guard gelfondPrecRound 2 .Floor == (F "16" 2, .lt)
#guard gelfondPrecRound 2 .Ceiling == (F "24" 2, .gt)
#guard gelfondPrecRound 3 .Nearest == (F "24" 3, .gt)
#guard gelfondPrecRound 3 .Floor == (F "20" 3, .lt)
#guard gelfondPrecRound 3 .Ceiling == (F "24" 3, .gt)
#guard gelfondPrecRound 53 .Nearest == (F "3256762959939997/140737488355328" 53, .gt)
#guard gelfondPrecRound 53 .Floor == (F "6513525919879993/281474976710656" 53, .lt)
#guard gelfondPrecRound 53 .Ceiling == (F "3256762959939997/140737488355328" 53, .gt)
#guard gelfondPrecRound 100 .Nearest
  == (F "916697278301237701639758172109/39614081257132168796771975168" 100, .lt)
#guard gelfondPrecRound 100 .Floor
  == (F "916697278301237701639758172109/39614081257132168796771975168" 100, .lt)
#guard gelfondPrecRound 100 .Ceiling
  == (F "458348639150618850819879086055/19807040628566084398385987584" 100, .gt)

#guard gelfondPrecRound 0 .Nearest == (nan, .eq)
#guard (gelfondPrecRound 200 .Floor).2 == .lt
#guard (gelfondPrecRound 200 .Ceiling).2 == .gt
#guard gelfond 100 == (expPrecRound (pi 300) 100 .Nearest).1
#guard toString (gelfond 53) == "23.14069263277927"
