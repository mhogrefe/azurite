/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.GelfondSchneider
import Azurite.AzFloat.Pow2
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Gelfond–Schneider constant

`2^√2 = 2.665144142690225188650297249873139848274211313714659492835979593364920446178705954…`.
The correctly rounded values at 1, 2, 3, 53 and 100 bits in the nearest, floor and ceiling
modes (exact rationals from a 130-digit evaluation), precision `0`, agreement with
`pow2 (sqrt2 300)` at a lower precision, and the decimal string at 53 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard gelfondSchneiderPrecRound 1 .Nearest == (F "2" 1, .lt)
#guard gelfondSchneiderPrecRound 1 .Floor == (F "2" 1, .lt)
#guard gelfondSchneiderPrecRound 1 .Ceiling == (F "4" 1, .gt)
#guard gelfondSchneiderPrecRound 2 .Nearest == (F "3" 2, .gt)
#guard gelfondSchneiderPrecRound 2 .Floor == (F "2" 2, .lt)
#guard gelfondSchneiderPrecRound 2 .Ceiling == (F "3" 2, .gt)
#guard gelfondSchneiderPrecRound 3 .Nearest == (F "5/2" 3, .lt)
#guard gelfondSchneiderPrecRound 3 .Floor == (F "5/2" 3, .lt)
#guard gelfondSchneiderPrecRound 3 .Ceiling == (F "3" 3, .gt)
#guard gelfondSchneiderPrecRound 53 .Nearest == (F "6001371083954179/2251799813685248" 53, .lt)
#guard gelfondSchneiderPrecRound 53 .Floor == (F "6001371083954179/2251799813685248" 53, .lt)
#guard gelfondSchneiderPrecRound 53 .Ceiling == (F "1500342770988545/562949953421312" 53, .gt)
#guard gelfondSchneiderPrecRound 100 .Nearest
  == (F "844617893044003456779074190201/316912650057057350374175801344" 100, .lt)
#guard gelfondSchneiderPrecRound 100 .Floor
  == (F "844617893044003456779074190201/316912650057057350374175801344" 100, .lt)
#guard gelfondSchneiderPrecRound 100 .Ceiling
  == (F "422308946522001728389537095101/158456325028528675187087900672" 100, .gt)

#guard gelfondSchneiderPrecRound 0 .Nearest == (nan, .eq)
#guard (gelfondSchneiderPrecRound 200 .Floor).2 == .lt
#guard (gelfondSchneiderPrecRound 200 .Ceiling).2 == .gt
#guard gelfondSchneider 100 == (pow2PrecRound (sqrt2 300) 100 .Nearest).1
#guard toString (gelfondSchneider 53) == "2.665144142690225"
