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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (gelfondSchneiderPrecRound 1 .Nearest) == ("2.0", .lt)
#guard D (gelfondSchneiderPrecRound 1 .Floor) == ("2.0", .lt)
#guard D (gelfondSchneiderPrecRound 1 .Ceiling) == ("4.0", .gt)
#guard D (gelfondSchneiderPrecRound 2 .Nearest) == ("3.0", .gt)
#guard D (gelfondSchneiderPrecRound 2 .Floor) == ("2.0", .lt)
#guard D (gelfondSchneiderPrecRound 2 .Ceiling) == ("3.0", .gt)
#guard D (gelfondSchneiderPrecRound 3 .Nearest) == ("2.5", .lt)
#guard D (gelfondSchneiderPrecRound 3 .Floor) == ("2.5", .lt)
#guard D (gelfondSchneiderPrecRound 3 .Ceiling) == ("3.0", .gt)
#guard D (gelfondSchneiderPrecRound 53 .Nearest) == ("2.665144142690225", .lt)
#guard D (gelfondSchneiderPrecRound 53 .Floor) == ("2.665144142690225", .lt)
#guard D (gelfondSchneiderPrecRound 53 .Ceiling) == ("2.6651441426902256", .gt)
#guard D (gelfondSchneiderPrecRound 100 .Nearest) == ("2.665144142690225188650297249873", .lt)
#guard D (gelfondSchneiderPrecRound 100 .Floor) == ("2.665144142690225188650297249873", .lt)
#guard D (gelfondSchneiderPrecRound 100 .Ceiling) == ("2.665144142690225188650297249876", .gt)

#guard D (gelfondSchneiderPrecRound 0 .Nearest) == ("NaN", .eq)
#guard (gelfondSchneiderPrecRound 200 .Floor).2 == .lt
#guard (gelfondSchneiderPrecRound 200 .Ceiling).2 == .gt
#guard gelfondSchneider 100 == (pow2PrecRound (sqrt2 300) 100 .Nearest).1
#guard toString (gelfondSchneider 53) == "2.665144142690225"
