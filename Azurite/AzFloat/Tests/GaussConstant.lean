/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GaussConstant
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Gauss's constant

`G = 0.8346268416740731862814297327990468089939930134903470024498…`; `G · 2^53 =
7517650266313539.9272…`, `G · 2^100 = 1058015216814730263581923557728.0829…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (gaussConstantPrecRound 1 .Nearest) == ("1.0", .gt)
#guard D (gaussConstantPrecRound 1 .Floor) == ("0.5", .lt)
#guard D (gaussConstantPrecRound 2 .Nearest) == ("0.8", .lt)
#guard D (gaussConstantPrecRound 2 .Ceiling) == ("1.0", .gt)
#guard D (gaussConstantPrecRound 3 .Nearest) == ("0.9", .gt)
#guard D (gaussConstantPrecRound 3 .Floor) == ("0.8", .lt)
#guard D (gaussConstantPrecRound 53 .Nearest) == ("0.8346268416740732", .gt)
#guard D (gaussConstantPrecRound 53 .Floor) == ("0.8346268416740731", .lt)
#guard D (gaussConstantPrecRound 100 .Nearest) == ("0.834626841674073186281429732799", .lt)
#guard D (gaussConstantPrecRound 100 .Up) == ("0.8346268416740731862814297328", .gt)
#guard toString (gaussConstant 53) == "0.8346268416740732"
