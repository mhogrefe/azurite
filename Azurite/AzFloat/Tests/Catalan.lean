/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Catalan
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Catalan's constant

`G = 0.91596559417721901505460351493238411077414937428167213426649811962176301977625476947…`.
The correctly rounded values at 1, 2, 3, 53 and 100 bits in the nearest, floor and ceiling
modes (exact rationals from an independent evaluation to 2000 bits, in which Ramanujan's formula
and Broadhurst's BBP-type formula agree), precision `0`, and the decimal strings at 53, 200 and
400 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (catalanConstantPrecRound 1 .Nearest) == ("1.0", .gt)
#guard D (catalanConstantPrecRound 1 .Floor) == ("0.5", .lt)
#guard D (catalanConstantPrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (catalanConstantPrecRound 2 .Nearest) == ("1.0", .gt)
#guard D (catalanConstantPrecRound 2 .Floor) == ("0.8", .lt)
#guard D (catalanConstantPrecRound 2 .Ceiling) == ("1.0", .gt)
#guard D (catalanConstantPrecRound 3 .Nearest) == ("0.9", .lt)
#guard D (catalanConstantPrecRound 3 .Floor) == ("0.9", .lt)
#guard D (catalanConstantPrecRound 3 .Ceiling) == ("1.0", .gt)
#guard D (catalanConstantPrecRound 53 .Nearest) == ("0.915965594177219", .lt)
#guard D (catalanConstantPrecRound 53 .Floor) == ("0.915965594177219", .lt)
#guard D (catalanConstantPrecRound 53 .Ceiling) == ("0.9159655941772191", .gt)
#guard D (catalanConstantPrecRound 100 .Nearest) == ("0.9159655941772190150546035149325", .gt)
#guard D (catalanConstantPrecRound 100 .Floor) == ("0.915965594177219015054603514932", .lt)
#guard D (catalanConstantPrecRound 100 .Ceiling) == ("0.9159655941772190150546035149325", .gt)

#guard D (catalanConstantPrecRound 0 .Nearest) == ("NaN", .eq)
#guard (catalanConstantPrecRound 200 .Floor).2 == .lt
#guard (catalanConstantPrecRound 200 .Ceiling).2 == .gt
#guard toString (AzFloat.catalanConstant 53) == "0.915965594177219"
#guard toString (AzFloat.catalanConstant 200)
  == "0.9159655941772190150546035149323841107741493742816721342664983"
#guard toString (AzFloat.catalanConstant 400)
  == "0.9159655941772190150546035149323841107741493742816721342664981196217630197762547694793"
    ++ "56512926115106248574422619196199579"
