/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the constants `Γ(1/4)` and `Γ(1/3)`

`Γ(1/4) = 3.62560990822190831193068515586767200299516768288006546743337799956991…`,
`Γ(1/3) = 2.67893853470774763365569294097467764412868937795730110095042832759041…`:
precisions 1, 2, 3, 53, 100, 200 and the rounding modes, `p = 0`, and the fast paths of
`gammaPrecRound` (the float `1/4`) and `gammaRatPrecRound` (`1/4`, `1/3`), with the
neighbouring arguments that do not take them.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `Γ(1/4)`
#guard D (gammaOneQuarterPrecRound 1 .Nearest) == ("4.0", .gt)
#guard D (gammaOneQuarterPrecRound 2 .Nearest) == ("4.0", .gt)
#guard D (gammaOneQuarterPrecRound 3 .Nearest) == ("3.5", .lt)
#guard D (gammaOneQuarterPrecRound 53 .Nearest) == ("3.625609908221908", .lt)
#guard D (gammaOneQuarterPrecRound 53 .Floor) == ("3.625609908221908", .lt)
#guard D (gammaOneQuarterPrecRound 53 .Ceiling) == ("3.6256099082219087", .gt)
#guard D (gammaOneQuarterPrecRound 53 .Down) == ("3.625609908221908", .lt)
#guard D (gammaOneQuarterPrecRound 53 .Up) == ("3.6256099082219087", .gt)
#guard D (gammaOneQuarterPrecRound 100 .Nearest) == ("3.625609908221908311930685155867", .lt)
#guard D (gammaOneQuarterPrecRound 200 .Nearest)
  == ("3.625609908221908311930685155867672002995167682880065467433378", .gt)
#guard D (gammaOneQuarterPrecRound 0 .Nearest) == ("NaN", .eq)
#guard toString (gammaOneQuarter 53) == "3.625609908221908"

-- `Γ(1/3)`
#guard D (gammaOneThirdPrecRound 1 .Nearest) == ("2.0", .lt)
#guard D (gammaOneThirdPrecRound 2 .Nearest) == ("3.0", .gt)
#guard D (gammaOneThirdPrecRound 3 .Nearest) == ("2.5", .lt)
#guard D (gammaOneThirdPrecRound 53 .Nearest) == ("2.6789385347077475", .lt)
#guard D (gammaOneThirdPrecRound 53 .Floor) == ("2.6789385347077475", .lt)
#guard D (gammaOneThirdPrecRound 53 .Ceiling) == ("2.678938534707748", .gt)
#guard D (gammaOneThirdPrecRound 53 .Down) == ("2.6789385347077475", .lt)
#guard D (gammaOneThirdPrecRound 53 .Up) == ("2.678938534707748", .gt)
#guard D (gammaOneThirdPrecRound 100 .Nearest) == ("2.678938534707747633655692940974", .lt)
#guard D (gammaOneThirdPrecRound 200 .Nearest)
  == ("2.678938534707747633655692940974677644128689377957301100950429", .gt)
#guard D (gammaOneThirdPrecRound 0 .Nearest) == ("NaN", .eq)
#guard toString (gammaOneThird 53) == "2.6789385347077475"

-- the fast paths of `Γ`
#guard isQuarter (X "0.25" 53) && !isQuarter (X "0.5" 53) && !isQuarter (X "-0.25" 53)
#guard isUnitFraction (Q "1/4") 4 && isUnitFraction (Q "1/3") 3
#guard !isUnitFraction (Q "-1/4") 4 && !isUnitFraction (Q "3/4") 4 && !isUnitFraction (Q "1/3") 4
#guard gammaPrecRound (X "0.25" 53) 80 .Up == gammaOneQuarterPrecRound 80 .Up
#guard gammaPrecRound (X "0.25" 1) 53 .Nearest == gammaOneQuarterPrecRound 53 .Nearest
#guard gammaRatPrecRound (Q "1/4") 80 .Floor == gammaOneQuarterPrecRound 80 .Floor
#guard gammaRatPrecRound (Q "2/8") 53 .Nearest == gammaOneQuarterPrecRound 53 .Nearest
#guard gammaRatPrecRound (Q "1/3") 80 .Floor == gammaOneThirdPrecRound 80 .Floor
#guard D (gammaRatPrecRound (Q "-1/4") 53 .Nearest) == ("-4.901666809860711", .gt)
#guard D (gammaRatPrecRound (Q "2/3") 53 .Nearest) == ("1.3541179394264005", .gt)
