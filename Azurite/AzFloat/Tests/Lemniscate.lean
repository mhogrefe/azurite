/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Lemniscate
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the lemniscate constant

`ϖ = 2.62205755429211981046483958989111941368275495143162316281682170380079058707041425023…`;
`ϖ · 2^51 = 5904348712226992.4357…`, `ϖ · 2^98 = 830963208132842219828410015072.3447…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard lemniscateConstantPrecRound 1 .Nearest == (F "2" 1, .lt)
#guard lemniscateConstantPrecRound 1 .Ceiling == (F "4" 1, .gt)
#guard lemniscateConstantPrecRound 2 .Nearest == (F "3" 2, .gt)
#guard lemniscateConstantPrecRound 2 .Floor == (F "2" 2, .lt)
#guard lemniscateConstantPrecRound 3 .Nearest == (F "5/2" 3, .lt)
#guard lemniscateConstantPrecRound 3 .Ceiling == (F "3" 3, .gt)
#guard lemniscateConstantPrecRound 53 .Nearest
  == (F "5904348712226992/2251799813685248" 53, .lt)
#guard lemniscateConstantPrecRound 53 .Up == (F "5904348712226993/2251799813685248" 53, .gt)
#guard lemniscateConstantPrecRound 100 .Nearest
  == (F "830963208132842219828410015072/316912650057057350374175801344" 100, .lt)
#guard lemniscateConstantPrecRound 100 .Ceiling
  == (F "830963208132842219828410015073/316912650057057350374175801344" 100, .gt)
#guard toString (lemniscateConstant 53) == "2.6220575542921196"
