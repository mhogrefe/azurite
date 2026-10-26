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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard ramanujanPrecRound 1 .Nearest == (F "288230376151711744" 1, .gt)
#guard ramanujanPrecRound 1 .Floor == (F "144115188075855872" 1, .lt)
#guard ramanujanPrecRound 1 .Ceiling == (F "288230376151711744" 1, .gt)
#guard ramanujanPrecRound 2 .Nearest == (F "288230376151711744" 2, .gt)
#guard ramanujanPrecRound 2 .Floor == (F "216172782113783808" 2, .lt)
#guard ramanujanPrecRound 2 .Ceiling == (F "288230376151711744" 2, .gt)
#guard ramanujanPrecRound 3 .Nearest == (F "252201579132747776" 3, .lt)
#guard ramanujanPrecRound 3 .Floor == (F "252201579132747776" 3, .lt)
#guard ramanujanPrecRound 3 .Ceiling == (F "288230376151711744" 3, .gt)
#guard ramanujanPrecRound 53 .Nearest == (F "262537412640768736" 53, .lt)
#guard ramanujanPrecRound 53 .Floor == (F "262537412640768736" 53, .lt)
#guard ramanujanPrecRound 53 .Ceiling == (F "262537412640768768" 53, .gt)
#guard ramanujanPrecRound 60 .Nearest == (F "262537412640768744" 60, .gt)
#guard ramanujanPrecRound 60 .Floor == (F "1050149650563074975/4" 60, .lt)
#guard ramanujanPrecRound 60 .Ceiling == (F "262537412640768744" 60, .gt)
#guard ramanujanPrecRound 100 .Nearest
  == (F "1154651751699004161821692133373/4398046511104" 100, .gt)
#guard ramanujanPrecRound 100 .Floor == (F "288662937924751040455423033343/1099511627776" 100, .lt)
#guard ramanujanPrecRound 100 .Ceiling
  == (F "1154651751699004161821692133373/4398046511104" 100, .gt)
#guard ramanujanPrecRound 150 .Nearest
  == (F "1300022299673581403712273644576105914215875979/4951760157141521099596496896" 150, .lt)
#guard ramanujanPrecRound 150 .Floor
  == (F "1300022299673581403712273644576105914215875979/4951760157141521099596496896" 150, .lt)
#guard ramanujanPrecRound 150 .Ceiling
  == (F "325005574918395350928068411144026478553968995/1237940039285380274899124224" 150, .gt)

#guard ramanujanPrecRound 0 .Nearest == (nan, .eq)
#guard ramanujanPrecRound 60 .Nearest == (F "262537412640768744" 60, .gt)
#guard ramanujan 60 == F "262537412640768744" 60
#guard (ramanujanPrecRound 150 .Floor).2 == .lt
#guard (ramanujanPrecRound 150 .Ceiling).2 == .gt
