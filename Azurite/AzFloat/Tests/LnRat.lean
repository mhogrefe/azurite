/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln` of a rational

`ln (1/3) = −1.098612288668109691395245236922525704…`, `ln (22/7) = 1.145132304303002548373822…`,
`ln (3/2) = 0.405465108108164381978013115464349…`, `ln (123456789/1000) = 11.7236464871858809811…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard lnRat (Q "0") 53 == infinity false
#guard lnRat (Q "-1") 53 == nan
#guard lnRat (Q "-1/3") 53 == nan
#guard lnRat (Q "1") 53 == zero
#guard lnRatPrecRound (Q "1") 53 .Nearest == (zero, .eq)

-- agreement with the float logarithm and the constant `ln 2`
#guard lnRat (Q "2") 53 == ln2 53
#guard lnRat (Q "2") 200 == ln2 200
#guard lnRat (Q "10") 53 == ln (F "10" 53)
#guard lnRat (Q "3/2") 53 == ln (F "3/2" 53)
#guard lnRat (Q "1/2") 53 == ln (F "1/2" 53)
#guard lnRatPrecRound (Q "10") 53 .Floor == lnPrecRound (F "10" 53) 53 .Floor

-- known values at 53 bits
#guard toString (lnRat (Q "1/3") 53) == "-1.0986122886681098"
#guard toString (lnRat (Q "22/7") 53) == "1.1451323043030026"
#guard toString (lnRat (Q "3/2") 53) == "0.4054651081081644"
#guard toString (lnRat (Q "123456789/1000") 53) == "11.723646487185881"
#guard toString (lnRat (Q "1/1000000000000") 53) == "-27.631021115928547"

-- directed rounding brackets the exact value
#guard (lnRatPrecRound (Q "22/7") 53 .Floor).2 == .lt
#guard (lnRatPrecRound (Q "22/7") 53 .Ceiling).2 == .gt
#guard (lnRatPrecRound (Q "22/7") 53 .Floor).1 != (lnRatPrecRound (Q "22/7") 53 .Ceiling).1

-- high precision
#guard toString (lnRat (Q "1/3") 200)
  == "-1.098612288668109691395245236922525704647490557822749451734695"
#guard toString (lnRat (Q "22/7") 200)
  == "1.145132304303002548373822955980126138260122258715811240879858"
#guard toString (lnRat (Q "123456789/1000") 200)
  == "11.72364648718588098113995898391011158691037737513408304708511"
