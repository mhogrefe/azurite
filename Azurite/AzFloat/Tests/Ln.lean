/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln`

`ln 2 = 0.693147180559945309417232121458176568…`, `ln 10 = 2.302585092994045684017991454684364…`,
`ln 3 = 1.098612288668109691395245236922525704…`, `ln (3/2) = 0.405465108108164381978013115464349…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard ln nan == nan
#guard ln (infinity true) == infinity true
#guard ln (infinity false) == nan
#guard ln zero == infinity false
#guard ln (F "-1" 53) == nan
#guard ln (F "1" 53) == zero
#guard lnPrecRound (F "1" 53) 53 .Nearest == (zero, .eq)

-- agreement with the constant `ln 2`
#guard ln (F "2" 53) == ln2 53
#guard ln (F "2" 200) == ln2 200
#guard lnPrecRound (F "2" 53) 53 .Floor == ln2PrecRound 53 .Floor
#guard lnPrecRound (F "2" 53) 53 .Ceiling == ln2PrecRound 53 .Ceiling

-- known values at 53 bits
#guard toString (ln (F "10" 53)) == "2.302585092994046"
#guard toString (ln (F "3" 53)) == "1.0986122886681098"
#guard toString (ln (F "1/2" 53)) == "-0.6931471805599453"
#guard toString (ln (F "3/2" 53)) == "0.4054651081081644"
#guard toString (ln (F "1000000000000" 53)) == "27.631021115928547"
#guard toString (ln (F "1/1000000000000" 53)) == "-27.631021115928547"
#guard toString (ln (F "1267650600228229401496703205376" 53)) == "69.31471805599453"

-- directed rounding brackets the exact value
#guard (lnPrecRound (F "10" 53) 53 .Floor).2 == .lt
#guard (lnPrecRound (F "10" 53) 53 .Ceiling).2 == .gt
#guard (lnPrecRound (F "10" 53) 53 .Floor).1 != (lnPrecRound (F "10" 53) 53 .Ceiling).1

-- high precision
#guard toString (ln (F "10" 200))
  == "2.302585092994045684017991454684364207601101488628772976033328"
#guard toString (ln (F "3" 200))
  == "1.098612288668109691395245236922525704647490557822749451734695"
