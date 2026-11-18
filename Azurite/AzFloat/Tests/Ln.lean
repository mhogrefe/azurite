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
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `ln`

`ln 2 = 0.693147180559945309417232121458176568…`, `ln 10 = 2.302585092994045684017991454684364…`,
`ln 3 = 1.098612288668109691395245236922525704…`, `ln (3/2) = 0.405465108108164381978013115464349…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

-- special values
#guard toString (ln nan) == "NaN"
#guard toString (ln (infinity true)) == "Infinity"
#guard toString (ln (infinity false)) == "NaN"
#guard toString (ln zero) == "-Infinity"
#guard toString (ln (X "-1" 53)) == "NaN"
#guard toString (ln (X "1" 53)) == "0.0"
#guard D (lnPrecRound (X "1" 53) 53 .Nearest) == ("0.0", .eq)

-- agreement with the constant `ln 2`
#guard ln (X "2" 53) == ln2 53
#guard ln (X "2" 200) == ln2 200
#guard lnPrecRound (X "2" 53) 53 .Floor == ln2PrecRound 53 .Floor
#guard lnPrecRound (X "2" 53) 53 .Ceiling == ln2PrecRound 53 .Ceiling

-- known values at 53 bits
#guard toString (ln (X "10" 53)) == "2.302585092994046"
#guard toString (ln (X "3" 53)) == "1.0986122886681098"
#guard toString (ln (X "0.5" 53)) == "-0.6931471805599453"
#guard toString (ln (X "1.5" 53)) == "0.4054651081081644"
#guard toString (ln (X "1000000000000" 53)) == "27.631021115928547"
#guard toString (ln (X "0.000000000001" 53)) == "-27.631021115928547"
#guard toString (ln (X "1267650600228229401496703205376" 53)) == "69.31471805599453"

-- precomputed constants: the same results
#guard lnWith (LnConsts.forPrecision 53) (X "10" 53) == ln (X "10" 53)
#guard lnWith (LnConsts.forPrecision 53) (X "3" 53) == ln (X "3" 53)
#guard lnWith (LnConsts.forPrecision 53) (X "0.5" 53) == ln (X "0.5" 53)
#guard lnWith (LnConsts.forPrecision 200) (X "10" 200) == ln (X "10" 200)
#guard lnPrecRoundWith (LnConsts.forPrecision 53) (X "10" 53) 53 .Floor
  == lnPrecRound (X "10" 53) 53 .Floor
#guard lnPrecRoundWith (LnConsts.forPrecision 53) (X "10" 53) 53 .Ceiling
  == lnPrecRound (X "10" 53) 53 .Ceiling
#guard D (lnPrecRoundWith (LnConsts.forPrecision 53) (X "1" 53) 53 .Nearest) == ("0.0", .eq)
#guard toString (lnWith (LnConsts.forPrecision 53) nan) == "NaN"
#guard toString (lnWith (LnConsts.forPrecision 53) zero) == "-Infinity"
-- constants too coarse for the precision are ignored
#guard lnWith (LnConsts.make 64) (X "10" 200) == ln (X "10" 200)
#guard lnWith (LnConsts.make 1) (X "3" 53) == ln (X "3" 53)
-- finer constants than needed are fine
#guard lnWith (LnConsts.forPrecision 500) (X "3" 53) == ln (X "3" 53)

-- directed rounding brackets the exact value
#guard (lnPrecRound (X "10" 53) 53 .Floor).2 == .lt
#guard (lnPrecRound (X "10" 53) 53 .Ceiling).2 == .gt
#guard (lnPrecRound (X "10" 53) 53 .Floor).1 != (lnPrecRound (X "10" 53) 53 .Ceiling).1

-- high precision
#guard toString (ln (X "10" 200))
  == "2.302585092994045684017991454684364207601101488628772976033328"
#guard toString (ln (X "3" 200))
  == "1.098612288668109691395245236922525704647490557822749451734695"
