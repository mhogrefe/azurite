/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Div
import Azurite.AzRat.Parse

/-!
# Tests for `exp`

Special values, `exp 0 = 1`, and the correctly rounded values of
`e = 2.71828182845904523536028747135266249775724709369995957496696762772407663035354759457138…`,
`1/e = 0.367879441171442321595523770161460867445811131031767834507836801697461495744899803357…`,
`√e = 1.64872127070012814684865078781416357165377610071014801157507931164066102119421560863277…`,
`e³ = 20.08553692318766774092852965458171789698790783855415014437893422969884587809197373…`,
`e^(7/3) = 10.3122585013257650270155721085372969762103473276008287233926938459203052687560577…`,
`e^(1/1024) = 1.00097703949241653524284529261160650646585162918174419940186408264916250428896869…`,
`e^100 = 2.6881171418161354484126255515800135873611118773741922415191608615280287034909…·10^43`,
`e^(−100) = 3.720075976020835962959695803863118337358892292376781967120613876663290475…·10^(−44)`,
`e^(−1000) = 5.07595889754945676529180947957433691930559928289283736183239384541054054…·10^(−435)`
(references from a 90-digit decimal evaluation), the directed modes, and the agreement of
`exp (ln x)` with `x` at a lower precision.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := expPrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard E nan 53 == (nan, .eq)
#guard E pinf 53 == (infinity true, .eq)
#guard E ninf 53 == (zero, .eq)
#guard E zero 53 == (F "1" 53, .eq)
#guard E zero 1 == (one, .eq)
#guard E zero 0 == (nan, .eq)
#guard E (F "1" 53) 0 == (nan, .eq)
#guard exp nan == nan
#guard exp pinf == infinity true
#guard exp ninf == zero
#guard exp zero == one

-- `e`
private def refE : AzRat :=
  R "271828182845904523536028747135266249775724709369995957496696762772407663035354759457138218" 89
#guard (E (F "1" 53) 150).1 == ofAzRat refE 150
#guard E (F "1" 53) 150 .Floor == ofAzRatRound refE 150 .Floor
#guard E (F "1" 53) 150 .Ceiling == ofAzRatRound refE 150 .Ceiling
#guard E (F "1" 53) 150 .Down == ofAzRatRound refE 150 .Down
#guard E (F "1" 53) 150 .Up == ofAzRatRound refE 150 .Up
#guard E (F "1" 53) 53 == ofAzRatRound refE 53 .Nearest
#guard E (F "1" 53) 1 == (F "2" 1, .lt)
#guard E (F "1" 53) 2 == (F "3" 2, .gt)
#guard exp (F "1" 53) == ofAzRat refE 53
#guard exp (F "1" 200) == ofAzRat refE 200

-- `1/e`, `√e`, `e³`, `e^(7/3)`
private def refEinv : AzRat :=
  R "367879441171442321595523770161460867445811131031767834507836801697461495744899803357147274" 90
private def refEhalf : AzRat :=
  R "164872127070012814684865078781416357165377610071014801157507931164066102119421560863277652" 89
private def refE3 : AzRat :=
  R "200855369231876677409285296545817178969879078385541501443789342296988458780919737312044972" 88
private def refE73 : AzRat :=
  R "103122585013257650270155721085372969762103473276008287233926938459203052687560577516230921" 88
#guard (E (F "-1" 53) 150).1 == ofAzRat refEinv 150
#guard E (F "-1" 53) 150 .Floor == ofAzRatRound refEinv 150 .Floor
#guard E (F "-1" 53) 150 .Ceiling == ofAzRatRound refEinv 150 .Ceiling
#guard (E (F "1/2" 53) 150).1 == ofAzRat refEhalf 150
#guard (E (F "-1/2" 53) 100).1 == ofAzRat (Q "1" / refEhalf) 100
#guard (E (F "3" 53) 150).1 == ofAzRat refE3 150
#guard E (F "3" 53) 100 .Floor == ofAzRatRound refE3 100 .Floor
#guard (E (F "-3" 53) 100).1 == ofAzRat (Q "1" / refE3) 100
#guard (E (F "7/3" 100) 60).1 == ofAzRat refE73 60   -- `7/3` is not exact: 100-bit argument

-- small and large arguments
private def refE1024 : AzRat :=
  R "100097703949241653524284529261160650646585162918174419940186408264916250428896869173656854" 89
private def refE100 : AzRat :=
  R "268811714181613544841262555158001358736111187737419224151916086152802870349095649141588711" 46
private def refEm100 : AzRat :=
  R "372007597602083596295969580386311833735889229237678196712061387666329047589581571815711878" 133
private def refEm1000 : AzRat :=
  R "507595889754945676529180947957433691930559928289283736183239384541054054297481917567966217" 524
#guard (E (F "1/1024" 53) 150).1 == ofAzRat refE1024 150
#guard (E (F "100" 53) 150).1 == ofAzRat refE100 150
#guard E (F "100" 53) 150 .Floor == ofAzRatRound refE100 150 .Floor
#guard (E (F "-100" 53) 150).1 == ofAzRat refEm100 150
#guard E (F "-100" 53) 150 .Ceiling == ofAzRatRound refEm100 150 .Ceiling
#guard (E (F "-1000" 53) 100).1 == ofAzRat refEm1000 100
#guard (E (F "-1000" 53) 100).2 == (ofAzRatRound refEm1000 100 .Nearest).2
-- `exp (2^(−60))` at 53 bits rounds to `1` from above; at 70 bits to `1 + 2^(−60)` from above
#guard E (F "1/1152921504606846976" 53) 53 == (F "1" 53, .lt)
#guard E (F "1/1152921504606846976" 53) 70 == (F "1152921504606846977/1152921504606846976" 70, .lt)
#guard E (F "-1/1152921504606846976" 53) 53 .Ceiling == (F "1" 53, .gt)

-- directed modes are ordered
#guard partialCompare (E (F "5/7" 53) 60 .Floor).1 (E (F "5/7" 53) 60 .Nearest).1 != some .gt
#guard partialCompare (E (F "5/7" 53) 60 .Nearest).1 (E (F "5/7" 53) 60 .Ceiling).1 != some .gt
#guard (E (F "5/7" 53) 60 .Floor).2 == .lt
#guard (E (F "5/7" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (F "-5/7" 53) 60 .Floor).1 (E (F "-5/7" 53) 60 .Ceiling).1 == some .lt

-- `exp (ln x)` returns to `x` at a lower precision
#guard (E (ln (F "3" 200)) 100).1 == F "3" 100
#guard (E (ln (F "1/3" 200)) 100).1 == F "1/3" 100
#guard (E (ln (F "1000000" 200)) 100).1 == F "1000000" 100
#guard (E (lnPrecRound (F "2" 53) 200 .Nearest).1 100).1 == F "2" 100
