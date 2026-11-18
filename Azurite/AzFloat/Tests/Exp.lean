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
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := expPrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard D (E nan 53) == ("NaN", .eq)
#guard D (E pinf 53) == ("Infinity", .eq)
#guard D (E ninf 53) == ("0.0", .eq)
#guard D (E zero 53) == ("1.0", .eq)
#guard D (E zero 1) == ("1.0", .eq)
#guard D (E zero 0) == ("NaN", .eq)
#guard D (E (X "1" 53) 0) == ("NaN", .eq)
#guard toString (exp nan) == "NaN"
#guard toString (exp pinf) == "Infinity"
#guard toString (exp ninf) == "0.0"
#guard toString (exp zero) == "1.0"

-- `e`
private def refE : AzRat :=
  R "271828182845904523536028747135266249775724709369995957496696762772407663035354759457138218" 89
#guard toString ((E (X "1" 53) 150).1) == "2.718281828459045235360287471352662497757247093"
#guard D (E (X "1" 53) 150 .Floor) == ("2.718281828459045235360287471352662497757247093", .lt)
#guard D (E (X "1" 53) 150 .Ceiling) == ("2.718281828459045235360287471352662497757247095", .gt)
#guard D (E (X "1" 53) 150 .Down) == ("2.718281828459045235360287471352662497757247093", .lt)
#guard D (E (X "1" 53) 150 .Up) == ("2.718281828459045235360287471352662497757247095", .gt)
#guard D (E (X "1" 53) 53) == ("2.718281828459045", .lt)
#guard D (E (X "1" 53) 1) == ("2.0", .lt)
#guard D (E (X "1" 53) 2) == ("3.0", .gt)
#guard toString (exp (X "1" 53)) == "2.718281828459045"
#guard toString (exp (X "1" 200))
  == "2.718281828459045235360287471352662497757247093699959574966968"

-- `1/e`, `√e`, `e³`, `e^(7/3)`
private def refEinv : AzRat :=
  R "367879441171442321595523770161460867445811131031767834507836801697461495744899803357147274" 90
private def refEhalf : AzRat :=
  R "164872127070012814684865078781416357165377610071014801157507931164066102119421560863277652" 89
private def refE3 : AzRat :=
  R "200855369231876677409285296545817178969879078385541501443789342296988458780919737312044972" 88
private def refE73 : AzRat :=
  R "103122585013257650270155721085372969762103473276008287233926938459203052687560577516230921" 88
#guard toString ((E (X "-1" 53) 150).1) == "0.367879441171442321595523770161460867445811131"
#guard D (E (X "-1" 53) 150 .Floor) == ("0.3678794411714423215955237701614608674458111307", .lt)
#guard D (E (X "-1" 53) 150 .Ceiling) == ("0.367879441171442321595523770161460867445811131", .gt)
#guard toString ((E (X "0.5" 53) 150).1) == "1.6487212707001281468486507878141635716537761"
#guard toString ((E (X "-0.5" 53) 100).1) == "0.606530659712633423603799534991"
#guard toString ((E (X "3" 53) 150).1) == "20.08553692318766774092852965458171789698790783"
#guard D (E (X "3" 53) 100 .Floor) == ("20.08553692318766774092852965458", .lt)
#guard toString ((E (X "-3" 53) 100).1) == "0.04978706836786394297934241565005"
#guard toString ((E (X "2.333333333333333333333333333332" 100) 60).1)
  == "10.31225850132576503"  -- `7/3` is not exact: 100-bit argument

-- small and large arguments
private def refE1024 : AzRat :=
  R "100097703949241653524284529261160650646585162918174419940186408264916250428896869173656854" 89
private def refE100 : AzRat :=
  R "268811714181613544841262555158001358736111187737419224151916086152802870349095649141588711" 46
private def refEm100 : AzRat :=
  R "372007597602083596295969580386311833735889229237678196712061387666329047589581571815711878" 133
private def refEm1000 : AzRat :=
  R "507595889754945676529180947957433691930559928289283736183239384541054054297481917567966217" 524
#guard toString ((E (X "0.0009765625" 53) 150).1) == "1.0009770394924165352428452926116065064658516\
  3"
#guard toString ((E (X "100" 53) 150).1) == "26881171418161354484126255515800135873611118.78"
#guard D (E (X "100" 53) 150 .Floor) == ("26881171418161354484126255515800135873611118.75", .lt)
#guard toString ((E (X "-100" 53) 150).1) == "3.720075976020835962959695803863118337358892292e-44"
#guard D (E (X "-100" 53) 150 .Ceiling)
  == ("3.720075976020835962959695803863118337358892295e-44", .gt)
#guard toString ((E (X "-1000" 53) 100).1) == "5.07595889754945676529180947957e-435"
#guard (E (X "-1000" 53) 100).2 == (ofAzRatRound refEm1000 100 .Nearest).2
-- `exp (2^(−60))` at 53 bits rounds to `1` from above; at 70 bits to `1 + 2^(−60)` from above
#guard D (E (X "8.673617379884035e-19" 53) 53) == ("1.0", .lt)
#guard D (E (X "8.673617379884035e-19" 53) 70) == ("1.000000000000000000867", .lt)
#guard D (E (X "-8.673617379884035e-19" 53) 53 .Ceiling) == ("1.0", .gt)

-- directed modes are ordered
#guard partialCompare (E (X "0.7142857142857143" 53) 60 .Floor).1 (E (X "0.714285714285714\
  3" 53) 60 .Nearest).1 != some .gt
#guard partialCompare (E (X "0.7142857142857143" 53) 60 .Nearest).1 (E (X "0.714285714285714\
  3" 53) 60 .Ceiling).1 != some .gt
#guard (E (X "0.7142857142857143" 53) 60 .Floor).2 == .lt
#guard (E (X "0.7142857142857143" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (X "-0.7142857142857143" 53) 60 .Floor).1 (E (X "-0.714285714285714\
  3" 53) 60 .Ceiling).1 == some .lt

-- `exp (ln x)` returns to `x` at a lower precision
#guard toString ((E (ln (X "3" 200)) 100).1) == "3.0"
#guard toString ((E (ln (X "0.333333333333333333333333333333333333333333333333333333333333\
  4" 200)) 100).1) == "0.3333333333333333333333333333335"
#guard toString ((E (ln (X "1000000" 200)) 100).1) == "1.0e6"
#guard toString ((E (lnPrecRound (X "2" 53) 200 .Nearest).1 100).1) == "2.0"

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (expPrecRound tinyX 53 .Nearest) == ("1.0", .lt)
#guard D (expPrecRound tinyX 53 .Floor) == ("1.0", .lt)
#guard D (expPrecRound tinyX 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (expPrecRound (-tinyX) 53 .Nearest) == ("1.0", .gt)
#guard D (expPrecRound (-tinyX) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (expPrecRound (-tinyX) 53 .Ceiling) == ("1.0", .gt)
