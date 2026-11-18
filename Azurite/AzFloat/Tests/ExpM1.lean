/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.ExpM1
import Azurite.AzFloat.LnP1
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `exp x − 1`

Special values, `exp 0 − 1 = 0`, the correctly rounded values of `e − 1`, `1/e − 1`,
`exp (±2^(−30)) − 1 ≈ ±9.31322574…·10^(−10)`, `exp (1/1024) − 1`, `exp (±100) − 1` and
`exp (±2^(−200)) − 1` (references from a 200-digit decimal evaluation), the tiny-argument path
(`±2^(−200)` at 53 bits round to the argument itself, from below), the directed modes,
agreement with `exp x − 1` computed at a higher precision, and `expM1 (lnP1 x) ≈ x`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := expM1PrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E nan 53) == ("NaN", .eq)
#guard D (E pinf 53) == ("Infinity", .eq)
#guard D (E ninf 53) == ("-1.0", .eq)
#guard D (E ninf 0) == ("NaN", .eq)
#guard D (E zero 53) == ("0.0", .eq)
#guard D (E zero 0) == ("0.0", .eq)
#guard D (E (X "1" 53) 0) == ("NaN", .eq)
#guard toString (expM1 nan) == "NaN"
#guard toString (expM1 pinf) == "Infinity"
#guard toString (expM1 ninf) == "-1.0"
#guard toString (expM1 zero) == "0.0"

private def refE1 : AzRat :=
  R ("1718281828459045235360287471352662497757247093699959574966967627724076630353547594571382" ++
    "1785251664274274663919320030599218174135966290435729003342952605956307381323286279434907" ++
    "632338298807531952510190") 199
private def refEm1 : AzRat :=
  R ("-632120558828557678404476229838539132554188868968232165492163198302538504255100196642852" ++
    "7256540803562533726747231560047917530242072098709913733464105059012169078056326226618849" ++
    "5136100887485438365501228") 200
private def refE30 : AzRat :=
  R ("9313225750491593847538340347920469844993447701933340209396785855309108527498781178820618" ++
    "2493408840512363243825251557440088799616544309072909861187900407182057753424718313706625" ++
    "75069133515098") 199
private def refEm30 : AzRat :=
  R ("-931322574181797646765430487523391711759536067292563821046714781456467755845333879838355" ++
    "9157604913955863710604543625081991220483224303549446479858829058007817281821654399829932" ++
    "2328635594092956") 200
private def refE1024 : AzRat :=
  R ("9770394924165352428452926116065064658516291817441994018640826491625042889686917365685369" ++
    "0882467186075613761065459260696969179898943231122954769049191889764955875334240964352999" ++
    "87245139604295345222") 199
private def refE100 : AzRat :=
  R ("2688117141816135448412625551580013587361111777374192241519160861528028703490956491415887" ++
    "1097219845710811670879190576068697597709761868233548459638929871966089629133626120029380" ++
    "957276534032962269865668") 156
private def refEm100 : AzRat :=
  R ("-999999999999999999999999999999999999999999962799240239791640370403041961368816626411077" ++
    "0762321803287938612333670952410418428184288122135771850339806438235768893019975201435794" ++
    "7464399733814311716092443") 200
private def refE200 : AzRat :=
  R ("6223015277861141707144064053780124240590252168721167133101118551085656258694519850199261" ++
    "466301637402066562613950555226006588368991314568592") 199
private def refEm200 : AzRat :=
  R ("-622301527786114170714406405378012424059025216872116713310111467849374140937624703216862" ++
    "81799497898318473705651596897382436470245749664709058") 200

-- moderate arguments
#guard toString (E (X "1" 53) 150).1 == "1.718281828459045235360287471352662497757247094"
#guard D (E (X "1" 53) 150 .Floor) == ("1.718281828459045235360287471352662497757247093", .lt)
#guard D (E (X "1" 53) 150 .Ceiling) == ("1.718281828459045235360287471352662497757247094", .gt)
#guard toString (E (X "-1" 53) 150).1 == "-0.632120558828557678404476229838539132554188869"
#guard D (E (X "-1" 53) 150 .Down) == ("-0.6321205588285576784044762298385391325541888686", .gt)
#guard toString (E (X "0.0009765625" 53) 150).1 ==
  "0.000977039492416535242845292611606506465851629182"
#guard toString (E (X "100" 53) 150).1 == "26881171418161354484126255515800135873611117.78"
#guard toString (E (X "-100" 53) 150).1 == "-0.999999999999999999999999999999999999999999963"
#guard D (E (X "-100" 53) 150 .Up) == ("-0.999999999999999999999999999999999999999999963", .lt)
#guard toString (expM1 (X "1" 53)) == "1.7182818284590453"
#guard toString (expM1 (X "1" 200)) == "1.718281828459045235360287471352662497757247093699959574966\
  968"

-- small arguments: the cancellation is compensated
#guard toString (E (X "0.000000000931322574615478515625" 53) 150).1 == "9.3132257504915938475383403\
  479204698449934477e-10"
#guard D (E (X "0.000000000931322574615478515625" 53) 150 .Floor) ==
  ("9.31322575049159384753834034792046984499344769e-10", .lt)
#guard toString (E (X "-0.000000000931322574615478515625" 53) 150).1 == "-9.31322574181797646765430\
  4875233917117595360676e-10"
#guard D (E (X "-0.000000000931322574615478515625" 53) 150 .Ceiling) ==
  ("-9.31322574181797646765430487523391711759536067e-10", .gt)
#guard D (E (X "0.000000000931322574615478515625" 53) 53) == ("9.313225750491594e-10", .lt)
#guard toString (expM1 (X "-0.000000000931322574615478515625" 53)) == "-9.313225741817976e-10"

-- tiny arguments: `2^(−200)` at 53 bits is the argument itself, from below or above
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-200))
private def tinyS : String := "1/1606938044258990275541962092341162602522202993782792835301376"
#guard D (E tiny 53) == ("6.223015277861142e-61", .lt)
#guard D (E (-tiny) 53) == ("-6.223015277861142e-61", .lt)
#guard (E tiny 53 .Ceiling).2 == .gt
#guard toString (E tiny 53 .Floor).1 == "6.223015277861142e-61"
#guard (E (-tiny) 53 .Floor).2 == .lt
-- the same arguments at a precision that sees the quadratic term
#guard toString (E tiny 300).1 == "6.22301527786114170714406405378012424059025216872116713310111855\
  1085656258694519850199261466e-61"
#guard D (E tiny 300 .Floor) ==
  ("6.223015277861141707144064053780124240590252168721167133101118551085656258694519850199261466e-6\
  1", .lt)
#guard toString (E (-tiny) 300).1 == "-6.2230152778611417071440640537801242405902521687211671331011\
  1467849374140937624703216862818e-61"
#guard D (E (-tiny) 300 .Ceiling) ==
  ("-6.22301527786114170714406405378012424059025216872116713310111467849374140937624703216862818e-6\
  1", .gt)

-- directed modes are ordered
#guard (E (X "0.7142857142857143" 53) 60 .Floor).2 == .lt
#guard (E (X "0.7142857142857143" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (X "0.7142857142857143" 53) 60 .Floor).1
    (E (X "0.7142857142857143" 53) 60 .Ceiling).1 == some .lt
#guard partialCompare (E (X "-0.7142857142857143" 53) 60 .Floor).1
    (E (X "-0.7142857142857143" 53) 60 .Ceiling).1 == some .lt

-- agreement with `exp x − 1` at a higher precision, and `expM1 (lnP1 x) ≈ x`
#guard (E (X "3" 53) 100).1
  == (subPrecRound (expPrecRound (X "3" 53) 300 .Nearest).1 one 100 .Nearest).1
#guard toString (E (lnP1PrecRound (X "3" 53) 200 .Nearest).1 100).1 == "3.0"
#guard (E (lnP1PrecRound (X "-0.3333333333333333" 53) 200 .Nearest).1 100).1
  == (setPrecRound (X "-0.3333333333333333" 53) 100 .Nearest).1

-- a hugely negative exponent: the value is within `2^(−|x|/2)` above `−1`, and one test
-- (`expM1NearNegOne?`) rounds it at a cost independent of `|x|`
private def m1Above : AzFloat := X "-0.9999999999999999" 53
private def hugeNegX : AzFloat := (X "-3" 53) <<< AzInt.ofInt (2 ^ 40)
private def negX : AzFloat := X "-1000.5" 53
#guard D (expM1PrecRound hugeNegX 53 .Nearest) == ("-1.0", .lt)
#guard D (expM1PrecRound hugeNegX 53 .Floor) == ("-1.0", .lt)
#guard D (expM1PrecRound hugeNegX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard D (expM1PrecRound negX 53 .Nearest) == ("-1.0", .lt)
#guard D (expM1PrecRound negX 53 .Floor) == ("-1.0", .lt)
#guard D (expM1PrecRound negX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard expM1NearNegOne? true 126 53 .Nearest == none
#guard expM1NearNegOne? true 127 53 .Nearest == some (X "-1" 53, .lt)
#guard expM1NearNegOne? false 1000 53 .Nearest == none
