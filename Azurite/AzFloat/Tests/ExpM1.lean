/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.ExpM1
import Azurite.AzFloat.LnP1
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := expM1PrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard E nan 53 == (nan, .eq)
#guard E pinf 53 == (infinity true, .eq)
#guard E ninf 53 == (F "-1" 53, .eq)
#guard E ninf 0 == (nan, .eq)
#guard E zero 53 == (zero, .eq)
#guard E zero 0 == (zero, .eq)
#guard E (F "1" 53) 0 == (nan, .eq)
#guard expM1 nan == nan
#guard expM1 pinf == infinity true
#guard expM1 ninf == F "-1" 1
#guard expM1 zero == zero

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
#guard (E (F "1" 53) 150).1 == ofAzRat refE1 150
#guard E (F "1" 53) 150 .Floor == ofAzRatRound refE1 150 .Floor
#guard E (F "1" 53) 150 .Ceiling == ofAzRatRound refE1 150 .Ceiling
#guard (E (F "-1" 53) 150).1 == ofAzRat refEm1 150
#guard E (F "-1" 53) 150 .Down == ofAzRatRound refEm1 150 .Down
#guard (E (F "1/1024" 53) 150).1 == ofAzRat refE1024 150
#guard (E (F "100" 53) 150).1 == ofAzRat refE100 150
#guard (E (F "-100" 53) 150).1 == ofAzRat refEm100 150
#guard E (F "-100" 53) 150 .Up == ofAzRatRound refEm100 150 .Up
#guard expM1 (F "1" 53) == ofAzRat refE1 53
#guard expM1 (F "1" 200) == ofAzRat refE1 200

-- small arguments: the cancellation is compensated
#guard (E (F "1/1073741824" 53) 150).1 == ofAzRat refE30 150
#guard E (F "1/1073741824" 53) 150 .Floor == ofAzRatRound refE30 150 .Floor
#guard (E (F "-1/1073741824" 53) 150).1 == ofAzRat refEm30 150
#guard E (F "-1/1073741824" 53) 150 .Ceiling == ofAzRatRound refEm30 150 .Ceiling
#guard E (F "1/1073741824" 53) 53 == ofAzRatRound refE30 53 .Nearest
#guard expM1 (F "-1/1073741824" 53) == ofAzRat refEm30 53

-- tiny arguments: `2^(−200)` at 53 bits is the argument itself, from below or above
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-200))
private def tinyS : String := "1/1606938044258990275541962092341162602522202993782792835301376"
#guard E tiny 53 == (F tinyS 53, .lt)
#guard E (-tiny) 53 == (-F tinyS 53, .lt)
#guard (E tiny 53 .Ceiling).2 == .gt
#guard (E tiny 53 .Floor).1 == F tinyS 53
#guard (E (-tiny) 53 .Floor).2 == .lt
-- the same arguments at a precision that sees the quadratic term
#guard (E tiny 300).1 == ofAzRat refE200 300
#guard E tiny 300 .Floor == ofAzRatRound refE200 300 .Floor
#guard (E (-tiny) 300).1 == ofAzRat refEm200 300
#guard E (-tiny) 300 .Ceiling == ofAzRatRound refEm200 300 .Ceiling

-- directed modes are ordered
#guard (E (F "5/7" 53) 60 .Floor).2 == .lt
#guard (E (F "5/7" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (F "5/7" 53) 60 .Floor).1 (E (F "5/7" 53) 60 .Ceiling).1 == some .lt
#guard partialCompare (E (F "-5/7" 53) 60 .Floor).1 (E (F "-5/7" 53) 60 .Ceiling).1 == some .lt

-- agreement with `exp x − 1` at a higher precision, and `expM1 (lnP1 x) ≈ x`
#guard (E (F "3" 53) 100).1
  == (subPrecRound (expPrecRound (F "3" 53) 300 .Nearest).1 one 100 .Nearest).1
#guard (E (lnP1PrecRound (F "3" 53) 200 .Nearest).1 100).1 == F "3" 100
#guard (E (lnP1PrecRound (F "-1/3" 53) 200 .Nearest).1 100).1
  == (setPrecRound (F "-1/3" 53) 100 .Nearest).1
