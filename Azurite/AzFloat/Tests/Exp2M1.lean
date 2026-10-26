/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp2
import Azurite.AzFloat.Exp2M1
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `2^x − 1`

Special values, the exact `2^n − 1` for integers `n` (`2^3 − 1 = 7`, `2^(−3) − 1 = −7/8`,
`2^100 − 1`, `2^(−100) − 1` rounded at low precision), `2^(1/2) − 1 = √2 − 1`, the correctly
rounded values of `2^x − 1` at `x = ±1/2, 1/4, ±7/4, 1/1024, ±2^(−30), ±2^(−200), 12345/4096`
(references from a 200-digit evaluation of `exp (x ln 2) − 1`), the directed modes, and
agreement with `2^x − 1` computed at a higher precision.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := exp2M1PrecRound x p m
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
#guard exp2M1 nan == nan
#guard exp2M1 pinf == infinity true
#guard exp2M1 ninf == F "-1" 1
#guard exp2M1 zero == zero

-- integer arguments: exact `2^n − 1`
#guard E (F "1" 53) 1 == (one, .eq)
#guard E (F "-1" 53) 1 == (F "-1/2" 1, .eq)
#guard E (F "3" 53) 53 == (F "7" 53, .eq)
#guard E (F "-3" 53) 53 == (F "-7/8" 53, .eq)
#guard E (F "100" 53) 150 == (F "1267650600228229401496703205375" 150, .eq)
#guard E (F "100" 53) 10 == (F "1267650600228229401496703205376" 10, .gt)
#guard E (F "-100" 53) 10 == (F "-1" 10, .lt)
#guard E (F "-100" 53) 10 .Ceiling == (F "-1023/1024" 10, .gt)
#guard exp2M1 (F "10" 53) == F "1023" 53
#guard exp2M1 (F "64" 53) == F "18446744073709551616" 53

private def refHalf : AzRat :=
  R ("4142135623730950488016887242096980785696718753769480731766797379907324784621070388503875" ++
    "3432764157273501384623091229702492483605585073721264412149709993583141322266592750559275" ++
    "579995050115278206057147") 200
private def refQuarter : AzRat :=
  R ("1892071150027210667174999705604759152929720924638174130190022247194666682269171598707813" ++
    "4453813767371603739477476921318606372636178984775678536086253801777507015151140355709227" ++
    "316234286888992417544607") 200
private def refNegHalf : AzRat :=
  R ("-292893218813452475599155637895150960715164062311525963411660131004633760768946480574806" ++
    "2328361792136324930768845438514875375819720746313936779392514500320842933886670362472036" ++
    "2210002474942360896971426") 200
private def ref1024 : AzRat :=
  R ("6771306930663566781727848746471948378219842487376938696040679547579958003103997203954325" ++
    "5696752726563760483930754222784797268503329849736797033589993456850570059571628519026022" ++
    "760572409250616529437468") 203
private def ref30 : AzRat :=
  R ("6455436169949115052981368300278162892441468097374788490400875024485950159762828490330126" ++
    "1721720614482181596017391715275809328186850836884374307303061198482070603099142766803130" ++
    "308161195003256840932761") 209
private def refNeg30 : AzRat :=
  R ("-645543616578184944124279003175666007722912427460953321367140660548388299296811629637245" ++
    "3106963369046722579138330507749203316026789087635404774744442876482844791516659298797218" ++
    "8333292512988075398384242") 209
private def ref74 : AzRat :=
  R ("2363585661014858172124501904932859580160137049427138043252904343899699019815608959257296" ++
    "0167971701446912062949740763403207555052967118171533068857406478082015836973862848521538" ++
    "373292957753157671780043") 199
private def refNeg74 : AzRat :=
  R ("-702698221249319733320625007359881021176756976884045646745249443820133332943270710032304" ++
    "6638654655815709906513063076967034840684095525380608036597843654955562324621221491107269" ++
    "3170941428277751895613848") 200
private def ref200 : AzRat :=
  R ("4313465494430915021157413571165280192569580587457565334503453905936411073212881187677503" ++
    "157326464145129205767506190415235961579223988051638076402795388527809526679759967") 229
private def refNeg200 : AzRat :=
  R ("-431346549443091502115741357116528019256958058745756533450345204533795390859906264735205" ++
    "13096671492796647491883130927595789107270382294996868955924478935644040789293219510") 230
private def ref12345 : AzRat :=
  R ("7077540144938868974412652508337452940401211922693780486105932056212090027550120554883279" ++
    "3060945318872193146584598431859325509540538191765442285612966490744188690775523295375546" ++
    "043547355823630130081193") 199

-- `√2 − 1` and moderate arguments
#guard (E (F "1/2" 53) 150).1 == (subPrecRound (sqrt2PrecRound 300 .Nearest).1 one 150 .Nearest).1
#guard (E (F "1/2" 53) 150).1 == ofAzRat refHalf 150
#guard E (F "1/2" 53) 150 .Floor == ofAzRatRound refHalf 150 .Floor
#guard E (F "1/2" 53) 150 .Ceiling == ofAzRatRound refHalf 150 .Ceiling
#guard (E (F "1/4" 53) 150).1 == ofAzRat refQuarter 150
#guard (E (F "-1/2" 53) 150).1 == ofAzRat refNegHalf 150
#guard E (F "-1/2" 53) 150 .Down == ofAzRatRound refNegHalf 150 .Down
#guard (E (F "7/4" 53) 150).1 == ofAzRat ref74 150
#guard (E (F "-7/4" 53) 150).1 == ofAzRat refNeg74 150
#guard E (F "-7/4" 53) 150 .Up == ofAzRatRound refNeg74 150 .Up
#guard (E (F "1/1024" 53) 150).1 == ofAzRat ref1024 150
#guard (E (F "12345/4096" 53) 150).1 == ofAzRat ref12345 150
#guard exp2M1 (F "1/2" 53) == ofAzRat refHalf 53
#guard exp2M1 (F "7/4" 200) == ofAzRat ref74 200

-- small arguments: the cancellation is compensated
#guard (E (F "1/1073741824" 53) 150).1 == ofAzRat ref30 150
#guard E (F "1/1073741824" 53) 150 .Floor == ofAzRatRound ref30 150 .Floor
#guard (E (F "-1/1073741824" 53) 150).1 == ofAzRat refNeg30 150
#guard E (F "-1/1073741824" 53) 150 .Ceiling == ofAzRatRound refNeg30 150 .Ceiling
#guard exp2M1 (F "-1/1073741824" 53) == ofAzRat refNeg30 53

-- tiny arguments: `2^(±2^(−200)) − 1 ≈ ±ln 2 · 2^(−200)`
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard (E tiny 53).1 == ofAzRat ref200 53
#guard (E tiny 300).1 == ofAzRat ref200 300
#guard E tiny 300 .Floor == ofAzRatRound ref200 300 .Floor
#guard (E (-tiny) 300).1 == ofAzRat refNeg200 300
#guard E (-tiny) 300 .Ceiling == ofAzRatRound refNeg200 300 .Ceiling
#guard (E tiny 53).1 == (mulPrecRound tiny (ln2PrecRound 200 .Nearest).1 53 .Nearest).1

-- directed modes are ordered
#guard (E (F "5/8" 53) 60 .Floor).2 == .lt
#guard (E (F "5/8" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (F "5/8" 53) 60 .Floor).1 (E (F "5/8" 53) 60 .Ceiling).1 == some .lt
#guard partialCompare (E (F "-5/8" 53) 60 .Floor).1 (E (F "-5/8" 53) 60 .Ceiling).1 == some .lt

-- agreement with `2^x − 1` at a higher precision
#guard (E (F "7/4" 53) 100).1
  == (subPrecRound (exp2PrecRound (F "7/4" 53) 300 .Nearest).1 one 100 .Nearest).1
