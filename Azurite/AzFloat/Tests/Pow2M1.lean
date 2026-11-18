/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.Pow2
import Azurite.AzFloat.Pow2M1
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := pow2M1PrecRound x p m
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
#guard toString (pow2M1 nan) == "NaN"
#guard toString (pow2M1 pinf) == "Infinity"
#guard toString (pow2M1 ninf) == "-1.0"
#guard toString (pow2M1 zero) == "0.0"

-- integer arguments: exact `2^n − 1`
#guard D (E (X "1" 53) 1) == ("1.0", .eq)
#guard D (E (X "-1" 53) 1) == ("-0.5", .eq)
#guard D (E (X "3" 53) 53) == ("7.0", .eq)
#guard D (E (X "-3" 53) 53) == ("-0.875", .eq)
#guard D (E (X "100" 53) 150) == ("1267650600228229401496703205375.0", .eq)
#guard D (E (X "100" 53) 10) == ("1.268e30", .gt)
#guard D (E (X "-100" 53) 10) == ("-1.0", .lt)
#guard D (E (X "-100" 53) 10 .Ceiling) == ("-0.999", .gt)
#guard toString (pow2M1 (X "10" 53)) == "1023.0"
#guard toString (pow2M1 (X "64" 53)) == "1.8446744073709552e19"

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
#guard (E (X "0.5" 53) 150).1 == (subPrecRound (sqrt2PrecRound 300 .Nearest).1 one 150 .Nearest).1
#guard toString (E (X "0.5" 53) 150).1 == "0.4142135623730950488016887242096980785696718755"
#guard D (E (X "0.5" 53) 150 .Floor) == ("0.414213562373095048801688724209698078569671875", .lt)
#guard D (E (X "0.5" 53) 150 .Ceiling) == ("0.4142135623730950488016887242096980785696718755", .gt)
#guard toString (E (X "0.25" 53) 150).1 == "0.1892071150027210667174999705604759152929720924"
#guard toString (E (X "-0.5" 53) 150).1 == "-0.2928932188134524755991556378951509607151640624"
#guard D (E (X "-0.5" 53) 150 .Down) == ("-0.292893218813452475599155637895150960715164062", .gt)
#guard toString (E (X "1.75" 53) 150).1 == "2.36358566101485817212450190493285958016013705"
#guard toString (E (X "-1.75" 53) 150).1 == "-0.702698221249319733320625007359881021176756977"
#guard D (E (X "-1.75" 53) 150 .Up) == ("-0.702698221249319733320625007359881021176756977", .lt)
#guard toString (E (X "0.0009765625\
  " 53) 150).1 == "0.000677130693066356678172784874647194837821984249"
#guard toString (E (X "3.013916015625\
  " 53) 150).1 == "7.07754014493886897441265250833745294040121192"
#guard toString (pow2M1 (X "0.5" 53)) == "0.41421356237309503"
#guard toString (pow2M1 (X "1.75" 200))
  == "2.363585661014858172124501904932859580160137049427138043252905"

-- small arguments: the cancellation is compensated
#guard toString (E (X "0.000000000931322574615478515625" 53) 150).1
  == "6.4554361699491150529813683002781628924414681e-10"
#guard D (E (X "0.000000000931322574615478515625" 53) 150 .Floor)
  == ("6.4554361699491150529813683002781628924414681e-10", .lt)
#guard toString (E (X "-0.000000000931322574615478515625" 53) 150).1
  == "-6.45543616578184944124279003175666007722912427e-10"
#guard D (E (X "-0.000000000931322574615478515625" 53) 150 .Ceiling)
  == ("-6.45543616578184944124279003175666007722912427e-10", .gt)
#guard toString (pow2M1 (X "-0.000000000931322574615478515625" 53)) == "-6.455436165781849e-10"

-- tiny arguments: `2^(±2^(−200)) − 1 ≈ ±ln 2 · 2^(−200)`
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard toString (E tiny 53).1 == "4.313465494430915e-61"
#guard toString (E tiny 300).1
  == "4.313465494430915021157413571165280192569580587457565334503453905936411073212881187677503158\
    e-61"
#guard D (E tiny 300 .Floor)
  == ("4.31346549443091502115741357116528019256958058745756533450345390593641107321288118767750315\
    5e-61", .lt)
#guard toString (E (-tiny) 300).1
  == "-4.31346549443091502115741357116528019256958058745756533450345204533795390859906264735205131\
    e-61"
#guard D (E (-tiny) 300 .Ceiling)
  == ("-4.3134654944309150211574135711652801925695805874575653345034520453379539085990626473520513\
    08e-61", .gt)
#guard (E tiny 53).1 == (mulPrecRound tiny (ln2PrecRound 200 .Nearest).1 53 .Nearest).1

-- directed modes are ordered
#guard (E (X "0.625" 53) 60 .Floor).2 == .lt
#guard (E (X "0.625" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (X "0.625" 53) 60 .Floor).1 (E (X "0.625" 53) 60 .Ceiling).1 == some .lt
#guard partialCompare (E (X "-0.625" 53) 60 .Floor).1 (E (X "-0.625" 53) 60 .Ceiling).1 == some .lt

-- agreement with `2^x − 1` at a higher precision
#guard (E (X "1.75" 53) 100).1
  == (subPrecRound (pow2PrecRound (X "1.75" 53) 300 .Nearest).1 one 100 .Nearest).1

-- tiny arguments: `b^x − 1 ≈ x ln b` is rounded from a bracket at `p + 72` bits whatever the
-- exponent; the result at `2^(−2^30)` is that at `2^(−100)` (the ordinary path) rescaled
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def x100 : AzFloat := (X "1" 53) <<< AzInt.ofInt (-100)
private def rescale (r : AzFloat × Ordering) : AzFloat × Ordering :=
  (r.1 <<< (tinyE + AzInt.ofInt 100), r.2)
#guard pow2M1PrecRound tinyX 53 .Nearest == rescale (pow2M1PrecRound x100 53 .Nearest)
#guard pow2M1PrecRound tinyX 53 .Floor == rescale (pow2M1PrecRound x100 53 .Floor)
#guard pow2M1PrecRound (-tinyX) 53 .Ceiling == rescale (pow2M1PrecRound (-x100) 53 .Ceiling)
#guard pow2M1PrecRound (-tinyX) 80 .Nearest == rescale (pow2M1PrecRound (-x100) 80 .Nearest)

-- a hugely negative exponent: the value is within `2^(−|x|/2)` above `−1`, and one test
-- (`expM1NearNegOne?`) rounds it at a cost independent of `|x|`
private def m1Above : AzFloat := X "-0.9999999999999999" 53
private def hugeNegX : AzFloat :=
  ofAzRat (-(AzNat.ofNat (2 ^ 2000 + 1)).toAzRat * Q "1/2") 2010
private def negX : AzFloat := X "-1000.5" 53
#guard D (pow2M1PrecRound hugeNegX 53 .Nearest) == ("-1.0", .lt)
#guard D (pow2M1PrecRound hugeNegX 53 .Floor) == ("-1.0", .lt)
#guard D (pow2M1PrecRound hugeNegX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard D (pow2M1PrecRound negX 53 .Nearest) == ("-1.0", .lt)
#guard D (pow2M1PrecRound negX 53 .Floor) == ("-1.0", .lt)
#guard D (pow2M1PrecRound negX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard expM1NearNegOne? true 126 53 .Nearest == none
#guard (expM1NearNegOne? true 127 53 .Nearest).map D == some ("-1.0", .lt)
#guard expM1NearNegOne? false 1000 53 .Nearest == none

-- a huge negative integer exponent is rounded before the exact path could materialize it
private def hugeNegInt : AzFloat := (X "-3" 53) <<< AzInt.ofInt (2 ^ 40)
#guard D (pow2M1PrecRound hugeNegInt 53 .Nearest) == ("-1.0", .lt)
#guard D (pow2M1PrecRound hugeNegInt 53 .Ceiling) == ("-0.9999999999999999", .gt)
-- a moderate negative integer still takes the exact path
#guard D (pow2M1PrecRound (X "-3" 53) 53 .Nearest) == ("-0.875", .eq)
#guard D (pow2M1PrecRound (X "-100" 53) 200 .Nearest)
  == ("-0.999999999999999999999999999999211139094778988194588271434717", .eq)
