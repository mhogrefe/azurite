/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Pow2M1Rat
import Azurite.AzFloat.PowBaseM1
import Azurite.AzFloat.PowBaseM1Rat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `u^q − 1` with a natural base and a rational exponent

Special values (`0^q − 1`, `1^q − 1`, `u^0 − 1`), the exact `r^n − 1` (`8^(1/3) − 1 = 1`,
`8^(−2/3) − 1 = −3/4`, `27^(4/3) − 1 = 80`, `1000^(−1/3) − 1 = −9/10`, `1024^(1/10) − 1 = 1`,
`3^40 − 1`), agreement with the float `u^x − 1` on dyadic exponents and with `2^q − 1`, the
correctly rounded values of `3^(1/3) − 1`, `10^(−1/3) − 1`, `7^(22/7) − 1`, `12345^(1/10) − 1`,
`(2^64 − 1)^(1/7) − 1`, `6^(301/3) − 1`, `10^(−401/6) − 1` and the small arguments
`10^(±10^(−6)) − 1`, `10^(±10^(−60)) − 1` (references from a 200-digit evaluation of
`exp (q ln u) − 1`), and the directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBaseM1RatPrecRound u (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E 0 "0" 53) == ("0.0", .eq)
#guard D (E 0 "0" 0) == ("0.0", .eq)
#guard D (E 0 "1/3" 53) == ("-1.0", .eq)
#guard D (E 0 "1/3" 0) == ("NaN", .eq)
#guard D (E 0 "-1/3" 53) == ("Infinity", .eq)
#guard D (E 0 "-1/3" 0) == ("Infinity", .eq)
#guard D (E 1 "1/3" 53) == ("0.0", .eq)
#guard D (E 1 "-1000" 0) == ("0.0", .eq)
#guard D (E 7 "0" 53) == ("0.0", .eq)
#guard D (E 7 "0" 0) == ("0.0", .eq)
#guard D (E 7 "1/3" 0) == ("NaN", .eq)
#guard toString (powBaseM1Rat 0 (Q "-2") 53) == "Infinity"
#guard toString (powBaseM1Rat 5 (Q "0") 53) == "0.0"

-- exact rational powers
#guard D (E 8 "1/3" 53) == ("1.0", .eq)
#guard D (E 8 "-2/3" 53) == ("-0.75", .eq)
#guard D (E 27 "4/3" 53) == ("8.0e1", .eq)
#guard D (E 1000 "-1/3" 53) == ("-0.9", .lt)
#guard D (E 1000 "-1/3" 53 .Floor) == ("-0.9", .lt)
#guard D (E 1024 "1/10" 53) == ("1.0", .eq)
#guard D (E 1024 "-3/10" 53) == ("-0.875", .eq)
#guard D (E 2 "10/2" 53) == ("31.0", .eq)
#guard D (E 3 "40" 20) == ("1.215766e19", .lt)
#guard D (E 3 "-40" 20 .Ceiling) == ("-0.999999", .gt)
#guard (E 1024 "1/11" 53).2 != .eq
#guard toString (powBaseM1Rat 8 (Q "1/3") 53) == "1.0"

-- agreement with the float `u^x − 1` and with `2^q − 1`
#guard E 3 "1/2" 150 == powBaseM1PrecRound 3 (X "0.5" 53) 150 .Nearest
#guard E 7 "-7/4" 150 .Floor == powBaseM1PrecRound 7 (X "-1.75" 53) 150 .Floor
#guard E 10 "1/1073741824" 150 == powBaseM1PrecRound 10 (X "0.000000000931322574615478515625" 53)
    150 .Nearest
#guard E 2 "1/3" 150 == pow2M1RatPrecRound (Q "1/3") 150 .Nearest
#guard E 2 "-10/3" 150 .Ceiling == pow2M1RatPrecRound (Q "-10/3") 150 .Ceiling
#guard E 2 "1/1000000" 150 == pow2M1RatPrecRound (Q "1/1000000") 150 .Nearest

private def ref3Third : AzRat :=
  R ("4422495703074083823216383107801095883918692534993505775464161945416875968299973398547554" ++
    "7970564525668683508085448954996642542394611025971486895015718523722709033202384759844506" ++
    "108554002726008814549887") 200
private def ref10NegThird : AzRat :=
  R ("-535841116638722110758992364908055342344865087498875636234930714131522213030715517381004" ++
    "0929102428620158456691771734595179489729712504225622637677604969785349058225732803490837" ++
    "0454785391023663306189588") 200
private def ref7_22_7 : AzRat :=
  R ("4519209519803504605905992747045902373786538521268618803683128219056524080729419510380689" ++
    "8666447292200619985077406236188707011168086532520500540749683970698475035275656278484942" ++
    "506917768815267314924466") 197
private def ref12345Tenth : AzRat :=
  R ("1565364670309510515116329975018743199758175129929634043629305507944240078263393161935400" ++
    "8138215912070775784163544441141836556326925566254719763217233753014246680876312483634937" ++
    "152210687913391106391423") 199
private def refMaxSeventh : AzRat :=
  R ("5642938310009919168721689527512672899477509625481869637923603031212209466029358990459495" ++
    "7173133421999595198270557896620194140493113578125878741733504160463083322635144132863375" ++
    "604122889981160394130016") 197
private def ref10Micro : AzRat :=
  R ("2302587743945135602980545900009792650478115166377098017188031373794388675356178723827707" ++
    "0845685158178152829930646224884828751259330200653835876836451899091428072603696782744834" ++
    "298560890690237744223712") 205
private def ref10NegMicro : AzRat :=
  R ("-230258244204702512224002504051845613840651456147292561786512505613440237910074099430663" ++
    "3141179789553931141088767005881824439775779766730179895011372453999485101430681175871165" ++
    "0440904869740438604099281") 205
private def ref10Tiny : AzRat :=
  R ("2302585092994045684017991454684364207601101488628772976033330551916627848876357761069191" ++
    "5020984440970670073504471569273352712661453432145131812446980206313004834335383782698341" ++
    "638601393092348414248307") 259
private def ref10NegTiny : AzRat :=
  R ("-230258509299404568401799145468436420760110148862877297603332525001851737047834719940280" ++
    "2908080752499616928217637415569935617141969409351393813312423604553138964490931228275474" ++
    "6062231048948349235559609") 259
private def ref6Big : AzRat :=
  R ("1187158724442726293435019232164744577588801714784285541472358200083048270041862985952284" ++
    "6431571437624918703843911131780638032839304902020867334279053787496418124988493851610513" ++
    "122614029183453267416294") 121
private def ref10NegBig : AzRat :=
  R ("-999999999999999999999999999999999999999999999999999999999999999999853220073237793045907" ++
    "9482885183138745204357342994826004051617642142627592989658573940405023106711373083672667" ++
    "3911242313211578765212256") 200

-- correctly rounded irrational values
#guard toString ((E 3 "1/3" 150).1) == "0.4422495703074083823216383107801095883918692535"
#guard D (E 3 "1/3" 150 .Floor) == ("0.4422495703074083823216383107801095883918692535", .lt)
#guard D (E 3 "1/3" 150 .Ceiling) == ("0.4422495703074083823216383107801095883918692538", .gt)
#guard toString ((E 10 "-1/3" 150).1) == "-0.535841116638722110758992364908055342344865087"
#guard D (E 10 "-1/3" 150 .Up) == ("-0.535841116638722110758992364908055342344865088", .lt)
#guard toString ((E 7 "22/7" 150).1) == "451.9209519803504605905992747045902373786538522"
#guard D (E 7 "22/7" 150 .Down) == ("451.920951980350460590599274704590237378653852", .lt)
#guard toString ((E 12345 "1/10" 150).1) == "1.56536467030951051511632997501874319975817513"
#guard (E 18446744073709551615 "1/7" 150).1 == ofAzRat refMaxSeventh 150
#guard toString ((E 6 "301/3" 150).1) == "1.187158724442726293435019232164744577588801714e78"
#guard toString ((E 10 "-401/6" 150).1) == "-1.0"
#guard D (E 10 "-401/6" 150 .Ceiling) == ("-0.999999999999999999999999999999999999999999999", .gt)
#guard toString (powBaseM1Rat 10 (Q "-1/3") 53) == "-0.5358411166387221"
#guard toString (powBaseM1Rat 3 (Q "1/3") 200) == "0.4422495703074083823216383107801095883918692534\
  993505775464163"

-- small and tiny arguments: the cancellation is compensated
#guard toString ((E 10 "1/1000000" 150).1) == "2.302587743945135602980545900009792650478115167e-6"
#guard D (E 10 "1/1000000" 150 .Floor) == ("2.302587743945135602980545900009792650478115164e-6\
  ", .lt)
#guard toString ((E 10 "-1/1000000" 150).1) == "-2.30258244204702512224002504051845613840651456e-6"
#guard D (E 10 "-1/1000000" 150 .Ceiling) == ("-2.30258244204702512224002504051845613840651456e-6\
  ", .gt)
#guard toString ((E 10 "1/1000000000000000000000000000000000000000000000000000000000000" 53).1)
  == "2.3025850929940456e-60"
#guard toString ((E 10 "1/1000000000000000000000000000000000000000000000000000000000000" 300).1)
  == "2.302585092994045684017991454684364207601101488628772976033330551916627848876357761069191502e\
  -60"
#guard D (E 10 "-1/1000000000000000000000000000000000000000000000000000000000000" 300 .Ceiling)
  == ("-2.30258509299404568401799145468436420760110148862877297603332525001851737047834719940280290\
  7e-60", .gt)
#guard toString (powBaseM1Rat 10 (Q "-1/1000000") 53) == "-2.302582442047025e-6"

-- directed modes are ordered
#guard (E 7 "5/7" 60 .Floor).2 == .lt
#guard (E 7 "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 "5/7" 60 .Floor).1 (E 7 "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E 7 "-5/7" 60 .Floor).1 (E 7 "-5/7" 60 .Ceiling).1 == some .lt

-- tiny rational arguments: `q = ±1/(3·2^1000)` against `±1/(3·2^100)` (the ordinary path)
private def tq (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< k)
private def rescale (r : AzFloat × Ordering) : AzFloat × Ordering :=
  (r.1 <<< AzInt.ofInt (-900), r.2)
#guard powBaseM1RatPrecRound 10 (tq 1000) 53 .Nearest
  == rescale (powBaseM1RatPrecRound 10 (tq 100) 53 .Nearest)
#guard powBaseM1RatPrecRound 10 (-(tq 1000)) 53 .Ceiling
  == rescale (powBaseM1RatPrecRound 10 (-(tq 100)) 53 .Ceiling)

-- huge exponents: the starting precision of Ziv's loop is logarithmic in the exponent of `x`
-- (`lnMulW₀`), only the bracket of `x ln u` works at `p + e` bits; references from 700-digit
-- decimal arithmetic (`u^x = sig · 2^shift` with the 53-bit significand rounded to nearest)
private def big3 : AzFloat × Ordering :=
  let sh : Int := (Q ("9549794856605563740070467985241666727522968810983092175470230050049636"
    ++ "697480851670010552523856060425328708852050992822989")).num.toNat
  ((X "8158923442829460" 53) <<< AzInt.ofInt (sh), .lt)
private def big10 : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838752")).num.toNat
  ((X "6652583142272300" 53) <<< AzInt.ofInt (sh), .gt)
private def qBig : String :=
  "180757491466083601275914342040210831203079405498045645898146"
    ++ "15495784533354117888362407517472960964820051322203809232453633/3"
private def q200 : String :=
  "482081413277697082662588627702348780756660898134837850590412"
    ++ "8"
#guard E 3 qBig 53 == big3
#guard E 10 q200 53 == big10
#guard E 10 ("-" ++ q200) 53 == (X "-1" 53, .lt)

-- a hugely negative exponent: the value is within `2^(−|x|/2)` above `−1`, and one test
-- (`expM1NearNegOne?`) rounds it at a cost independent of `|x|`
private def m1Above : AzFloat := X "-0.9999999999999999" 53
private def hugeNegX : AzRat :=
  -((AzNat.ofNat 1) <<< (100000 : Nat)).toAzRat * Q "1/3"
private def negX : AzRat := Q "-2001/2"
#guard powBaseM1RatPrecRound 10 hugeNegX 53 .Nearest == (X "-1" 53, .lt)
#guard powBaseM1RatPrecRound 10 hugeNegX 53 .Floor == (X "-1" 53, .lt)
#guard powBaseM1RatPrecRound 10 hugeNegX 53 .Ceiling == (m1Above, .gt)
#guard powBaseM1RatPrecRound 10 negX 53 .Nearest == (X "-1" 53, .lt)
#guard powBaseM1RatPrecRound 10 negX 53 .Floor == (X "-1" 53, .lt)
#guard powBaseM1RatPrecRound 10 negX 53 .Ceiling == (m1Above, .gt)
#guard expM1NearNegOne? true 126 53 .Nearest == none
#guard expM1NearNegOne? true 127 53 .Nearest == some (X "-1" 53, .lt)
#guard expM1NearNegOne? false 1000 53 .Nearest == none
