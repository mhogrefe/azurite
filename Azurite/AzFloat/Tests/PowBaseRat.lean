/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow2Rat
import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `u^q` with a natural base and a rational exponent

Special values (`0^q`, `1^q`, `u^0`), the exact rational powers (`8^(1/3) = 2`,
`8^(−2/3) = 1/4`, `27^(4/3) = 81`, `1000^(1/3) = 10`, `1000^(−1/3)`, `2^(10/2) = 32`, `3^40`),
agreement with the float `u^x` on dyadic exponents and with `2^q`, the correctly rounded values
of `3^(1/3)`, `10^(1/3)`, `7^(−2/3)`, `10^(22/7)`, `12345^(1/10)`, `(2^64 − 1)^(1/7)`,
`6^(301/3)` and `10^(−401/6)` (references from a 200-digit evaluation of `exp (q ln u)`), and
the directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBaseRatPrecRound u (Q q) p m

-- special values
#guard E 0 "0" 53 == (F "1" 53, .eq)
#guard E 0 "0" 0 == (nan, .eq)
#guard E 0 "1/3" 53 == (zero, .eq)
#guard E 0 "1/3" 0 == (zero, .eq)
#guard E 0 "-1/3" 53 == (infinity true, .eq)
#guard E 1 "1/3" 53 == (F "1" 53, .eq)
#guard E 1 "-1000" 7 == (F "1" 7, .eq)
#guard E 1 "1/3" 0 == (nan, .eq)
#guard E 7 "0" 53 == (F "1" 53, .eq)
#guard E 7 "0" 1 == (one, .eq)
#guard E 7 "1/3" 0 == (nan, .eq)
#guard powBaseRat 0 (Q "-2") 53 == infinity true
#guard powBaseRat 5 (Q "0") 53 == F "1" 53

-- exact rational powers
#guard E 8 "1/3" 53 == (F "2" 53, .eq)
#guard E 8 "-2/3" 53 == (F "1/4" 53, .eq)
#guard E 27 "4/3" 53 == (F "81" 53, .eq)
#guard E 1000 "1/3" 53 == (F "10" 53, .eq)
#guard E 1000 "-1/3" 53 == ofAzRatRound (Q "1/10") 53 .Nearest
#guard E 1000 "-1/3" 53 .Floor == ofAzRatRound (Q "1/10") 53 .Floor
#guard E 2 "10/2" 53 == (F "32" 53, .eq)
#guard E 4 "1/2" 1 == (F "2" 1, .eq)
#guard E 3 "40" 20 == ofAzRatRound (Q "12157665459056928801") 20 .Nearest
#guard E 3 "-40" 20 .Ceiling == ofAzRatRound (Q "1/12157665459056928801") 20 .Ceiling
#guard E 1024 "1/10" 53 == (F "2" 53, .eq)
#guard E 1024 "-3/10" 53 == (F "1/8" 53, .eq)
#guard (E 1024 "1/11" 53).2 != .eq
#guard powBaseRat 8 (Q "1/3") 53 == F "2" 53

-- agreement with the float `u^x` and with `2^q`
#guard E 3 "1/2" 150 == powBasePrecRound 3 (F "1/2" 53) 150 .Nearest
#guard E 7 "-7/4" 150 .Floor == powBasePrecRound 7 (F "-7/4" 53) 150 .Floor
#guard E 12345 "5/4" 150 == powBasePrecRound 12345 (F "5/4" 53) 150 .Nearest
#guard E 2 "1/3" 150 == pow2RatPrecRound (Q "1/3") 150 .Nearest
#guard E 2 "-10/3" 150 .Ceiling == pow2RatPrecRound (Q "-10/3") 150 .Ceiling

private def ref3Third : AzRat :=
  R ("1442249570307408382321638310780109588391869253499350577546416194541687596829997339854755" ++
    "4797056452566868350808544895499664254239461102597148689501571852372270903320238475984450" ++
    "610855400272600881454989") 199
private def ref10Third : AzRat :=
  R ("2154434690031883721759293566519350495259344942192108582489235506346411106648340800185441" ++
    "5035432432761012612204917809204465575051000832749571206753778093319327305836534892638281" ++
    "254969314038783827968633") 199
private def ref7Neg23 : AzRat :=
  R ("2732758832531984430284452627926800404089198643351251094586639486353191823113186794296464" ++
    "9163961224427207741627982725131827780218483774457330678381367320651629141259566878162567" ++
    "180382077808743486587825") 200
private def ref10_22_7 : AzRat :=
  R ("1389495494373137637129985217353011622113046714491000204945628679031600242410316581384175" ++
    "6389754214323881923266149080532501908980741273813959901199701429753073470907628244009525" ++
    "403778763687048007997790") 196
private def ref12345Tenth : AzRat :=
  R ("2565364670309510515116329975018743199758175129929634043629305507944240078263393161935400" ++
    "8138215912070775784163544441141836556326925566254719763217233753014246680876312483634937" ++
    "152210687913391106391423") 199
private def refMaxSeventh : AzRat :=
  R ("5652938310009919168721689527512672899477509625481869637923603031212209466029358990459495" ++
    "7173133421999595198270557896620194140493113578125878741733504160463083322635144132863375" ++
    "604122889981160394130016") 197
private def ref6Big : AzRat :=
  R ("1187158724442726293435019232164744577588801714784285541472358200083048270041863985952284" ++
    "6431571437624918703843911131780638032839304902020867334279053787496418124988493851610513" ++
    "122614029183453267416294") 121
private def ref10NegBig : AzRat :=
  R ("1467799267622069540920517114816861254795642657005173995948382357857372407010341426059594" ++
    "9768932886269163273326088757686788421234787744098000034452459294765039239717790327283438" ++
    "972143374655049437279144") 266
private def ref2Third : AzRat :=
  R ("1259921049894873164767210607278228350570251464701507980081975112155299676513959483729396" ++
    "5624362550941543102560356156652593990240406137372284591103042693552469606426166250009774" ++
    "745265654803068671854055") 199

-- correctly rounded irrational powers
#guard (E 2 "1/3" 150).1 == ofAzRat ref2Third 150
#guard (E 3 "1/3" 150).1 == ofAzRat ref3Third 150
#guard E 3 "1/3" 150 .Floor == ofAzRatRound ref3Third 150 .Floor
#guard E 3 "1/3" 150 .Ceiling == ofAzRatRound ref3Third 150 .Ceiling
#guard (E 10 "1/3" 150).1 == ofAzRat ref10Third 150
#guard (E 7 "-2/3" 150).1 == ofAzRat ref7Neg23 150
#guard E 7 "-2/3" 150 .Up == ofAzRatRound ref7Neg23 150 .Up
#guard (E 10 "22/7" 150).1 == ofAzRat ref10_22_7 150
#guard E 10 "22/7" 150 .Down == ofAzRatRound ref10_22_7 150 .Down
#guard (E 12345 "1/10" 150).1 == ofAzRat ref12345Tenth 150
#guard (E 18446744073709551615 "1/7" 150).1 == ofAzRat refMaxSeventh 150
#guard E 18446744073709551615 "1/7" 150 .Floor == ofAzRatRound refMaxSeventh 150 .Floor
#guard (E 6 "301/3" 150).1 == ofAzRat ref6Big 150
#guard (E 10 "-401/6" 150).1 == ofAzRat ref10NegBig 150
#guard E 10 "-401/6" 150 .Ceiling == ofAzRatRound ref10NegBig 150 .Ceiling
#guard powBaseRat 10 (Q "1/3") 53 == ofAzRat ref10Third 53
#guard powBaseRat 3 (Q "1/3") 200 == ofAzRat ref3Third 200

-- directed modes are ordered
#guard (E 7 "5/7" 60 .Floor).2 == .lt
#guard (E 7 "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 "5/7" 60 .Floor).1 (E 7 "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E 7 "-5/7" 60 .Floor).1 (E 7 "-5/7" 60 .Ceiling).1 == some .lt
