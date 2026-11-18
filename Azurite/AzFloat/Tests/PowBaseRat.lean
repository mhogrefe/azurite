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
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBaseRatPrecRound u (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E 0 "0" 53) == ("1.0", .eq)
#guard D (E 0 "0" 0) == ("NaN", .eq)
#guard D (E 0 "1/3" 53) == ("0.0", .eq)
#guard D (E 0 "1/3" 0) == ("0.0", .eq)
#guard D (E 0 "-1/3" 53) == ("Infinity", .eq)
#guard D (E 1 "1/3" 53) == ("1.0", .eq)
#guard D (E 1 "-1000" 7) == ("1.0", .eq)
#guard D (E 1 "1/3" 0) == ("NaN", .eq)
#guard D (E 7 "0" 53) == ("1.0", .eq)
#guard D (E 7 "0" 1) == ("1.0", .eq)
#guard D (E 7 "1/3" 0) == ("NaN", .eq)
#guard toString (powBaseRat 0 (Q "-2") 53) == "Infinity"
#guard toString (powBaseRat 5 (Q "0") 53) == "1.0"

-- exact rational powers
#guard D (E 8 "1/3" 53) == ("2.0", .eq)
#guard D (E 8 "-2/3" 53) == ("0.25", .eq)
#guard D (E 27 "4/3" 53) == ("81.0", .eq)
#guard D (E 1000 "1/3" 53) == ("1.0e1", .eq)
#guard D (E 1000 "-1/3" 53) == ("0.1", .gt)
#guard D (E 1000 "-1/3" 53 .Floor) == ("0.09999999999999999", .lt)
#guard D (E 2 "10/2" 53) == ("32.0", .eq)
#guard D (E 4 "1/2" 1) == ("2.0", .eq)
#guard D (E 3 "40" 20) == ("1.215766e19", .lt)
#guard D (E 3 "-40" 20 .Ceiling) == ("8.22527e-20", .gt)
#guard D (E 1024 "1/10" 53) == ("2.0", .eq)
#guard D (E 1024 "-3/10" 53) == ("0.125", .eq)
#guard (E 1024 "1/11" 53).2 != .eq
#guard toString (powBaseRat 8 (Q "1/3") 53) == "2.0"

-- agreement with the float `u^x` and with `2^q`
#guard E 3 "1/2" 150 == powBasePrecRound 3 (X "0.5" 53) 150 .Nearest
#guard E 7 "-7/4" 150 .Floor == powBasePrecRound 7 (X "-1.75" 53) 150 .Floor
#guard E 12345 "5/4" 150 == powBasePrecRound 12345 (X "1.25" 53) 150 .Nearest
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
#guard toString (E 2 "1/3" 150).1 == "1.259921049894873164767210607278228350570251465"
#guard toString (E 3 "1/3" 150).1 == "1.442249570307408382321638310780109588391869254"
#guard D (E 3 "1/3" 150 .Floor) == ("1.442249570307408382321638310780109588391869253", .lt)
#guard D (E 3 "1/3" 150 .Ceiling) == ("1.442249570307408382321638310780109588391869254", .gt)
#guard toString (E 10 "1/3" 150).1 == "2.154434690031883721759293566519350495259344943"
#guard toString (E 7 "-2/3" 150).1 == "0.2732758832531984430284452627926800404089198643"
#guard D (E 7 "-2/3" 150 .Up) == ("0.2732758832531984430284452627926800404089198646", .gt)
#guard toString (E 10 "22/7" 150).1 == "1389.495494373137637129985217353011622113046714"
#guard D (E 10 "22/7" 150 .Down) == ("1389.495494373137637129985217353011622113046714", .lt)
#guard toString (E 12345 "1/10" 150).1 == "2.56536467030951051511632997501874319975817513"
#guard toString (E 18446744073709551615 "1/7" 150).1
  == "565.2938310009919168721689527512672899477509626"
#guard D (E 18446744073709551615 "1/7" 150 .Floor)
  == ("565.293831000991916872168952751267289947750962", .lt)
#guard toString (E 6 "301/3" 150).1 == "1.187158724442726293435019232164744577588801714e78"
#guard toString (E 10 "-401/6" 150).1 == "1.467799267622069540920517114816861254795642657e-67"
#guard D (E 10 "-401/6" 150 .Ceiling)
  == ("1.467799267622069540920517114816861254795642657e-67", .gt)
#guard toString (powBaseRat 10 (Q "1/3") 53) == "2.154434690031884"
#guard toString (powBaseRat 3 (Q "1/3") 200)
  == "1.442249570307408382321638310780109588391869253499350577546416"

-- directed modes are ordered
#guard (E 7 "5/7" 60 .Floor).2 == .lt
#guard (E 7 "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 "5/7" 60 .Floor).1 (E 7 "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E 7 "-5/7" 60 .Floor).1 (E 7 "-5/7" 60 .Ceiling).1 == some .lt

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (powBaseRatPrecRound 10 tinyQ 53 .Nearest) == ("1.0", .lt)
#guard D (powBaseRatPrecRound 10 tinyQ 53 .Floor) == ("1.0", .lt)
#guard D (powBaseRatPrecRound 10 tinyQ 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (powBaseRatPrecRound 10 (-tinyQ) 53 .Nearest) == ("1.0", .gt)
#guard D (powBaseRatPrecRound 10 (-tinyQ) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (powBaseRatPrecRound 10 (-tinyQ) 53 .Ceiling) == ("1.0", .gt)

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
private def big10Neg : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838857")).num.toNat
  ((X "6097604244814858" 53) <<< AzInt.ofInt (-sh), .gt)
private def qBig : String :=
  "180757491466083601275914342040210831203079405498045645898146"
    ++ "15495784533354117888362407517472960964820051322203809232453633/3"
private def q200 : String :=
  "482081413277697082662588627702348780756660898134837850590412"
    ++ "8"
#guard E 3 qBig 53 == big3
#guard E 10 q200 53 == big10
#guard E 10 ("-" ++ q200) 53 == big10Neg
#guard E 10 q200 53 == powBasePrecRound 10 ((X "3" 53) <<< AzInt.ofInt 200) 53 .Nearest
