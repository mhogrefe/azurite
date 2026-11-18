/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow2M1
import Azurite.AzFloat.Pow2M1Rat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `2^q − 1` of a rational

`2^0 − 1 = 0`, the exact `2^n − 1` for integers `n`, agreement with the float `2^x − 1` on dyadic
rationals, the correctly rounded values of `2^q − 1` at `q = ±1/3, 10/3, 1/10, 22/7, 123.456,
±10^(−6), ±10^(−60)` (references from a 200-digit evaluation of `exp (q ln 2) − 1`), and the
directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := pow2M1RatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- zero, integers and precision `0`
#guard D (E "0" 53) == ("0.0", .eq)
#guard D (E "0" 0) == ("NaN", .eq)
#guard D (E "1/3" 0) == ("NaN", .eq)
#guard D (E "1" 1) == ("1.0", .eq)
#guard D (E "-1" 1) == ("-0.5", .eq)
#guard D (E "3" 53) == ("7.0", .eq)
#guard D (E "-3" 53) == ("-0.875", .eq)
#guard D (E "100" 150) == ("1267650600228229401496703205375.0", .eq)
#guard D (E "100" 10) == ("1.268e30", .gt)
#guard D (E "-100" 10) == ("-1.0", .lt)
#guard D (E "-100" 10 .Ceiling) == ("-0.999", .gt)
#guard toString (pow2M1Rat (Q "10") 53) == "1023.0"

-- agreement with the float `2^x − 1` on dyadic rationals
#guard E "1/2" 150 == pow2M1PrecRound (X "0.5" 53) 150 .Nearest
#guard E "1/2" 150 .Floor == pow2M1PrecRound (X "0.5" 53) 150 .Floor
#guard E "-7/4" 150 == pow2M1PrecRound (X "-1.75" 53) 150 .Nearest
#guard E "12345/4096" 100 .Ceiling == pow2M1PrecRound (X "3.013916015625" 53) 100 .Ceiling
#guard E "1/1073741824" 150 == pow2M1PrecRound (X "0.000000000931322574615478515625\
  " 53) 150 .Nearest
#guard E "-1/1073741824" 150 .Up == pow2M1PrecRound (X "-0.000000000931322574615478515625\
  " 53) 150 .Up

private def refThird : AzRat :=
  R ("2599210498948731647672106072782283505702514647015079800819751121552996765139594837293965" ++
    "6243625509415431025603561566525939902404061373722845911030426935524696064261662500097747" ++
    "452656548030686718540552") 200
private def refTen3 : AzRat :=
  R ("9079368399158985318137684858225826804562011717612063840655800897242397412111675869835172" ++
    "4994900407532344820482849253220751921923249098978276728824341548419756851409330000078197" ++
    "962125238424549374832441") 199
private def refNegThird : AzRat :=
  R ("-206299474015900262624147180363845869804253336050073495095857119087391747187890413363227" ++
    "8933688895214885326191593389910482511700509236238609299944777292766903122408607187815633" ++
    "5474375746385383127511286") 200
private def refTenth : AzRat :=
  R ("7177346253629316421300632502334202290638460497755678348278066814424543883746895451690744" ++
    "3983687769866393036548139521082376815013417416448812541823889953456652257669347408168095" ++
    "223946974002637187218233") 201
private def ref227 : AzRat :=
  R ("7832716109390498701196043100986757770602612806240993324116259713136850583043047845732786" ++
    "3190904160411751772725246394500317537174434468463720851844671046556931135891513772467051" ++
    "640987517981071606312532") 199
private def refBig : AzRat :=
  R ("1458677031955785148317937357186622240085857387481039782818850322498201376355228161031215" ++
    "9007408476441095510351517300887581881086225370537529561050950104294001043260487155767228" ++
    "230371364759416039894948") 162
private def refMicro : AzRat :=
  R ("6931474207865077726362274070303773195118972218601966230792941802609972760457045850155298" ++
    "2884935168933561054363111062323532794117191100138140197054577855031192833515736512149428" ++
    "091931801001418070701880") 206
private def refNegMicro : AzRat :=
  R ("-693146940333493854415566481712593730452359480525085111473872091495856193198268944187055" ++
    "2885265420666023707746603900911341465897299311924642977875578097875901354427783519188230" ++
    "4725796672273287299561193") 206
private def refTiny : AzRat :=
  R ("6931471805599453094172321214581765680755001343602552541206802497199005810704070491571264" ++
    "903289045528184772782933641191658078361771140820542219129895354196827855483428520") 229
private def refNegTiny : AzRat :=
  R ("-693147180559945309417232121458176568075500134360255254120679769266886662868982382054600" ++
    "16366393282226552568374777725230167421251173182221974971304127197575579461562725431") 230

-- non-dyadic rationals
#guard toString (E "1/3" 150).1 == "0.2599210498948731647672106072782283505702514647"
#guard D (E "1/3" 150 .Floor) == ("0.2599210498948731647672106072782283505702514647", .lt)
#guard D (E "1/3" 150 .Ceiling) == ("0.259921049894873164767210607278228350570251465", .gt)
#guard toString (E "10/3" 150).1 == "9.07936839915898531813768485822582680456201172"
#guard D (E "10/3" 100 .Down) == ("9.07936839915898531813768485821", .lt)
#guard toString (E "-1/3" 150).1 == "-0.206299474015900262624147180363845869804253336"
#guard D (E "-1/3" 150 .Up) == ("-0.206299474015900262624147180363845869804253336", .lt)
#guard toString (E "1/10" 150).1 == "0.0717734625362931642130063250233420229063846049"
#guard toString (E "22/7" 150).1 == "7.83271610939049870119604310098675777060261281"
#guard toString (E "123456/1000" 150).1 == "14586770319557851483179373571866222400.85857387"
#guard D (E "123456/1000" 150 .Floor) == ("14586770319557851483179373571866222400.85857387", .lt)
#guard toString (pow2M1Rat (Q "1/3") 53) == "0.2599210498948732"
#guard toString (pow2M1Rat (Q "22/7") 200)
  == "7.83271610939049870119604310098675777060261280624099332411626"

-- small and tiny arguments: the cancellation is compensated
#guard toString (E "1/1000000" 150).1 == "6.93147420786507772636227407030377319511897222e-7"
#guard D (E "1/1000000" 150 .Floor) == ("6.93147420786507772636227407030377319511897222e-7", .lt)
#guard toString (E "-1/1000000" 150).1 == "-6.9314694033349385441556648171259373045235948e-7"
#guard D (E "-1/1000000" 150 .Ceiling) == ("-6.9314694033349385441556648171259373045235948e-7", .gt)
#guard toString (E "1/1000000000000000000000000000000000000000000000000000000000000" 53).1
  == "6.931471805599453e-61"
#guard toString (E "1/1000000000000000000000000000000000000000000000000000000000000" 300).1
  == "6.9314718055994530941723212145817656807550013436025525412068024971990058107040704915712649e-\
    61"
#guard D (E "-1/1000000000000000000000000000000000000000000000000000000000000" 300 .Ceiling)
  == ("-6.9314718055994530941723212145817656807550013436025525412067976926688666286898238205460016\
    3e-61", .gt)
#guard toString (pow2M1Rat (Q "-1/1000000") 53) == "-6.931469403334938e-7"

-- directed modes are ordered
#guard (E "5/7" 60 .Floor).2 == .lt
#guard (E "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E "5/7" 60 .Floor).1 (E "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E "-5/7" 60 .Floor).1 (E "-5/7" 60 .Ceiling).1 == some .lt

-- tiny rational arguments: `q = ±1/(3·2^1000)` against `±1/(3·2^100)` (the ordinary path)
private def tq (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< k)
private def rescale (r : AzFloat × Ordering) : AzFloat × Ordering :=
  (r.1 <<< AzInt.ofInt (-900), r.2)
#guard pow2M1RatPrecRound (tq 1000) 53 .Nearest == rescale (pow2M1RatPrecRound (tq 100) 53 .Nearest)
#guard pow2M1RatPrecRound (-(tq 1000)) 53 .Floor
  == rescale (pow2M1RatPrecRound (-(tq 100)) 53 .Floor)

-- a hugely negative exponent: the value is within `2^(−|x|/2)` above `−1`, and one test
-- (`expM1NearNegOne?`) rounds it at a cost independent of `|x|`
private def m1Above : AzFloat := X "-0.9999999999999999" 53
private def hugeNegX : AzRat :=
  -((AzNat.ofNat 1) <<< (100000 : Nat)).toAzRat * Q "1/3"
private def negX : AzRat := Q "-2001/2"
#guard D (pow2M1RatPrecRound hugeNegX 53 .Nearest) == ("-1.0", .lt)
#guard D (pow2M1RatPrecRound hugeNegX 53 .Floor) == ("-1.0", .lt)
#guard D (pow2M1RatPrecRound hugeNegX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard D (pow2M1RatPrecRound negX 53 .Nearest) == ("-1.0", .lt)
#guard D (pow2M1RatPrecRound negX 53 .Floor) == ("-1.0", .lt)
#guard D (pow2M1RatPrecRound negX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard expM1NearNegOne? true 126 53 .Nearest == none
#guard (expM1NearNegOne? true 127 53 .Nearest).map D == some ("-1.0", .lt)
#guard expM1NearNegOne? false 1000 53 .Nearest == none
