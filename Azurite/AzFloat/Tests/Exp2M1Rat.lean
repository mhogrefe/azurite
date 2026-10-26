/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp2M1
import Azurite.AzFloat.Exp2M1Rat
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `2^q − 1` of a rational

`2^0 − 1 = 0`, the exact `2^n − 1` for integers `n`, agreement with the float `2^x − 1` on dyadic
rationals, the correctly rounded values of `2^q − 1` at `q = ±1/3, 10/3, 1/10, 22/7, 123.456,
±10^(−6), ±10^(−60)` (references from a 200-digit evaluation of `exp (q ln 2) − 1`), and the
directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := exp2M1RatPrecRound (Q q) p m

-- zero, integers and precision `0`
#guard E "0" 53 == (zero, .eq)
#guard E "0" 0 == (nan, .eq)
#guard E "1/3" 0 == (nan, .eq)
#guard E "1" 1 == (one, .eq)
#guard E "-1" 1 == (F "-1/2" 1, .eq)
#guard E "3" 53 == (F "7" 53, .eq)
#guard E "-3" 53 == (F "-7/8" 53, .eq)
#guard E "100" 150 == (F "1267650600228229401496703205375" 150, .eq)
#guard E "100" 10 == (F "1267650600228229401496703205376" 10, .gt)
#guard E "-100" 10 == (F "-1" 10, .lt)
#guard E "-100" 10 .Ceiling == (F "-1023/1024" 10, .gt)
#guard exp2M1Rat (Q "10") 53 == F "1023" 53

-- agreement with the float `2^x − 1` on dyadic rationals
#guard E "1/2" 150 == exp2M1PrecRound (F "1/2" 53) 150 .Nearest
#guard E "1/2" 150 .Floor == exp2M1PrecRound (F "1/2" 53) 150 .Floor
#guard E "-7/4" 150 == exp2M1PrecRound (F "-7/4" 53) 150 .Nearest
#guard E "12345/4096" 100 .Ceiling == exp2M1PrecRound (F "12345/4096" 53) 100 .Ceiling
#guard E "1/1073741824" 150 == exp2M1PrecRound (F "1/1073741824" 53) 150 .Nearest
#guard E "-1/1073741824" 150 .Up == exp2M1PrecRound (F "-1/1073741824" 53) 150 .Up

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
#guard (E "1/3" 150).1 == ofAzRat refThird 150
#guard E "1/3" 150 .Floor == ofAzRatRound refThird 150 .Floor
#guard E "1/3" 150 .Ceiling == ofAzRatRound refThird 150 .Ceiling
#guard (E "10/3" 150).1 == ofAzRat refTen3 150
#guard E "10/3" 100 .Down == ofAzRatRound refTen3 100 .Down
#guard (E "-1/3" 150).1 == ofAzRat refNegThird 150
#guard E "-1/3" 150 .Up == ofAzRatRound refNegThird 150 .Up
#guard (E "1/10" 150).1 == ofAzRat refTenth 150
#guard (E "22/7" 150).1 == ofAzRat ref227 150
#guard (E "123456/1000" 150).1 == ofAzRat refBig 150
#guard E "123456/1000" 150 .Floor == ofAzRatRound refBig 150 .Floor
#guard exp2M1Rat (Q "1/3") 53 == ofAzRat refThird 53
#guard exp2M1Rat (Q "22/7") 200 == ofAzRat ref227 200

-- small and tiny arguments: the cancellation is compensated
#guard (E "1/1000000" 150).1 == ofAzRat refMicro 150
#guard E "1/1000000" 150 .Floor == ofAzRatRound refMicro 150 .Floor
#guard (E "-1/1000000" 150).1 == ofAzRat refNegMicro 150
#guard E "-1/1000000" 150 .Ceiling == ofAzRatRound refNegMicro 150 .Ceiling
#guard (E "1/1000000000000000000000000000000000000000000000000000000000000" 53).1
  == ofAzRat refTiny 53
#guard (E "1/1000000000000000000000000000000000000000000000000000000000000" 300).1
  == ofAzRat refTiny 300
#guard E "-1/1000000000000000000000000000000000000000000000000000000000000" 300 .Ceiling
  == ofAzRatRound refNegTiny 300 .Ceiling
#guard exp2M1Rat (Q "-1/1000000") 53 == ofAzRat refNegMicro 53

-- directed modes are ordered
#guard (E "5/7" 60 .Floor).2 == .lt
#guard (E "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E "5/7" 60 .Floor).1 (E "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E "-5/7" 60 .Floor).1 (E "-5/7" 60 .Ceiling).1 == some .lt
