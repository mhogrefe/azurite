/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseM1
import Azurite.AzFloat.Exp2M1
import Azurite.AzFloat.Ln10Bracket
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `u^x − 1` with a natural base

Special values, the exact `r^n − 1` (`4^(1/2) − 1 = 1`, `4^(−1/2) − 1 = −1/2`,
`9^(5/2) − 1 = 242`, `16^(−3/4) − 1 = −7/8`, `10^2 − 1 = 99`, `10^(−2) − 1 = −99/100`,
`2^10 − 1 = 1023`), agreement with `2^x − 1` and with `u^x` at a higher precision, the correctly
rounded values of `3^(1/2) − 1`, `10^(−1/2) − 1`, `7^(3/4) − 1`, `10^(13/8) − 1`,
`12345^(5/4) − 1`, `(2^64 − 1)^(1/4) − 1`, `3^(201/2) − 1`, `6^(−201/4) − 1` and the small
arguments `10^(±2^(−30)) − 1`, `10^(1/1024) − 1`, `10^(±2^(−200)) − 1` (references from a
200-digit evaluation of `exp (x ln u) − 1`), and the directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBaseM1PrecRound u x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard E 5 nan 53 == (nan, .eq)
#guard E 5 pinf 53 == (infinity true, .eq)
#guard E 5 ninf 53 == (F "-1" 53, .eq)
#guard E 5 ninf 0 == (nan, .eq)
#guard E 0 pinf 53 == (F "-1" 53, .eq)
#guard E 0 ninf 53 == (infinity true, .eq)
#guard E 1 pinf 53 == (nan, .eq)
#guard E 1 ninf 53 == (nan, .eq)
#guard E 5 zero 53 == (zero, .eq)
#guard E 0 zero 0 == (zero, .eq)
#guard E 0 (F "3/2" 53) 53 == (F "-1" 53, .eq)
#guard E 0 (F "3/2" 53) 0 == (nan, .eq)
#guard E 0 (F "-3/2" 53) 53 == (infinity true, .eq)
#guard E 1 (F "3/2" 53) 53 == (zero, .eq)
#guard E 1 (F "3/2" 53) 0 == (zero, .eq)
#guard E 7 (F "3/2" 53) 0 == (nan, .eq)
#guard powBaseM1 5 nan == nan
#guard powBaseM1 0 ninf == infinity true
#guard powBaseM1 3 zero == zero

-- exact rational powers
#guard E 4 (F "1/2" 53) 53 == (F "1" 53, .eq)
#guard E 4 (F "-1/2" 53) 53 == (F "-1/2" 53, .eq)
#guard E 9 (F "5/2" 53) 53 == (F "242" 53, .eq)
#guard E 16 (F "-3/4" 53) 53 == (F "-7/8" 53, .eq)
#guard E 10 (F "2" 53) 53 == (F "99" 53, .eq)
#guard E 10 (F "-2" 53) 53 == ofAzRatRound (Q "-99/100") 53 .Nearest
#guard E 10 (F "-2" 53) 53 .Floor == ofAzRatRound (Q "-99/100") 53 .Floor
#guard E 2 (F "10" 53) 53 == (F "1023" 53, .eq)
#guard E 2 (F "10" 53) 4 == (F "1024" 4, .gt)
#guard E 3 (F "40" 53) 20 == ofAzRatRound (Q "12157665459056928800") 20 .Nearest
#guard E 3 (F "-40" 53) 20 .Ceiling
  == ofAzRatRound (Q "-12157665459056928800/12157665459056928801") 20 .Ceiling
#guard powBaseM1 4 (F "3/2" 53) == F "7" 53

-- agreement with `2^x − 1` and with `u^x` at a higher precision
#guard E 2 (F "1/2" 53) 150 == exp2M1PrecRound (F "1/2" 53) 150 .Nearest
#guard E 2 (F "-7/4" 53) 150 .Floor == exp2M1PrecRound (F "-7/4" 53) 150 .Floor
#guard E 2 (F "1/1073741824" 53) 150 == exp2M1PrecRound (F "1/1073741824" 53) 150 .Nearest
#guard (E 7 (F "3/4" 53) 100).1
  == (subPrecRound (powBasePrecRound 7 (F "3/4" 53) 300 .Nearest).1 one 100 .Nearest).1

private def ref3Half : AzRat :=
  R ("7320508075688772935274463415058723669428052538103806280558069794519330169088000370811461" ++
    "8675724857567562614141540670302996994509499895247881165551209437364852809323190230558206" ++
    "797482010108467492326502") 200
private def ref10NegHalf : AzRat :=
  R ("-683772233983162066800110645556728146628044486067478317314249514720740556136076177865575" ++
    "1891620699704812652715847159944851451143969546119985309480403299846096655078342820740059" ++
    "3408498465258866605158759") 200
private def ref7 : AzRat :=
  R ("3303517070658850556514375138711314691200025713233276025604495913670522459831081688872831" ++
    "1009441498485973455211858037161792134691821826296899384493325968875905441126724090839046" ++
    "413317277551889215481407") 199
private def ref10_13_8 : AzRat :=
  R ("4116965034285822485690133595094063782509665771017425987502364996237549700438583247117483" ++
    "2270903931217185848535936982412758975140127195911165870310062869724031862689784819559173" ++
    "450721747861228292087665") 198
private def ref12345 : AzRat :=
  R ("1301249364227956217467057252019821366167841645659580520600532406590948867591519489517852" ++
    "6347717138181442374712918775483126879803081866392759543854083457548139351935976057021268" ++
    "409952229641380388382864") 194
private def ref10Small : AzRat :=
  R ("2251148292912915465673638866571192454241130208227099208420545124889760120029589233262904" ++
    "6652501812633734239741938986063096780983259127238584639303012818152099944166693221004991" ++
    "826042083425634607518943") 202
private def ref10_30 : AzRat :=
  R ("2144449479377767429764042616358462669803678161945889735390668966125527249184772168607149" ++
    "0293963190370942207121096352479430933130169899994626242220038057783452403588059512738296" ++
    "442443395811661247034634") 208
private def ref10Neg30 : AzRat :=
  R ("-214444947477910387002206651585660521211069200818849763500060169055697851186109654178878" ++
    "7306978187188208682638843149114093400327911245983834701589131398223524808054300928402969" ++
    "1368472229086405682835716") 208
private def ref10Tiny : AzRat :=
  R ("1432902221227726401950524154919789403010516485816338776232401578888242180720860543563687" ++
    "2530765595097685058107101591279707804468531831189582990929621061379441990832010710260734" ++
    "087704668286178472072879") 259
private def ref10NegTiny : AzRat :=
  R ("-143290222122772640195052415491978940301051648581633877623239952567946658136868522121478" ++
    "5710316243027305850106989723936583482914533075582815892209414379221783570970337539349074" ++
    "2627456194723636368800082") 259
private def refMaxQuarter : AzRat :=
  R ("6553499999999999999911182158029987476764303907229871341387702924264731643549259686679410" ++
    "1035046943904774202189019052384579187667207386763101082321220128568844800853039026435621" ++
    "717882192234317979429267") 195
private def ref3Big : AzRat :=
  R ("8926600509867260257937586184844912024483791768553276262712739899740159884014984130985186" ++
    "9276324124346207549154621298220611841933672944829607148814117011412122902635423807667270" ++
    "314481837926106479972662") 152
private def ref6NegBig : AzRat :=
  R ("-999999999999999999999999999999999999999209504015421009990634335519782546842927931616537" ++
    "2332827166910181884860759571852708224872316508502780779471337412622084153647990298809102" ++
    "2937059857854147719253575") 200

-- correctly rounded irrational values
#guard (E 3 (F "1/2" 53) 150).1 == ofAzRat ref3Half 150
#guard E 3 (F "1/2" 53) 150 .Floor == ofAzRatRound ref3Half 150 .Floor
#guard E 3 (F "1/2" 53) 150 .Ceiling == ofAzRatRound ref3Half 150 .Ceiling
#guard (E 10 (F "-1/2" 53) 150).1 == ofAzRat ref10NegHalf 150
#guard E 10 (F "-1/2" 53) 150 .Down == ofAzRatRound ref10NegHalf 150 .Down
#guard (E 7 (F "3/4" 53) 150).1 == ofAzRat ref7 150
#guard (E 10 (F "13/8" 53) 150).1 == ofAzRat ref10_13_8 150
#guard (E 12345 (F "5/4" 53) 150).1 == ofAzRat ref12345 150
#guard (E 18446744073709551615 (F "1/4" 53) 150).1 == ofAzRat refMaxQuarter 150
#guard (E 3 (F "201/2" 53) 150).1 == ofAzRat ref3Big 150
#guard (E 6 (F "-201/4" 53) 150).1 == ofAzRat ref6NegBig 150
#guard E 6 (F "-201/4" 53) 150 .Up == ofAzRatRound ref6NegBig 150 .Up
#guard powBaseM1 10 (F "13/8" 53) == ofAzRat ref10_13_8 53
#guard powBaseM1 7 (F "3/4" 200) == ofAzRat ref7 200

-- small arguments: the cancellation is compensated
#guard (E 10 (F "1/1024" 53) 150).1 == ofAzRat ref10Small 150
#guard (E 10 (F "1/1073741824" 53) 150).1 == ofAzRat ref10_30 150
#guard E 10 (F "1/1073741824" 53) 150 .Floor == ofAzRatRound ref10_30 150 .Floor
#guard (E 10 (F "-1/1073741824" 53) 150).1 == ofAzRat ref10Neg30 150
#guard E 10 (F "-1/1073741824" 53) 150 .Ceiling == ofAzRatRound ref10Neg30 150 .Ceiling
#guard powBaseM1 10 (F "-1/1073741824" 53) == ofAzRat ref10Neg30 53

-- tiny arguments: `10^(±2^(−200)) − 1 ≈ ±ln 10 · 2^(−200)`
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard (E 10 tiny 53).1 == ofAzRat ref10Tiny 53
#guard (E 10 tiny 300).1 == ofAzRat ref10Tiny 300
#guard E 10 tiny 300 .Floor == ofAzRatRound ref10Tiny 300 .Floor
#guard (E 10 (-tiny) 300).1 == ofAzRat ref10NegTiny 300
#guard E 10 (-tiny) 300 .Ceiling == ofAzRatRound ref10NegTiny 300 .Ceiling
#guard (E 10 tiny 53).1 == (mulPrecRound tiny (ln10Bracket 200).1 53 .Nearest).1

-- directed modes are ordered
#guard (E 7 (F "5/8" 53) 60 .Floor).2 == .lt
#guard (E 7 (F "5/8" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 (F "5/8" 53) 60 .Floor).1 (E 7 (F "5/8" 53) 60 .Ceiling).1 == some .lt
#guard partialCompare (E 7 (F "-5/8" 53) 60 .Floor).1 (E 7 (F "-5/8" 53) 60 .Ceiling).1
  == some .lt
