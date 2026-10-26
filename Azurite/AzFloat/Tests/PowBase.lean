/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow2
import Azurite.AzFloat.PowBase
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `u^x` with a natural base

Special values (`NaN`, the infinities, `0^x`, `1^x`, `u^0`), the exact rational powers
(`4^(1/2) = 2`, `4^(3/2) = 8`, `4^(−1/2) = 1/2`, `9^(5/2) = 243`, `16^(1/4) = 2`,
`16^(−3/4) = 1/8`, `10^2`, `10^(−2)`, `2^10`), agreement with `2^x` and with `√u`, the correctly
rounded values of `3^(1/2)`, `10^(±1/2)`, `7^(3/4)`, `7^(−7/4)`, `10^(13/8)`, `12345^(5/4)`,
`(2^64 − 1)^(1/4)`, `3^(201/2)`, `10^(1/1024)` and `6^(−201/4)` (references from a 200-digit
evaluation of `exp (x ln u)`), and the directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBasePrecRound u x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard E 5 nan 53 == (nan, .eq)
#guard E 0 nan 53 == (nan, .eq)
#guard E 5 pinf 53 == (infinity true, .eq)
#guard E 5 ninf 53 == (zero, .eq)
#guard E 0 pinf 53 == (zero, .eq)
#guard E 0 ninf 53 == (infinity true, .eq)
#guard E 1 pinf 53 == (nan, .eq)
#guard E 1 ninf 53 == (nan, .eq)
#guard E 5 zero 53 == (F "1" 53, .eq)
#guard E 0 zero 53 == (F "1" 53, .eq)
#guard E 1 zero 53 == (F "1" 53, .eq)
#guard E 5 zero 0 == (nan, .eq)
#guard E 0 (F "3/2" 53) 53 == (zero, .eq)
#guard E 0 (F "-3/2" 53) 53 == (infinity true, .eq)
#guard E 0 (F "-3/2" 53) 0 == (infinity true, .eq)
#guard E 1 (F "3/2" 53) 53 == (F "1" 53, .eq)
#guard E 1 (F "-1000" 53) 7 == (F "1" 7, .eq)
#guard E 1 (F "3/2" 53) 0 == (nan, .eq)
#guard E 7 (F "3/2" 53) 0 == (nan, .eq)
#guard powBase 5 nan == nan
#guard powBase 0 ninf == infinity true
#guard powBase 3 zero == one

-- exact rational powers
#guard E 4 (F "1/2" 53) 53 == (F "2" 53, .eq)
#guard E 4 (F "3/2" 53) 53 == (F "8" 53, .eq)
#guard E 4 (F "-1/2" 53) 53 == (F "1/2" 53, .eq)
#guard E 9 (F "5/2" 53) 53 == (F "243" 53, .eq)
#guard E 16 (F "1/4" 53) 1 == (F "2" 1, .eq)
#guard E 16 (F "1/4" 53) 53 == (F "2" 53, .eq)
#guard E 16 (F "-3/4" 53) 53 == (F "1/8" 53, .eq)
#guard E 8 (F "-1/3" 53) 53 != (F "1/2" 53, .eq)
#guard E 10 (F "2" 53) 53 == (F "100" 53, .eq)
#guard E 10 (F "-2" 53) 53 == ofAzRatRound (Q "1/100") 53 .Nearest
#guard E 10 (F "-2" 53) 53 .Floor == ofAzRatRound (Q "1/100") 53 .Floor
#guard E 2 (F "10" 53) 53 == (F "1024" 53, .eq)
#guard E 2 (F "-10" 53) 53 == (F "1/1024" 53, .eq)
#guard E 1000 (F "3" 53) 53 == (F "1000000000" 53, .eq)
#guard E 1000 (F "3" 53) 10 == ofAzRatRound (Q "1000000000") 10 .Nearest
#guard E 3 (F "40" 53) 20 == ofAzRatRound (Q "12157665459056928801") 20 .Nearest
#guard E 3 (F "40" 53) 20 .Ceiling == ofAzRatRound (Q "12157665459056928801") 20 .Ceiling
#guard E 3 (F "-40" 53) 20 .Floor == ofAzRatRound (Q "1/12157665459056928801") 20 .Floor
#guard powBase 4 (F "3/2" 53) == F "8" 53
#guard (E 1024 (F "1/10" 53) 53).2 != .eq

-- agreement with `2^x` and with `√u`
#guard E 2 (F "1/2" 53) 150 == pow2PrecRound (F "1/2" 53) 150 .Nearest
#guard E 2 (F "5/4" 53) 150 .Floor == pow2PrecRound (F "5/4" 53) 150 .Floor
#guard E 2 (F "-7/4" 53) 150 == pow2PrecRound (F "-7/4" 53) 150 .Nearest
#guard E 3 (F "1/2" 150) 150 == sqrt3PrecRound 150 .Nearest
#guard E 3 (F "1/2" 150) 150 .Ceiling == sqrt3PrecRound 150 .Ceiling
#guard E 18446744073709551615 (F "1/2" 53) 150
  == sqrtPrecRound (F "18446744073709551615" 64) 150 .Nearest

private def ref3Half : AzRat :=
  R ("1732050807568877293527446341505872366942805253810380628055806979451933016908800037081146" ++
    "1867572485756756261414154067030299699450949989524788116555120943736485280932319023055820" ++
    "679748201010846749232650") 199
private def ref10Half : AzRat :=
  R ("3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248" ++
    "1083793002951873472841528400551485488560304538800146905195967001539033449216571792599406" ++
    "591501534741133394841241") 199
private def ref10NegHalf : AzRat :=
  R ("3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248" ++
    "1083793002951873472841528400551485488560304538800146905195967001539033449216571792599406" ++
    "591501534741133394841241") 200
private def ref7 : AzRat :=
  R ("4303517070658850556514375138711314691200025713233276025604495913670522459831081688872831" ++
    "1009441498485973455211858037161792134691821826296899384493325968875905441126724090839046" ++
    "413317277551889215481407") 199
private def ref7Neg : AzRat :=
  R ("3319544003464868863696392541824000353098511820958158404464195068344238247291183711627229" ++
    "7302511295771802895700218560417954936338927506308224388174435742906389409040121183765851" ++
    "959961065336873926813435") 201
private def ref10_13_8 : AzRat :=
  R ("4216965034285822485690133595094063782509665771017425987502364996237549700438583247117483" ++
    "2270903931217185848535936982412758975140127195911165870310062869724031862689784819559173" ++
    "450721747861228292087665") 198
private def ref12345 : AzRat :=
  R ("1301259364227956217467057252019821366167841645659580520600532406590948867591519489517852" ++
    "6347717138181442374712918775483126879803081866392759543854083457548139351935976057021268" ++
    "409952229641380388382864") 194
private def refMax : AzRat :=
  R ("6553599999999999999911182158029987476764303907229871341387702924264731643549259686679410" ++
    "1035046943904774202189019052384579187667207386763101082321220128568844800853039026435621" ++
    "717882192234317979429267") 195
private def ref3Big : AzRat :=
  R ("8926600509867260257937586184844912024483791768563276262712739899740159884014984130985186" ++
    "9276324124346207549154621298220611841933672944829607148814117011412122902635423807667270" ++
    "314481837926106479972662") 152
private def ref10Small : AzRat :=
  R ("1002251148292912915465673638866571192454241130208227099208420545124889760120029589233262" ++
    "9046652501812633734239741938986063096780983259127238584639303012818152099944166693221004" ++
    "991826042083425634607519") 199
private def ref6NegBig : AzRat :=
  R ("7904959845789900093656644802174531570720683834627667172833089818115139240428147291775127" ++
    "6834914972192205286625873779158463520097011908977062940142145852280746425040102709583434" ++
    "212415242437428385719788") 239

-- correctly rounded irrational powers
#guard (E 3 (F "1/2" 53) 150).1 == ofAzRat ref3Half 150
#guard (E 10 (F "1/2" 53) 150).1 == ofAzRat ref10Half 150
#guard E 10 (F "1/2" 53) 150 .Floor == ofAzRatRound ref10Half 150 .Floor
#guard E 10 (F "1/2" 53) 150 .Ceiling == ofAzRatRound ref10Half 150 .Ceiling
#guard (E 10 (F "-1/2" 53) 150).1 == ofAzRat ref10NegHalf 150
#guard E 10 (F "-1/2" 53) 150 .Down == ofAzRatRound ref10NegHalf 150 .Down
#guard (E 7 (F "3/4" 53) 150).1 == ofAzRat ref7 150
#guard (E 7 (F "-7/4" 53) 150).1 == ofAzRat ref7Neg 150
#guard E 7 (F "-7/4" 53) 150 .Up == ofAzRatRound ref7Neg 150 .Up
#guard (E 10 (F "13/8" 53) 150).1 == ofAzRat ref10_13_8 150
#guard (E 12345 (F "5/4" 53) 150).1 == ofAzRat ref12345 150
#guard (E 18446744073709551615 (F "1/4" 53) 150).1 == ofAzRat refMax 150
#guard E 18446744073709551615 (F "1/4" 53) 150 .Floor == ofAzRatRound refMax 150 .Floor
#guard (E 3 (F "201/2" 53) 150).1 == ofAzRat ref3Big 150
#guard (E 10 (F "1/1024" 53) 150).1 == ofAzRat ref10Small 150
#guard (E 6 (F "-201/4" 53) 150).1 == ofAzRat ref6NegBig 150
#guard E 6 (F "-201/4" 53) 150 .Ceiling == ofAzRatRound ref6NegBig 150 .Ceiling
#guard powBase 10 (F "1/2" 53) == ofAzRat ref10Half 53
#guard powBase 7 (F "3/4" 200) == ofAzRat ref7 200

-- directed modes are ordered
#guard (E 7 (F "5/8" 53) 60 .Floor).2 == .lt
#guard (E 7 (F "5/8" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 (F "5/8" 53) 60 .Floor).1 (E 7 (F "5/8" 53) 60 .Ceiling).1 == some .lt
#guard partialCompare (E 7 (F "-5/8" 53) 60 .Floor).1 (E 7 (F "-5/8" 53) 60 .Ceiling).1
  == some .lt
