/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBasePrecRound u x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E 5 nan 53) == ("NaN", .eq)
#guard D (E 0 nan 53) == ("NaN", .eq)
#guard D (E 5 pinf 53) == ("Infinity", .eq)
#guard D (E 5 ninf 53) == ("0.0", .eq)
#guard D (E 0 pinf 53) == ("0.0", .eq)
#guard D (E 0 ninf 53) == ("Infinity", .eq)
-- `1^x = 1` for every `x`, even `NaN` and `±∞` (MPFR)
#guard D (E 1 pinf 53) == ("1.0", .eq)
#guard D (E 1 ninf 53) == ("1.0", .eq)
#guard D (E 1 nan 53) == ("1.0", .eq)
#guard D (E 1 nan 7 .Floor) == ("1.0", .eq)
#guard D (E 1 nan 0) == ("NaN", .eq)
#guard D (E 1 pinf 0) == ("NaN", .eq)
#guard toString (powBase 1 nan) == "1.0"
#guard toString (powBase 1 ninf) == "1.0"
#guard D (E 5 zero 53) == ("1.0", .eq)
#guard D (E 0 zero 53) == ("1.0", .eq)
#guard D (E 1 zero 53) == ("1.0", .eq)
#guard D (E 5 zero 0) == ("NaN", .eq)
#guard D (E 0 (X "1.5" 53) 53) == ("0.0", .eq)
#guard D (E 0 (X "-1.5" 53) 53) == ("Infinity", .eq)
#guard D (E 0 (X "-1.5" 53) 0) == ("Infinity", .eq)
#guard D (E 1 (X "1.5" 53) 53) == ("1.0", .eq)
#guard D (E 1 (X "-1000" 53) 7) == ("1.0", .eq)
#guard D (E 1 (X "1.5" 53) 0) == ("NaN", .eq)
#guard D (E 7 (X "1.5" 53) 0) == ("NaN", .eq)
#guard toString (powBase 5 nan) == "NaN"
#guard toString (powBase 0 ninf) == "Infinity"
#guard toString (powBase 3 zero) == "1.0"

-- exact rational powers
#guard D (E 4 (X "0.5" 53) 53) == ("2.0", .eq)
#guard D (E 4 (X "1.5" 53) 53) == ("8.0", .eq)
#guard D (E 4 (X "-0.5" 53) 53) == ("0.5", .eq)
#guard D (E 9 (X "2.5" 53) 53) == ("243.0", .eq)
#guard D (E 16 (X "0.25" 53) 1) == ("2.0", .eq)
#guard D (E 16 (X "0.25" 53) 53) == ("2.0", .eq)
#guard D (E 16 (X "-0.75" 53) 53) == ("0.125", .eq)
#guard E 8 (X "-0.3333333333333333" 53) 53 != (X "0.5" 53, .eq)
#guard D (E 10 (X "2" 53) 53) == ("1.0e2", .eq)
#guard D (E 10 (X "-2" 53) 53) == ("0.01", .gt)
#guard D (E 10 (X "-2" 53) 53 .Floor) == ("0.009999999999999998", .lt)
#guard D (E 2 (X "10" 53) 53) == ("1024.0", .eq)
#guard D (E 2 (X "-10" 53) 53) == ("0.0009765625", .eq)
#guard D (E 1000 (X "3" 53) 53) == ("1.0e9", .eq)
#guard D (E 1000 (X "3" 53) 10) == ("1.0e9", .gt)
#guard D (E 3 (X "40" 53) 20) == ("1.215766e19", .lt)
#guard D (E 3 (X "40" 53) 20 .Ceiling) == ("1.215768e19", .gt)
#guard D (E 3 (X "-40" 53) 20 .Floor) == ("8.22526e-20", .lt)
#guard toString (powBase 4 (X "1.5" 53)) == "8.0"
#guard (E 1024 (X "0.1" 53) 53).2 != .eq

-- agreement with `2^x` and with `√u`
#guard E 2 (X "0.5" 53) 150 == pow2PrecRound (X "0.5" 53) 150 .Nearest
#guard E 2 (X "1.25" 53) 150 .Floor == pow2PrecRound (X "1.25" 53) 150 .Floor
#guard E 2 (X "-1.75" 53) 150 == pow2PrecRound (X "-1.75" 53) 150 .Nearest
#guard E 3 (X "0.5" 150) 150 == sqrt3PrecRound 150 .Nearest
#guard E 3 (X "0.5" 150) 150 .Ceiling == sqrt3PrecRound 150 .Ceiling
#guard E 18446744073709551615 (X "0.5" 53) 150
  == sqrtPrecRound (X "18446744073709551615" 64) 150 .Nearest

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
#guard toString ((E 3 (X "0.5" 53) 150).1) == "1.732050807568877293527446341505872366942805254"
#guard toString ((E 10 (X "0.5" 53) 150).1) == "3.16227766016837933199889354443271853371955514"
#guard D (E 10 (X "0.5" 53) 150 .Floor) == ("3.162277660168379331998893544432718533719555137", .lt)
#guard D (E 10 (X "0.5" 53) 150 .Ceiling) == ("3.16227766016837933199889354443271853371955514", .gt)
#guard toString ((E 10 (X "-0.5" 53) 150).1) == "0.316227766016837933199889354443271853371955514"
#guard D (E 10 (X "-0.5" 53) 150 .Down) == ("0.3162277660168379331998893544432718533719555137", .lt)
#guard toString ((E 7 (X "0.75" 53) 150).1) == "4.303517070658850556514375138711314691200025714"
#guard toString ((E 7 (X "-1.75" 53) 150).1) == "0.0331954400346486886369639254182400035309851182"
#guard D (E 7 (X "-1.75" 53) 150 .Up) == ("0.0331954400346486886369639254182400035309851182", .gt)
#guard toString ((E 10 (X "1.625" 53) 150).1) == "42.1696503428582248569013359509406378250966577"
#guard toString ((E 12345 (X "1.25" 53) 150).1) == "130125.9364227956217467057252019821366167841646"
#guard (E 18446744073709551615 (X "0.25" 53) 150).1 == ofAzRat refMax 150
#guard E 18446744073709551615 (X "0.25" 53) 150 .Floor == ofAzRatRound refMax 150 .Floor
#guard toString ((E 3 (X "100.5" 53) 150).1) == "8.92660050986726025793758618484491202448379177e47"
#guard toString ((E 10 (X "0.0009765625" 53) 150).1) ==
    "1.002251148292912915465673638866571192454241131"
#guard toString ((E 6 (X "-50.25" 53) 150).1) == "7.90495984578990009365664480217453157072068384e-4\
  0"
#guard D (E 6 (X "-50.25" 53) 150 .Ceiling) == ("7.90495984578990009365664480217453157072068384e-40\
  ", .gt)
#guard toString (powBase 10 (X "0.5" 53)) == "3.1622776601683795"
#guard toString (powBase 7 (X "0.75" 200)) ==
    "4.303517070658850556514375138711314691200025713233276\
  025604494"

-- directed modes are ordered
#guard (E 7 (X "0.625" 53) 60 .Floor).2 == .lt
#guard (E 7 (X "0.625" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 (X "0.625" 53) 60 .Floor).1 (E 7 (X "0.625" 53) 60 .Ceiling).1 == some
    .lt
#guard partialCompare (E 7 (X "-0.625" 53) 60 .Floor).1 (E 7 (X "-0.625" 53) 60 .Ceiling).1
  == some .lt

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard powBasePrecRound 10 tinyX 53 .Nearest == (X "1" 53, .lt)
#guard powBasePrecRound 10 tinyX 53 .Floor == (X "1" 53, .lt)
#guard powBasePrecRound 10 tinyX 53 .Ceiling == (aboveOne, .gt)
#guard powBasePrecRound 10 (-tinyX) 53 .Nearest == (X "1" 53, .gt)
#guard powBasePrecRound 10 (-tinyX) 53 .Floor == (belowOne, .lt)
#guard powBasePrecRound 10 (-tinyX) 53 .Ceiling == (X "1" 53, .gt)

-- exact powers of a power-of-two base with huge exponents: only the odd part of the
-- (left-aligned) significand is powered, so `2^k` is a shift, not a `64 k`-bit power
private def powBaseExpo (u : UInt64) (n : Int) (p : Nat) : Option Int × Ordering :=
  let r := powBasePrecRound u (ofAzInt (AzInt.ofInt n)) p .Nearest
  (r.1.exponent?.map (·.toInt), r.2)
#guard powBaseExpo 2 59011072 2 == (some 59011073, .eq)
#guard powBaseExpo 8 1033216 30 == (some 3099649, .eq)
#guard powBaseExpo 8 (-371200) 13 == (some (-1113599), .eq)

-- huge exponents: the starting precision of Ziv's loop is logarithmic in the exponent of `x`
-- (`lnMulW₀`), only the bracket of `x ln u` works at `p + e` bits; references from 700-digit
-- decimal arithmetic (`u^x = sig · 2^shift` with the 53-bit significand rounded to nearest)
private def big10 : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838752")).num.toNat
  ((X "6652583142272300" 53) <<< AzInt.ofInt (sh), .gt)
private def big10Neg : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838857")).num.toNat
  ((X "6097604244814858" 53) <<< AzInt.ofInt (-sh), .gt)
private def big7Half : AzFloat × Ordering :=
  let sh : Int := (Q ("1429670743642759167967541555146598396066131518940442486861224786649148"
    ++ "6205945014501641681117")).num.toNat
  ((X "5830758831792293" 53) <<< AzInt.ofInt (sh), .gt)
private def big10K : AzFloat × Ordering :=
  let sh : Int := (Q ("3559474546125688097888749891311268280803030836889066085434085705866357"
    ++ "9654905565667573402117123831097190952436189486273642075435448175445398"
    ++ "5284277067328506910520976703894954997864912893728468090593464779075863"
    ++ "4959954372251970503160189587153683416380628010576355627013788365862628"
    ++ "8980639316732982265838")).num.toNat
  ((X "6240855869311329" 53) <<< AzInt.ofInt (sh), .lt)
private def x200 : AzFloat := (X "3" 53) <<< AzInt.ofInt 200
private def xHalf : AzFloat := ofAzRat ((AzNat.ofNat (5 * 2 ^ 300 + 1)).toAzRat * Q "1/2") 310
#guard E 10 x200 53 == big10
#guard E 10 (-x200) 53 == big10Neg
#guard E 7 xHalf 53 == big7Half
#guard E 10 ((X "1" 53) <<< AzInt.ofInt 1000) 53 == big10K
#guard (E 10 x200 53 .Floor).2 == .lt && (E 10 x200 53 .Ceiling).1 == big10.1
-- an exact power with a huge exponent: `100^x = 10^(2x)`, `4^x = 2^(2x)`
#guard E 100 ((X "3" 53) <<< AzInt.ofInt 199) 53 == big10
#guard E 4 x200 53 == ((setPrecRound (powerOf2 (AzInt.ofInt (3 * 2 ^ 201))) 53 .Nearest).1, .eq)

-- the exactness test reads the dyadic structure: more than six fractional bits are never
-- converted to a rational (`powBaseExactSkip`), fewer may give an exact power
#guard powBaseExactSkip (X "0.0078125" 53) && !powBaseExactSkip (X "0.015625" 53)
#guard powBaseExactSkip ((X "3" 53) <<< AzInt.ofInt (-(2 ^ 60)))
#guard !powBaseExactSkip x200
#guard powBaseExact? ((X "3" 53) <<< AzInt.ofInt (-(2 ^ 60))) (AzNat.ofNat 10) == none
#guard powBaseExact? (X "0.09375" 53) (AzNat.ofNat (2 ^ 32)) == some (AzNat.ofNat 2, AzInt.ofInt 3)
#guard powBaseExact? (X "0.046875" 53) (AzNat.ofNat (2 ^ 32)) == none
#guard powBaseExact? (X "-2.5" 53) (AzNat.ofNat 9) == some (AzNat.ofNat 3, AzInt.ofInt (-5))
#guard E (4294967296 : UInt64) (X "0.09375" 53) 53 == (X "8" 53, .eq)
#guard lnMulW₀ 4 == 92 && lnMulW₀ 1000 == 176 && lnMulW₀ (2 ^ 40) == 356
