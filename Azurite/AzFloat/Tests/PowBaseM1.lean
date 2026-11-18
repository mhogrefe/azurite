/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Ln10Bracket
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Pow2M1
import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseM1
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (u : UInt64) (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  powBaseM1PrecRound u x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E 5 nan 53) == ("NaN", .eq)
#guard D (E 5 pinf 53) == ("Infinity", .eq)
#guard D (E 5 ninf 53) == ("-1.0", .eq)
#guard D (E 5 ninf 0) == ("NaN", .eq)
#guard D (E 0 pinf 53) == ("-1.0", .eq)
#guard D (E 0 ninf 53) == ("Infinity", .eq)
-- `1^x − 1 = 0` for every `x`, even `NaN` and `±∞` (MPFR's `1^x = 1`)
#guard D (E 1 pinf 53) == ("0.0", .eq)
#guard D (E 1 ninf 53) == ("0.0", .eq)
#guard D (E 1 nan 53) == ("0.0", .eq)
#guard D (E 1 nan 0) == ("0.0", .eq)
#guard toString (powBaseM1 1 nan) == "0.0"
#guard D (E 5 zero 53) == ("0.0", .eq)
#guard D (E 0 zero 0) == ("0.0", .eq)
#guard D (E 0 (X "1.5" 53) 53) == ("-1.0", .eq)
#guard D (E 0 (X "1.5" 53) 0) == ("NaN", .eq)
#guard D (E 0 (X "-1.5" 53) 53) == ("Infinity", .eq)
#guard D (E 1 (X "1.5" 53) 53) == ("0.0", .eq)
#guard D (E 1 (X "1.5" 53) 0) == ("0.0", .eq)
#guard D (E 7 (X "1.5" 53) 0) == ("NaN", .eq)
#guard toString (powBaseM1 5 nan) == "NaN"
#guard toString (powBaseM1 0 ninf) == "Infinity"
#guard toString (powBaseM1 3 zero) == "0.0"

-- exact rational powers
#guard D (E 4 (X "0.5" 53) 53) == ("1.0", .eq)
#guard D (E 4 (X "-0.5" 53) 53) == ("-0.5", .eq)
#guard D (E 9 (X "2.5" 53) 53) == ("242.0", .eq)
#guard D (E 16 (X "-0.75" 53) 53) == ("-0.875", .eq)
#guard D (E 10 (X "2" 53) 53) == ("99.0", .eq)
#guard D (E 10 (X "-2" 53) 53) == ("-0.99", .gt)
#guard D (E 10 (X "-2" 53) 53 .Floor) == ("-0.9900000000000001", .lt)
#guard D (E 2 (X "10" 53) 53) == ("1023.0", .eq)
#guard D (E 2 (X "10" 53) 4) == ("1.0e3", .gt)
#guard D (E 3 (X "40" 53) 20) == ("1.215766e19", .lt)
#guard D (E 3 (X "-40" 53) 20 .Ceiling) == ("-0.999999", .gt)
#guard toString (powBaseM1 4 (X "1.5" 53)) == "7.0"

-- agreement with `2^x − 1` and with `u^x` at a higher precision
#guard E 2 (X "0.5" 53) 150 == pow2M1PrecRound (X "0.5" 53) 150 .Nearest
#guard E 2 (X "-1.75" 53) 150 .Floor == pow2M1PrecRound (X "-1.75" 53) 150 .Floor
#guard E 2 (X "0.000000000931322574615478515625" 53) 150 == pow2M1PrecRound (X
    "0.000000000931322574615478515625" 53) 150 .Nearest
#guard (E 7 (X "0.75" 53) 100).1
  == (subPrecRound (powBasePrecRound 7 (X "0.75" 53) 300 .Nearest).1 one 100 .Nearest).1

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
#guard toString ((E 3 (X "0.5" 53) 150).1) == "0.732050807568877293527446341505872366942805254"
#guard D (E 3 (X "0.5" 53) 150 .Floor) == ("0.732050807568877293527446341505872366942805254", .lt)
#guard D (E 3 (X "0.5" 53) 150 .Ceiling) == ("0.7320508075688772935274463415058723669428052544\
  ", .gt)
#guard toString ((E 10 (X "-0.5" 53) 150).1) == "-0.683772233983162066800110645556728146628044486"
#guard D (E 10 (X "-0.5" 53) 150 .Down) == ("-0.6837722339831620668001106455567281466280444856\
  ", .gt)
#guard toString ((E 7 (X "0.75" 53) 150).1) == "3.303517070658850556514375138711314691200025714"
#guard toString ((E 10 (X "1.625" 53) 150).1) == "41.1696503428582248569013359509406378250966577"
#guard toString ((E 12345 (X "1.25" 53) 150).1) == "130124.9364227956217467057252019821366167841646"
#guard (E 18446744073709551615 (X "0.25" 53) 150).1 == ofAzRat refMaxQuarter 150
#guard toString ((E 3 (X "100.5" 53) 150).1) == "8.92660050986726025793758618484491202448379177e47"
#guard toString ((E 6 (X "-50.25" 53) 150).1) == "-0.999999999999999999999999999999999999999209504"
#guard D (E 6 (X "-50.25" 53) 150 .Up) == ("-0.9999999999999999999999999999999999999992095044", .lt)
#guard toString (powBaseM1 10 (X "1.625" 53)) == "41.169650342858226"
#guard toString (powBaseM1 7 (X "0.75" 200)) ==
    "3.3035170706588505565143751387113146912000257132332\
  76025604497"

-- small arguments: the cancellation is compensated
#guard toString ((E 10 (X "0.0009765625" 53) 150).1) ==
    "0.0022511482929129154656736388665711924542411302\
  09"
#guard toString ((E 10 (X "0.000000000931322574615478515625" 53) 150).1) ==
    "2.1444494793777674297640426163584626698036\
  78161e-9"
#guard D (E 10 (X "0.000000000931322574615478515625" 53) 150 .Floor) ==
    ("2.1444494793777674297640426163584626698036781\
  61e-9", .lt)
#guard toString ((E 10 (X "-0.000000000931322574615478515625" 53) 150).1) ==
    "-2.14444947477910387002206651585660521211\
  0692007e-9"
#guard D (E 10 (X "-0.000000000931322574615478515625" 53) 150 .Ceiling) ==
    ("-2.144449474779103870022066515856605212110\
  692007e-9", .gt)
#guard toString (powBaseM1 10 (X "-0.000000000931322574615478515625" 53)) ==
    "-2.1444494747791037e-9"

-- tiny arguments: `10^(±2^(−200)) − 1 ≈ ±ln 10 · 2^(−200)`
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard (E 10 tiny 53).1 == ofAzRat ref10Tiny 53
#guard (E 10 tiny 300).1 == ofAzRat ref10Tiny 300
#guard E 10 tiny 300 .Floor == ofAzRatRound ref10Tiny 300 .Floor
#guard (E 10 (-tiny) 300).1 == ofAzRat ref10NegTiny 300
#guard E 10 (-tiny) 300 .Ceiling == ofAzRatRound ref10NegTiny 300 .Ceiling
#guard (E 10 tiny 53).1 == (mulPrecRound tiny (ln10Bracket 200).1 53 .Nearest).1

-- directed modes are ordered
#guard (E 7 (X "0.625" 53) 60 .Floor).2 == .lt
#guard (E 7 (X "0.625" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E 7 (X "0.625" 53) 60 .Floor).1 (E 7 (X "0.625" 53) 60 .Ceiling).1 == some
    .lt
#guard partialCompare (E 7 (X "-0.625" 53) 60 .Floor).1 (E 7 (X "-0.625" 53) 60 .Ceiling).1
  == some .lt

-- tiny arguments: `b^x − 1 ≈ x ln b` is rounded from a bracket at `p + 72` bits whatever the
-- exponent; the result at `2^(−2^30)` is that at `2^(−100)` (the ordinary path) rescaled
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def x100 : AzFloat := (X "1" 53) <<< AzInt.ofInt (-100)
private def rescale (r : AzFloat × Ordering) : AzFloat × Ordering :=
  (r.1 <<< (tinyE + AzInt.ofInt 100), r.2)
#guard powBaseM1PrecRound 10 tinyX 53 .Nearest
  == rescale (powBaseM1PrecRound 10 x100 53 .Nearest)
#guard powBaseM1PrecRound 10 (-tinyX) 53 .Floor
  == rescale (powBaseM1PrecRound 10 (-x100) 53 .Floor)
#guard powBaseM1PrecRound 3 tinyX 80 .Ceiling == rescale (powBaseM1PrecRound 3 x100 80 .Ceiling)

-- huge exponents: the starting precision of Ziv's loop is logarithmic in the exponent of `x`
-- (`lnMulW₀`), only the bracket of `x ln u` works at `p + e` bits; references from 700-digit
-- decimal arithmetic (`u^x = sig · 2^shift` with the 53-bit significand rounded to nearest)
private def big10 : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838752")).num.toNat
  ((X "6652583142272300" 53) <<< AzInt.ofInt (sh), .gt)
private def big7Half : AzFloat × Ordering :=
  let sh : Int := (Q ("1429670743642759167967541555146598396066131518940442486861224786649148"
    ++ "6205945014501641681117")).num.toNat
  ((X "5830758831792293" 53) <<< AzInt.ofInt (sh), .gt)
private def x200 : AzFloat := (X "3" 53) <<< AzInt.ofInt 200
private def xHalf : AzFloat := ofAzRat ((AzNat.ofNat (5 * 2 ^ 300 + 1)).toAzRat * Q "1/2") 310
#guard E 10 x200 53 == big10
#guard E 7 xHalf 53 == big7Half
#guard E 10 (-x200) 53 == (X "-1" 53, .lt)
#guard E 10 (-x200) 53 .Ceiling == (X "-0.9999999999999999" 53, .gt)
#guard E 100 ((X "3" 53) <<< AzInt.ofInt 199) 53 == big10

-- a hugely negative exponent: the value is within `2^(−|x|/2)` above `−1`, and one test
-- (`expM1NearNegOne?`) rounds it at a cost independent of `|x|`
private def m1Above : AzFloat := X "-0.9999999999999999" 53
private def hugeNegX : AzFloat := (X "-3" 53) <<< AzInt.ofInt (2 ^ 40)
private def negX : AzFloat := X "-1000.5" 53
#guard powBaseM1PrecRound 10 hugeNegX 53 .Nearest == (X "-1" 53, .lt)
#guard powBaseM1PrecRound 10 hugeNegX 53 .Floor == (X "-1" 53, .lt)
#guard powBaseM1PrecRound 10 hugeNegX 53 .Ceiling == (m1Above, .gt)
#guard powBaseM1PrecRound 10 negX 53 .Nearest == (X "-1" 53, .lt)
#guard powBaseM1PrecRound 10 negX 53 .Floor == (X "-1" 53, .lt)
#guard powBaseM1PrecRound 10 negX 53 .Ceiling == (m1Above, .gt)
#guard expM1NearNegOne? true 126 53 .Nearest == none
#guard expM1NearNegOne? true 127 53 .Nearest == some (X "-1" 53, .lt)
#guard expM1NearNegOne? false 1000 53 .Nearest == none
