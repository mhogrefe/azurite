/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp2
import Azurite.AzFloat.Exp2Rat
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `2^q` of a rational

The exact powers of two, agreement with the float `2^x` on dyadic rationals and with `√2` at
`1/2`, and the correctly rounded values of `2^(1/3)`, `2^(10/3)`, `2^(−1/3)`, `2^(1/10)`,
`2^(22/7)` and `2^(123.456)` (references from a 120-digit evaluation of `exp (q ln 2)`), and the
directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := exp2RatPrecRound (Q q) p m

-- exact powers of two and precision `0`
#guard E "0" 53 == (F "1" 53, .eq)
#guard E "0" 1 == (one, .eq)
#guard E "10" 1 == (F "1024" 1, .eq)
#guard E "-3" 1 == (F "1/8" 1, .eq)
#guard E "100" 5 == (F "1267650600228229401496703205376" 5, .eq)
#guard E "-100" 5 == (F "1/1267650600228229401496703205376" 5, .eq)
#guard E "1" 0 == (nan, .eq)
#guard E "1/3" 0 == (nan, .eq)
#guard exp2Rat (Q "64") 53 == F "18446744073709551616" 53

-- agreement with the float `2^x` on dyadic rationals and with `√2`
#guard E "1/2" 150 == exp2PrecRound (F "1/2" 53) 150 .Nearest
#guard E "1/2" 150 == sqrt2PrecRound 150 .Nearest
#guard E "1/2" 150 .Floor == sqrt2PrecRound 150 .Floor
#guard E "-7/4" 150 == exp2PrecRound (F "-7/4" 53) 150 .Nearest
#guard E "12345/4096" 100 .Ceiling == exp2PrecRound (F "12345/4096" 53) 100 .Ceiling
#guard E "201/2" 150 == exp2PrecRound (F "201/2" 53) 150 .Nearest

private def refThird : AzRat :=
  R ("1259921049894873164767210607278228350570251464701507980081975112155299676513959483729396" ++
    "56243625509415431025603561566526") 119
private def refTen3 : AzRat :=
  R ("1007936839915898531813768485822582680456201171761206384065580089724239741211167586983517" ++
    "24994900407532344820482849253220") 118
private def refNegThird : AzRat :=
  R ("7937005259840997373758528196361541301957466639499265049041428809126082528121095866367721" ++
    "06631110478511467380840661008952") 120
private def refTenth : AzRat :=
  R ("1071773462536293164213006325023342022906384604977556783482780668144245438837468954516907" ++
    "44398368776986639303654813952108") 119
private def ref227 : AzRat :=
  R ("8832716109390498701196043100986757770602612806240993324116259713136850583043047845732786" ++
    "31909041604117517727252463945004") 119
private def refBig : AzRat :=
  R ("1458677031955785148317937357186622240185857387481039782818850322498201376355228161031215" ++
    "90074084764410955103515173008885") 82

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
#guard exp2Rat (Q "1/3") 53 == ofAzRat refThird 53
#guard exp2Rat (Q "22/7") 200 == ofAzRat ref227 200

-- directed modes are ordered
#guard (E "5/7" 60 .Floor).2 == .lt
#guard (E "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E "5/7" 60 .Floor).1 (E "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E "-5/7" 60 .Floor).1 (E "-5/7" 60 .Ceiling).1 == some .lt
