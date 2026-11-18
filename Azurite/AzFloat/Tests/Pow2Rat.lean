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
import Azurite.AzFloat.Pow2Rat
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := pow2RatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- exact powers of two and precision `0`
#guard D (E "0" 53) == ("1.0", .eq)
#guard D (E "0" 1) == ("1.0", .eq)
#guard D (E "10" 1) == ("1.0e3", .eq)
#guard D (E "-3" 1) == ("0.1", .eq)
#guard D (E "100" 5) == ("1.3e30", .eq)
#guard D (E "-100" 5) == ("8.0e-31", .eq)
#guard D (E "1" 0) == ("NaN", .eq)
#guard D (E "1/3" 0) == ("NaN", .eq)
#guard toString (pow2Rat (Q "64") 53) == "1.8446744073709552e19"

-- agreement with the float `2^x` on dyadic rationals and with `√2`
#guard E "1/2" 150 == pow2PrecRound (X "0.5" 53) 150 .Nearest
#guard E "1/2" 150 == sqrt2PrecRound 150 .Nearest
#guard E "1/2" 150 .Floor == sqrt2PrecRound 150 .Floor
#guard E "-7/4" 150 == pow2PrecRound (X "-1.75" 53) 150 .Nearest
#guard E "12345/4096" 100 .Ceiling == pow2PrecRound (X "3.013916015625" 53) 100 .Ceiling
#guard E "201/2" 150 == pow2PrecRound (X "100.5" 53) 150 .Nearest

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
#guard toString (E "1/3" 150).1 == "1.259921049894873164767210607278228350570251465"
#guard D (E "1/3" 150 .Floor) == ("1.259921049894873164767210607278228350570251465", .lt)
#guard D (E "1/3" 150 .Ceiling) == ("1.259921049894873164767210607278228350570251466", .gt)
#guard toString (E "10/3" 150).1 == "10.07936839915898531813768485822582680456201172"
#guard D (E "10/3" 100 .Down) == ("10.07936839915898531813768485821", .lt)
#guard toString (E "-1/3" 150).1 == "0.793700525984099737375852819636154130195746664"
#guard D (E "-1/3" 150 .Up) == ("0.7937005259840997373758528196361541301957466645", .gt)
#guard toString (E "1/10" 150).1 == "1.071773462536293164213006325023342022906384605"
#guard toString (E "22/7" 150).1 == "8.8327161093904987011960431009867577706026128"
#guard toString (E "123456/1000" 150).1 == "14586770319557851483179373571866222401.85857387"
#guard D (E "123456/1000" 150 .Floor) == ("14586770319557851483179373571866222401.85857387", .lt)
#guard toString (pow2Rat (Q "1/3") 53) == "1.2599210498948732"
#guard toString (pow2Rat (Q "22/7") 200) == "8.8327161093904987011960431009867577706026128062409933\
  2411626"

-- directed modes are ordered
#guard (E "5/7" 60 .Floor).2 == .lt
#guard (E "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E "5/7" 60 .Floor).1 (E "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E "-5/7" 60 .Floor).1 (E "-5/7" 60 .Ceiling).1 == some .lt

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (pow2RatPrecRound tinyQ 53 .Nearest) == ("1.0", .lt)
#guard D (pow2RatPrecRound tinyQ 53 .Floor) == ("1.0", .lt)
#guard D (pow2RatPrecRound tinyQ 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (pow2RatPrecRound (-tinyQ) 53 .Nearest) == ("1.0", .gt)
#guard D (pow2RatPrecRound (-tinyQ) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (pow2RatPrecRound (-tinyQ) 53 .Ceiling) == ("1.0", .gt)
